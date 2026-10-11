#!/usr/bin/env python3
'''Isolated, fail-closed verification against the immutable init-e statement.
Preparation/build is performed by the operator; this command never reseals.
'''
import argparse,hashlib,json,resource,shutil,subprocess
from pathlib import Path
from policy import Rejected,read_claim,check_source,literal_module,check_kernel_context
ROOT=Path(__file__).resolve().parents[1]
PROOF=ROOT/'_build/default/theories'
GALETTE=ROOT/'_build/default/galette-theories'
SEAL=ROOT/'.artifacts/verifier-seal.json'

def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()

def check_seal():
 if not SEAL.is_file():raise Rejected('operator seal missing; run scripts/seal_verifier.py after verified build')
 raw=SEAL.read_bytes()
 seal=json.loads(raw)
 inventory=set()
 for base,ext in [('theories','.v'),('vendor/galette/theories','.v'),('_build/default/theories','.vo'),('_build/default/galette-theories','.vo')]:
  inventory.update(str(p.relative_to(ROOT)) for p in (ROOT/base).rglob('*'+ext) if p.is_file())
 inventory.update(['dune','dune-project','reference-lock.json','verifier/verify.py','verifier/policy.py'])
 if inventory!=set(seal['files']):raise Rejected('trusted file inventory differs from seal')
 for name,digest in seal['files'].items():
  path=ROOT/name
  if not path.is_file() or sha(path)!=digest:raise Rejected('trusted file changed: '+name)
 rocq=Path(shutil.which('rocq') or '')
 if not rocq.is_file() or sha(rocq)!=seal['rocq_sha256']:raise Rejected('Rocq launcher differs from seal')
 return rocq,hashlib.sha256(raw).hexdigest()

def sources(package):
 import re
 paths=[]
 for p in package.rglob('*'):
  if p.is_symlink():raise Rejected('package symlinks are forbidden')
  rel=p.relative_to(package)
  if p.is_file() and rel.as_posix() in {'rom.bin','claim.json'}:continue
  if any(not re.fullmatch('[A-Za-z_][A-Za-z_0-9]*(?:\\.v)?',x) for x in rel.parts):
   raise Rejected('unsupported package path: '+str(rel))
  if p.is_file():
   if p.suffix!='.v':raise Rejected('package may contain only Rocq sources, rom.bin and claim.json')
   check_source(p);paths.append(rel)
 if Path('Solution.v') not in paths:raise Rejected('Solution.v is missing')
 return paths

def sandbox(rocq,work,mounts,args,timeout,log):
 prefix=rocq.parent.parent
 cmd=['bwrap','--unshare-all','--die-with-parent','--new-session','--clearenv',
  '--ro-bind','/usr','/usr','--ro-bind','/lib','/lib','--ro-bind','/lib64','/lib64',
  '--ro-bind',str(prefix),str(prefix),'--proc','/proc','--dev','/dev','--tmpfs','/tmp',
  '--dir','/work','--dir','/work/literals','--dir','/work/candidate','--dir','/work/check','--setenv','HOME','/tmp','--setenv','PATH',str(prefix/'bin')+':/usr/bin',
  '--ro-bind',str(PROOF),'/trusted/init-e','--ro-bind',str(GALETTE),'/trusted/galette']
 for host,inside,writable in mounts:
  cmd+=['--bind' if writable else '--ro-bind',str(host),inside]
 cmd+=['--chdir',work,str(rocq),*args]
 def limits():
  resource.setrlimit(resource.RLIMIT_AS,(112*1024**3,112*1024**3))
  resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 try:
  with log.open('w') as stream:
   run=subprocess.run(cmd,text=True,stdout=stream,stderr=subprocess.STDOUT,
    timeout=timeout,preexec_fn=limits)
 except subprocess.TimeoutExpired as e:
  raise Rejected('verification stage timed out; see '+str(log)) from e
 output=log.read_text()
 if run.returncode:raise Rejected('verification stage failed; see '+str(log))
 return output

LOAD=['-Q','/trusted/galette','Galette','-Q','/trusted/init-e','InitE',
 '-Q','/work/literals','SubmissionLiterals','-Q','/work/candidate','Candidate',
 '-Q','/work/check','Verified']

def verify(package,output,timeout):
 rocq,seal_digest=check_seal()
 package=package.resolve();output=output.resolve()
 if not package.is_dir():raise Rejected('package is not a directory')
 paths=sources(package)
 rom=package/'rom.bin'
 if not rom.is_file() or rom.is_symlink():raise Rejected('rom.bin is missing or a symlink')
 if not 0<rom.stat().st_size<=134217728:raise Rejected('ROM length outside challenge admission bound')
 claim=package/'claim.json'
 if not claim.is_file() or claim.is_symlink():raise Rejected('claim.json is missing or a symlink')
 score=read_claim(claim)
 if output.exists():raise Rejected('output directory already exists')
 output.mkdir(parents=True)
 candidate=output/'candidate';literals=output/'literals';checker=output/'check'
 for d in (candidate,literals,checker):d.mkdir()
 for rel in paths:
  dest=candidate/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(package/rel,dest)
  check_source(dest)
 code=rom.read_bytes()
 (literals/'Values.v').write_text(literal_module(code,score))
 mounts=[(literals,'/work/literals',True)]
 sandbox(rocq,'/work/literals',mounts,['compile',*LOAD,'Values.v'],timeout,output/'literals.log')
 mounts=[(literals,'/work/literals',False),(candidate,'/work/candidate',True)]
 listing=sandbox(rocq,'/work/candidate',mounts,
  ['dep','-sort',*LOAD,*[str(p) for p in paths]],timeout,output/'dependencies.log')
 submitted={str(p) for p in paths}
 ordered=[p for p in listing.split() if p in submitted]
 if len(ordered)!=len(paths) or set(ordered)!={str(p) for p in paths}:
  raise Rejected('dependency sorter did not return exactly the submitted sources')
 for i,p in enumerate(ordered):
  sandbox(rocq,'/work/candidate',mounts,['compile',*LOAD,p],timeout,output/f'compile-{i}.log')
 (checker/'Check.v').write_text('''Require InitE.InitE.VerificationCore.
Require SubmissionLiterals.Values.
Require Candidate.Solution.
Module Gate := InitE.InitE.VerificationCore.Check(SubmissionLiterals.Values).
Module Result := Gate.Accept(Candidate.Solution).
''')
 mounts=[(literals,'/work/literals',False),(candidate,'/work/candidate',False),(checker,'/work/check',True)]
 sandbox(rocq,'/work/check',mounts,['compile',*LOAD,'Check.v'],timeout,output/'comparison.log')
 mounts=[(literals,'/work/literals',False),(candidate,'/work/candidate',False),(checker,'/work/check',False)]
 context=sandbox(rocq,'/work/check',mounts,
  ['check','-bytecode-compiler','yes','-silent','-o',*LOAD,
   'Verified.Check'],timeout,output/'kernel.log')
 axioms=check_kernel_context(context)
 _,final_digest=check_seal()
 if final_digest!=seal_digest:raise Rejected('operator seal changed during verification')
 result={'verified':True,'rom_bytes':len(code),'rom_sha256':hashlib.sha256(code).hexdigest(),
  'score_literal':score,'axioms':axioms,'kernel_exit':0,'seal_sha256':seal_digest}
 (output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
 return result

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('package',type=Path);p.add_argument('--output',type=Path,required=True)
 p.add_argument('--timeout',type=int,default=10800);a=p.parse_args()
 try:
  verify(a.package,a.output,a.timeout)
 except (Rejected,OSError,ValueError) as e:
  print('REJECTED: '+str(e));raise SystemExit(1)
 print('VERIFIED')
