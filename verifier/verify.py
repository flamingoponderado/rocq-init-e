#!/usr/bin/env python3
'''Isolated, fail-closed verification against the immutable init-e statement.
Preparation/build is performed by the operator; this command never reseals.
'''
import argparse,hashlib,json,resource,shutil,subprocess,os,stat,tempfile,re
from pathlib import Path
from policy import Rejected,check_source,literal_module,check_kernel_context,parse_claim,check_source_text
ROOT=Path(__file__).resolve().parents[1]
PROOF=ROOT/'_build/default/theories'
GALETTE=ROOT/'_build/default/galette-theories'
SEAL=ROOT/'.artifacts/verifier-seal.json'

def read_regular(path,limit=None):
 """Open every component without following links; read one regular-file fd."""
 path=Path(path).absolute()
 fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY)
 try:
  for part in path.parts[1:-1]:
   child=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
   os.close(fd);fd=child
  filefd=os.open(path.name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=fd)
  with os.fdopen(filefd,'rb') as stream:
   before=os.fstat(stream.fileno())
   if not stat.S_ISREG(before.st_mode):raise Rejected('input is not a regular file: '+str(path))
   if limit is not None and before.st_size>limit:raise Rejected('input exceeds size bound')
   data=stream.read() if limit is None else stream.read(limit+1)
   after=os.fstat(stream.fileno())
   if (before.st_size,before.st_mtime_ns,before.st_ctime_ns)!=(after.st_size,after.st_mtime_ns,after.st_ctime_ns):
    raise Rejected('input changed while reading: '+str(path))
   if limit is not None and len(data)>limit:raise Rejected('input exceeds size bound')
   return data
 finally:os.close(fd)

def sha(path):return hashlib.sha256(read_regular(path)).hexdigest()

def check_seal(snapshot=None):
 if not SEAL.is_file():raise Rejected('operator seal missing; run scripts/seal_verifier.py after verified build')
 raw=read_regular(SEAL)
 def unique_pairs(pairs):
  result={}
  for key,value in pairs:
   if key in result:raise Rejected('duplicate operator seal key')
   result[key]=value
  return result
 seal=json.loads(raw,object_pairs_hook=unique_pairs)
 if (not isinstance(seal,dict) or set(seal)!={'files','rocq_sha256'}
     or not isinstance(seal['files'],dict)
     or any(not isinstance(k,str) or not isinstance(v,str) or not re.fullmatch(r'[0-9a-f]{64}',v)
            for k,v in seal['files'].items())
     or not isinstance(seal['rocq_sha256'],str)
     or not re.fullmatch(r'[0-9a-f]{64}',seal['rocq_sha256'])):
  raise Rejected('invalid operator seal schema')
 inventory=set()
 for base,ext in [('theories','.v'),('vendor/galette/theories','.v'),('_build/default/theories','.vo'),('_build/default/galette-theories','.vo')]:
  inventory.update(str(p.relative_to(ROOT)) for p in (ROOT/base).rglob('*'+ext) if p.is_file())
 inventory.update(['dune','dune-project','reference-lock.json','verifier/verify.py','verifier/policy.py'])
 if inventory!=set(seal['files']):raise Rejected('trusted file inventory differs from seal')
 for name,digest in seal['files'].items():
  path=ROOT/name
  data=read_regular(path)
  if hashlib.sha256(data).hexdigest()!=digest:raise Rejected('trusted file changed: '+name)
  if snapshot is not None:
   target_name=None
   if name.endswith('.vo'):target_name=name
   elif name.startswith('theories/') and name.endswith('.v'):
    target_name='_build/default/'+name
   elif name.startswith('vendor/galette/theories/') and name.endswith('.v'):
    target_name='_build/default/galette-theories/'+name.removeprefix('vendor/galette/theories/')
   if target_name is not None:
    dest=snapshot/target_name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 launcher=shutil.which('rocq')
 if not launcher:raise Rejected('Rocq launcher missing')
 rocq=Path(launcher).resolve()
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
   check_source_text(read_regular(p).decode());paths.append(rel)
  elif not p.is_dir():raise Rejected('unsupported package file type: '+str(rel))
 if Path('Solution.v') not in paths:raise Rejected('Solution.v is missing')
 return paths

def sandbox(rocq,work,mounts,args,timeout,log,trusted=None):
 proof,galette=trusted or (PROOF,GALETTE)
 prefix=rocq.parent.parent
 if ROOT.is_relative_to(prefix) or Path('/tmp').is_relative_to(prefix):
  raise Rejected('toolchain prefix would expose verifier workspace or private temporary files')
 cmd=['bwrap','--unshare-all','--die-with-parent','--new-session','--clearenv',
  '--ro-bind','/usr','/usr','--ro-bind','/lib','/lib','--ro-bind','/lib64','/lib64',
  '--ro-bind',str(prefix),str(prefix),'--proc','/proc','--dev','/dev','--tmpfs','/tmp',
  '--dir','/work','--dir','/work/literals','--dir','/work/candidate','--dir','/work/check','--setenv','HOME','/tmp','--setenv','PATH',str(prefix/'bin')+':/usr/bin',
  '--ro-bind',str(proof),'/trusted/init-e','--ro-bind',str(galette),'/trusted/galette']
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
 # Hostile sources and writable compiler outputs live in an operator-owned,
 # unpredictable directory. Publish logs only after all sandbox processes exit.
 if timeout<=0:raise Rejected('timeout must be positive')
 with tempfile.TemporaryDirectory(prefix='init-e-verifier-',dir='/tmp') as tmp:
  private=Path(tmp);trusted=private/'trusted';trusted.mkdir()
  rocq,seal_digest=check_seal(trusted)
  replay=private/'replay'
  output=Path(output).absolute()
  if output.exists() or output.is_symlink():raise Rejected('output directory already exists')
  try:return _verify(package,replay,timeout,rocq,seal_digest,trusted)
  finally:
   if replay.exists():shutil.copytree(replay,output,symlinks=True)

def _verify(package,output,timeout,rocq,seal_digest,trusted):
 package=Path(package).absolute()
 if package.is_symlink():raise Rejected('package symlinks are forbidden')
 if not package.is_dir():raise Rejected('package is not a directory')
 paths=sources(package)
 rom=package/'rom.bin'
 if not rom.is_file() or rom.is_symlink():raise Rejected('rom.bin is missing or a symlink')
 if not 0<rom.stat().st_size<=134217728:raise Rejected('ROM length outside challenge admission bound')
 claim=package/'claim.json'
 if not claim.is_file() or claim.is_symlink():raise Rejected('claim.json is missing or a symlink')
 score=parse_claim(read_regular(claim,1048576).decode())
 code=read_regular(rom,134217728)
 if output.exists():raise Rejected('output directory already exists')
 output.mkdir(parents=True)
 candidate=output/'candidate';literals=output/'literals';checker=output/'check'
 for d in (candidate,literals,checker):d.mkdir()
 for rel in paths:
  dest=candidate/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(read_regular(package/rel))
  check_source(dest)
 (literals/'Values.v').write_text(literal_module(code,score))
 def run(*args):
  return sandbox(*args,trusted=(trusted/'_build/default/theories',trusted/'_build/default/galette-theories'))
 mounts=[(literals,'/work/literals',True)]
 run(rocq,'/work/literals',mounts,['compile',*LOAD,'Values.v'],timeout,output/'literals.log')
 mounts=[(literals,'/work/literals',False),(candidate,'/work/candidate',True)]
 listing=run(rocq,'/work/candidate',mounts,
  ['dep','-sort',*LOAD,*[str(p) for p in paths]],timeout,output/'dependencies.log')
 submitted={str(p) for p in paths}
 ordered=[p for p in listing.split() if p in submitted]
 if len(ordered)!=len(paths) or set(ordered)!={str(p) for p in paths}:
  raise Rejected('dependency sorter did not return exactly the submitted sources')
 for i,p in enumerate(ordered):
  run(rocq,'/work/candidate',mounts,['compile',*LOAD,p],timeout,output/f'compile-{i}.log')
 (checker/'Check.v').write_text('''Require InitE.InitE.VerificationCore.
Require SubmissionLiterals.Values.
Require Candidate.Solution.
Module Gate := InitE.InitE.VerificationCore.Check(SubmissionLiterals.Values).
Module Result := Gate.Accept(Candidate.Solution).
''')
 mounts=[(literals,'/work/literals',False),(candidate,'/work/candidate',False),(checker,'/work/check',True)]
 run(rocq,'/work/check',mounts,['compile',*LOAD,'Check.v'],timeout,output/'comparison.log')
 mounts=[(literals,'/work/literals',False),(candidate,'/work/candidate',False),(checker,'/work/check',False)]
 context=run(rocq,'/work/check',mounts,
  ['check','-bytecode-compiler','yes','-silent','-o',*LOAD,
   'Verified.Check'],timeout,output/'kernel.log')
 axioms=check_kernel_context(context)
 final_rocq,final_digest=check_seal()
 if final_rocq!=rocq:raise Rejected('Rocq launcher changed during verification')
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
