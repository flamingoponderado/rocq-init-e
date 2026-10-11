import hashlib,json,os,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import verify
from policy import Rejected

class FileBoundaryTests(unittest.TestCase):
 def test_no_follow_at_every_component(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);real=root/'real';real.mkdir();(real/'file').write_bytes(b'original')
   (root/'link').symlink_to(real,target_is_directory=True)
   (root/'filelink').symlink_to(real/'file')
   for path in [root/'link/file',root/'filelink']:
    with self.subTest(path=path),self.assertRaises(OSError):verify.read_regular(path)
 def test_fifo_and_size_bound(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);os.mkfifo(root/'fifo')
   with self.assertRaises(Rejected):verify.read_regular(root/'fifo')
   (root/'file').write_bytes(b'1234')
   with self.assertRaises(Rejected):verify.read_regular(root/'file',3)
 def test_detect_concurrent_write(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp)/'file';p.write_bytes(b'original');fstat=os.fstat;calls=0
   def mutate(fd):
    nonlocal calls
    calls+=1
    if calls==2:p.write_bytes(b'changed and longer')
    return fstat(fd)
   with patch.object(verify.os,'fstat',side_effect=mutate),self.assertRaises(Rejected):
    verify.read_regular(p)
 def test_replaced_source_is_checked_after_copy(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);package=root/'package';package.mkdir()
   (package/'rom.bin').write_bytes(b'x');(package/'claim.json').write_text('{"K":0}')
   source=package/'Solution.v';source.write_text('Definition x := 0.')
   original=verify.sources
   def replace(package):
    paths=original(package);source.write_text('Declare ML Module "evil".');return paths
   with patch.object(verify,'sources',side_effect=replace),patch.object(verify,'sandbox') as sandbox:
    with self.assertRaises(Rejected):
     verify._verify(package,root/'replay',1,Path('/tool/bin/rocq'),'digest',root/'trusted')
    sandbox.assert_not_called()
 def test_seal_snapshots_exact_hashed_bytes(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);files={}
   names=['theories/A.v','vendor/galette/theories/B.v',
    '_build/default/theories/A.vo','_build/default/galette-theories/B.vo',
    'dune','dune-project','reference-lock.json','verifier/verify.py','verifier/policy.py']
   for name in names:
    p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(name.encode())
    files[name]=hashlib.sha256(p.read_bytes()).hexdigest()
   launcher=root/'tool/bin/rocq';launcher.parent.mkdir(parents=True);launcher.write_bytes(b'tool')
   seal=root/'seal.json';seal.write_text(json.dumps({'files':files,'rocq_sha256':hashlib.sha256(b'tool').hexdigest()}))
   snapshot=root/'snapshot'
   with patch.object(verify,'ROOT',root),patch.object(verify,'SEAL',seal),patch.object(verify.shutil,'which',return_value=str(launcher)):
    verify.check_seal(snapshot)
    self.assertEqual((snapshot/'_build/default/theories/A.v').read_bytes(),b'theories/A.v')
    self.assertEqual((snapshot/'_build/default/galette-theories/B.v').read_bytes(),b'vendor/galette/theories/B.v')
    vo=root/'_build/default/theories/A.vo';vo.write_bytes(b'changed')
    self.assertEqual((snapshot/'_build/default/theories/A.vo').read_bytes(),b'_build/default/theories/A.vo')
    with self.assertRaises(Rejected):verify.check_seal()
 def test_private_replay_uses_captured_rom_and_publishes(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);package=root/'package';package.mkdir()
   (package/'rom.bin').write_bytes(b'x');(package/'claim.json').write_text('{"K":0}')
   (package/'Solution.v').write_text('Definition x := 0.')
   private_roots=[]
   def seal(snapshot=None):
    if snapshot is not None:
     for name in ['theories','galette-theories']:(snapshot/'_build/default'/name).mkdir(parents=True)
    return Path('/tool/bin/rocq'),'seal-digest'
   def stage(rocq,work,mounts,args,timeout,log,trusted=None):
    private_roots.append(log.parent)
    self.assertNotEqual(log.parent,root/'output')
    self.assertTrue(all(str(p).startswith(str(log.parent.parent)) for p in trusted))
    (package/'rom.bin').write_bytes(b'changed')
    log.write_text('stage log')
    if args[0]=='dep':return 'Solution.v'
    if args[0]=='check':return (verify.ROOT/'docs/challenge-kernel-check.log').read_text()
    return ''
   with patch.object(verify,'check_seal',side_effect=seal),patch.object(verify,'sandbox',side_effect=stage):
    result=verify.verify(package,root/'output',1)
   self.assertEqual(result['rom_sha256'],hashlib.sha256(b'x').hexdigest())
   self.assertIn('n2w 120',(root/'output/literals/Values.v').read_text())
   self.assertTrue((root/'output/result.json').is_file())
   self.assertTrue(all(not p.exists() for p in private_roots))
 def test_reseal_during_run_rejects_without_result(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);package=root/'package';package.mkdir()
   (package/'rom.bin').write_bytes(b'x');(package/'claim.json').write_text('{"K":0}')
   (package/'Solution.v').write_text('Definition x := 0.')
   def seal(snapshot=None):
    return Path('/tool/bin/rocq'),'initial' if snapshot is not None else 'changed'
   def stage(rocq,work,mounts,args,timeout,log,trusted=None):
    log.write_text('stage log')
    if args[0]=='dep':return 'Solution.v'
    if args[0]=='check':return (verify.ROOT/'docs/challenge-kernel-check.log').read_text()
    return ''
   with patch.object(verify,'check_seal',side_effect=seal),patch.object(verify,'sandbox',side_effect=stage):
    with self.assertRaises(Rejected):verify.verify(package,root/'output',1)
   self.assertTrue((root/'output/kernel.log').exists())
   self.assertFalse((root/'output/result.json').exists())
 def test_unsafe_toolchain_prefix_is_rejected(self):
  with patch.object(verify.subprocess,'run') as run:
   for rocq in [Path('/bin/rocq'),verify.ROOT/'bin/rocq',Path('/tmp/bin/rocq')]:
    with self.subTest(rocq=rocq),self.assertRaises(Rejected):
     verify.sandbox(rocq,'/work',[],[],1,Path('/unused'))
   run.assert_not_called()
 def test_malformed_and_duplicate_seal_keys(self):
  with tempfile.TemporaryDirectory() as tmp:
   seal=Path(tmp)/'seal'
   for text in ['[]','{"files":[],"rocq_sha256":"bad"}',
                '{"files":{},"files":{},"rocq_sha256":"bad"}']:
    seal.write_text(text)
    with patch.object(verify,'SEAL',seal),self.assertRaises(Rejected):verify.check_seal()
 def test_sandbox_mounts_snapshots_and_clears_environment(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);log=root/'log';commands=[]
   def run(cmd,**kwargs):
    commands.append(cmd);kwargs['stdout'].write('ok')
    return type('Result',(),{'returncode':0})()
   with patch.object(verify.subprocess,'run',side_effect=run):
    verify.sandbox(Path('/tool/bin/rocq'),'/work/check',[(root,'/work/check',False)],
     ['check'],1,log,trusted=(root/'proof',root/'galette'))
   cmd=commands[0]
   for flag in ['--unshare-all','--clearenv','--die-with-parent','--new-session']:self.assertIn(flag,cmd)
   self.assertNotIn(str(verify.PROOF),cmd)
   i=cmd.index('/trusted/init-e');self.assertEqual(cmd[i-2:i],['--ro-bind',str(root/'proof')])
   i=cmd.index('/work/check',cmd.index('/trusted/galette'))
   self.assertEqual(cmd[i-2:i],['--ro-bind',str(root)])

if __name__=='__main__':unittest.main()
