#!/usr/bin/env python3
'''Operator-only sealing of a freshly built, checked trusted installation.'''
import hashlib,json,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['theories/InitE/VerificationCore.v','_build/default/theories/InitE/VerificationCore.vo']:
 if not (ROOT/name).is_file():raise SystemExit('missing verified build file '+name)
paths=set()
for base,ext in [('theories','.v'),('vendor/galette/theories','.v'),('_build/default/theories','.vo'),('_build/default/galette-theories','.vo')]:
 paths.update(p for p in (ROOT/base).rglob('*'+ext) if p.is_file())
paths.update(ROOT/x for x in ['dune','dune-project','reference-lock.json','verifier/verify.py','verifier/policy.py'])
rocq=Path(shutil.which('rocq'))
seal={'files':{str(p.relative_to(ROOT)):sha(p) for p in sorted(paths)},'rocq_sha256':sha(rocq)}
(ROOT/'.artifacts').mkdir(exist_ok=True)
(ROOT/'.artifacts/verifier-seal.json').write_text(json.dumps(seal,indent=2)+'\n')
print('Sealed '+str(len(paths))+' trusted source/artifact files')
