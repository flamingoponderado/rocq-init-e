#!/usr/bin/env python3
'''Real negative integration checks; never creates a weaker positive challenge.'''
import argparse,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
HEADER='''From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.InitE Require Import NatE SubmissionModel Challenge.
From SubmissionLiterals Require Import Values.
'''
CASES={
 'wrong-statement':('submittedCode','claimedScore','Definition certificate : True := I.','comparison.log'),
 'wrong-rom':('[n2w 0]','claimedScore','Axiom certificate : Certificate submission claimedScore.','comparison.log'),
 'wrong-score':('submittedCode','finite 1','Axiom certificate : Certificate submission (finite 1).','comparison.log'),
 'extra-axiom':('submittedCode','claimedScore','Axiom certificate : Certificate submission claimedScore.','kernel.log')}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--case',choices=CASES,action='append');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 if a.output.exists():raise SystemExit('output already exists')
 a.output.mkdir(parents=True)
 results={}
 for name in a.case or list(CASES):
  code,score,proof,stage=CASES[name]
  package=a.output/(name+'-package');package.mkdir()
  (package/'rom.bin').write_bytes(bytes([19,0,0,0]));(package/'claim.json').write_text('{"K":"infinity"}\n')
  (package/'Solution.v').write_text(HEADER+'Definition submission : Submission := Build_Submission '+code+' ('+score+') 0 [] 0 [].\n'+proof+'\n')
  replay=a.output/(name+'-replay')
  run=subprocess.run(['python3',str(ROOT/'verifier/verify.py'),str(package),'--output',str(replay),'--timeout','900'],text=True,capture_output=True)
  (a.output/(name+'.log')).write_text(run.stdout+run.stderr)
  if run.returncode!=1 or 'VERIFIED' in run.stdout or not (replay/stage).is_file():
   raise SystemExit('negative case missed intended stage: '+name)
  detail=(replay/stage).read_text()
  if stage=='comparison.log' and 'Signature components for field certificate do not match' not in detail:
   raise SystemExit('wrong rejection for '+name)
  if stage=='kernel.log' and 'Candidate.Solution.certificate' not in detail:
   raise SystemExit('missing candidate axiom audit')
  results[name]={'rejected':True,'gate':stage}
 (a.output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(results))
