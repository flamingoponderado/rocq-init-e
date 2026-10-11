import tempfile,unittest
from pathlib import Path
from policy import AXIOMS,Rejected,check_kernel_context,read_claim,check_source,literal_module
ROOT=Path(__file__).resolve().parents[1]
class PolicyTests(unittest.TestCase):
 def test_real_kernel_context(self):
  self.assertEqual(set(check_kernel_context((ROOT/'docs/challenge-kernel-check.log').read_text())),AXIOMS)
 def test_injected_axiom(self):
  log=(ROOT/'docs/challenge-kernel-check.log').read_text().replace('* Axioms:','* Axioms:\n    Candidate.Solution.false_axiom')
  with self.assertRaises(Rejected):check_kernel_context(log)
 def test_unsafe_kernel_flags(self):
  for name in ['Constants/Inductives relying on unsafe (co)fixpoints','Inductives whose positivity is assumed','Constants/Inductives relying on type-in-type']:
   log=(ROOT/'docs/challenge-kernel-check.log').read_text().replace('* '+name+': <none>','* '+name+': Candidate.Solution.bad')
   with self.assertRaises(Rejected):check_kernel_context(log)
 def test_claim_is_literal(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp)/'claim.json'
   for text in ['{"K": true}','{"K": -1}','{"K": 0.0}','{"K": "finite 0. Proof. exact I. Qed."}','{"K":0,"K":1}','{"K":"infinity","statement":"True"}']:
    p.write_text(text)
    with self.assertRaises(Rejected):read_claim(p)
   p.write_text('{"K":123}');self.assertEqual(read_claim(p),'finite 123')
   p.write_text('{"K":"infinity"}');self.assertEqual(read_claim(p),'infinity')
 def test_grammar_and_ml_injection(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp)/'Solution.v'
   for text in ['Declare ML Module "bad".','Notation "Certificate" := True.','Module Export InitE := Fake.','Load "outside.v".','Redirect "Bindings.v" Print nat.']:
    p.write_text(text)
    with self.assertRaises(Rejected):check_source(p)
   p.write_text('(* Notation (* nested *) *) Definition x := ReducedTypes.Load.');check_source(p)
 def test_wrapped_load_and_nested_comments(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp)/'Solution.v'
   for text in ['Fail (* outer (* inner *) tail *) Load "x".',
                'Time Timeout 2 Load "x".', 'Fail Add Rec LoadPath "x".',
                'Remove LoadPath "x".', 'Add ML Path "x".',
                'Definition x := 0.Load "x".']:
    p.write_text(text)
    with self.subTest(text=text),self.assertRaises(Rejected):check_source(p)
   p.write_text('(* Load "x". (* nested *) *) Definition x := "Load". Definition y := ReducedTypes.Load.')
   check_source(p)
 def test_ambiguous_kernel_context(self):
  log=(ROOT/'docs/challenge-kernel-check.log').read_text()
  for extra in ['* Axioms: Candidate.bad',
                '* Constants/Inductives relying on type-in-type: Candidate.bad',
                '* Theory: Set is impredicative', '* Unknown audit section: <none>']:
   with self.subTest(extra=extra),self.assertRaises(Rejected):
    check_kernel_context(log+'\n'+extra+'\n')
  with self.assertRaises(Rejected):check_kernel_context(log+log)
  # A closed proof with no assumptions is still admissible.
  start=log.index('* Axioms:');end=log.index('* Constants/',start)
  self.assertEqual(check_kernel_context(log[:start]+'* Axioms: <none>\n\n'+log[end:]),[])
 def test_rom_bounds(self):
  with self.assertRaises(Rejected):literal_module(b'','infinity')
  text=literal_module(bytes([0,255,19]),'finite 12')
  self.assertIn('[n2w 0;n2w 255;n2w 19]',text)
  self.assertIn('claimedScore : NatE := finite 12.',text)
if __name__=='__main__':unittest.main()
