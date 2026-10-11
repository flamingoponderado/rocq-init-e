"""Literal/package checks and authoritative rocqchk context policy.
These checks support the fixed challenge; they never change its premises.
"""
import json,re
from pathlib import Path
AXIOMS=frozenset({
 'Stdlib.Logic.ClassicalEpsilon.constructive_indefinite_description',
 'Stdlib.Logic.ProofIrrelevance.proof_irrelevance',
 'Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep',
 'Stdlib.Logic.PropExtensionality.propositional_extensionality',
 'Stdlib.Logic.Classical_Prop.classic'})
UNSAFE_SECTIONS=(
 'Constants/Inductives relying on type-in-type',
 'Constants/Inductives relying on unsafe (co)fixpoints',
 'Inductives whose positivity is assumed')
FORBIDDEN=frozenset({'Notation','Infix','Reserved','Declare','Redirect',
 'Extraction','Separate','Recursive','Cd','Include','Plugin','Export'})
class Rejected(ValueError): pass

def read_claim(path):
 return parse_claim(Path(path).read_text())

def parse_claim(text):
 def unique_pairs(pairs):
  result={}
  for k,v in pairs:
   if k in result: raise Rejected('duplicate claim key')
   result[k]=v
  return result
 try:
  value=json.loads(text,object_pairs_hook=unique_pairs,
   parse_constant=lambda _: (_ for _ in ()).throw(Rejected('nonfinite JSON number')))
 except (ValueError,UnicodeError) as e: raise Rejected('invalid claim: '+str(e)) from e
 if not isinstance(value,dict) or set(value)!={'K'}: raise Rejected('claim must contain only K')
 score=value['K']
 if score=='infinity': return 'infinity'
 if type(score) is not int or score<0: raise Rejected('K must be a natural or infinity')
 return 'finite '+str(score)

def tokens(source):
 """Ignore nested comments/strings; preserve actual command identifier tokens."""
 i=0;depth=0
 while i<len(source):
  if source.startswith('(*',i): depth+=1;i+=2;continue
  if source.startswith('*)',i):
   if not depth: raise Rejected('unmatched comment close')
   depth-=1;i+=2;continue
  if depth: i+=1;continue
  if source[i]=='"':
   i+=1
   while i<len(source):
    if source[i]=='"':
     if i+1<len(source) and source[i+1]=='"':i+=2;continue
     i+=1;break
    i+=1
   else: raise Rejected('unterminated string')
   continue
  m=re.compile(r'[A-Za-z_][A-Za-z_0-9\x27]*').match(source,i)
  if m: yield m[0];i+=len(m[0])
  else:i+=1
 if depth:raise Rejected('unterminated comment')

def check_source(path):
 return check_source_text(Path(path).read_text())

def check_source_text(source):
 identifiers=list(tokens(source))
 bad=set(identifiers)&FORBIDDEN
 # Reject filesystem commands at any position, including vernacular wrappers.
 # Qualified instruction constructors such as ReducedTypes.Load remain valid.
 clean=[];i=0;depth=0
 while i<len(source):
  if source.startswith('(*',i):depth+=1;i+=2;clean.append(' ');continue
  if depth and source.startswith('*)',i):depth-=1;i+=2;continue
  if depth:i+=1;continue
  if source[i]=='"':
   i+=1;clean.append(' ')
   while i<len(source):
    if source[i]=='"':
     if i+1<len(source) and source[i+1]=='"':i+=2;continue
     i+=1;break
    i+=1
   continue
  clean.append(source[i]);i+=1
 cleaned=''.join(clean)
 if (any(not re.search(r'[A-Za-z_][A-Za-z_0-9\x27]*\.$',cleaned[:m.start()])
         for m in re.finditer(r'(?<![\w\x27])Load\b',cleaned))
     or re.search(r'\b(?:Add|Remove)\s+(?:Rec\s+)?(?:LoadPath|ML\s+Path)\b',cleaned)):
  bad.add('load-path command')
 if bad:raise Rejected('unsupported submission command: '+', '.join(sorted(bad)))
 return source

def check_kernel_context(output):
 marker='CONTEXT SUMMARY\n==============='
 if output.count(marker)!=1:raise Rejected('missing or ambiguous kernel context')
 text=output.split(marker,1)[1]
 headers=[re.sub(r': <none>$', ':', h) for h in re.findall(r'^\* (.*)$',text,re.M)]
 expected={'Theory: Set is predicative','Theory: Rewrite rules are not allowed',
  'Axioms:',*(name+':' for name in UNSAFE_SECTIONS),
  'Inductives relying on indices not mattering:'}
 if set(headers)!=expected or len(headers)!=len(expected):
  raise Rejected('unexpected or duplicate kernel sections')
 if text.splitlines().count('* Theory: Set is predicative')!=1:raise Rejected('unexpected Set theory')
 if text.splitlines().count('* Theory: Rewrite rules are not allowed')!=1:raise Rejected('rewrite rules enabled')
 def section(name):
  matches=list(re.finditer(r'^\* '+re.escape(name)+r':([^*]*)(?=^\*|\Z)',text,re.M|re.S))
  if len(matches)!=1:raise Rejected('missing kernel section '+name)
  return matches[0][1].strip()
 values=section('Axioms')
 found=set(values.split()) if values!='<none>' else set()
 if not found<=AXIOMS:raise Rejected('unapproved axioms: '+', '.join(sorted(found-AXIOMS)))
 for name in UNSAFE_SECTIONS:
  if section(name)!='<none>':raise Rejected('unsafe kernel declarations: '+name)
 return sorted(found)

def literal_module(code,score):
 if not 0<len(code)<=134217728:raise Rejected('ROM must contain 1..128 MiB of bytes')
 out=['From Galette Require Import Base.',
  'From Galette.HOL.src.n_bit Require Import words.',
  'From InitE.InitE Require Import NatE.', 'Open Scope N_scope.']
 count=(len(code)+1023)//1024
 for i in range(count):
  chunk=code[1024*i:1024*(i+1)]
  out.append('Definition chunk_'+str(i)+' : list (word 8) := ['+';'.join('n2w '+str(b) for b in chunk)+'].')
 out.append('Definition submittedCode : list (word 8) := concat ['+';'.join('chunk_'+str(i) for i in range(count))+'].')
 out.append('Definition claimedScore : NatE := '+score+'.')
 return '\n'.join(out)+'\n'
