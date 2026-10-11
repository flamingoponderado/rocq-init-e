#!/usr/bin/env python3
"""Port original Types.lean's reduced carriers, field for field.
No full-model fields or constructors are inserted. Products stay right nested.
"""
import re,hashlib,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'reference/flapjack/Flapjack/RiscV/L3/Types.lean'
TARGET=ROOT/'theories/Target/ReducedTypes.v'
RENAMES={n:n+'_ty' for n in ['Internal','System','Store','Load','Branch','MulDiv','Shift','ArithR','ArithI']}
def typename(s): return RENAMES.get(s,s)
def port_type(text):
 tokens=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()×→]',text)
 pos=0
 def atom():
  nonlocal pos
  token=tokens[pos];pos+=1
  if token=='(':
   value=arrow();assert tokens[pos]==')';pos+=1;return value
  if token=='BitVec':
   width=tokens[pos];pos+=1;assert width.isdecimal();return 'word '+width
  if token in ('Option','List'):
   return ('option' if token=='Option' else 'list')+' ('+atom()+')'
  return {'Bool':'bool','Nat':'N','HolChar':'ascii'}.get(token,typename(token))
 def product():
  nonlocal pos
  x=atom()
  if pos<len(tokens) and tokens[pos]=='×':
   pos+=1;return '('+x+' * '+product()+')%type'
  return x
 def arrow():
  nonlocal pos
  x=product()
  if pos<len(tokens) and tokens[pos]=='→':
   pos+=1;return '('+x+' -> '+arrow()+')'
  return x
 value=arrow();assert pos==len(tokens),(text,tokens[pos:]);return value

def declarations():
 s=SOURCE.read_text()
 matches=list(re.finditer(r'^(inductive|structure) (\w+) where\n',s,re.M))
 for m in matches:
  end=s.index('  deriving',m.end());deriving=s[end:s.index('\n',end)]
  body=s[m.end():end]
  if m[1]=='structure':
   fields=[]
   for line in body.splitlines():
    if not line.strip(): continue
    f,t=line.strip().split(' : ',1);f=f.strip('«»')
    fields.append((f,port_type(t)))
   yield m[1],m[2],fields,deriving
  else:
   constructors=[]
   for line in body.splitlines():
    v=re.fullmatch(r'  \| (\w+)(?: \(a0 : (.*)\))?',line)
    if not v: raise ValueError('unknown constructor syntax '+line)
    constructors.append((v[1],port_type(v[2]) if v[2] else None))
   yield m[1],m[2],constructors,deriving

def render():
 out=['(* Generated from original reduced Types.lean; do not edit. *)',
      '(* SHA256: '+hashlib.sha256(SOURCE.read_bytes()).hexdigest()+' *)',
      'From Galette Require Import Base.',
      'From Galette.HOL.src.n_bit Require Import words.',
      'From Stdlib Require Import Strings.Ascii.',
      'Open Scope N_scope.']
 for kind,name,entries,deriving in declarations():
  typ=typename(name)
  if kind=='structure':
   out.append('Record '+typ+' : Type := {')
   out.append(';\n'.join(' '+name+'_'+f+' : '+t for f,t in entries)+'\n}.')
   out.append('#[global] Instance '+name+'_inhabited : Inhabited '+typ+' :=\n {| '+
      ';\n    '.join(name+'_'+f+' := inhabitant _' for f,_ in entries)+' |}.')
   for f,t in entries:
    out.append('Definition '+name+'_'+f+'_fupd (update : '+t+' -> '+t+') (x : '+typ+') : '+typ+' :=\n {| '+
      ';\n    '.join(name+'_'+g+' := '+('update ('+name+'_'+g+' x)' if g==f else name+'_'+g+' x') for g,_ in entries)+' |}.')
  else:
   out.append('Inductive '+typ+' : Type :=')
   out.append('\n'.join(' | '+n+' : '+(t+' -> ' if t else '')+typ for n,t in entries)+'.')
   first,arg=entries[0]
   out.append('#[global] Instance '+name+'_inhabited : Inhabited '+typ+' := '+first+(' (inhabitant _)' if arg else '')+'.')
  if 'DecidableEq' in deriving:
   out.extend(['#[global] Instance '+name+'_eq_dec : EqDecision '+typ+'.',
    'Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.'])
  out.append('')
 return '\n'.join(out)
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
 text=render()
 if args.check:
  if TARGET.read_text()!=text: raise SystemExit('reduced types differ from reference')
 else: TARGET.write_text(text)
