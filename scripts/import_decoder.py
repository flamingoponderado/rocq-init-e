#!/usr/bin/env python3
"""Literal translation of original RV64IM decoder; no whitelist inference.
Lean right nested tuples become Galette's Rocq flat tuple notation.
The compiler's Galette decoder remains a separate object requiring agreement.
"""
from pathlib import Path
import re,hashlib,argparse
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'reference/flapjack/Flapjack/RiscV/L3/Defs/Decode.lean'
TARGET=ROOT/'theories/Target/Decode.v'
def render():
 s=SOURCE.read_text();body=s.split('def Decode (')[1].split('=>',1)[1].split('\ndef DecodeRVC')[0].strip()
 assert body.endswith(')');body=body[:-1]
 body=re.sub(r'\(\[\] : \(List Bool\)\)', '[]',body)
 body=re.sub(r'holV2w ([0-9]+)',r'(@v2w \1)',body)
 body=re.sub(r'\b(?:instruction|Branch|ArithI|ArithR|Shift|MulDiv|Load|Store|System)\.([A-Za-z_0-9]+)',r'riscv.\1',body)
 body=re.sub(r'!b_([0-9]+)',r'negb b_\1',body)
 def groups(pos,closing=None):
  parts=[[]]
  while pos<len(body):
   c=body[pos]
   if c in '([':
    close={'(':')','[':']'}[c];node,pos=groups(pos+1,close)
    if c=='[': node='['+show(node)+']'
    parts[-1].append(node)
   elif c==closing:
    nodes=[]
    for part in parts:
     nonspace=[x for x in part if not (isinstance(x,str) and x.isspace())]
     if len(nonspace)==1 and isinstance(nonspace[0],list): nodes.append(nonspace[0])
     else: nodes.append(''.join(show(x) for x in part).strip())
    if len(nodes)==1:
     node=nodes[0]
     return node if isinstance(node,list) else ('('+node+')' if node else ''),pos+1
    flat=[]
    for n in nodes: flat.extend(n if isinstance(n,list) else [n])
    return flat,pos+1
   elif c==',' and closing==')': parts.append([]);pos+=1
   else: parts[-1].append(c);pos+=1
  if closing: raise ValueError('unclosed group')
  return ''.join(show(x) for x in parts[0]),pos
 def show(node): return '('+', '.join(map(show,node))+')' if isinstance(node,list) else node
 result,_=groups(0)
 header=['(* Generated from original RV64IM Decode.lean; do not edit. *)',
  '(* SHA256: '+hashlib.sha256(SOURCE.read_bytes()).hexdigest()+' *)',
  'From Galette Require Import Base.',
  'From Galette.HOL.src.n_bit Require Import words bitstring.',
  'From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.',
  'Open Scope N_scope.', 'Definition Decode (w : word32) : instruction :=']
 for i in range(31,-1,-1): header.append(f' let b_{i} := fcp_index w {i} in')
 return '\n'.join(header)+'\n '+result+'.\nDefinition DecodeRVC (_ : word16) : instruction := UnknownInstruction.\n'
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
 text=render()
 if args.check:
  if TARGET.read_text()!=text: raise SystemExit('decoder differs from reference')
 else: TARGET.write_text(text)
