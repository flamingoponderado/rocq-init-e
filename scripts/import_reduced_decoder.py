#!/usr/bin/env python3
"""Direct original decoder over original reduced carriers and right tuples."""
import re,hashlib,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'reference/flapjack/Flapjack/RiscV/L3/Defs/Decode.lean'
TARGET=ROOT/'theories/Target/ReducedDecode.v'
def render():
 s=SOURCE.read_text();body=s.split('def Decode (')[1].split('=>',1)[1].split('\ndef DecodeRVC')[0].strip()
 assert body.endswith(')');body=body[:-1]
 body=re.sub(r'\(\[\] : \(List Bool\)\)', '[]',body)
 body=re.sub(r'holV2w ([0-9]+)',r'(@v2w \1)',body)
 body=re.sub(r'\b(?:instruction|Branch|ArithI|ArithR|Shift|MulDiv|Load|Store|System)\.([A-Za-z_0-9]+)',r'ReducedTypes.\1',body)
 body=re.sub(r'!b_([0-9]+)',r'negb b_\1',body)
 header=['(* Generated from original Decode.lean over reduced Types.lean. *)',
 '(* SHA256: '+hashlib.sha256(SOURCE.read_bytes()).hexdigest()+' *)',
 'From Galette Require Import Base.',
 'From Galette.HOL.src.n_bit Require Import words bitstring.',
 'From InitE.Target Require Import ReducedTypes.',
 'Open Scope N_scope.',
 "Definition asImm12 '((a,(b,(c,d))) : (word 1 * (word 1 * (word 6 * word 4)))%type) : word 12 :=",
 ' word_concat a (word_concat b (word_concat c d : word 10) : word 11).',
 "Definition asImm20 '((a,(b,(c,d))) : (word 1 * (word 8 * (word 1 * word 10)))%type) : word 20 :=",
 ' word_concat a (word_concat b (word_concat c d : word 11) : word 19).',
 "Definition asSImm12 '((a,b) : (word 7 * word 5)%type) : word 12 := word_concat a b.",
 'Definition Decode (w : word 32) : instruction :=']
 for i in range(31,-1,-1): header.append(f' let b_{i} := fcp_index w {i} in')
 return '\n'.join(header)+'\n '+body+'.\nDefinition DecodeRVC (_ : word 16) : instruction := UnknownInstruction.\n'
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
 text=render()
 if args.check:
  if TARGET.read_text()!=text: raise SystemExit('reduced decoder differs from reference')
 else: TARGET.write_text(text)
