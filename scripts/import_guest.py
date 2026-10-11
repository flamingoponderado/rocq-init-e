#!/usr/bin/env python3
"""Translate the literal authoritative Lean AST, refusing unknown syntax.
No Pancake parser or textual-source agreement is assumed by the challenge.
"""
import hashlib, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'reference/init-e/Guest/Ast.lean'
TARGET = ROOT / 'theories/Guest/Ast.v'
MAP = {
'Decl.decl':'panLang.Decl', 'Decl.exnDecl':'ExnDecl', 'Decl.function':'Function',
'Shape.one':'One', 'Shape.comb':'Comb',
'VarKind.local':'Local','VarKind.global':'Global',
'Exp.const':'panLang.Const','Exp.var':'Var','Exp.rStruct':'RStruct',
'Exp.rField':'RField','Exp.load':'panLang.Load','Exp.loadByte':'LoadByte',
'Exp.op':'Op','Exp.panOp':'Panop','Exp.cmp':'Cmp','Exp.shift':'panLang.Shift',
'Exp.baseAddr':'BaseAddr',
'Prog.skip':'panLang.Skip','Prog.dec':'Dec','Prog.assign':'Assign',
'Prog.primitive':'Primitive','Prog.store':'Store','Prog.storeByte':'StoreByte',
'Prog.seq':'Seq','Prog.ite':'If','Prog.while':'While','Prog.break':'Break',
'Prog.call':'Call','Prog.decCall':'DecCall','Prog.extCall':'ExtCall',
'Prog.raise':'Raise','Prog.return':'Return','Prog.shMemLoad':'ShMemLoad',
'Prog.shMemStore':'ShMemStore','OpSize.op8':'Op8','OpSize.opW':'OpW',
'PanOp.mul':'Mul','PrimOp.addCarry':'panLang.AddCarry',
'BinOp.add':'Add','BinOp.sub':'Sub','BinOp.and':'And','BinOp.or':'Or',
'BinOp.xor':'Xor','Cmp.equal':'Equal','Cmp.notEqual':'NotEqual',
'Cmp.less':'Less','Cmp.notLess':'NotLess','Cmp.lower':'Lower',
'Cmp.notLower':'NotLower','Shift.asr':'Asr','Shift.lsl':'Lsl','Shift.lsr':'Lsr',
'some':'Some','none':'None'}
def translate(body):
    body = re.sub(r'BitVec\.ofNat 64 ([0-9]+)', r'n2w \1', body)
    body = re.sub(r'"[^"\\]*"', lambda m:'(strlit '+m[0]+')',body)
    def identifier(m):
        s=m[0]
        if s.startswith(chr(34)): return s
        if '.' in s and s not in MAP: raise ValueError('unknown constructor '+s)
        return MAP.get(s,s)
    body = re.sub(r'"[^"\\]*"|[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',identifier,body)
    body = body.replace('exported :=','export :=') .replace('returnShape :=','fun_decl_return :=')
    body = re.sub(r'\n(\s*)(inline|export|params|body|fun_decl_return) :=',r';\n\1\2 :=',body)
    stack=[]; out=[]; quoted=False
    for c in body:
        if c=='"': quoted=not quoted
        if not quoted:
            if c in '[({': stack.append(c)
            elif c in '])}':
                if not stack or stack.pop() != {']':'[',')':'(','}':'{'}[c]: raise ValueError('unbalanced literal')
            elif c==',' and stack[-1]=='[': c=';'
        out.append(c)
    if stack or quoted: raise ValueError('unclosed literal')
    # Lean tuples nest to the right; Rocq tuple notation nests to the left.
    text=''.join(out)
    def groups(pos,closing=None):
        parts=['']
        while pos<len(text):
            c=text[pos]
            if c=='"':
                end=text.index('"',pos+1);parts[-1]+=text[pos:end+1];pos=end+1
            elif c in '([{':
                close={'(':')','[':']','{':'}'}[c]
                inner,pos=groups(pos+1,close);parts[-1]+=c+inner+close
            elif c==closing:
                def pair(xs):
                    return xs[0] if len(xs)==1 else xs[0]+', ('+pair(xs[1:])+')'
                return pair(parts),pos+1
            elif c==',' and closing==')': parts.append('');pos+=1
            else: parts[-1]+=c;pos+=1
        if closing: raise ValueError('unclosed group')
        return parts[0],pos
    converted,_=groups(0)
    return converted.replace('{ name :=','{| name :=').replace(' }',' |}')
def render():
    source=SOURCE.read_text()
    declarations=list(re.finditer(r'^def (guest\w+) : (Decl \(BitVec 64\)|List \(Decl \(BitVec 64\)\)) :=\n',source,re.M))
    if not declarations: raise ValueError('no declarations')
    result=['(* Generated from original init-e Guest/Ast.lean; do not edit. *)',
        '(* SHA256: '+hashlib.sha256(SOURCE.read_bytes()).hexdigest()+' *)',
        'From Galette Require Import Base.',
        'From Galette.HOL.src.n_bit Require Import words.',
        'From Galette.HOL.src.string Require Import string.',
        'From Galette.cakeml.basis.pure Require Import mlstring.',
        'From Galette.cakeml.semantics Require Import ast.',
        'From Galette.cakeml.compiler.encoders.asm Require Import asm.',
        'From Galette.cakeml.pancake Require Import panLang.',
        'Open Scope N_scope.','Open Scope hol_string_scope.']
    for i,m in enumerate(declarations):
        end=declarations[i+1].start() if i+1<len(declarations) else source.index('\nend Guest',m.end())
        body=re.sub(r'/\-.*?\-/', '', source[m.end():end], flags=re.S).strip()
        typ='list (decl 64)' if m[2].startswith('List') else 'decl 64'
        result.append('Definition '+m[1]+' : '+typ+' :=\n'+translate(body)+'.\n')
    return '\n'.join(result)
if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    generated=render()
    if args.check:
        if TARGET.read_text()!=generated: raise SystemExit('AST differs from pinned reference')
    else: TARGET.write_text(generated)
