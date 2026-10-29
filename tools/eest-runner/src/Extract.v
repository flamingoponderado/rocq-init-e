(** Extraction of [InitE.Witness.Runner.runInput] for the EEST runner.

    The directives below are trusted.  They realize Rocq's binary numbers
    by Zarith integers, [nat] by OCaml integers, [ascii] by characters,
    Galette's finite maps by [Fmap] (fmap.ml) and [nthN] by an array lookup
    (nth.ml).  The one classical axiom that reaches the code, behind
    [select]/[ARB], fails if it is ever called. *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlChar.
From Stdlib Require Import BinNat BinPos ClassicalEpsilon.
From Galette.HOL.src.finite_maps Require Import finite_map.
From InitE.Guest Require Import Basic.
From InitE.Witness Require Import Runner.
Set Warnings "-extraction-default-directory,-extraction-reserved-identifier".

Extract Inductive positive => "Z.t"
  [ "(fun p -> Z.succ (Z.shift_left p 1))" "(fun p -> Z.shift_left p 1)" "Z.one" ]
  "(fun fI fO fH p -> if Z.equal p Z.one then fH () else
     let q = Z.shift_right p 1 in if Z.is_odd p then fI q else fO q)".
Extract Inductive N => "Z.t" [ "Z.zero" "(fun p -> p)" ]
  "(fun f0 fp n -> if Z.sign n = 0 then f0 () else fp n)".

Extract Inlined Constant N.add => "Z.add".
Extract Inlined Constant N.sub => "(fun a b -> Z.max Z.zero (Z.sub a b))".
Extract Inlined Constant N.mul => "Z.mul".
Extract Inlined Constant N.div => "(fun a b -> if Z.sign b = 0 then Z.zero else Z.div a b)".
Extract Inlined Constant N.modulo => "(fun a b -> if Z.sign b = 0 then a else Z.rem a b)".
Extract Inlined Constant N.pow => "(fun a b -> Z.pow a (Z.to_int b))".
Extract Inlined Constant N.eqb => "Z.equal".
Extract Inlined Constant N.ltb => "Z.lt".
Extract Inlined Constant N.leb => "Z.leq".
Extract Inlined Constant N.max => "Z.max".
Extract Inlined Constant N.succ => "Z.succ".
Extract Inlined Constant N.succ_pos => "Z.succ".
Extract Inlined Constant N.log2 => "(fun a -> if Z.sign a = 0 then Z.zero else Z.of_int (Z.log2 a))".
Extract Inlined Constant N.land => "Z.logand".
Extract Inlined Constant N.lor => "Z.logor".
Extract Inlined Constant N.lxor => "Z.logxor".
Extract Inlined Constant N.eq_dec => "Z.equal".
Extract Inlined Constant N.to_nat => "Z.to_int".
Extract Inlined Constant N.of_nat => "Z.of_int".
Extract Inlined Constant Pos.succ => "Z.succ".
Extract Inlined Constant Pos.add => "Z.add".
Extract Inlined Constant Pos.mul => "Z.mul".
Extract Inlined Constant Pos.eqb => "Z.equal".
Extract Inlined Constant Pos.eq_dec => "Z.equal".
Extract Inlined Constant Pos.to_nat => "Z.to_int".
Extract Inlined Constant Pos.of_succ_nat => "(fun n -> Z.of_int (n + 1))".
Extract Inlined Constant Pos.compare =>
  "(fun a b -> let c = Z.compare a b in if c = 0 then Eq else if c < 0 then Lt else Gt)".

(** Galette's finite maps, by [Fmap] in this directory. *)
Extract Inductive fmap => "Fmap.t" [ "Fmap.of_fun" ] "Fmap.case".
Extract Inlined Constant FLOOKUP => "Fmap.lookup".
Extract Inlined Constant FEMPTY => "Fmap.empty".
Extract Inlined Constant FUPDATE => "Fmap.update".
Extract Inlined Constant fdomsub => "Fmap.domsub".

Extract Constant nthN => "Nth.nthN".

Extract Constant constructive_indefinite_description =>
  "(fun _ -> failwith ""unrealized axiom: constructive_indefinite_description"")".

Extraction "runner_extracted.ml" runInput.
