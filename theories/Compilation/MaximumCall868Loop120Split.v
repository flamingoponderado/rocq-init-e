From Galette Require Import Base.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum StructuredDepth
  MaximumContext MaximumCall868Context MaximumCall868Loop120Context.

Definition loop_names :=
  match MaximumCall868Loop120Context.outer with
  | wordLang.Loop x _ _ => Some x | _ => None end.
Definition loop_exit :=
  match MaximumCall868Loop120Context.outer with
  | wordLang.Loop _ _ y => Some y | _ => None end.

Lemma outer_shape :
  MaximumCall868Loop120Context.outer =
    wordLang.Loop (THE loop_names) MaximumCall868Loop120Context.body (THE loop_exit).
Proof. vm_cast_no_check (eq_refl MaximumCall868Loop120Context.outer). Qed.

Lemma outer_depth_split :
  MaximumCall868Context.depth MaximumCall868Loop120Context.outer =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall868Loop120Context.depth MaximumCall868Loop120Context.leaves).
Proof.
  unfold MaximumCall868Context.depth.
  rewrite outer_shape.
  rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 word_depth.call_graph_eqns))))))).
  unfold MaximumCall868Loop120Context.depth, MaximumCall868Loop120Context.leaves.
  apply StructuredDepth.depth_leaves.
Qed.
