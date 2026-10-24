From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall65Context MaximumCall65Value.
Open Scope N_scope.

Definition leaf := List.nth 339 MaximumContext.leaves wordLang.Skip.
Definition args := match leaf with wordLang.Call _ _ xs _ => xs | _ => [] end.
Definition argc := match sptree.lookup 65 MaximumContext.funs with
  | Some (n, _) => n | None => 0 end.

Lemma leaf_shape : leaf = wordLang.Call None (Some 65) args None.
Proof. vm_cast_no_check (eq_refl leaf). Qed.
Lemma body_lookup : sptree.lookup 65 MaximumContext.funs =
  Some (argc, MaximumCall65Context.body).
Proof. vm_cast_no_check (eq_refl (sptree.lookup 65 MaximumContext.funs)). Qed.
Lemma not_visited : MEM 65 [MaximumContext.root] = false.
Proof. vm_cast_no_check (eq_refl (MEM 65 [MaximumContext.root])). Qed.
Lemma enough_fuel :
  (LENGTH [MaximumContext.root] <? sptree.size MaximumContext.funs) = true.
Proof. vm_cast_no_check
  (eq_refl (LENGTH [MaximumContext.root] <? sptree.size MaximumContext.funs)). Qed.

Definition callee_body_depth :=
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall65Context.depth MaximumCall65Context.leaves).
Lemma callee_body_depth_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumContext.funs 65
      [65; MaximumContext.root] (sptree.size MaximumContext.funs)
      MaximumCall65Context.body) = callee_body_depth.
Proof.
  unfold callee_body_depth, MaximumCall65Context.depth, MaximumCall65Context.leaves.
  transitivity
    (FastMaximum.fast_depth MaximumContext.frames MaximumContext.funs 65
      [65; MaximumContext.root] (sptree.size MaximumContext.funs)
      MaximumCall65Context.body).
  - symmetry; apply FastMaximum.fast_depth_exact.
  - apply FastMaximum.fast_depth_leaves.
Qed.

