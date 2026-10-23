From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum CallDepthLemma
  MaximumContext MaximumCall65Context.
Open Scope N_scope.

Definition tail := List.nth 339 MaximumContext.leaves wordLang.Skip.
Definition tail_args :=
  match tail with
  | wordLang.Call _ _ args _ => args
  | _ => []
  end.
Definition callee_argc :=
  match sptree.lookup 65 MaximumContext.funs with
  | Some (argc, _) => argc
  | None => 0
  end.

Lemma tail_shape : tail = wordLang.Call None (Some 65) tail_args None.
Proof. vm_cast_no_check (eq_refl tail). Qed.

Lemma body_lookup :
  sptree.lookup 65 MaximumContext.funs =
  Some (callee_argc, MaximumCall65Context.body).
Proof. vm_cast_no_check (eq_refl (sptree.lookup 65 MaximumContext.funs)). Qed.

Lemma tail_depth_split :
  MaximumContext.depth tail =
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames
      (word_depth.Call 65 word_depth.Leaf))
    (fold_right FastMaximum.join_depth (Some 0)
      (List.map MaximumCall65Context.depth MaximumCall65Context.leaves)).
Proof.
  unfold MaximumContext.depth.
  rewrite tail_shape.
  rewrite (CallDepthLemma.max_depth_noret_call
    MaximumContext.frames MaximumContext.funs MaximumContext.root
    [MaximumContext.root] (sptree.size MaximumContext.funs)
    65 tail_args None callee_argc MaximumCall65Context.body).
  - rewrite <- FastMaximum.fast_depth_exact.
    rewrite FastMaximum.fast_depth_leaves.
    reflexivity.
  - vm_compute; reflexivity.
  - exact body_lookup.
  - vm_compute; reflexivity.
Qed.
