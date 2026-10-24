From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall861StructuredContext MaximumCall861Leaf25Split MaximumCall860Via861Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall861StructuredContext.funs MaximumCall861StructuredContext.callee
    [MaximumCall861StructuredContext.callee] (sptree.size MaximumContext.funs)
    860 MaximumCall861Leaf25Split.ret_data MaximumCall861Leaf25Split.handler_data
    MaximumCall860Via861Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall861StructuredContext.depth MaximumCall861Leaf25Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall861Leaf25Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall861Leaf25Split.callee_body_depth,
    MaximumCall860Via861Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall860Via861Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall861StructuredContext.depth MaximumCall861Leaf25Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
