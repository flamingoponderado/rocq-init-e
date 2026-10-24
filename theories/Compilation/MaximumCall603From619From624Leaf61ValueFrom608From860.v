From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall603Via619From624ContextFrom608From860 MaximumCall603From619From624Leaf61SplitFrom608From860 MaximumCall599Via603From619From624ValueFrom608From860.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall603Via619From624ContextFrom608From860.funs MaximumCall603Via619From624ContextFrom608From860.callee
    [MaximumCall603Via619From624ContextFrom608From860.callee] (sptree.size MaximumContext.funs)
    599 MaximumCall603From619From624Leaf61SplitFrom608From860.ret_data MaximumCall603From619From624Leaf61SplitFrom608From860.handler_data
    MaximumCall599Via603From619From624ValueFrom608From860.depth_value.

Lemma cached_depth_eq :
  MaximumCall603Via619From624ContextFrom608From860.depth MaximumCall603From619From624Leaf61SplitFrom608From860.leaf = cached_depth.
Proof.
  rewrite MaximumCall603From619From624Leaf61SplitFrom608From860.leaf_depth_compact.
  unfold cached_depth, MaximumCall603From619From624Leaf61SplitFrom608From860.callee_body_depth,
    MaximumCall599Via603From619From624ValueFrom608From860.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall599Via603From619From624ValueFrom608From860.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall603Via619From624ContextFrom608From860.depth MaximumCall603From619From624Leaf61SplitFrom608From860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
