From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall606Via608Context MaximumCall606Leaf37SplitFrom608 MaximumCall602Via606ValueFrom608.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall606Via608Context.funs MaximumCall606Via608Context.callee
    [MaximumCall606Via608Context.callee] (sptree.size MaximumContext.funs)
    602 MaximumCall606Leaf37SplitFrom608.ret_data MaximumCall606Leaf37SplitFrom608.handler_data
    MaximumCall602Via606ValueFrom608.depth_value.

Lemma cached_depth_eq :
  MaximumCall606Via608Context.depth MaximumCall606Leaf37SplitFrom608.leaf = cached_depth.
Proof.
  rewrite MaximumCall606Leaf37SplitFrom608.leaf_depth_compact.
  unfold cached_depth, MaximumCall606Leaf37SplitFrom608.callee_body_depth,
    MaximumCall602Via606ValueFrom608.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall602Via606ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall606Via608Context.depth MaximumCall606Leaf37SplitFrom608.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
