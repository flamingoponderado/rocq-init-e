From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall618Via595ContextFrom608 MaximumCall618Leaf72SplitFrom608 MaximumCall615Via618ValueFrom608.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall618Via595ContextFrom608.funs MaximumCall618Via595ContextFrom608.callee
    [MaximumCall618Via595ContextFrom608.callee] (sptree.size MaximumContext.funs)
    615 MaximumCall618Leaf72SplitFrom608.ret_data MaximumCall618Leaf72SplitFrom608.handler_data
    MaximumCall615Via618ValueFrom608.depth_value.

Lemma cached_depth_eq :
  MaximumCall618Via595ContextFrom608.depth MaximumCall618Leaf72SplitFrom608.leaf = cached_depth.
Proof.
  rewrite MaximumCall618Leaf72SplitFrom608.leaf_depth_compact.
  unfold cached_depth, MaximumCall618Leaf72SplitFrom608.callee_body_depth,
    MaximumCall615Via618ValueFrom608.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall615Via618ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall618Via595ContextFrom608.depth MaximumCall618Leaf72SplitFrom608.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
