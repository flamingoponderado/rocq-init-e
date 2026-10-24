From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall618Via595ContextFrom608From860From861 MaximumCall618Leaf72SplitFrom608From860From861 MaximumCall615Via618ValueFrom608From860From861.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall618Via595ContextFrom608From860From861.funs MaximumCall618Via595ContextFrom608From860From861.callee
    [MaximumCall618Via595ContextFrom608From860From861.callee] (sptree.size MaximumContext.funs)
    615 MaximumCall618Leaf72SplitFrom608From860From861.ret_data MaximumCall618Leaf72SplitFrom608From860From861.handler_data
    MaximumCall615Via618ValueFrom608From860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall618Via595ContextFrom608From860From861.depth MaximumCall618Leaf72SplitFrom608From860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall618Leaf72SplitFrom608From860From861.leaf_depth_compact.
  unfold cached_depth, MaximumCall618Leaf72SplitFrom608From860From861.callee_body_depth,
    MaximumCall615Via618ValueFrom608From860From861.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall615Via618ValueFrom608From860From861.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall618Via595ContextFrom608From860From861.depth MaximumCall618Leaf72SplitFrom608From860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
