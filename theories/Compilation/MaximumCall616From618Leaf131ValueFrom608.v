From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall616Via618ContextFrom608 MaximumCall616From618Leaf131SplitFrom608 MaximumCall603Via616From618ValueFrom608.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall616Via618ContextFrom608.funs MaximumCall616Via618ContextFrom608.callee
    [MaximumCall616Via618ContextFrom608.callee] (sptree.size MaximumContext.funs)
    603 MaximumCall616From618Leaf131SplitFrom608.ret_data MaximumCall616From618Leaf131SplitFrom608.handler_data
    MaximumCall603Via616From618ValueFrom608.depth_value.

Lemma cached_depth_eq :
  MaximumCall616Via618ContextFrom608.depth MaximumCall616From618Leaf131SplitFrom608.leaf = cached_depth.
Proof.
  rewrite MaximumCall616From618Leaf131SplitFrom608.leaf_depth_compact.
  unfold cached_depth, MaximumCall616From618Leaf131SplitFrom608.callee_body_depth,
    MaximumCall603Via616From618ValueFrom608.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall603Via616From618ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall616Via618ContextFrom608.depth MaximumCall616From618Leaf131SplitFrom608.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
