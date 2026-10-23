From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall616Via618Context MaximumCall616From618Leaf124Split MaximumCall612Via616From618Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall616Via618Context.funs MaximumCall616Via618Context.callee
    [MaximumCall616Via618Context.callee] (sptree.size MaximumContext.funs)
    612 MaximumCall616From618Leaf124Split.ret_data MaximumCall616From618Leaf124Split.handler_data
    MaximumCall612Via616From618Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall616Via618Context.depth MaximumCall616From618Leaf124Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall616From618Leaf124Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall616From618Leaf124Split.callee_body_depth,
    MaximumCall612Via616From618Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall612Via616From618Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall616Via618Context.depth MaximumCall616From618Leaf124Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
