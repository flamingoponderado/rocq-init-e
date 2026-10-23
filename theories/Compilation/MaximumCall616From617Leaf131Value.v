From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall616Via617Context MaximumCall616From617Leaf131Split MaximumCall603Via616From617Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall616Via617Context.funs MaximumCall616Via617Context.callee
    [MaximumCall616Via617Context.callee] (sptree.size MaximumContext.funs)
    603 MaximumCall616From617Leaf131Split.ret_data MaximumCall616From617Leaf131Split.handler_data
    MaximumCall603Via616From617Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall616Via617Context.depth MaximumCall616From617Leaf131Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall616From617Leaf131Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall616From617Leaf131Split.callee_body_depth,
    MaximumCall603Via616From617Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall603Via616From617Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall616Via617Context.depth MaximumCall616From617Leaf131Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
