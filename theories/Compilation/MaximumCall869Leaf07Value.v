From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall869Context MaximumCall869Leaf07Split MaximumCall278Value.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall869Context.funs MaximumCall869Context.callee
    [MaximumCall869Context.callee] (sptree.size MaximumContext.funs)
    278 MaximumCall869Leaf07Split.ret_data MaximumCall869Leaf07Split.handler_data
    MaximumCall278Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall869Context.depth MaximumCall869Leaf07Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall869Leaf07Split.leaf_depth_compact.
  unfold cached_depth, MaximumCall869Leaf07Split.callee_body_depth,
    MaximumCall278Value.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall278Value.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall869Context.depth MaximumCall869Leaf07Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
