From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall603Via616From617ContextFrom860From861 MaximumCall603From616From617Leaf61SplitFrom860From861 MaximumCall599Via603From616From617ValueFrom860From861.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall603Via616From617ContextFrom860From861.funs MaximumCall603Via616From617ContextFrom860From861.callee
    [MaximumCall603Via616From617ContextFrom860From861.callee] (sptree.size MaximumContext.funs)
    599 MaximumCall603From616From617Leaf61SplitFrom860From861.ret_data MaximumCall603From616From617Leaf61SplitFrom860From861.handler_data
    MaximumCall599Via603From616From617ValueFrom860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall603Via616From617ContextFrom860From861.depth MaximumCall603From616From617Leaf61SplitFrom860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall603From616From617Leaf61SplitFrom860From861.leaf_depth_compact.
  unfold cached_depth, MaximumCall603From616From617Leaf61SplitFrom860From861.callee_body_depth,
    MaximumCall599Via603From616From617ValueFrom860From861.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall599Via603From616From617ValueFrom860From861.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall603Via616From617ContextFrom860From861.depth MaximumCall603From616From617Leaf61SplitFrom860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
