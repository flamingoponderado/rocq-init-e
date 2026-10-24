From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall598StructuredFrom616From618ContextFrom860 MaximumCall598From616From618Leaf77SplitFrom860 MaximumCall837Via598From616From618ContextFrom860 MaximumCall837StructuredFrom598From616From618SplitFrom860 MaximumCall837StructuredFrom598From616From618ValueFrom860.

Lemma callee_body_depth_cached :
  MaximumCall598From616From618Leaf77SplitFrom860.callee_body_depth = MaximumCall837StructuredFrom598From616From618ValueFrom860.depth_value.
Proof.
  unfold MaximumCall837StructuredFrom598From616From618ValueFrom860.depth_value.
  rewrite <- MaximumCall837StructuredFrom598From616From618ValueFrom860.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall837Via598From616From618ContextFrom860.funs 837 [837]
        (sptree.size MaximumContext.funs) MaximumCall837Via598From616From618ContextFrom860.body)).
  - symmetry; exact MaximumCall598From616From618Leaf77SplitFrom860.callee_body_depth_eq.
  - exact MaximumCall837StructuredFrom598From616From618SplitFrom860.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall598StructuredFrom616From618ContextFrom860.funs MaximumCall598StructuredFrom616From618ContextFrom860.callee
    [MaximumCall598StructuredFrom616From618ContextFrom860.callee] (sptree.size MaximumContext.funs)
    837 MaximumCall598From616From618Leaf77SplitFrom860.ret_data MaximumCall598From616From618Leaf77SplitFrom860.handler_data
    MaximumCall837StructuredFrom598From616From618ValueFrom860.depth_value.

Lemma cached_depth_eq :
  MaximumCall598StructuredFrom616From618ContextFrom860.depth MaximumCall598From616From618Leaf77SplitFrom860.leaf = cached_depth.
Proof.
  rewrite MaximumCall598From616From618Leaf77SplitFrom860.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall598StructuredFrom616From618ContextFrom860.depth MaximumCall598From616From618Leaf77SplitFrom860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
