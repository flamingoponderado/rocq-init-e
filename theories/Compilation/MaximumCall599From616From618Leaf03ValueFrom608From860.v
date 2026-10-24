From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall599Via603From616From618ContextFrom608From860 MaximumCall599From616From618Leaf03SplitFrom608From860 MaximumCall598Via599From616From618ContextFrom608From860 MaximumCall598StructuredFrom616From618SplitFrom608From860 MaximumCall598StructuredFrom616From618ValueFrom608From860.

Lemma callee_body_depth_cached :
  MaximumCall599From616From618Leaf03SplitFrom608From860.callee_body_depth = MaximumCall598StructuredFrom616From618ValueFrom608From860.depth_value.
Proof.
  unfold MaximumCall598StructuredFrom616From618ValueFrom608From860.depth_value.
  rewrite <- MaximumCall598StructuredFrom616From618ValueFrom608From860.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall598Via599From616From618ContextFrom608From860.funs 598 [598]
        (sptree.size MaximumContext.funs) MaximumCall598Via599From616From618ContextFrom608From860.body)).
  - symmetry; exact MaximumCall599From616From618Leaf03SplitFrom608From860.callee_body_depth_eq.
  - exact MaximumCall598StructuredFrom616From618SplitFrom608From860.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall599Via603From616From618ContextFrom608From860.funs MaximumCall599Via603From616From618ContextFrom608From860.callee
    [MaximumCall599Via603From616From618ContextFrom608From860.callee] (sptree.size MaximumContext.funs)
    598 MaximumCall599From616From618Leaf03SplitFrom608From860.ret_data MaximumCall599From616From618Leaf03SplitFrom608From860.handler_data
    MaximumCall598StructuredFrom616From618ValueFrom608From860.depth_value.

Lemma cached_depth_eq :
  MaximumCall599Via603From616From618ContextFrom608From860.depth MaximumCall599From616From618Leaf03SplitFrom608From860.leaf = cached_depth.
Proof.
  rewrite MaximumCall599From616From618Leaf03SplitFrom608From860.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall599Via603From616From618ContextFrom608From860.depth MaximumCall599From616From618Leaf03SplitFrom608From860.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
