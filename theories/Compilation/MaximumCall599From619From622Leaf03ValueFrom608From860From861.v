From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall599Via603From619From622ContextFrom608From860From861 MaximumCall599From619From622Leaf03SplitFrom608From860From861 MaximumCall598Via599From619From622ContextFrom608From860From861 MaximumCall598StructuredFrom619From622SplitFrom608From860From861 MaximumCall598StructuredFrom619From622ValueFrom608From860From861.

Lemma callee_body_depth_cached :
  MaximumCall599From619From622Leaf03SplitFrom608From860From861.callee_body_depth = MaximumCall598StructuredFrom619From622ValueFrom608From860From861.depth_value.
Proof.
  unfold MaximumCall598StructuredFrom619From622ValueFrom608From860From861.depth_value.
  rewrite <- MaximumCall598StructuredFrom619From622ValueFrom608From860From861.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall598Via599From619From622ContextFrom608From860From861.funs 598 [598]
        (sptree.size MaximumContext.funs) MaximumCall598Via599From619From622ContextFrom608From860From861.body)).
  - symmetry; exact MaximumCall599From619From622Leaf03SplitFrom608From860From861.callee_body_depth_eq.
  - exact MaximumCall598StructuredFrom619From622SplitFrom608From860From861.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall599Via603From619From622ContextFrom608From860From861.funs MaximumCall599Via603From619From622ContextFrom608From860From861.callee
    [MaximumCall599Via603From619From622ContextFrom608From860From861.callee] (sptree.size MaximumContext.funs)
    598 MaximumCall599From619From622Leaf03SplitFrom608From860From861.ret_data MaximumCall599From619From622Leaf03SplitFrom608From860From861.handler_data
    MaximumCall598StructuredFrom619From622ValueFrom608From860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall599Via603From619From622ContextFrom608From860From861.depth MaximumCall599From619From622Leaf03SplitFrom608From860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall599From619From622Leaf03SplitFrom608From860From861.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall599Via603From619From622ContextFrom608From860From861.depth MaximumCall599From619From622Leaf03SplitFrom608From860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
