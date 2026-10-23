From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall599Via603From619From624Context MaximumCall599From619From624Leaf03Split MaximumCall598Via599From619From624Context MaximumCall598StructuredFrom619From624Split MaximumCall598StructuredFrom619From624Value.

Lemma callee_body_depth_cached :
  MaximumCall599From619From624Leaf03Split.callee_body_depth = MaximumCall598StructuredFrom619From624Value.depth_value.
Proof.
  unfold MaximumCall598StructuredFrom619From624Value.depth_value.
  rewrite <- MaximumCall598StructuredFrom619From624Value.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall598Via599From619From624Context.funs 598 [598]
        (sptree.size MaximumContext.funs) MaximumCall598Via599From619From624Context.body)).
  - symmetry; exact MaximumCall599From619From624Leaf03Split.callee_body_depth_eq.
  - exact MaximumCall598StructuredFrom619From624Split.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall599Via603From619From624Context.funs MaximumCall599Via603From619From624Context.callee
    [MaximumCall599Via603From619From624Context.callee] (sptree.size MaximumContext.funs)
    598 MaximumCall599From619From624Leaf03Split.ret_data MaximumCall599From619From624Leaf03Split.handler_data
    MaximumCall598StructuredFrom619From624Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall599Via603From619From624Context.depth MaximumCall599From619From624Leaf03Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall599From619From624Leaf03Split.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall599Via603From619From624Context.depth MaximumCall599From619From624Leaf03Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
