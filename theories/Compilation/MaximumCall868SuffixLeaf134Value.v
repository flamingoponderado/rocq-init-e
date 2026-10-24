From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall868SuffixContext MaximumCall868SuffixLeaf134Split MaximumCall867Via868Context MaximumCall867StructuredSplit MaximumCall867StructuredValue.

Lemma callee_body_depth_cached :
  MaximumCall868SuffixLeaf134Split.callee_body_depth = MaximumCall867StructuredValue.depth_value.
Proof.
  unfold MaximumCall867StructuredValue.depth_value.
  rewrite <- MaximumCall867StructuredValue.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall867Via868Context.funs 867 [867]
        (sptree.size MaximumContext.funs) MaximumCall867Via868Context.body)).
  - symmetry; exact MaximumCall868SuffixLeaf134Split.callee_body_depth_eq.
  - exact MaximumCall867StructuredSplit.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall868SuffixContext.funs MaximumCall868SuffixContext.callee
    [MaximumCall868SuffixContext.callee] (sptree.size MaximumContext.funs)
    867 MaximumCall868SuffixLeaf134Split.ret_data MaximumCall868SuffixLeaf134Split.handler_data
    MaximumCall867StructuredValue.depth_value.

Lemma cached_depth_eq :
  MaximumCall868SuffixContext.depth MaximumCall868SuffixLeaf134Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall868SuffixLeaf134Split.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall868SuffixContext.depth MaximumCall868SuffixLeaf134Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
