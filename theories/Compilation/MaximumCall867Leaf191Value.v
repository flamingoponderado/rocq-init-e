From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall867StructuredContext MaximumCall867Leaf191Split MaximumCall861Via867Context MaximumCall861StructuredSplit MaximumCall861StructuredValue.

Lemma callee_body_depth_cached :
  MaximumCall867Leaf191Split.callee_body_depth = MaximumCall861StructuredValue.depth_value.
Proof.
  unfold MaximumCall861StructuredValue.depth_value.
  rewrite <- MaximumCall861StructuredValue.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall861Via867Context.funs 861 [861]
        (sptree.size MaximumContext.funs) MaximumCall861Via867Context.body)).
  - symmetry; exact MaximumCall867Leaf191Split.callee_body_depth_eq.
  - exact MaximumCall861StructuredSplit.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall867StructuredContext.funs MaximumCall867StructuredContext.callee
    [MaximumCall867StructuredContext.callee] (sptree.size MaximumContext.funs)
    861 MaximumCall867Leaf191Split.ret_data MaximumCall867Leaf191Split.handler_data
    MaximumCall861StructuredValue.depth_value.

Lemma cached_depth_eq :
  MaximumCall867StructuredContext.depth MaximumCall867Leaf191Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall867Leaf191Split.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall867StructuredContext.depth MaximumCall867Leaf191Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
