From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall602Leaf04Context MaximumCall602Inner35Split MaximumCall595Via602Context MaximumCall595StructuredSplit MaximumCall595StructuredValue.

Lemma callee_body_depth_cached :
  MaximumCall602Inner35Split.callee_body_depth = MaximumCall595StructuredValue.depth_value.
Proof.
  unfold MaximumCall595StructuredValue.depth_value.
  rewrite <- MaximumCall595StructuredValue.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall595Via602Context.funs 595 [595]
        (sptree.size MaximumContext.funs) MaximumCall595Via602Context.body)).
  - symmetry; exact MaximumCall602Inner35Split.callee_body_depth_eq.
  - exact MaximumCall595StructuredSplit.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall602Leaf04Context.funs MaximumCall602Leaf04Context.callee
    [MaximumCall602Leaf04Context.callee] (sptree.size MaximumContext.funs)
    595 MaximumCall602Inner35Split.ret_data MaximumCall602Inner35Split.handler_data
    MaximumCall595StructuredValue.depth_value.

Lemma cached_depth_eq :
  MaximumCall602Leaf04Context.depth MaximumCall602Inner35Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall602Inner35Split.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall602Leaf04Context.depth MaximumCall602Inner35Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
