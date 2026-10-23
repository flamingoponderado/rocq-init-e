From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall598StructuredFrom606Context MaximumCall598From606Leaf77Split MaximumCall837Via598From606Context MaximumCall837StructuredFrom598From606Split MaximumCall837StructuredFrom598From606Value.

Lemma callee_body_depth_cached :
  MaximumCall598From606Leaf77Split.callee_body_depth = MaximumCall837StructuredFrom598From606Value.depth_value.
Proof.
  unfold MaximumCall837StructuredFrom598From606Value.depth_value.
  rewrite <- MaximumCall837StructuredFrom598From606Value.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall837Via598From606Context.funs 837 [837]
        (sptree.size MaximumContext.funs) MaximumCall837Via598From606Context.body)).
  - symmetry; exact MaximumCall598From606Leaf77Split.callee_body_depth_eq.
  - exact MaximumCall837StructuredFrom598From606Split.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall598StructuredFrom606Context.funs MaximumCall598StructuredFrom606Context.callee
    [MaximumCall598StructuredFrom606Context.callee] (sptree.size MaximumContext.funs)
    837 MaximumCall598From606Leaf77Split.ret_data MaximumCall598From606Leaf77Split.handler_data
    MaximumCall837StructuredFrom598From606Value.depth_value.

Lemma cached_depth_eq :
  MaximumCall598StructuredFrom606Context.depth MaximumCall598From606Leaf77Split.leaf = cached_depth.
Proof.
  rewrite MaximumCall598From606Leaf77Split.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall598StructuredFrom606Context.depth MaximumCall598From606Leaf77Split.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
