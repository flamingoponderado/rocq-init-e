From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall602Leaf04ContextFrom860From861 MaximumCall602Inner35SplitFrom860From861 MaximumCall595Via602ContextFrom860From861 MaximumCall595StructuredSplitFrom860From861 MaximumCall595StructuredValueFrom860From861.

Lemma callee_body_depth_cached :
  MaximumCall602Inner35SplitFrom860From861.callee_body_depth = MaximumCall595StructuredValueFrom860From861.depth_value.
Proof.
  unfold MaximumCall595StructuredValueFrom860From861.depth_value.
  rewrite <- MaximumCall595StructuredValueFrom860From861.values_eq.
  transitivity
    (word_depth.max_depth MaximumContext.frames
      (word_depth.call_graph MaximumCall595Via602ContextFrom860From861.funs 595 [595]
        (sptree.size MaximumContext.funs) MaximumCall595Via602ContextFrom860From861.body)).
  - symmetry; exact MaximumCall602Inner35SplitFrom860From861.callee_body_depth_eq.
  - exact MaximumCall595StructuredSplitFrom860From861.body_depth_split.
Qed.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall602Leaf04ContextFrom860From861.funs MaximumCall602Leaf04ContextFrom860From861.callee
    [MaximumCall602Leaf04ContextFrom860From861.callee] (sptree.size MaximumContext.funs)
    595 MaximumCall602Inner35SplitFrom860From861.ret_data MaximumCall602Inner35SplitFrom860From861.handler_data
    MaximumCall595StructuredValueFrom860From861.depth_value.

Lemma cached_depth_eq :
  MaximumCall602Leaf04ContextFrom860From861.depth MaximumCall602Inner35SplitFrom860From861.leaf = cached_depth.
Proof.
  rewrite MaximumCall602Inner35SplitFrom860From861.leaf_depth_compact.
  unfold cached_depth.
  now rewrite callee_body_depth_cached.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall602Leaf04ContextFrom860From861.depth MaximumCall602Inner35SplitFrom860From861.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
