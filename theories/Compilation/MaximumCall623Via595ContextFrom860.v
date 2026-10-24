From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum MaximumContext MaximumCall595StructuredContextFrom860.

Definition callee : N := 623.
Definition funs := sptree.delete callee MaximumCall595StructuredContextFrom860.funs.
Definition body :=
  match sptree.lookup callee MaximumCall595StructuredContextFrom860.funs with
  | Some (_, p) => p
  | None => wordLang.Skip
  end.
Definition leaves := FastMaximum.seq_leaves body.
Definition depth p := word_depth.max_depth MaximumContext.frames
  (word_depth.call_graph funs callee [callee]
    (sptree.size MaximumContext.funs) p).
Definition leaf_chunk (i : nat) := List.firstn 1 (List.skipn i leaves).
