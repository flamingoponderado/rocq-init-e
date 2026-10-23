From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum MaximumContext.

Definition callee : N := 65.
Definition body :=
  match sptree.lookup callee MaximumContext.funs with
  | Some (_, p) => p
  | None => wordLang.Skip
  end.
Definition leaves := FastMaximum.seq_leaves body.
Definition depth p := word_depth.max_depth MaximumContext.frames
  (word_depth.call_graph MaximumContext.funs callee
    [callee; MaximumContext.root] (sptree.size MaximumContext.funs) p).
Definition leaf_chunk (i : nat) :=
  List.firstn 8 (List.skipn (8 * i) leaves).
