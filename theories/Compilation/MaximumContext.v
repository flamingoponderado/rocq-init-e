From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.coretypes Require Import option.
From Galette.cakeml.compiler.backend Require Import word_to_stack word_depth wordLang bvl_to_bvi.
From InitE.Compilation Require Import WordPipeline Stack FastMaximum.
Open Scope N_scope.

Definition frames := word_to_stack.stack_frame_size (fst (snd Stack.stackResult)).
Definition funs := sptree.fromAList WordPipeline.optimized.
Definition root := bvl_to_bvi.InitGlobals_location.
Definition program :=
  match sptree.lookup root funs with
  | Some (_, p) => p
  | None => wordLang.Skip
  end.
Definition leaves := FastMaximum.seq_leaves program.
Definition depth p := word_depth.max_depth frames
  (word_depth.call_graph funs root [root] (sptree.size funs) p).
Definition leaf_chunk (i : nat) :=
  List.firstn 8 (List.skipn (8 * i) leaves).
