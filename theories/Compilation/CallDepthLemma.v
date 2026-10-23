From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From Galette.cakeml.compiler.backend.proofs Require Import word_depthProof.
Open Scope N_scope.

Lemma max_depth_noret_call {a} ss
    (funs : num_map (N * wordLang.prog a)) n ns total d
    (args : list N) handler argc body :
  MEM d ns = false ->
  sptree.lookup d funs = Some (argc, body) ->
  (LENGTH ns <? total) = true ->
  word_depth.max_depth ss
    (word_depth.call_graph funs n ns total
      (wordLang.Call None (Some d) args handler)) =
  OPTION_MAP2 MAX
    (word_depth.max_depth ss (word_depth.Call d word_depth.Leaf))
    (word_depth.max_depth ss
      (word_depth.call_graph funs d (d :: ns) total body)).
Proof.
  intros Hmem Hlookup Hlen.
  destruct (@word_depth.call_graph_eqns a) as
    (_ & _ & Ecall & _ & _ & _ & _ & _).
  rewrite Ecall.
  rewrite Hmem, Hlookup, Hlen.
  cbn [andb].
  rewrite word_depthProof.max_depth_mk_Branch.
  reflexivity.
Qed.
