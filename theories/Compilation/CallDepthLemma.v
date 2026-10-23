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

Lemma max_depth_ret_handler_call {a} ss
    (funs : num_map (N * wordLang.prog a)) n ns total d
    (args ret_args : list N) cuts (ret_prog : wordLang.prog a)
    ret_i ret_j h_idx (hprog : wordLang.prog a) h_i h_j argc body :
  sptree.lookup d funs = Some (argc, body) ->
  word_depth.max_depth ss
    (word_depth.call_graph funs n ns total
      (wordLang.Call
        (Some (ret_args, (cuts, (ret_prog, (ret_i, ret_j)))))
        (Some d) args (Some (h_idx, (hprog, (h_i, h_j)))))) =
  OPTION_MAP2 MAX
    (word_depth.max_depth ss
      (word_depth.Call n
        (word_depth.Const 3 (word_depth.Call d word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (word_depth.max_depth ss
        (word_depth.Call n
          (word_depth.Const 3
            (word_depth.call_graph (sptree.delete d funs) d [d] total body))))
      (OPTION_MAP2 MAX
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total hprog))
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total ret_prog)))).
Proof.
  intro Hlookup.
  destruct (@word_depth.call_graph_eqns a) as
    (_ & _ & Ecall & _ & _ & _ & _ & _).
  rewrite Ecall, Hlookup.
  rewrite andb_false_r.
  cbn [max_depth].
  cbn [max_depth].
  repeat rewrite word_depthProof.max_depth_mk_Branch.
  cbn [max_depth].
  rewrite word_depthProof.max_depth_mk_Branch.
  reflexivity.
Qed.

Lemma max_depth_ret_handler_call_pair {a} ss
    (funs : num_map (N * wordLang.prog a)) n ns total d
    (args : list N)
    (ret : list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))
    (handler : N * (wordLang.prog a * (N * N))) argc body :
  sptree.lookup d funs = Some (argc, body) ->
  word_depth.max_depth ss
    (word_depth.call_graph funs n ns total
      (wordLang.Call (Some ret) (Some d) args (Some handler))) =
  OPTION_MAP2 MAX
    (word_depth.max_depth ss
      (word_depth.Call n
        (word_depth.Const 3 (word_depth.Call d word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (word_depth.max_depth ss
        (word_depth.Call n
          (word_depth.Const 3
            (word_depth.call_graph (sptree.delete d funs) d [d] total body))))
      (OPTION_MAP2 MAX
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total (fst (snd handler))))
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total (fst (snd (snd ret))))))).
Proof.
  destruct ret as [ret_args [cuts [ret_prog [ri rj]]]].
  destruct handler as [hidx [hprog [hi hj]]].
  cbn [fst snd].
  apply max_depth_ret_handler_call.
Qed.

Lemma max_depth_ret_handler_call_pair_subst {a} ss
    (funs : num_map (N * wordLang.prog a)) n ns total d
    (args : list N)
    (ret : list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))
    (handler : N * (wordLang.prog a * (N * N))) argc body depth :
  sptree.lookup d funs = Some (argc, body) ->
  word_depth.max_depth ss
    (word_depth.call_graph (sptree.delete d funs) d [d] total body) = depth ->
  word_depth.max_depth ss
    (word_depth.call_graph funs n ns total
      (wordLang.Call (Some ret) (Some d) args (Some handler))) =
  OPTION_MAP2 MAX
    (word_depth.max_depth ss
      (word_depth.Call n
        (word_depth.Const 3 (word_depth.Call d word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (OPTION_MAP2 N.add (sptree.lookup n ss)
        (OPTION_MAP (N.add 3) depth))
      (OPTION_MAP2 MAX
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total (fst (snd handler))))
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total (fst (snd (snd ret))))))).
Proof.
  intros Hlookup Hdepth.
  rewrite (max_depth_ret_handler_call_pair ss funs n ns total d
    args ret handler argc body Hlookup).
  cbn [word_depth.max_depth].
  now rewrite Hdepth.
Qed.

Definition ret_handler_result {a} ss
    (funs : num_map (N * wordLang.prog a)) n ns total d
    (ret : list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))
    (handler : N * (wordLang.prog a * (N * N))) (depth : option N) :=
  OPTION_MAP2 MAX
    (word_depth.max_depth ss
      (word_depth.Call n
        (word_depth.Const 3 (word_depth.Call d word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (OPTION_MAP2 N.add (sptree.lookup n ss)
        (OPTION_MAP (N.add 3) depth))
      (OPTION_MAP2 MAX
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total (fst (snd handler))))
        (word_depth.max_depth ss
          (word_depth.call_graph funs n ns total (fst (snd (snd ret))))))).

Lemma max_depth_ret_handler_call_pair_compact {a} ss
    (funs : num_map (N * wordLang.prog a)) n ns total d
    (args : list N)
    (ret : list N * (wordLang.cutsets * (wordLang.prog a * (N * N))))
    (handler : N * (wordLang.prog a * (N * N))) argc body depth :
  sptree.lookup d funs = Some (argc, body) ->
  word_depth.max_depth ss
    (word_depth.call_graph (sptree.delete d funs) d [d] total body) = depth ->
  word_depth.max_depth ss
    (word_depth.call_graph funs n ns total
      (wordLang.Call (Some ret) (Some d) args (Some handler))) =
  ret_handler_result ss funs n ns total d ret handler depth.
Proof.
  intros Hlookup Hdepth.
  exact (max_depth_ret_handler_call_pair_subst ss funs n ns total d
    args ret handler argc body depth Hlookup Hdepth).
Qed.
