(** Compute sequence call-graph depths without constructing one combined tree.
    The theorem below equates this evaluator to Galette's exact call graph. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.coretypes Require Import option.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From Stdlib Require Import Lia.
Open Scope N_scope.

Lemma max_depth_mk_Branch ss t1 t2 :
  max_depth ss (mk_Branch t1 t2) =
  OPTION_MAP2 MAX (max_depth ss t1) (max_depth ss t2).
Proof.
  unfold mk_Branch.
  destruct (decide (t1 = t2)) as [E|E].
  - subst t2. destruct (max_depth ss t1) as [d|] eqn:H;
      cbn [OPTION_MAP2 IS_SOME THE]; try reflexivity.
    unfold OPTION_MAP2; cbn; rewrite MAX_max, N.max_id; reflexivity.
  - destruct (decide (t1 = Leaf)) as [H1|H1].
    + subst t1. destruct (max_depth ss t2) as [d|] eqn:H;
        cbn [max_depth OPTION_MAP2 IS_SOME THE]; try reflexivity.
      unfold OPTION_MAP2; cbn; rewrite MAX_max, N.max_0_l; reflexivity.
    + destruct (decide (t2 = Leaf)) as [H2|H2].
      * subst t2. destruct (max_depth ss t1) as [d|] eqn:H;
          cbn [max_depth OPTION_MAP2 IS_SOME THE]; try reflexivity.
        unfold OPTION_MAP2; cbn; rewrite MAX_max, N.max_0_r; reflexivity.
      * destruct (decide (t1 = Unknown)) as [Hu|Hu].
        -- subst t1. destruct (max_depth ss t2);
             reflexivity.
        -- destruct (decide (t2 = Unknown)) as [Hu2|Hu2].
           ++ subst t2. destruct (max_depth ss t1); reflexivity.
           ++ reflexivity.
Qed.

Fixpoint fast_depth {a} (ss : num_map N)
    (funs : num_map (N * wordLang.prog a)) n ns total
    (p : wordLang.prog a) : option N :=
  match p with
  | wordLang.Seq p q =>
      OPTION_MAP2 MAX (fast_depth ss funs n ns total p)
                      (fast_depth ss funs n ns total q)
  | _ => max_depth ss (call_graph funs n ns total p)
  end.

Lemma fast_depth_exact {a} ss (funs : num_map (N * wordLang.prog a)) n ns total p :
  fast_depth ss funs n ns total p = max_depth ss (call_graph funs n ns total p).
Proof.
  induction p; cbn [fast_depth]; try reflexivity.
  rewrite (proj1 word_depth.call_graph_eqns).
  rewrite max_depth_mk_Branch.
  now rewrite IHp1, IHp2.
Qed.

Fixpoint seq_leaves {a} (p : wordLang.prog a) : list (wordLang.prog a) :=
  match p with
  | wordLang.Seq p q => seq_leaves p ++ seq_leaves q
  | _ => [p]
  end.

Definition join_depth (x y : option N) : option N := OPTION_MAP2 MAX x y.

Lemma join_depth_assoc x y z :
  join_depth x (join_depth y z) = join_depth (join_depth x y) z.
Proof.
  destruct x as [x|], y as [y|], z as [z|];
    cbv [join_depth OPTION_MAP2 IS_SOME THE]; cbn; try reflexivity.
  repeat rewrite MAX_max.
  now rewrite N.max_assoc.
Qed.

Lemma join_depth_zero_r x : join_depth x (Some 0) = x.
Proof.
  destruct x as [x|]; cbv [join_depth OPTION_MAP2 IS_SOME THE]; cbn;
    try reflexivity.
  rewrite MAX_max, N.max_0_r; reflexivity.
Qed.

Lemma join_depth_zero_l x : join_depth (Some 0) x = x.
Proof.
  destruct x as [x|]; cbv [join_depth OPTION_MAP2 IS_SOME THE]; cbn;
    try reflexivity.
  rewrite MAX_max, N.max_0_l; reflexivity.
Qed.

Lemma fold_depth_app l r :
  fold_right join_depth (Some 0) (l ++ r) =
  join_depth (fold_right join_depth (Some 0) l)
             (fold_right join_depth (Some 0) r).
Proof.
  induction l as [|x xs IH]; cbn.
  - symmetry; apply join_depth_zero_l.
  - rewrite IH, join_depth_assoc. reflexivity.
Qed.

Lemma fast_depth_leaves {a} ss (funs : num_map (N * wordLang.prog a)) n ns total p :
  fast_depth ss funs n ns total p =
  fold_right join_depth (Some 0)
    (List.map (fun q => max_depth ss (call_graph funs n ns total q))
      (seq_leaves p)).
Proof.
  induction p; cbn [fast_depth seq_leaves]; try
    (cbn [List.map fold_right]; rewrite join_depth_zero_r; reflexivity).
  rewrite List.map_app, fold_depth_app.
  now rewrite IHp1, IHp2.
Qed.
