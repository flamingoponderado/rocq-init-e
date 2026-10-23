From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.coretypes Require Import option.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum.
Open Scope N_scope.

Fixpoint leaves {a} (p : wordLang.prog a) : list (wordLang.prog a) :=
  match p with
  | wordLang.Seq p q => leaves p ++ leaves q
  | wordLang.If _ _ _ p q => leaves p ++ leaves q
  | wordLang.Loop _ p _ => leaves p
  | wordLang.MustTerminate p => leaves p
  | _ => [p]
  end.

Lemma depth_leaves {a} ss (funs : num_map (N * wordLang.prog a)) n ns total p :
  word_depth.max_depth ss (word_depth.call_graph funs n ns total p) =
  fold_right FastMaximum.join_depth (Some 0)
    (List.map (fun q => word_depth.max_depth ss
      (word_depth.call_graph funs n ns total q)) (leaves p)).
Proof.
  induction p; cbn [leaves]; try
    (cbn [List.map fold_right]; rewrite FastMaximum.join_depth_zero_r; reflexivity).
  - rewrite (proj1 (proj2 (proj2 (proj2 word_depth.call_graph_eqns)))).
    exact IHp.
  - rewrite (proj1 word_depth.call_graph_eqns).
    rewrite FastMaximum.max_depth_mk_Branch.
    rewrite List.map_app, FastMaximum.fold_depth_app.
    now rewrite IHp1, IHp2.
  - rewrite (proj1 (proj2 word_depth.call_graph_eqns)).
    rewrite FastMaximum.max_depth_mk_Branch.
    rewrite List.map_app, FastMaximum.fold_depth_app.
    now rewrite IHp1, IHp2.
  - rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 word_depth.call_graph_eqns))))))).
    exact IHp.
Qed.
