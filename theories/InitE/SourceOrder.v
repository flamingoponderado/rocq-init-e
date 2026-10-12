(** Moving the existing main declaration preserves the original source
    initialization and behaviour; global declaration order is retained. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.string Require Import string.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.pancake Require Import panLang.
From Galette.cakeml.pancake.semantics Require Import panSem panProps.
From InitE.Guest Require Import Ast.
From InitE.InitE Require Import SourceDeclarations SourceSemantics.
Open Scope N_scope.
Open Scope hol_string_scope.

Definition different_function {a} (nm : funname) (d : decl a) : bool :=
 match d with Function fi => negb (bool_decide (name fi = nm)) | _ => true end.

Lemma function_declaration_commutes {a ffi_t} (s : state a ffi_t) fi d ds :
 different_function (name fi) d = true ->
 evaluate_decls s (Function fi::d::ds) = evaluate_decls s (d::Function fi::ds).
Proof.
 destruct d as [fj|sh v e|eid sh|nm fields]; intros H.
 - cbn [different_function] in H.
   apply Bool.negb_true_iff in H.
   assert (Hne : name fi <> name fj).
   { intros E; assert (He : bool_decide (name fj = name fi) = true).
     { apply (proj2 (bool_decide_spec _)); symmetry; exact E. }
     congruence. }
   rewrite !evaluate_decls_cons_cases; cbn [set_code structs code].
   destruct (EVERY (is_wf_shape (structs s) ∘ snd) (params fi) && is_wf_shape (structs s) (fun_decl_return fi)) eqn:Hfi;
   destruct (EVERY (is_wf_shape (structs s) ∘ snd) (params fj) && is_wf_shape (structs s) (fun_decl_return fj)) eqn:Hfj;
   try reflexivity.
   destruct s; cbn; rewrite FUPDATE_COMMUTES by congruence; reflexivity.
 - apply evaluate_decl_commute.
 - rewrite !evaluate_decls_cons_cases; cbn [set_code structs eshapes set_eshapes].
   destruct (EVERY (is_wf_shape (structs s) ∘ snd) (params fi) && is_wf_shape (structs s) (fun_decl_return fi)) eqn:Hfi;
   destruct (bool_decide (FLOOKUP (eshapes s) eid = None) && is_wf_shape (structs s) sh) eqn:Hex;
   reflexivity.
 - rewrite !evaluate_decls_cons_cases; reflexivity.
Qed.

Lemma declaration_suffix_congruence {a ffi_t} d xs ys :
 (forall s : state a ffi_t, evaluate_decls s xs = evaluate_decls s ys) ->
 forall s : state a ffi_t, evaluate_decls s (d::xs) = evaluate_decls s (d::ys).
Proof.
 intros He s.
 change (evaluate_decls s ([d]++xs) = evaluate_decls s ([d]++ys)).
 rewrite !evaluate_decls_append.
 destruct (evaluate_decls s [d]); [apply He|reflexivity].
Qed.

Lemma function_moves_across_prefix {a ffi_t} (fi : fun_decl a) before after :
 EVERY (different_function (name fi)) before = true ->
 forall s : state a ffi_t,
 evaluate_decls s (Function fi::before++after) =
 evaluate_decls s (before++Function fi::after).
Proof.
 induction before as [|d before IH]; intros H s; [reflexivity|].
 cbn [EVERY] in H; apply Bool.andb_true_iff in H as [Hd Hb].
 cbn [List.app].
 rewrite function_declaration_commutes by exact Hd.
 apply declaration_suffix_congruence; intros t; apply IH; exact Hb.
Qed.

Definition sourcePrefix : list (decl 64) := List.removelast guestAst.

Lemma guest_ast_main_last : guestAst = sourcePrefix++[guestFn_main].
Proof. cbn [sourcePrefix guestAst List.removelast List.app]; reflexivity. Qed.

Lemma source_prefix_no_main :
 EVERY (different_function (strlit "main")) sourcePrefix = true.
Proof. vm_compute; reflexivity. Qed.

Lemma splitp_before_named_function {a} nm (fi : fun_decl a) before :
 name fi = nm -> EVERY (different_function nm) before = true ->
 SPLITP (fun d => match d with
  | Function fj => bool_decide (name fj = nm) | _ => false end)
  (before++[Function fi]) = (before,[Function fi]).
Proof.
 intros Hname; induction before as [|d before IH]; intros H.
 - cbn [List.app SPLITP]; rewrite Hname.
   assert (He : bool_decide (nm = nm) = true) by (apply (proj2 (bool_decide_spec _)); reflexivity).
   rewrite He; reflexivity.
 - cbn [EVERY] in H; apply Bool.andb_true_iff in H as [Hd Hb].
   cbn [List.app SPLITP]; destruct d; cbn [different_function] in Hd.
   + apply Bool.negb_true_iff in Hd; rewrite Hd,IH by exact Hb; reflexivity.
   + rewrite IH by exact Hb; reflexivity.
   + rewrite IH by exact Hb; reflexivity.
   + rewrite IH by exact Hb; reflexivity.
Qed.

Lemma source_prefix_nonempty : sourcePrefix <> [].
Proof. cbn [sourcePrefix guestAst List.removelast]; discriminate. Qed.

Lemma source_declarations_main_front :
 sourceDeclarations = guestFn_main::sourcePrefix.
Proof.
 unfold sourceDeclarations,mainFirst; rewrite guest_ast_main_last.
 unfold guestFn_main.
 rewrite splitp_before_named_function by (try reflexivity; exact source_prefix_no_main).
 destruct sourcePrefix as [|d ds] eqn:E.
 - exfalso; apply source_prefix_nonempty; exact E.
 - cbn [List.app]; rewrite List.app_nil_r; reflexivity.
Qed.

Theorem source_declarations_evaluation {ffi_t} (s : state 64 ffi_t) :
 evaluate_decls s sourceDeclarations = evaluate_decls s guestAst.
Proof.
 rewrite source_declarations_main_front,guest_ast_main_last.
 rewrite <- (List.app_nil_r sourcePrefix) at 1.
 unfold guestFn_main at 1 2.
 apply (function_moves_across_prefix _ sourcePrefix []).
 exact source_prefix_no_main.
Qed.

Lemma guest_ast_structs_empty : decs_stcnames [] guestAst = Some [].
Proof. vm_compute; reflexivity. Qed.

Lemma source_declarations_structs_empty : decs_stcnames [] sourceDeclarations = Some [].
Proof. vm_compute; reflexivity. Qed.

Theorem source_declarations_semantics {ffi_t} (s : state 64 ffi_t) start :
 semantics_decls s start sourceDeclarations = semantics_decls s start guestAst.
Proof.
 unfold semantics_decls; rewrite source_declarations_structs_empty,guest_ast_structs_empty.
 rewrite source_declarations_evaluation; reflexivity.
Qed.

Theorem source_declarations_behaviour input :
 semantics_decls (sourceInitialState input) (strlit "main") sourceDeclarations =
 sourceBehaviour input.
Proof. unfold sourceBehaviour; apply source_declarations_semantics. Qed.
