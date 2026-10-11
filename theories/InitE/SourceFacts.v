(** Concrete fixed-source obligations for the compiler theorem. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import finite_map.
From Galette.cakeml.pancake Require Import panLang panStatic pan_globals.
From Galette.cakeml.pancake.semantics Require panSem panProps.
From Galette.cakeml.pancake.proofs Require pan_to_wordProof.
From InitE.InitE Require Import Parameters SourceDeclarations.
Open Scope N_scope.
#[local] Instance shape_eq : EqDecision shape := shape_eq_dec_f.
Definition panopArity (x : exp 64) : bool :=
 match x with Panop _ es => LENGTH es =? 2 | _ => true end.
Lemma boolean_extensionality (x y : bool) : (x = true <-> y = true) -> x = y.
Proof. destruct x,y; intuition discriminate. Qed.
Lemma panop_arity_reflect (x : exp 64) :
 bool_decide (forall op es, x = Panop op es -> LENGTH es = 2) = panopArity x.
Proof.
 apply boolean_extensionality; rewrite bool_decide_spec.
 destruct x; cbn [panopArity].
 all: try (split; [intros _; reflexivity|intros _ op es E; discriminate E]).
 split.
 - intros H; apply N.eqb_eq; eapply H; reflexivity.
 - intros H op es E; inversion E; subst; apply N.eqb_eq in H; exact H.
Qed.
Definition computableGoodPanops (d : decl 64) : bool :=
 match d with
 | Function fi => EVERY (panProps.every_exp panopArity) (panProps.exps_of (body fi))
 | Decl _ _ e => panProps.every_exp panopArity e
 | _ => true
 end.
Lemma good_panops_computation (d : decl 64) :
 pan_to_wordProof.good_panops d = computableGoodPanops d.
Proof.
 assert (H : (fun x : exp 64 => bool_decide (forall op es, x = Panop op es -> LENGTH es = 2)) = panopArity).
 { apply functional_extensionality; intro x; apply panop_arity_reflect. }
 unfold pan_to_wordProof.good_panops, computableGoodPanops.
 rewrite H; reflexivity.
Qed.
Example source_good_panops : EVERY pan_to_wordProof.good_panops sourceDeclarations = true.
Proof.
 assert (H : (@pan_to_wordProof.good_panops 64) = computableGoodPanops).
 { apply functional_extensionality; intro d; apply good_panops_computation. }
 rewrite H; vm_compute; reflexivity.
Qed.
Example source_distinct_names : ALL_DISTINCT (MAP fst (functions sourceDeclarations)) = true.
Proof. vm_compute; reflexivity. Qed.
Example source_distinct_parameters : pan_to_wordProof.distinct_params (functions sourceDeclarations) = true.
Proof. vm_compute; reflexivity. Qed.
Example source_structs_empty : panSem.decs_stcnames [] sourceDeclarations = Some [].
Proof. vm_compute; reflexivity. Qed.
Example source_globals_size :
 SUM (MAP (size_of_sh_with_ctxt []) (pan_globals.dec_shapes sourceDeclarations)) = globalsWords.
Proof. vm_compute; reflexivity. Qed.
Example source_exception_bound : size_of_eids sourceDeclarations < dimword 64.
Proof. vm_compute; reflexivity. Qed.
