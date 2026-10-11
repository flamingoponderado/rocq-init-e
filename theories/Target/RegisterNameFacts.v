(** Concrete register-name map facts needed by backend_config_ok. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.misc Require Import misc.
From Galette.cakeml.compiler.backend Require Import stack_names.
From Galette.cakeml.compiler.backend.riscv Require riscv_config.
Open Scope N_scope.
Theorem riscv_name_large n : 31 <= n -> find_name riscv_config.riscv_names n = n.
Proof.
 intros Hn; unfold find_name,tlookup,riscv_config.riscv_names.
 cbn beta.
 rewrite !lookup_insert,lookup_LN.
 repeat match goal with |- context [if decide ?P then _ else _] => destruct (decide P); [try lia|] end.
 reflexivity.
Qed.

Definition riscv_name_inverse (n : N) : N :=
 if n =? 1 then 0 else if n =? 10 then 1 else if n =? 11 then 2 else if n =? 12 then 3 else if n =? 13 then 4 else if n =? 27 then 10 else if n =? 28 then 11 else if n =? 29 then 12 else if n =? 30 then 13 else if n =? 0 then 27 else if n =? 2 then 28 else if n =? 3 then 29 else if n =? 4 then 30 else n.

Lemma inverse_large n : 31 <= n -> riscv_name_inverse n = n.
Proof.
 intros H; unfold riscv_name_inverse.
 repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; [apply N.eqb_eq in E; lia|] end.
 reflexivity.
Qed.

Theorem name_left_inverse n : riscv_name_inverse (find_name riscv_config.riscv_names n) = n.
Proof.
 destruct (N.le_gt_cases 31 n) as [H|H].
 - rewrite ?riscv_name_large by exact H; rewrite inverse_large by exact H; rewrite ?riscv_name_large by exact H; reflexivity.
 - assert (n=0 \/ n=1 \/ n=2 \/ n=3 \/ n=4 \/ n=5 \/ n=6 \/ n=7 \/ n=8 \/ n=9 \/ n=10 \/ n=11 \/ n=12 \/ n=13 \/ n=14 \/ n=15 \/ n=16 \/ n=17 \/ n=18 \/ n=19 \/ n=20 \/ n=21 \/ n=22 \/ n=23 \/ n=24 \/ n=25 \/ n=26 \/ n=27 \/ n=28 \/ n=29 \/ n=30) by lia.
   destruct H0 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; subst n; vm_compute; reflexivity.
Qed.

Theorem name_right_inverse n : find_name riscv_config.riscv_names (riscv_name_inverse n) = n.
Proof.
 destruct (N.le_gt_cases 31 n) as [H|H].
 - rewrite ?riscv_name_large by exact H; rewrite inverse_large by exact H; rewrite ?riscv_name_large by exact H; reflexivity.
 - assert (n=0 \/ n=1 \/ n=2 \/ n=3 \/ n=4 \/ n=5 \/ n=6 \/ n=7 \/ n=8 \/ n=9 \/ n=10 \/ n=11 \/ n=12 \/ n=13 \/ n=14 \/ n=15 \/ n=16 \/ n=17 \/ n=18 \/ n=19 \/ n=20 \/ n=21 \/ n=22 \/ n=23 \/ n=24 \/ n=25 \/ n=26 \/ n=27 \/ n=28 \/ n=29 \/ n=30) by lia.
   destruct H0 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; subst n; vm_compute; reflexivity.
Qed.

Theorem riscv_names_bijective : BIJ (find_name riscv_config.riscv_names) UNIV UNIV.
Proof.
 unfold BIJ,INJ,SURJ,pred_set.IN,UNIV; split; split.
 - auto.
 - intros x y _ E; pose proof (f_equal riscv_name_inverse E) as H.
   rewrite !name_left_inverse in H; exact H.
 - auto.
 - intros x _; exists (riscv_name_inverse x); split; [exact I|apply name_right_inverse].
Qed.

Theorem riscv_names_admissible : names_ok riscv_config.riscv_names 32 [0;2;3;4;31] = true.
Proof. vm_compute; reflexivity. Qed.
