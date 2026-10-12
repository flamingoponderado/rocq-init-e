(** Generic encoded-path simulation over the original reduced carrier.
    Interference is arbitrary subject to the original reduced projection;
    every executed step obtains its support from the existing path witness. *)
From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.compiler.encoders.asm Require Import asm asmSem asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.encoders.riscv.proofs Require Import riscv_targetProof.
From InitE.Target Require Import ReducedTypes Configuration StateEmbedding
 StateAgreement TargetProperties ReducedEncoderStep.
Open Scope N_scope.

Theorem reduced_rv_rel_env dom env k s A :
 interference_ok env (Configuration.riscvProj dom) ->
 rv_rel dom (embedriscv_state s) A ->
 rv_rel dom (embedriscv_state (env k s)) A.
Proof.
 intros Hi (Hok & Hg & Hpc & Hm).
 assert (He : riscv_target.riscv_proj dom (embedriscv_state (env k s)) =
              riscv_target.riscv_proj dom (embedriscv_state s)).
 { rewrite !projection_embedding; apply f_equal; exact (Hi k s). }
 destruct (riscv_proj_eq dom (embedriscv_state (env k s)) (embedriscv_state s) He)
  as (Eok & Eg & Epc & Em).
 unfold rv_rel; rewrite Eok,Eg,Epc.
 split; [exact Hok|split; [exact Hg|split; [exact Hpc|]]].
 intros a Ha; rewrite Em by exact Ha; apply Hm; exact Ha.
Qed.

Section ReducedPath.
Variable dom : word 64 -> Prop.
Variable env : N -> ReducedTypes.riscv_state -> ReducedTypes.riscv_state.
Hypothesis Henv : interference_ok env (Configuration.riscvProj dom).

Theorem reduced_path_asserts
 (P Q : ReducedTypes.riscv_state -> Prop) (PA QA : astate -> Prop) :
 (forall s A, rv_rel dom (embedriscv_state s) A -> PA A -> P s) ->
 (forall s A, rv_rel dom (embedriscv_state s) A -> QA A -> Q s) ->
 forall instructions s A (f : N -> N), instructions <> [] ->
 rv_rel dom (embedriscv_state s) A -> run_ok dom A instructions PA ->
 QA (arun A instructions) ->
 asserts (LENGTH instructions-1)
  (fun k s => env (f k) (Configuration.riscvNext s)) s P Q.
Proof.
 intros HP HQ instructions; induction instructions as [|i rest IH];
 intros s A f Hne Hr Hrun HQA; [congruence|].
 destruct rest as [|i' rest'].
 - cbn [LENGTH]; replace (SUC 0-1) with 0 by lia.
   unfold asserts; rewrite num_rec_0.
   cbn [run_ok] in Hrun; destruct (reduced_one_step dom s A i Hr Hrun) as [Hr' _].
   apply HQ with (aexec i A); [apply reduced_rv_rel_env; assumption|exact HQA].
 - cbn [LENGTH] in *.
   replace (SUC (SUC (LENGTH rest'))-1) with (SUC (LENGTH rest')) by lia.
   unfold asserts; rewrite num_rec_SUC.
   fold (asserts (LENGTH rest') (fun k s => env (f k) (Configuration.riscvNext s))).
   cbv zeta; destruct Hrun as (Hs & HPA & Hrun).
   destruct (reduced_one_step dom s A i Hr Hs) as [Hr' _].
   pose proof (reduced_rv_rel_env dom env (f (SUC (LENGTH rest')))
     (Configuration.riscvNext s) (aexec i A) Henv Hr') as Hr''.
   set (s' := env (f (SUC (LENGTH rest'))) (Configuration.riscvNext s)) in *.
   split; [apply HP with (aexec i A); assumption|].
   replace (LENGTH rest') with (LENGTH (i'::rest')-1) by (cbn [LENGTH]; lia).
   apply IH with (aexec i A); [discriminate|exact Hr''|exact Hrun|exact HQA].
Qed.

Theorem reduced_path_asserts2 :
 forall instructions s A (g : N -> N),
 rv_rel dom (embedriscv_state s) A -> run_ok2 dom A instructions ->
 asserts2 (LENGTH instructions) (fun k => env (g k)) Configuration.riscvNext s
  (fun s1 s2 => forall x, x NOTIN dom ->
   ReducedTypes.riscv_state_MEM8 s1 x = ReducedTypes.riscv_state_MEM8 s2 x).
Proof.
 intros instructions; induction instructions as [|i rest IH]; intros s A g Hr Hrun;
 [exact Logic.I|].
 cbn [LENGTH]; unfold asserts2; rewrite num_rec_SUC.
 fold (asserts2 (LENGTH rest) (fun k => env (g k)) Configuration.riscvNext).
 destruct Hrun as (Hs & Hrun).
 destruct (reduced_one_step dom s A i Hr Hs) as [Hr' Hout].
 split.
 - intros x Hx; symmetry; apply Hout; exact Hx.
 - apply IH with (aexec i A); [apply reduced_rv_rel_env; assumption|exact Hrun].
Qed.
End ReducedPath.

Definition reduced_enc_goal (s1 : asm_state 64) (i : asm.asm 64)
 (s2 : asm_state 64) (s : ReducedTypes.riscv_state) : Prop :=
 exists n, forall env,
 interference_ok env (proj Configuration.riscvTarget s1.(mem_domain)) ->
 let pcs := all_pcs (LENGTH (encode (config Configuration.riscvTarget) i)) s1.(pc) in
 asserts n (fun k s => env (n-k) (next Configuration.riscvTarget s)) s
  (fun s' => state_ok Configuration.riscvTarget s' /\
   (forall pc0, pc0 IN pcs 0 ->
    get_byte Configuration.riscvTarget s' pc0 = get_byte Configuration.riscvTarget s pc0) /\
   get_pc Configuration.riscvTarget s' IN pcs (code_alignment (config Configuration.riscvTarget)))
  (fun s' => target_state_rel Configuration.riscvTarget s2 s') /\
 asserts2 (n+1) (fun k => env (n+1-k)) (next Configuration.riscvTarget) s
  (fun s1' s2' => forall x, x NOTIN s1.(mem_domain) ->
   get_byte Configuration.riscvTarget s1' x = get_byte Configuration.riscvTarget s2' x).

Theorem reduced_enc_sim s1 i s2 s (instructions : list riscv.instruction) :
 asm_step riscv_target.riscv_config s1 i s2 ->
 target_state_rel Configuration.riscvTarget s1 s -> instructions <> [] ->
 run_ok s1.(mem_domain) (A0_of s1 (embedriscv_state s)) instructions (PA_of s1 i) ->
 QA_of s2 (arun (A0_of s1 (embedriscv_state s)) instructions) ->
 reduced_enc_goal s1 i s2 s.
Proof.
 intros Hstep Hrel Hne Hrun HQA.
 pose proof Hstep as (Hb & _ & _ & _ & Hasm & _ & _).
 pose proof (proj1 (asm_relation_embedding s1 s) Hrel) as Hfullrel.
 assert (Hr0 : rv_rel s1.(mem_domain) (embedriscv_state s) (A0_of s1 (embedriscv_state s))).
 { destruct Hfullrel as (Hok & Hpc & Hm & _).
   split; [exact Hok|split; [reflexivity|split; [exact Hpc|]]].
   intros a Ha; apply Hm; exact Ha. }
 assert (Hdom : s2.(mem_domain) = s1.(mem_domain)) by (rewrite <- Hasm; apply asm_consts).
 unfold reduced_enc_goal; exists (LENGTH instructions-1); intros env Henv; cbv zeta.
 unfold Configuration.riscvTarget in *; cbn [config next get_byte state_ok get_pc proj] in *.
 split.
 - refine (reduced_path_asserts s1.(mem_domain) env Henv _ _ (PA_of s1 i) (QA_of s2)
   _ _ instructions s (A0_of s1 (embedriscv_state s)) _ Hne Hr0 Hrun HQA).
   + intros s' A' (Hok & Hg & Hpc & Hm) (HmA & HpcA); cbv beta.
     change (forall a, a IN s1.(mem_domain) ->
      ReducedTypes.riscv_state_MEM8 s' a = amem A' a) in Hm.
     change (ReducedTypes.riscv_state_c_PC s' (ReducedTypes.riscv_state_procID s') = apc A') in Hpc.
     split; [rewrite <- validity_embedding; exact Hok|split].
     * intros pc0 Hpc0; assert (Hd : pc0 IN s1.(mem_domain)).
       { apply (bytes_in_memory_all_pcs _ _ 0 _ _ Hb); exact Hpc0. }
       rewrite Hm by exact Hd; rewrite HmA.
       destruct Hrel as (_ & _ & Hm0 & _); symmetry; apply Hm0; exact Hd.
     * rewrite Hpc; exact HpcA.
   + intros s' A' (Hok & Hg & Hpc & Hm) (HpcA & HmA & HrA).
     apply (proj2 (asm_relation_embedding s2 s')).
     unfold target_state_rel.
     cbn [riscv_target.riscv_target config next get_byte state_ok get_pc get_reg get_fp_reg proj
      reg_count avoid_regs fp_reg_count riscv_target.riscv_config]; cbv beta.
     split; [exact Hok|split; [rewrite Hpc; exact HpcA|split; [|split]]].
     * intros ad Had; cbn.
       change (forall a, a IN s1.(mem_domain) ->
        ReducedTypes.riscv_state_MEM8 s' a = amem A' a) in Hm.
       rewrite Hm by (rewrite <- Hdom; exact Had); apply HmA; exact Had.
     * intros r (Hr & Hav); cbn in Hr,Hav |- *; unfold gregs in Hg.
       change (ReducedTypes.riscv_state_c_gpr s' (ReducedTypes.riscv_state_procID s') = aregs A') in Hg.
       rewrite Hg; apply HrA; assumption.
     * intros r Hr; cbn in Hr; lia.
 - replace (LENGTH instructions-1+1) with (LENGTH instructions)
    by (destruct instructions; [congruence|cbn [LENGTH]; lia]).
   refine (reduced_path_asserts2 s1.(mem_domain) env Henv instructions s
     (A0_of s1 (embedriscv_state s)) _ Hr0 _).
   apply run_ok_ok2 with (PA_of s1 i); exact Hrun.
Qed.
