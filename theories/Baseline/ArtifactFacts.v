(** Kernel facts about imported original literals, not compiler equality. *)
From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From InitE.Baseline Require Import Artifacts BootstrapProgram.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.InitE Require Import BaselineArtifactLayout.
Open Scope N_scope.
Theorem original_literal_sizes :
 LENGTH nativeCode = nativeByteCount /\ LENGTH bitmaps = bitmapWordCount /\
 LENGTH bootPrefix = nativePc-2147483648 /\ LENGTH code = fullRomByteCount.
Proof.
 split; [lazy; reflexivity|].
 split; [lazy; reflexivity|].
 split; lazy; reflexivity.
Qed.
Theorem bootstrap_literal_binding : TAKE 208 bootPrefix = originalBootstrapBytes.
Proof. lazy; reflexivity. Qed.
Theorem encoded_bootstrap_in_rom :
 TAKE 208 code = concat (MAP (fun block => riscv_target.riscv_enc (snd block)) bootstrapBlocks).
Proof. rewrite bootstrap_bytes_match; lazy; reflexivity. Qed.
