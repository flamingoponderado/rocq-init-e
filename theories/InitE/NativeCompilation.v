(** Executable form of the exact baseline compilation, eliminating unused
    machine callbacks before extraction. Equality is checked by the kernel. *)
From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import alist sptree.
From Galette.cakeml.compiler.encoders.asm Require asm asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.backend Require backend word_to_word word_to_stack word_depth bvl_to_bvi.
From Galette.cakeml.pancake Require pan_to_word panLang.
From Galette.cakeml.compiler.backend.semantics Require targetSem.
From Galette.cakeml.pancake.proofs Require pan_to_targetProof.
From InitE.InitE Require Import BaselineCompiler SourceDeclarations.
Open Scope N_scope.
Definition compileWithConfig (c : backend.config) (ac : asm.asm_config 64)
 (declarations : list (panLang.decl 64)) :=
 let prog := pan_to_word.compile_prog (asm.ISA ac) declarations in
 let '(col,wprog) := word_to_word.compile (backend.word_to_word_conf c) ac prog in
 let '(bm,(c',(fs,p))) := word_to_stack.compile ac false wprog in
 let maximum := word_depth.max_depth (word_to_stack.stack_frame_size c')
   (word_depth.full_call_graph bvl_to_bvi.InitGlobals_location (fromAList wprog)) in
 (backend.from_stack ac c LN p bm,maximum).
Lemma compile_with_config_exact {B C} c (mc : targetSem.machine_config 64 B C) declarations :
 pan_to_targetProof.compile_prog_max c mc declarations =
 compileWithConfig c (asmProps.config (targetSem.target mc)) declarations.
Proof. reflexivity. Qed.
Definition directCompilation := compileWithConfig baselineBackendConfig riscv_target.riscv_config sourceDeclarations.
Theorem direct_compilation_exact : directCompilation = baselineCompilation.
Proof.
 unfold directCompilation,baselineCompilation.
 rewrite compile_with_config_exact.
 apply (f_equal (fun ac => compileWithConfig baselineBackendConfig ac sourceDeclarations)).
 reflexivity.
Qed.
