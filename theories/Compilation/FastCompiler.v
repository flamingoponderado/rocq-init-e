(** Computational compiler with proved exact register-allocation replacement.
    The challenge and its original compiler specification are unchanged. *)
From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.encoders.asm Require Import asm.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.cakeml.compiler.backend Require backend word_to_word wordLang word_simp
 word_inst word_alloc word_cse word_copy word_unreach word_remove word_to_stack
 word_depth bvl_to_bvi.
From Galette.cakeml.pancake Require pan_to_word.
From InitE.InitE Require Import BaselineCompiler NativeCompilation.
From InitE.Compilation Require FastAllocation.
Open Scope N_scope.
Definition word_alloc_fast {a} fc (c : asm_config a) alg k (prog : wordLang.prog a) col_opt :=
 let tree := word_alloc.get_clash_tree prog [] in
 let fs := word_alloc.get_stack_only prog in
 let forced := word_alloc.get_forced c prog [] in
 match word_alloc.oracle_colour_ok k col_opt tree prog forced with
 | None =>
   let '(heu_moves,spillcosts) := word_alloc.get_heuristics alg fc prog in
   match FastAllocation.select_reg_alloc_fast alg spillcosts k heu_moves tree forced fs with
   | ml_monadBase.M_success col => word_alloc.apply_colour (word_alloc.total_colour col) prog
   | ml_monadBase.M_failure _ => prog
   end
 | Some col_prog => col_prog
 end.
Theorem word_alloc_fast_exact {a} fc (c : asm_config a) alg k prog col_opt :
 word_alloc_fast fc c alg k prog col_opt = word_alloc.word_alloc fc c alg k prog col_opt.
Proof.
 unfold word_alloc_fast,word_alloc.word_alloc.
 destruct (word_alloc.oracle_colour_ok k col_opt (word_alloc.get_clash_tree prog []) prog (word_alloc.get_forced c prog [])); [reflexivity|].
 destruct (word_alloc.get_heuristics alg fc prog) as [moves costs].
 rewrite FastAllocation.select_reg_alloc_fast_exact. reflexivity.
Qed.
Definition compile_single_fast {a} two reg_count alg (c : asm_config a)
 (p : (N*(N*wordLang.prog a))*option (num_map N)) :=
 let '((name,(argc,prog)),col) := p in
 let prog := word_simp.compile_exp prog in
 let inst := word_inst.inst_select c (wordLang.max_var prog+1) prog in
 let ssa := word_alloc.full_ssa_cc_trans argc inst in
 let dead := word_alloc.remove_dead_prog ssa in
 let cse := word_cse.word_common_subexp_elim dead in
 let cp := word_copy.copy_prop cse in
 let two_prog := word_inst.three_to_two_reg_prog two cp in
 let unreach := word_unreach.remove_unreach two_prog in
 let dead := word_alloc.remove_dead_prog unreach in
 (name,(argc,word_alloc_fast name c alg reg_count dead col)).
Theorem compile_single_fast_exact {a} two regs alg (c : asm_config a) p :
 compile_single_fast two regs alg c p = word_to_word.compile_single two regs alg c p.
Proof.
 destruct p as [[name [argc prog]] col]. unfold compile_single_fast,word_to_word.compile_single.
 rewrite word_alloc_fast_exact. reflexivity.
Qed.
Definition full_compile_single_fast {a} two regs alg (c : asm_config a) p :=
 let '(name,(argc,prog)) := compile_single_fast two regs alg c p in
 (name,(argc,word_remove.remove_must_terminate prog)).
Theorem full_compile_single_fast_exact {a} two regs alg (c : asm_config a) p :
 full_compile_single_fast two regs alg c p = word_to_word.full_compile_single two regs alg c p.
Proof.
 unfold full_compile_single_fast,word_to_word.full_compile_single.
 rewrite compile_single_fast_exact. reflexivity.
Qed.
Definition compile_fast {a} (wc : word_to_word.config) (ac : asm_config a) progs :=
 let two := asm.two_reg_arith ac in
 let regs := asm.reg_count ac - (5+LENGTH (asm.avoid_regs ac)) in
 let '(oracles,col) := word_to_word.next_n_oracle (LENGTH progs) (word_to_word.col_oracle wc) in
 (col,MAP (full_compile_single_fast two regs (word_to_word.reg_alg wc) ac) (ZIP (progs,oracles))).
Theorem compile_fast_exact {a} wc (ac : asm_config a) progs :
 compile_fast wc ac progs = word_to_word.compile wc ac progs.
Proof.
 unfold compile_fast,word_to_word.compile.
 destruct (word_to_word.next_n_oracle (LENGTH progs) (word_to_word.col_oracle wc)) as [oracles col].
 cbv beta iota zeta. f_equal. apply List.map_ext. intro p. apply full_compile_single_fast_exact.
Qed.
Definition compileWithConfigFast c (ac : asm_config 64) declarations :=
 let prog := pan_to_word.compile_prog (asm.ISA ac) declarations in
 let '(col,wprog) := compile_fast (backend.word_to_word_conf c) ac prog in
 let '(bm,(c',(fs,p))) := word_to_stack.compile ac false wprog in
 let maximum := word_depth.max_depth (word_to_stack.stack_frame_size c')
   (word_depth.full_call_graph bvl_to_bvi.InitGlobals_location (fromAList wprog)) in
 (backend.from_stack ac c LN p bm,maximum).
Theorem compileWithConfigFast_exact c ac declarations :
 compileWithConfigFast c ac declarations = compileWithConfig c ac declarations.
Proof. unfold compileWithConfigFast,compileWithConfig. rewrite compile_fast_exact. reflexivity. Qed.
Definition baselineCompilationFast :=
 compileWithConfigFast baselineBackendConfig riscv_target.riscv_config SourceDeclarations.sourceDeclarations.
Local Opaque compileWithConfig.
Theorem baselineCompilationFast_exact : baselineCompilationFast = baselineCompilation.
Proof.
 unfold baselineCompilationFast. rewrite compileWithConfigFast_exact.
 exact direct_compilation_exact.
Qed.
