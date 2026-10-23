From Galette Require Import Base.
From Galette.HOL.src.list.src Require Import list.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From InitE.InitE Require Import BaselineCompiler.
Open Scope N_scope.
Definition ac := riscv_target.riscv_config.
Definition regs := Eval vm_compute in
 (asm.reg_count ac - (5 + LENGTH (asm.avoid_regs ac))).
Definition alg := Eval vm_compute in
 word_to_word.reg_alg (backend.word_to_word_conf baselineBackendConfig).
