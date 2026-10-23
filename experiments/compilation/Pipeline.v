(** Composition of computation checkpoints. This proof is symbolic: it never
    evaluates a concrete compiler pass. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.cakeml.compiler.encoders.asm Require asm.
From Galette.cakeml.compiler.backend Require backend wordLang stackLang labLang
 word_to_word word_to_stack word_depth bvl_to_bvi stack_to_lab stack_rawcall
 stack_alloc stack_remove stack_names data_to_word lab_to_target.
From Galette.cakeml.pancake Require panLang pan_to_word.
From InitE.InitE Require Import NativeCompilation.
Open Scope N_scope.
Theorem compile_with_checkpoints
 (c : backend.config) (ac : asm.asm_config 64) (declarations : list (panLang.decl 64))
 (words optimized : list (N * (N * wordLang.prog 64)))
 (bm : list (word 64)) (wc : word_to_stack.config) (fs : list N)
 (stack raw allocated removed renamed : list (N * stackLang.prog 64))
 (sections : labLang.prog 64)
 (targetResult : option (list word8 * lab_to_target.config)) (maximum : option N)
 (Hfront : pan_to_word.compile_prog (asm.ISA ac) declarations = words)
 (Hword : word_to_word.compile (backend.word_to_word_conf c) ac words = ([],optimized))
 (Hstack : word_to_stack.compile ac false optimized = (bm,(wc,(fs,stack))))
 (Hraw : stack_rawcall.compile stack = raw)
 (Halloc : stack_alloc.compile (backend.data_conf c) raw = allocated)
 (Hremove : stack_remove.compile (stack_to_lab.jump (backend.stack_conf c))
   (asm.addr_offset ac) (stack_to_lab.is_gen_gc (data_to_word.gc_kind (backend.data_conf c)))
   (2 * data_to_word.max_heap_limit 64 (backend.data_conf c) - 1)
   (asm.reg_count ac - (LENGTH (asm.avoid_regs ac) + 3))
   bvl_to_bvi.InitGlobals_location allocated = removed)
 (Hnames : stack_names.compile (stack_to_lab.reg_names (backend.stack_conf c)) removed = renamed)
 (Hsections : MAP stack_to_lab.prog_to_section renamed = sections)
 (Htarget : lab_to_target.compile ac (backend.lab_conf c) sections = targetResult)
 (Hmax : word_depth.max_depth (word_to_stack.stack_frame_size wc)
   (word_depth.full_call_graph bvl_to_bvi.InitGlobals_location (fromAList optimized)) = maximum) :
 compileWithConfig c ac declarations =
 (backend.attach_bitmaps LN c bm targetResult, maximum).
Proof.
 unfold compileWithConfig.
 rewrite Hfront,Hword. cbv beta iota zeta.
 rewrite Hstack. cbv beta iota zeta.
 rewrite Hmax.
 unfold backend.from_stack, stack_to_lab.compile.
 rewrite Hraw,Halloc,Hremove,Hnames,Hsections.
 unfold backend.from_lab. rewrite Htarget. reflexivity.
Qed.
