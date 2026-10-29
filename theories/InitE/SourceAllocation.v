From Galette Require Import Base.
From Stdlib Require Import Lia.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.n_bit.words Require Import lemmas.
From Galette.HOL.src.pred_set.src Require Import pred_set.
From Galette.cakeml.pancake.proofs Require pan_to_wordProof pan_globalsProof.
From Galette.cakeml.compiler.backend Require Import backend_common.
From InitE.InitE Require Import Parameters SourceDeclarations SourceSemantics SourceFacts BaselineLayout.
Open Scope N_scope.
Theorem source_globals_allocatable input :
 pan_to_wordProof.globals_allocatable (sourceInitialState input) sourceDeclarations.
Proof.
 unfold pan_to_wordProof.globals_allocatable.
 rewrite source_structs_empty.
 cbn [option.THE]. rewrite source_globals_size.
 split; [discriminate|].
 split.
 - change (DISJOINT (stack_removeProof.addresses (n2w sourceBase : word 64) (baselineHeapLen-globalsWords))
   (stack_removeProof.addresses (n2w heapEnd) globalsWords)).
   apply pan_globalsProof.DISJOINT_addresses_lemma; repeat split; vm_compute; intuition congruence.
 - split.
   + change (~stack_removeProof.addresses (n2w sourceBase : word 64) (baselineHeapLen-globalsWords) (n2w stackStart)).
     intros Hin; apply pan_globalsProof.in_addresses in Hin as [i [E Hi]].
     change (i<3888119741) in Hi.
     change (n2w stackStart = (n2w sourceBase+n2w i*n2w 8 : word 64)%w) in E.
     rewrite word_mul_n2w,word_add_n2w in E.
     apply (f_equal (@w2n 64)) in E; rewrite !w2n_n2w in E.
     change (33806090240 mod 18446744073709551616 = (2701131776+i*8) mod 18446744073709551616) in E.
     rewrite !N.mod_small in E by lia; lia.
   + vm_compute; congruence.
Qed.
(** Every aligned cell of the guest's scratch arena is ordinary source memory. *)
Theorem scratch_in_ordinaryDomain (address : word 64) :
 w2n address mod 8 = 0 -> scratchStart <= w2n address < scratchEnd ->
 ordinaryDomain address.
Proof.
 intros Haligned Hinside; unfold ordinaryDomain.
 apply (proj2 (pan_globalsProof.in_addresses _ _ _)).
 exists ((w2n address - sourceBase) / 8).
 cbv [scratchStart scratchEnd sourceBase stackStart ramEnd ramStart ramSize stackSize globalsWords] in *.
 split; [|lia].
 change (address = n2w 2701131776 + n2w ((w2n address - 2701131776) / 8) * n2w 8)%w.
 rewrite word_mul_n2w,word_add_n2w,<-(n2w_w2n address) at 1.
 f_equal; lia.
Qed.
