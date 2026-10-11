(** Original L3/Step/Next.lean outer step equation.
    Decoder is the directly translated original RV64IM decoder.
    Shared integer primitives use Galette's L3 model; their agreement with
    the pinned reduced Lean model remains a port review obligation. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.examples.l3_machine_code.riscv.model Require Import riscv.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From InitE.Target Require Import Decode.
Open Scope N_scope.
Definition DecodeAny (f : rawInstType) : instruction :=
 match f with Half h => Decode.DecodeRVC h | Word w => Decode.Decode w end.
Definition NextRISCV (s : riscv_state) : option riscv_state :=
 let '(f,s) := riscv_step.Fetch s in
 let s := riscv.Run (DecodeAny f) s in
 if negb (bool_decide (riscv_state_exception s = NoException)) then None else
 let pc := PC s in
 match NextFetch s with
 | None => riscv_step.update_pc (word_add pc (Skip s)) s
 | Some (BranchTo a) => riscv_step.update_pc a (write'NextFetch None s)
 | _ => None
 end.
Example compressed_unknown h : DecodeAny (Half h) = UnknownInstruction.
Proof. reflexivity. Qed.
