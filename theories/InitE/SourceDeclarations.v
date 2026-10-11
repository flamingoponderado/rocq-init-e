(** Original InitE/SourceDeclarationsCore.lean and mainFirstHOL. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From Galette.cakeml.pancake Require Import panLang.
From InitE.Guest Require Import Ast.
Open Scope N_scope.
Open Scope hol_string_scope.
Definition mainFirst (program : list (decl 64)) : list (decl 64) :=
 let '(before,after) := SPLITP (fun declaration =>
   match declaration with
   | Function entry => bool_decide (name entry = strlit "main")
   | _ => false
   end) program in
 match before,after with
 | [],rest => rest
 | before,[] => Function {| name := strlit "main"; inline := false;
      export := false; params := []; body := Return (Const (n2w 0));
      fun_decl_return := One |} :: before
 | before,main::rest => main::before++rest
 end.
Definition sourceDeclarations : list (decl 64) := mainFirst guestAst.
Example source_main_first :
 match sourceDeclarations with Function entry::_ => name entry = strlit "main" | _ => False end.
Proof. vm_compute; reflexivity. Qed.
