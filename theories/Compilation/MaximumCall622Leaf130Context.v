From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall622Via595Context.

Definition outer := List.nth 130 MaximumCall622Via595Context.leaves wordLang.Skip.
Definition leaves := StructuredDepth.leaves outer.
Definition depth := MaximumCall622Via595Context.depth.
Definition callee := MaximumCall622Via595Context.callee.
Definition funs := MaximumCall622Via595Context.funs.
Definition leaf := outer.
