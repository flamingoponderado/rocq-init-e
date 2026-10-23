From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall621Via595Context.

Definition outer := List.nth 148 MaximumCall621Via595Context.leaves wordLang.Skip.
Definition leaves := StructuredDepth.leaves outer.
Definition depth := MaximumCall621Via595Context.depth.
Definition callee := MaximumCall621Via595Context.callee.
Definition funs := MaximumCall621Via595Context.funs.
Definition leaf := outer.
