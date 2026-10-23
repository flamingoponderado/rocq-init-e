From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall625Via863Context.

Definition outer := List.nth 13 MaximumCall625Via863Context.leaves wordLang.Skip.
Definition leaves := StructuredDepth.leaves outer.
Definition depth := MaximumCall625Via863Context.depth.
Definition callee := MaximumCall625Via863Context.callee.
Definition funs := MaximumCall625Via863Context.funs.
