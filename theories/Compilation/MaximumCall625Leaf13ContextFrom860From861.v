From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall625Via860ContextFrom861.

Definition outer := List.nth 13 MaximumCall625Via860ContextFrom861.leaves wordLang.Skip.
Definition leaves := StructuredDepth.leaves outer.
Definition depth := MaximumCall625Via860ContextFrom861.depth.
Definition callee := MaximumCall625Via860ContextFrom861.callee.
Definition funs := MaximumCall625Via860ContextFrom861.funs.
