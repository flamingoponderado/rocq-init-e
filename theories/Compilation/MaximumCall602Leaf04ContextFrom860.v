From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall602Via606ContextFrom860.

Definition outer := List.nth 4 MaximumCall602Via606ContextFrom860.leaves wordLang.Skip.
Definition leaves := StructuredDepth.leaves outer.
Definition depth := MaximumCall602Via606ContextFrom860.depth.
Definition callee := MaximumCall602Via606ContextFrom860.callee.
Definition funs := MaximumCall602Via606ContextFrom860.funs.
