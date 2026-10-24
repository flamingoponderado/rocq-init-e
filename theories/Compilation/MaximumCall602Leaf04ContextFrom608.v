From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall602Via606ContextFrom608.

Definition outer := List.nth 4 MaximumCall602Via606ContextFrom608.leaves wordLang.Skip.
Definition leaves := StructuredDepth.leaves outer.
Definition depth := MaximumCall602Via606ContextFrom608.depth.
Definition callee := MaximumCall602Via606ContextFrom608.callee.
Definition funs := MaximumCall602Via606ContextFrom608.funs.
