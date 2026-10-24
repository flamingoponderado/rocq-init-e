From Galette Require Import Base.
From InitE.Compilation Require Import StructuredDepth MaximumCall867Via868Context.

Definition leaves := StructuredDepth.leaves MaximumCall867Via868Context.body.
Definition depth := MaximumCall867Via868Context.depth.
Definition funs := MaximumCall867Via868Context.funs.
Definition callee := MaximumCall867Via868Context.callee.
