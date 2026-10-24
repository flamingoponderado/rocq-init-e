From Galette Require Import Base.
From InitE.Compilation Require Import StructuredDepth MaximumCall865Via868Context.

Definition leaves := StructuredDepth.leaves MaximumCall865Via868Context.body.
Definition depth := MaximumCall865Via868Context.depth.
Definition funs := MaximumCall865Via868Context.funs.
Definition callee := MaximumCall865Via868Context.callee.
