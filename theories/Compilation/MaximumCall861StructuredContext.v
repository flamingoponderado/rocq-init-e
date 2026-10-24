From Galette Require Import Base.
From InitE.Compilation Require Import StructuredDepth MaximumCall861Via867Context.

Definition leaves := StructuredDepth.leaves MaximumCall861Via867Context.body.
Definition depth := MaximumCall861Via867Context.depth.
Definition funs := MaximumCall861Via867Context.funs.
Definition callee := MaximumCall861Via867Context.callee.
