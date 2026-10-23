From Galette Require Import Base.
From InitE.Compilation Require Import StructuredDepth MaximumCall837Via598From606Context.

Definition leaves := StructuredDepth.leaves MaximumCall837Via598From606Context.body.
Definition depth := MaximumCall837Via598From606Context.depth.
Definition funs := MaximumCall837Via598From606Context.funs.
Definition callee := MaximumCall837Via598From606Context.callee.
