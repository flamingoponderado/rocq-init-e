From Galette Require Import Base.
From InitE.Compilation Require Import StructuredDepth MaximumCall595Via602Context.

Definition leaves := StructuredDepth.leaves MaximumCall595Via602Context.body.
Definition depth := MaximumCall595Via602Context.depth.
Definition funs := MaximumCall595Via602Context.funs.
Definition callee := MaximumCall595Via602Context.callee.
