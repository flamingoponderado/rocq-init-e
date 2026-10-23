From Galette Require Import Base.
From InitE.Compilation Require Import StructuredDepth MaximumCall598Via599From606Context.

Definition leaves := StructuredDepth.leaves MaximumCall598Via599From606Context.body.
Definition depth := MaximumCall598Via599From606Context.depth.
Definition funs := MaximumCall598Via599From606Context.funs.
Definition callee := MaximumCall598Via599From606Context.callee.
