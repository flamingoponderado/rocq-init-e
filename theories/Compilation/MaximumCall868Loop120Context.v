From Galette Require Import Base.
From Galette.cakeml.compiler.backend Require Import wordLang.
From InitE.Compilation Require Import StructuredDepth MaximumCall868Context MaximumCall868Pieces.

Definition outer := List.nth 120 MaximumCall868Pieces.suffix wordLang.Skip.
Definition body := match outer with wordLang.Loop _ p _ => p | _ => wordLang.Skip end.
Definition leaves := StructuredDepth.leaves body.
Definition depth := MaximumCall868Context.depth.
Definition callee := MaximumCall868Context.callee.
Definition funs := MaximumCall868Context.funs.
