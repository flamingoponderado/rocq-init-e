From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumCall868Context.

Definition prefix := List.firstn 6 MaximumCall868Context.leaves.
Definition suffix := List.skipn 7 MaximumCall868Context.leaves.
