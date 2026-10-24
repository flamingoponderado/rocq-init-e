From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumCall869Context.

Definition prefix := List.firstn 7 MaximumCall869Context.leaves.
Definition suffix := List.firstn 216 (List.skipn 8 MaximumCall869Context.leaves).
Definition tail := List.skipn 224 MaximumCall869Context.leaves.
