From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall603Via616From618ContextFrom608From860From861 MaximumCall603Via616From618Chunk00From608From860From861 MaximumCall603Via616From618Chunk01From608From860From861 MaximumCall603Via616From618Chunk02From608From860From861 MaximumCall603Via616From618Chunk03From608From860From861 MaximumCall603Via616From618Chunk04From608From860From861 MaximumCall603Via616From618Chunk05From608From860From861 MaximumCall603Via616From618Chunk06From608From860From861 MaximumCall603Via616From618Chunk07From608From860From861 MaximumCall603Via616From618Chunk08From608From860From861.

Definition values :=
  MaximumCall603Via616From618Chunk00From608From860From861.values ++
  MaximumCall603Via616From618Chunk01From608From860From861.values ++
  MaximumCall603Via616From618Chunk02From608From860From861.values ++
  MaximumCall603Via616From618Chunk03From608From860From861.values ++
  MaximumCall603Via616From618Chunk04From608From860From861.values ++
  MaximumCall603Via616From618Chunk05From608From860From861.values ++
  MaximumCall603Via616From618Chunk06From608From860From861.values ++
  MaximumCall603Via616From618Chunk07From608From860From861.values ++
  MaximumCall603Via616From618Chunk08From608From860From861.values.

Lemma values_eq :
  List.map MaximumCall603Via616From618ContextFrom608From860From861.depth MaximumCall603Via616From618ContextFrom608From860From861.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 9
    MaximumCall603Via616From618ContextFrom608From860From861.depth MaximumCall603Via616From618ContextFrom608From860From861.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall603Via616From618Chunk00From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk01From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk02From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk03From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk04From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk05From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk06From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk07From608From860From861.values_eq,
      MaximumCall603Via616From618Chunk08From608From860From861.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
