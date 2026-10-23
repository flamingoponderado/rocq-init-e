From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall598StructuredFrom616From617Context MaximumCall598From616From617Leaf77Split MaximumCall598From616From617Leaf77Value MaximumCall598StructuredFrom616From617Chunk09Prefix MaximumCall598StructuredFrom616From617Chunk09Suffix.

Definition values :=
  MaximumCall598StructuredFrom616From617Chunk09Prefix.values ++ MaximumCall598From616From617Leaf77Value.value :: MaximumCall598StructuredFrom616From617Chunk09Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom616From617Context.leaves)
    5 = Some MaximumCall598From616From617Leaf77Split.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 9
    MaximumCall598StructuredFrom616From617Context.leaves) 5)). Qed.

Lemma values_eq :
  List.map MaximumCall598StructuredFrom616From617Context.depth
    (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom616From617Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall598StructuredFrom616From617Chunk09Prefix.values_eq.
  rewrite <- MaximumCall598StructuredFrom616From617Chunk09Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall598StructuredFrom616From617Context.depth (MaximumListChunks.chunk_at 9 MaximumCall598StructuredFrom616From617Context.leaves)
    5 MaximumCall598From616From617Leaf77Split.leaf MaximumCall598From616From617Leaf77Value.value).
  - exact leaf_lookup.
  - exact MaximumCall598From616From617Leaf77Value.value_eq.
Qed.
