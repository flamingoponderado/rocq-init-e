From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import MaximumListChunks
  MaximumCall622Via595Context MaximumCall622Leaf130Context MaximumCall622Leaf130OuterValue MaximumCall622Via595Chunk16Prefix MaximumCall622Via595Chunk16Suffix.

Definition values :=
  MaximumCall622Via595Chunk16Prefix.values ++ MaximumCall622Leaf130OuterValue.value :: MaximumCall622Via595Chunk16Suffix.values.

Lemma leaf_lookup :
  List.nth_error (MaximumListChunks.chunk_at 16 MaximumCall622Via595Context.leaves)
    2 = Some MaximumCall622Leaf130Context.leaf.
Proof. vm_cast_no_check
  (eq_refl (List.nth_error (MaximumListChunks.chunk_at 16
    MaximumCall622Via595Context.leaves) 2)). Qed.

Lemma values_eq :
  List.map MaximumCall622Via595Context.depth
    (MaximumListChunks.chunk_at 16 MaximumCall622Via595Context.leaves) = values.
Proof.
  unfold values.
  rewrite <- MaximumCall622Via595Chunk16Prefix.values_eq.
  rewrite <- MaximumCall622Via595Chunk16Suffix.values_eq.
  apply (MaximumListChunks.map_replace_middle
    MaximumCall622Via595Context.depth (MaximumListChunks.chunk_at 16 MaximumCall622Via595Context.leaves)
    2 MaximumCall622Leaf130Context.leaf MaximumCall622Leaf130OuterValue.value).
  - exact leaf_lookup.
  - exact MaximumCall622Leaf130OuterValue.value_eq.
Qed.
