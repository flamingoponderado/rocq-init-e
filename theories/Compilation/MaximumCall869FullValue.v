From Galette Require Import Base.
From Stdlib Require Import List.
From InitE.Compilation Require Import FastMaximum MaximumCall869Context
  MaximumCall869Pieces MaximumCall869Prefix MaximumCall869Leaf07Split
  MaximumCall869Leaf07Value MaximumCall869SuffixContext MaximumCall869Value
  MaximumCall869TailContext MaximumCall869TailValue.

Definition values :=
  MaximumCall869Prefix.values ++
  (MaximumCall869Leaf07Value.value ::
    (MaximumCall869Value.values ++ MaximumCall869TailValue.values)).

Lemma leaves_shape :
  MaximumCall869Context.leaves =
  MaximumCall869Pieces.prefix ++
    (MaximumCall869Leaf07Split.leaf ::
      (MaximumCall869Pieces.suffix ++ MaximumCall869Pieces.tail)).
Proof. vm_cast_no_check (eq_refl MaximumCall869Context.leaves). Qed.

Lemma suffix_values_eq :
  List.map MaximumCall869Context.depth MaximumCall869Pieces.suffix =
    MaximumCall869Value.values.
Proof. exact MaximumCall869Value.values_eq. Qed.

Lemma tail_values_eq :
  List.map MaximumCall869Context.depth MaximumCall869Pieces.tail =
    MaximumCall869TailValue.values.
Proof. exact MaximumCall869TailValue.values_eq. Qed.

Lemma map_cons {A B} (f : A -> B) x xs :
  List.map f (x :: xs) = f x :: List.map f xs.
Proof. reflexivity. Qed.

Lemma values_eq :
  List.map MaximumCall869Context.depth MaximumCall869Context.leaves = values.
Proof.
  unfold values.
  rewrite leaves_shape.
  rewrite List.map_app.
  rewrite (map_cons MaximumCall869Context.depth
    MaximumCall869Leaf07Split.leaf
    (MaximumCall869Pieces.suffix ++ MaximumCall869Pieces.tail)).
  rewrite List.map_app.
  rewrite MaximumCall869Prefix.values_eq,
    MaximumCall869Leaf07Value.value_eq,
    suffix_values_eq, tail_values_eq.
  reflexivity.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
