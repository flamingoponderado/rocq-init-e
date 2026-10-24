From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From InitE.Compilation Require Import CallDepthLemma FastMaximum
  MaximumContext MaximumCall595StructuredContextFrom608 MaximumCall595Leaf1055SplitFrom608 MaximumCall618Via595ValueFrom608.

Definition cached_depth :=
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall595StructuredContextFrom608.funs MaximumCall595StructuredContextFrom608.callee
    [MaximumCall595StructuredContextFrom608.callee] (sptree.size MaximumContext.funs)
    618 MaximumCall595Leaf1055SplitFrom608.ret_data MaximumCall595Leaf1055SplitFrom608.handler_data
    MaximumCall618Via595ValueFrom608.depth_value.

Lemma cached_depth_eq :
  MaximumCall595StructuredContextFrom608.depth MaximumCall595Leaf1055SplitFrom608.leaf = cached_depth.
Proof.
  rewrite MaximumCall595Leaf1055SplitFrom608.leaf_depth_compact.
  unfold cached_depth, MaximumCall595Leaf1055SplitFrom608.callee_body_depth,
    MaximumCall618Via595ValueFrom608.depth_value.
  apply f_equal.
  apply f_equal.
  exact MaximumCall618Via595ValueFrom608.values_eq.
Qed.

Definition value := Eval vm_compute in cached_depth.
Lemma value_eq : MaximumCall595StructuredContextFrom608.depth MaximumCall595Leaf1055SplitFrom608.leaf = value.
Proof.
  rewrite cached_depth_eq.
  vm_cast_no_check (eq_refl value).
Qed.
