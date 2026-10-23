From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum CallDepthLemma
  MaximumContext MaximumCall871Context MaximumCall870Context.
Open Scope N_scope.

Definition leaf := List.nth 1 MaximumCall871Context.leaves wordLang.Skip.
Definition leaf_args :=
  match leaf with wordLang.Call _ _ args _ => args | _ => [] end.
Definition leaf_ret :=
  match leaf with wordLang.Call ret _ _ _ => ret | _ => None end.
Definition leaf_handler :=
  match leaf with wordLang.Call _ _ _ handler => handler | _ => None end.
Definition ret_data := THE leaf_ret.
Definition handler_data := THE leaf_handler.
Definition callee_argc :=
  match sptree.lookup 870 MaximumCall871Context.funs with
  | Some (argc, _) => argc
  | None => 0
  end.

Lemma leaf_shape :
  leaf = wordLang.Call (Some ret_data) (Some 870) leaf_args (Some handler_data).
Proof. vm_cast_no_check (eq_refl leaf). Qed.

Lemma body_lookup :
  sptree.lookup 870 MaximumCall871Context.funs =
  Some (callee_argc, MaximumCall870Context.body).
Proof. vm_cast_no_check (eq_refl (sptree.lookup 870 MaximumCall871Context.funs)). Qed.

Definition callee_body_depth :=
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall870Context.depth MaximumCall870Context.leaves).

Lemma callee_body_depth_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall870Context.funs 870 [870]
      (sptree.size MaximumContext.funs) MaximumCall870Context.body) =
  callee_body_depth.
Proof.
  unfold callee_body_depth, MaximumCall870Context.depth, MaximumCall870Context.leaves.
  transitivity
    (FastMaximum.fast_depth MaximumContext.frames
      MaximumCall870Context.funs 870 [870]
      (sptree.size MaximumContext.funs) MaximumCall870Context.body).
  - symmetry; apply FastMaximum.fast_depth_exact.
  - apply FastMaximum.fast_depth_leaves.
Qed.

Lemma leaf_depth_split :
  MaximumCall871Context.depth leaf =
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames
      (word_depth.Call MaximumCall871Context.callee
        (word_depth.Const 3 (word_depth.Call 870 word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (OPTION_MAP2 N.add
        (sptree.lookup MaximumCall871Context.callee MaximumContext.frames)
        (OPTION_MAP (N.add 3) callee_body_depth))
      (OPTION_MAP2 MAX
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall871Context.funs
            MaximumCall871Context.callee [MaximumCall871Context.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd handler_data))))
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall871Context.funs
            MaximumCall871Context.callee [MaximumCall871Context.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd (snd ret_data))))))).
Proof.
  unfold MaximumCall871Context.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_subst
    MaximumContext.frames MaximumCall871Context.funs MaximumCall871Context.callee
    [MaximumCall871Context.callee] (sptree.size MaximumContext.funs)
    870 leaf_args ret_data handler_data
    callee_argc MaximumCall870Context.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall870Context.funs, MaximumCall870Context.callee in Hbody.
    exact Hbody.
Qed.

Lemma leaf_depth_compact :
  MaximumCall871Context.depth leaf =
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall871Context.funs MaximumCall871Context.callee
    [MaximumCall871Context.callee] (sptree.size MaximumContext.funs)
    870 ret_data handler_data callee_body_depth.
Proof.
  unfold MaximumCall871Context.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_compact
    MaximumContext.frames MaximumCall871Context.funs
    MaximumCall871Context.callee [MaximumCall871Context.callee]
    (sptree.size MaximumContext.funs) 870 leaf_args ret_data handler_data
    callee_argc MaximumCall870Context.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall870Context.funs,
      MaximumCall870Context.callee in Hbody.
    exact Hbody.
Qed.
