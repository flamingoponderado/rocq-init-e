From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum CallDepthLemma
  MaximumContext MaximumCall599Via603From619From622ContextFrom860 MaximumCall598Via599From619From622ContextFrom860.
Open Scope N_scope.

Definition leaf := List.nth 3 MaximumCall599Via603From619From622ContextFrom860.leaves wordLang.Skip.
Definition leaf_args :=
  match leaf with wordLang.Call _ _ args _ => args | _ => [] end.
Definition leaf_ret :=
  match leaf with wordLang.Call ret _ _ _ => ret | _ => None end.
Definition leaf_handler :=
  match leaf with wordLang.Call _ _ _ handler => handler | _ => None end.
Definition ret_data := THE leaf_ret.
Definition handler_data := THE leaf_handler.
Definition callee_argc :=
  match sptree.lookup 598 MaximumCall599Via603From619From622ContextFrom860.funs with
  | Some (argc, _) => argc
  | None => 0
  end.

Lemma leaf_shape :
  leaf = wordLang.Call (Some ret_data) (Some 598) leaf_args (Some handler_data).
Proof. vm_cast_no_check (eq_refl leaf). Qed.

Lemma body_lookup :
  sptree.lookup 598 MaximumCall599Via603From619From622ContextFrom860.funs =
  Some (callee_argc, MaximumCall598Via599From619From622ContextFrom860.body).
Proof. vm_cast_no_check (eq_refl (sptree.lookup 598 MaximumCall599Via603From619From622ContextFrom860.funs)). Qed.

Definition callee_body_depth :=
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall598Via599From619From622ContextFrom860.depth MaximumCall598Via599From619From622ContextFrom860.leaves).

Lemma callee_body_depth_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall598Via599From619From622ContextFrom860.funs 598 [598]
      (sptree.size MaximumContext.funs) MaximumCall598Via599From619From622ContextFrom860.body) =
  callee_body_depth.
Proof.
  unfold callee_body_depth, MaximumCall598Via599From619From622ContextFrom860.depth, MaximumCall598Via599From619From622ContextFrom860.leaves.
  transitivity
    (FastMaximum.fast_depth MaximumContext.frames
      MaximumCall598Via599From619From622ContextFrom860.funs 598 [598]
      (sptree.size MaximumContext.funs) MaximumCall598Via599From619From622ContextFrom860.body).
  - symmetry; apply FastMaximum.fast_depth_exact.
  - apply FastMaximum.fast_depth_leaves.
Qed.

Lemma leaf_depth_split :
  MaximumCall599Via603From619From622ContextFrom860.depth leaf =
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames
      (word_depth.Call MaximumCall599Via603From619From622ContextFrom860.callee
        (word_depth.Const 3 (word_depth.Call 598 word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (OPTION_MAP2 N.add
        (sptree.lookup MaximumCall599Via603From619From622ContextFrom860.callee MaximumContext.frames)
        (OPTION_MAP (N.add 3) callee_body_depth))
      (OPTION_MAP2 MAX
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall599Via603From619From622ContextFrom860.funs
            MaximumCall599Via603From619From622ContextFrom860.callee [MaximumCall599Via603From619From622ContextFrom860.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd handler_data))))
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall599Via603From619From622ContextFrom860.funs
            MaximumCall599Via603From619From622ContextFrom860.callee [MaximumCall599Via603From619From622ContextFrom860.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd (snd ret_data))))))).
Proof.
  unfold MaximumCall599Via603From619From622ContextFrom860.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_subst
    MaximumContext.frames MaximumCall599Via603From619From622ContextFrom860.funs MaximumCall599Via603From619From622ContextFrom860.callee
    [MaximumCall599Via603From619From622ContextFrom860.callee] (sptree.size MaximumContext.funs)
    598 leaf_args ret_data handler_data
    callee_argc MaximumCall598Via599From619From622ContextFrom860.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall598Via599From619From622ContextFrom860.funs, MaximumCall598Via599From619From622ContextFrom860.callee in Hbody.
    exact Hbody.
Qed.

Lemma leaf_depth_compact :
  MaximumCall599Via603From619From622ContextFrom860.depth leaf =
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall599Via603From619From622ContextFrom860.funs MaximumCall599Via603From619From622ContextFrom860.callee
    [MaximumCall599Via603From619From622ContextFrom860.callee] (sptree.size MaximumContext.funs)
    598 ret_data handler_data callee_body_depth.
Proof.
  unfold MaximumCall599Via603From619From622ContextFrom860.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_compact
    MaximumContext.frames MaximumCall599Via603From619From622ContextFrom860.funs
    MaximumCall599Via603From619From622ContextFrom860.callee [MaximumCall599Via603From619From622ContextFrom860.callee]
    (sptree.size MaximumContext.funs) 598 leaf_args ret_data handler_data
    callee_argc MaximumCall598Via599From619From622ContextFrom860.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall598Via599From619From622ContextFrom860.funs, MaximumCall598Via599From619From622ContextFrom860.callee in Hbody.
    exact Hbody.
Qed.
