From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum CallDepthLemma
  MaximumContext MaximumCall595StructuredContextFrom608 MaximumCall624Via595ContextFrom608.
Open Scope N_scope.

Definition leaf := List.nth 1067 MaximumCall595StructuredContextFrom608.leaves wordLang.Skip.
Definition leaf_args :=
  match leaf with wordLang.Call _ _ args _ => args | _ => [] end.
Definition leaf_ret :=
  match leaf with wordLang.Call ret _ _ _ => ret | _ => None end.
Definition leaf_handler :=
  match leaf with wordLang.Call _ _ _ handler => handler | _ => None end.
Definition ret_data := THE leaf_ret.
Definition handler_data := THE leaf_handler.
Definition callee_argc :=
  match sptree.lookup 624 MaximumCall595StructuredContextFrom608.funs with
  | Some (argc, _) => argc
  | None => 0
  end.

Lemma leaf_shape :
  leaf = wordLang.Call (Some ret_data) (Some 624) leaf_args (Some handler_data).
Proof. vm_cast_no_check (eq_refl leaf). Qed.

Lemma body_lookup :
  sptree.lookup 624 MaximumCall595StructuredContextFrom608.funs =
  Some (callee_argc, MaximumCall624Via595ContextFrom608.body).
Proof. vm_cast_no_check (eq_refl (sptree.lookup 624 MaximumCall595StructuredContextFrom608.funs)). Qed.

Definition callee_body_depth :=
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall624Via595ContextFrom608.depth MaximumCall624Via595ContextFrom608.leaves).

Lemma callee_body_depth_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall624Via595ContextFrom608.funs 624 [624]
      (sptree.size MaximumContext.funs) MaximumCall624Via595ContextFrom608.body) =
  callee_body_depth.
Proof.
  unfold callee_body_depth, MaximumCall624Via595ContextFrom608.depth, MaximumCall624Via595ContextFrom608.leaves.
  transitivity
    (FastMaximum.fast_depth MaximumContext.frames
      MaximumCall624Via595ContextFrom608.funs 624 [624]
      (sptree.size MaximumContext.funs) MaximumCall624Via595ContextFrom608.body).
  - symmetry; apply FastMaximum.fast_depth_exact.
  - apply FastMaximum.fast_depth_leaves.
Qed.

Lemma leaf_depth_split :
  MaximumCall595StructuredContextFrom608.depth leaf =
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames
      (word_depth.Call MaximumCall595StructuredContextFrom608.callee
        (word_depth.Const 3 (word_depth.Call 624 word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (OPTION_MAP2 N.add
        (sptree.lookup MaximumCall595StructuredContextFrom608.callee MaximumContext.frames)
        (OPTION_MAP (N.add 3) callee_body_depth))
      (OPTION_MAP2 MAX
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall595StructuredContextFrom608.funs
            MaximumCall595StructuredContextFrom608.callee [MaximumCall595StructuredContextFrom608.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd handler_data))))
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall595StructuredContextFrom608.funs
            MaximumCall595StructuredContextFrom608.callee [MaximumCall595StructuredContextFrom608.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd (snd ret_data))))))).
Proof.
  unfold MaximumCall595StructuredContextFrom608.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_subst
    MaximumContext.frames MaximumCall595StructuredContextFrom608.funs MaximumCall595StructuredContextFrom608.callee
    [MaximumCall595StructuredContextFrom608.callee] (sptree.size MaximumContext.funs)
    624 leaf_args ret_data handler_data
    callee_argc MaximumCall624Via595ContextFrom608.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall624Via595ContextFrom608.funs, MaximumCall624Via595ContextFrom608.callee in Hbody.
    exact Hbody.
Qed.

Lemma leaf_depth_compact :
  MaximumCall595StructuredContextFrom608.depth leaf =
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall595StructuredContextFrom608.funs MaximumCall595StructuredContextFrom608.callee
    [MaximumCall595StructuredContextFrom608.callee] (sptree.size MaximumContext.funs)
    624 ret_data handler_data callee_body_depth.
Proof.
  unfold MaximumCall595StructuredContextFrom608.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_compact
    MaximumContext.frames MaximumCall595StructuredContextFrom608.funs
    MaximumCall595StructuredContextFrom608.callee [MaximumCall595StructuredContextFrom608.callee]
    (sptree.size MaximumContext.funs) 624 leaf_args ret_data handler_data
    callee_argc MaximumCall624Via595ContextFrom608.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall624Via595ContextFrom608.funs, MaximumCall624Via595ContextFrom608.callee in Hbody.
    exact Hbody.
Qed.
