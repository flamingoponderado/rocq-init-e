From Galette Require Import Base.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list.
From Galette.HOL.src.coretypes Require Import option.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.cakeml.compiler.backend Require Import word_depth wordLang.
From InitE.Compilation Require Import FastMaximum CallDepthLemma
  MaximumContext MaximumCall598StructuredFrom616From617ContextFrom860From861 MaximumCall837Via598From616From617ContextFrom860From861.
Open Scope N_scope.

Definition leaf := List.nth 77 MaximumCall598StructuredFrom616From617ContextFrom860From861.leaves wordLang.Skip.
Definition leaf_args :=
  match leaf with wordLang.Call _ _ args _ => args | _ => [] end.
Definition leaf_ret :=
  match leaf with wordLang.Call ret _ _ _ => ret | _ => None end.
Definition leaf_handler :=
  match leaf with wordLang.Call _ _ _ handler => handler | _ => None end.
Definition ret_data := THE leaf_ret.
Definition handler_data := THE leaf_handler.
Definition callee_argc :=
  match sptree.lookup 837 MaximumCall598StructuredFrom616From617ContextFrom860From861.funs with
  | Some (argc, _) => argc
  | None => 0
  end.

Lemma leaf_shape :
  leaf = wordLang.Call (Some ret_data) (Some 837) leaf_args (Some handler_data).
Proof. vm_cast_no_check (eq_refl leaf). Qed.

Lemma body_lookup :
  sptree.lookup 837 MaximumCall598StructuredFrom616From617ContextFrom860From861.funs =
  Some (callee_argc, MaximumCall837Via598From616From617ContextFrom860From861.body).
Proof. vm_cast_no_check (eq_refl (sptree.lookup 837 MaximumCall598StructuredFrom616From617ContextFrom860From861.funs)). Qed.

Definition callee_body_depth :=
  fold_right FastMaximum.join_depth (Some 0)
    (List.map MaximumCall837Via598From616From617ContextFrom860From861.depth MaximumCall837Via598From616From617ContextFrom860From861.leaves).

Lemma callee_body_depth_eq :
  word_depth.max_depth MaximumContext.frames
    (word_depth.call_graph MaximumCall837Via598From616From617ContextFrom860From861.funs 837 [837]
      (sptree.size MaximumContext.funs) MaximumCall837Via598From616From617ContextFrom860From861.body) =
  callee_body_depth.
Proof.
  unfold callee_body_depth, MaximumCall837Via598From616From617ContextFrom860From861.depth, MaximumCall837Via598From616From617ContextFrom860From861.leaves.
  transitivity
    (FastMaximum.fast_depth MaximumContext.frames
      MaximumCall837Via598From616From617ContextFrom860From861.funs 837 [837]
      (sptree.size MaximumContext.funs) MaximumCall837Via598From616From617ContextFrom860From861.body).
  - symmetry; apply FastMaximum.fast_depth_exact.
  - apply FastMaximum.fast_depth_leaves.
Qed.

Lemma leaf_depth_split :
  MaximumCall598StructuredFrom616From617ContextFrom860From861.depth leaf =
  OPTION_MAP2 MAX
    (word_depth.max_depth MaximumContext.frames
      (word_depth.Call MaximumCall598StructuredFrom616From617ContextFrom860From861.callee
        (word_depth.Const 3 (word_depth.Call 837 word_depth.Leaf))))
    (OPTION_MAP2 MAX
      (OPTION_MAP2 N.add
        (sptree.lookup MaximumCall598StructuredFrom616From617ContextFrom860From861.callee MaximumContext.frames)
        (OPTION_MAP (N.add 3) callee_body_depth))
      (OPTION_MAP2 MAX
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall598StructuredFrom616From617ContextFrom860From861.funs
            MaximumCall598StructuredFrom616From617ContextFrom860From861.callee [MaximumCall598StructuredFrom616From617ContextFrom860From861.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd handler_data))))
        (word_depth.max_depth MaximumContext.frames
          (word_depth.call_graph MaximumCall598StructuredFrom616From617ContextFrom860From861.funs
            MaximumCall598StructuredFrom616From617ContextFrom860From861.callee [MaximumCall598StructuredFrom616From617ContextFrom860From861.callee]
            (sptree.size MaximumContext.funs)
            (fst (snd (snd ret_data))))))).
Proof.
  unfold MaximumCall598StructuredFrom616From617ContextFrom860From861.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_subst
    MaximumContext.frames MaximumCall598StructuredFrom616From617ContextFrom860From861.funs MaximumCall598StructuredFrom616From617ContextFrom860From861.callee
    [MaximumCall598StructuredFrom616From617ContextFrom860From861.callee] (sptree.size MaximumContext.funs)
    837 leaf_args ret_data handler_data
    callee_argc MaximumCall837Via598From616From617ContextFrom860From861.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall837Via598From616From617ContextFrom860From861.funs, MaximumCall837Via598From616From617ContextFrom860From861.callee in Hbody.
    exact Hbody.
Qed.

Lemma leaf_depth_compact :
  MaximumCall598StructuredFrom616From617ContextFrom860From861.depth leaf =
  CallDepthLemma.ret_handler_result MaximumContext.frames
    MaximumCall598StructuredFrom616From617ContextFrom860From861.funs MaximumCall598StructuredFrom616From617ContextFrom860From861.callee
    [MaximumCall598StructuredFrom616From617ContextFrom860From861.callee] (sptree.size MaximumContext.funs)
    837 ret_data handler_data callee_body_depth.
Proof.
  unfold MaximumCall598StructuredFrom616From617ContextFrom860From861.depth.
  rewrite leaf_shape.
  apply (CallDepthLemma.max_depth_ret_handler_call_pair_compact
    MaximumContext.frames MaximumCall598StructuredFrom616From617ContextFrom860From861.funs
    MaximumCall598StructuredFrom616From617ContextFrom860From861.callee [MaximumCall598StructuredFrom616From617ContextFrom860From861.callee]
    (sptree.size MaximumContext.funs) 837 leaf_args ret_data handler_data
    callee_argc MaximumCall837Via598From616From617ContextFrom860From861.body callee_body_depth).
  - exact body_lookup.
  - pose proof callee_body_depth_eq as Hbody.
    unfold MaximumCall837Via598From616From617ContextFrom860From861.funs, MaximumCall837Via598From616From617ContextFrom860From861.callee in Hbody.
    exact Hbody.
Qed.
