(** Exact IRC evaluation using sparse working arrays. The algorithm,
    priorities and ordered neighbour lists are unchanged. *)
From Galette Require Import Base.
From Galette.HOL.src.num.theories Require Import arithmetic.
From Galette.HOL.src.coretypes Require Import pair.
From Galette.HOL.src.sort Require Import sorting.
From Galette.cakeml.basis.pure Require Import mllist.
From Galette.HOL.src.finite_maps Require Import sptree.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.cakeml.translator.monadic.monad_base Require Import ml_monadBase.
From Galette.cakeml.compiler.backend.reg_alloc Require Import reg_alloc.
From InitE.Compilation Require Import Allocation SparseState.
From InitE.Compilation Require FastGraph FastLookup IRCBulk.
Open Scope N_scope.
Open Scope monad_scope.
Definition insert_edge (x y : N) : IM unit :=
  adjx <- adj_ls_sub x ;;
  adjy <- adj_ls_sub y ;;
  update_adj_ls x (FastGraph.sortedInsert y adjx) ;;
  update_adj_ls y (FastGraph.sortedInsert x adjy).


Fixpoint list_insert_edge (x : N) (l : list N) : IM unit :=
  match l with
  | [] => st_ex_return tt
  | y :: ys => insert_edge x y ;; list_insert_edge x ys
  end.


Fixpoint clique_insert_edge (l : list N) : IM unit :=
  match l with
  | [] => st_ex_return tt
  | x :: xs => list_insert_edge x xs ;; clique_insert_edge xs
  end.


Fixpoint extend_clique (l : list N) (cli : list N) : IM (list N) :=
  match l with
  | [] => st_ex_return cli
  | x :: xs =>
      if MEM x cli then extend_clique xs cli
      else list_insert_edge x cli ;; extend_clique xs (x :: cli)
  end.


Definition dec_deg (n : N) : IM unit :=
  cd <- degrees_sub n ;;
  update_degrees n (cd - 1).


Definition dec_degree (n : N) : IM unit :=
  d <- get_dim ;;
  if n <? d then
    adjs <- adj_ls_sub n ;;
    st_ex_FOREACH adjs dec_deg
  else st_ex_return tt.


Definition add_simp_wl (ls : list N) : IM unit :=
  swl <- get_simp_wl ;;
  set_simp_wl (ls ++ swl).


Definition add_spill_wl (ls : list N) : IM unit :=
  swl <- get_spill_wl ;;
  set_spill_wl (ls ++ swl).


Definition add_freeze_wl (ls : list N) : IM unit :=
  fwl <- get_freeze_wl ;;
  set_freeze_wl (ls ++ fwl).


Definition push_stack (x : N) : IM unit :=
  swl <- get_stack ;;
  update_degrees x 0 ;;
  update_move_related x false ;;
  set_stack (x :: swl).


Definition add_unavail_moves_wl (ls : list (N * (N * N))) : IM unit :=
  swl <- get_unavail_moves_wl ;;
  set_unavail_moves_wl (ls ++ swl).


Definition is_not_coalesced (d : N) : IM bool :=
  dt <- coalesced_sub d ;;
  st_ex_return (d =? dt).


Definition split_degree (d k v : N) : IM bool :=
  if v <? d then
    vd <- degrees_sub v ;;
    b <- is_not_coalesced v ;;
    st_ex_return ((vd <? k) && b)
  else st_ex_return true.


Definition partition_degree d k xs : IM (list N * list N) :=
 IRCBulk.partition d k xs (st_ex_PARTITION (split_degree d k) xs [] []).

Definition revive_moves (vs : list N) : IM unit :=
  nbs <- st_ex_MAP adj_ls_sub vs ;;
  uam <- get_unavail_moves_wl ;;
  am <- get_avail_moves_wl ;;
  let '(rev, unavail) :=
    PARTITION (fun '(_, (x, y)) => EXISTS (sorted_mem x) nbs || EXISTS (sorted_mem y) nbs) uam in
  let sorted := smerge (sort_moves rev) am in
  set_avail_moves_wl sorted ;;
  set_unavail_moves_wl unavail.


Definition unspill (k : N) : IM unit :=
  d <- get_dim ;;
  swl <- get_spill_wl ;;
  '(ltk, gtk) <- partition_degree d k swl ;;
  revive_moves ltk ;;
  '(ltkfreeze, ltksimp) <- st_ex_PARTITION move_related_sub ltk [] [] ;;
  set_spill_wl gtk ;;
  add_simp_wl ltksimp ;;
  add_freeze_wl ltkfreeze.


Definition do_simplify (k : N) : IM bool :=
  simps <- get_simp_wl ;;
  if NULL simps then st_ex_return false
  else
    st_ex_FOREACH simps dec_degree ;;
    st_ex_FOREACH simps push_stack ;;
    set_simp_wl [] ;;
    unspill k ;;
    st_ex_return true.


Definition inc_deg (n d : N) : IM unit :=
  cd <- degrees_sub n ;;
  update_degrees n (cd + d).


Definition is_Fixed (x : N) : IM bool :=
  xt <- node_tag_sub x ;;
  st_ex_return (match xt with Fixed n => true | _ => false end).


Definition do_coalesce_real (x y : N) (case1 case2 : list N) : IM unit :=
  update_coalesced y x ;;
  bx <- is_Fixed x ;;
  (if bx then st_ex_return tt else inc_deg x (LENGTH case2)) ;;
  list_insert_edge x case2 ;;
  st_ex_FOREACH case1 dec_deg ;;
  push_stack y.


Definition is_Atemp (d : N) : IM bool :=
  dt <- node_tag_sub d ;;
  st_ex_return (bool_decide (dt = Atemp)).


Definition is_Fixed_k (k x : N) : IM bool :=
  xt <- node_tag_sub x ;;
  st_ex_return (match xt with Fixed n => n <? k | _ => false end).


Definition considered_var (k x : N) : IM bool :=
  bx <- is_Atemp x ;;
  fx <- is_Fixed_k k x ;;
  st_ex_return (bx || fx).


Definition deg_or_inf (k x : N) : IM N :=
  bx <- is_Fixed_k k x ;;
  if bx then st_ex_return k else degrees_sub x.


Definition bg_ok (k x y : N) : IM (option (list N * list N)) :=
  adjx <- adj_ls_sub x ;;
  adjy <- adj_ls_sub y ;;
  let '(case1, case2) := PARTITION (fun v => sorted_mem v adjx) adjy in
  case1 <- st_ex_FILTER (considered_var k) case1 [] ;;
  case2 <- st_ex_FILTER (considered_var k) case2 [] ;;
  case2degs <- st_ex_MAP (deg_or_inf k) case2 ;;
  let c2len := LENGTH (FILTER (fun x => k <=? x) case2degs) in
  if c2len =? 0 then st_ex_return (Some (case1, case2))
  else
    let case3 := FILTER (fun v => negb (sorted_mem v adjy)) adjx in
    case3 <- st_ex_FILTER (considered_var k) case3 [] ;;
    case1degs <- st_ex_MAP (deg_or_inf (k + 1)) case1 ;;
    case3degs <- st_ex_MAP (deg_or_inf k) case3 ;;
    c1len <- st_ex_return (LENGTH (FILTER (fun x => k <=? x - 1) case1degs)) ;;
    c3len <- st_ex_return (LENGTH (FILTER (fun x => k <=? x) case3degs)) ;;
    if c1len + c2len + c3len <? k then st_ex_return (Some (case1, case2))
    else st_ex_return None.


Definition consistency_ok (x y : N) : IM bool :=
  if x =? y then st_ex_return false
  else
    adjy <- adj_ls_sub y ;;
    if sorted_mem x adjy then st_ex_return false
    else
      bx <- is_Fixed x ;;
      by_ <- is_Fixed y ;;
      movrelx <- move_related_sub x ;;
      movrely <- move_related_sub y ;;
      st_ex_return ((bx || movrelx) && (by_ || movrely) && negb (bx && by_)).


Fixpoint coalesce_parent_fuel (fuel : nat) (x : N) : IM N :=
 match fuel with
 | O => st_ex_return x
 | S fuel =>
   xt <- coalesced_sub x ;;
   bx <- is_Fixed xt ;;
   if bx then st_ex_return xt
   else if x <=? xt then st_ex_return x
   else anc <- coalesce_parent_fuel fuel xt ;;
        update_coalesced x anc ;; st_ex_return anc
 end.
Definition coalesce_parent x := coalesce_parent_fuel (S (N.to_nat x)) x.
Definition canonize_move (x y : N) : IM (N * N) :=
  bx <- is_Fixed x ;;
  by_ <- is_Fixed y ;;
  if by_ then st_ex_return (y, x)
  else if bx then st_ex_return (x, y)
  else if x <? y then st_ex_return (x, y)
  else st_ex_return (y, x).


Fixpoint st_ex_FIRST {A B} (P : N -> N -> IM bool) (Q : N -> N -> IM (option B))
    (l : list (A * (N * N))) (unavail : list (A * (N * N)))
    : IM (option ((N * N) * (B * list (A * (N * N)))) * list (A * (N * N))) :=
  match l with
  | [] => st_ex_return (None, unavail)
  | m :: ms =>
      let '(p, (x, y)) := m in
      x <- coalesce_parent x ;;
      y <- coalesce_parent y ;;
      b1 <- P x y ;;
      if negb b1 then st_ex_FIRST P Q ms unavail
      else
        '(x, y) <- canonize_move x y ;;
        optb2 <- Q x y ;;
        match optb2 with
        | None => st_ex_FIRST P Q ms ((p, (x, y)) :: unavail)
        | Some pr => st_ex_return (Some ((x, y), (pr, ms)), unavail)
        end
  end.


Definition respill (k x : N) : IM unit :=
  xd <- degrees_sub x ;;
  if xd <? k then st_ex_return tt
  else
    freeze <- get_freeze_wl ;;
    if MEM x freeze then
      add_spill_wl [x] ;;
      set_freeze_wl (FILTER (fun y => negb (y =? x)) freeze)
    else st_ex_return tt.


Definition do_coalesce (k : N) : IM bool :=
  am <- get_avail_moves_wl ;;
  '(ores, unavail) <- st_ex_FIRST consistency_ok (bg_ok k) am [] ;;
  add_unavail_moves_wl unavail ;;
  match ores with
  | None =>
      set_avail_moves_wl [] ;;
      st_ex_return false
  | Some ((x, y), ((case1, case2), ms)) =>
      set_avail_moves_wl ms ;;
      do_coalesce_real x y case1 case2 ;;
      unspill k ;;
      respill k x ;;
      st_ex_return true
  end.


Definition reset_move_related {A} (ls : list (A * (N * N))) : IM unit :=
  d <- get_dim ;;
  st_ex_FOREACH (COUNT_LIST d) (fun x => update_move_related x false) ;;
  st_ex_FOREACH ls (fun '(_, (x, y)) =>
    bx <- is_Fixed x ;;
    by_ <- is_Fixed y ;;
    update_move_related x (negb bx) ;;
    update_move_related y (negb by_)).


Definition do_prefreeze (k : N) : IM bool :=
  fwl_pre <- get_freeze_wl ;;
  fwl <- st_ex_FILTER is_not_coalesced fwl_pre [] ;;
  swl_pre <- get_spill_wl ;;
  swl <- st_ex_FILTER is_not_coalesced swl_pre [] ;;
  set_spill_wl swl ;;
  uam_pre <- get_unavail_moves_wl ;;
  uam <- st_ex_FILTER (fun '(_, (x, y)) => consistency_ok x y) uam_pre [] ;;
  reset_move_related uam ;;
  uam <- set_unavail_moves_wl uam ;;
  '(ltkfreeze, ltksimp) <- st_ex_PARTITION move_related_sub fwl [] [] ;;
  add_simp_wl ltksimp ;;
  set_freeze_wl ltkfreeze ;;
  do_simplify k.


Definition do_freeze (k : N) : IM bool :=
  freeze <- get_freeze_wl ;;
  match freeze with
  | [] => st_ex_return false
  | x :: xs =>
      dec_degree x ;;
      push_stack x ;;
      set_freeze_wl xs ;;
      unspill k ;;
      st_ex_return true
  end.


Definition fast_lookup_any (x : N) (scost : num_map N) : N :=
  match FastLookup.binary_lookup x scost with None => 0 | Some cost => cost end.
Lemma fast_lookup_any_exact x scost :
  fast_lookup_any x scost = reg_alloc.lookup_any x scost 0.
Proof. unfold fast_lookup_any, reg_alloc.lookup_any.
  now rewrite FastLookup.binary_lookup_exact. Qed.

Fixpoint st_ex_list_MIN_cost (scost : num_map N) (l : list N) (d k v : N) (acc : list N)
    : IM (N * list N) :=
  match l with
  | [] => st_ex_return (k, acc)
  | x :: xs =>
      if x <? d then
        xv <- degrees_sub x ;;
        cost <- st_ex_return (safe_div (fast_lookup_any x scost) xv) ;;
        if cost <? v then st_ex_list_MIN_cost scost xs d x cost (k :: acc)
        else st_ex_list_MIN_cost scost xs d k v (x :: acc)
      else st_ex_list_MIN_cost scost xs d k v acc
  end.


Fixpoint st_ex_list_MAX_deg (l : list N) (d k v : N) (acc : list N) : IM (N * list N) :=
  match l with
  | [] => st_ex_return (k, acc)
  | x :: xs =>
      if x <? d then
        xv <- degrees_sub x ;;
        if v <? xv then st_ex_list_MAX_deg xs d x xv (k :: acc)
        else st_ex_list_MAX_deg xs d k v (x :: acc)
      else st_ex_list_MAX_deg xs d k v acc
  end.


Definition do_spill (scostopt : option (num_map N)) (k : N) : IM bool :=
  spills <- get_spill_wl ;;
  d <- get_dim ;;
  match spills with
  | [] => st_ex_return false
  | x :: xs =>
      xv <- degrees_sub x ;;
      '(y, ys) <-
        match scostopt with
        | None => st_ex_list_MAX_deg xs d x xv []
        | Some scost =>
            st_ex_list_MIN_cost scost xs d x (safe_div (fast_lookup_any x scost) xv) []
        end ;;
      dec_degree y ;;
      push_stack y ;;
      set_spill_wl ys ;;
      unspill k ;;
      st_ex_return true
  end.


Definition do_step (scost : option (num_map N)) (k : N) : IM bool :=
  b <- do_simplify k ;;
  if b then st_ex_return b
  else
    b <- do_coalesce k ;;
    if b then st_ex_return b
    else
      b <- do_prefreeze k ;;
      if b then st_ex_return b
      else
        b <- do_freeze k ;;
        if b then st_ex_return b
        else
          b <- do_spill scost k ;;
          st_ex_return b.


Definition rpt_do_step (scost : option (num_map N)) (k c : N) : IM unit :=
  num_rec (st_ex_return tt)
    (fun _ r => b <- do_step scost k ;; if b then r else st_ex_return tt) c.


Definition do_upd_coalesce (i : N) : IM unit := update_coalesced i (0 + i).


Definition init_alloc1_heu (moves : list (N * (N * N))) (d k : N) : IM N :=
  ds <- st_ex_return (COUNT_LIST d) ;;
  allocs <- st_ex_FILTER is_Atemp ds [] ;;
  st_ex_FOREACH ds (fun i =>
    adjls <- adj_ls_sub i ;;
    fills <- st_ex_FILTER (fun v => considered_var k v) adjls [] ;;
    update_degrees i (LENGTH fills)) ;;
  st_ex_FOREACH ds do_upd_coalesce ;;
  set_avail_moves_wl (sort_moves moves) ;;
  reset_move_related moves ;;
  '(ltk, gtk) <- partition_degree d k allocs ;;
  '(ltkfreeze, ltksimp) <- st_ex_PARTITION move_related_sub ltk [] [] ;;
  set_spill_wl gtk ;;
  set_simp_wl ltksimp ;;
  set_freeze_wl ltkfreeze ;;
  st_ex_return (LENGTH allocs).


Definition do_alloc1 (moves : list (N * (N * N))) (scost : option (num_map N)) (k : N)
    : IM (list N) :=
  d <- get_dim ;;
  l <- init_alloc1_heu moves d k ;;
  rpt_do_step scost k l ;;
  st <- get_stack ;;
  st_ex_return st.



Lemma sim_foreach {A B} (f : A -> RA B) (g : A -> IM B) xs :
 (forall x, sim (f x) (g x)) -> sim (st_ex_FOREACH xs f) (st_ex_FOREACH xs g).
Proof.
 intro H; induction xs as [|x xs IH]; cbn [st_ex_FOREACH].
 - apply sim_return.
 - apply sim_ignore; auto.
Qed.
Lemma sim_map {A B} (f : A -> RA B) (g : A -> IM B) xs :
 (forall x, sim (f x) (g x)) -> sim (st_ex_MAP f xs) (st_ex_MAP g xs).
Proof.
 intro H; induction xs as [|x xs IH]; cbn [st_ex_MAP].
 - apply sim_return.
 - apply sim_bind; [apply H|]. intro y.
   apply sim_bind; [exact IH|]. intro ys. apply sim_return.
Qed.
Lemma sim_filter {A} (f : A -> RA bool) (g : A -> IM bool) xs :
 (forall x, sim (f x) (g x)) -> forall acc, sim (st_ex_FILTER f xs acc) (st_ex_FILTER g xs acc).
Proof.
 intro H; induction xs as [|x xs IH]; intro acc; cbn [st_ex_FILTER].
 - apply sim_return.
 - apply sim_bind; [apply H|]. intros []; apply IH.
Qed.
Lemma sim_partition {A} (f : A -> RA bool) (g : A -> IM bool) xs :
 (forall x, sim (f x) (g x)) -> forall tt_ ff, sim (st_ex_PARTITION f xs tt_ ff) (st_ex_PARTITION g xs tt_ ff).
Proof.
 intro H; induction xs as [|x xs IH]; intros tt_ ff; cbn [st_ex_PARTITION].
 - apply sim_return.
 - apply sim_bind; [apply H|]. intros []; apply IH.
Qed.
Create HintDb irc_sim.
#[local] Hint Resolve sim_return sim_adj_ls_sub sim_update_adj_ls sim_node_tag_sub sim_degrees_sub sim_update_degrees sim_coalesced_sub sim_update_coalesced sim_move_related_sub sim_update_move_related sim_get_dim sim_get_simp_wl sim_set_simp_wl sim_get_spill_wl sim_set_spill_wl sim_get_freeze_wl sim_set_freeze_wl sim_get_avail_moves_wl sim_set_avail_moves_wl sim_get_unavail_moves_wl sim_set_unavail_moves_wl sim_get_stack sim_set_stack : irc_sim.
Ltac solve_sim :=
 first [ solve [eauto 2 with irc_sim]
 | apply sim_bind; [solve_sim | let v := fresh "v" in intro v; solve_sim]
 | apply sim_ignore; [solve_sim | solve_sim]
 | apply sim_foreach; let v := fresh "v" in intro v; solve_sim
 | apply sim_map; let v := fresh "v" in intro v; solve_sim
 | apply sim_filter; let v := fresh "v" in intro v; solve_sim
 | apply sim_partition; let v := fresh "v" in intro v; solve_sim
 | progress rewrite fast_lookup_any_exact; solve_sim
 | progress rewrite FastGraph.sortedInsert_exact; solve_sim
 | match goal with
   | |- sim (if ?b then _ else _) (if ?b then _ else _) => destruct b; solve_sim
   | |- sim (match ?x with _ => _ end) _ => destruct x; cbv beta iota zeta; solve_sim
   end ].
Lemma sim_insert_edge (x y : N) : sim (@reg_alloc.insert_edge x y) (@insert_edge x y).
Proof.
 unfold reg_alloc.insert_edge,insert_edge.
 solve_sim.
Qed.
#[local] Hint Resolve sim_insert_edge : irc_sim.
Lemma sim_list_insert_edge x l : sim (reg_alloc.list_insert_edge x l) (list_insert_edge x l).
Proof. induction l as [|y ys IH]; cbn [reg_alloc.list_insert_edge list_insert_edge]; solve_sim. Qed.
#[local] Hint Resolve sim_list_insert_edge : irc_sim.
Lemma sim_clique_insert_edge l : sim (reg_alloc.clique_insert_edge l) (clique_insert_edge l).
Proof. induction l as [|x xs IH]; cbn [reg_alloc.clique_insert_edge clique_insert_edge]; solve_sim. Qed.
#[local] Hint Resolve sim_clique_insert_edge : irc_sim.
Lemma sim_extend_clique l : forall cli, sim (reg_alloc.extend_clique l cli) (extend_clique l cli).
Proof. induction l as [|x xs IH]; intro cli; cbn [reg_alloc.extend_clique extend_clique]; solve_sim. Qed.
#[local] Hint Resolve sim_extend_clique : irc_sim.
Lemma sim_dec_deg (n : N) : sim (@reg_alloc.dec_deg n) (@dec_deg n).
Proof.
 unfold reg_alloc.dec_deg,dec_deg.
 solve_sim.
Qed.
#[local] Hint Resolve sim_dec_deg : irc_sim.
Lemma sim_dec_degree (n : N) : sim (@reg_alloc.dec_degree n) (@dec_degree n).
Proof.
 unfold reg_alloc.dec_degree,dec_degree.
 solve_sim.
Qed.
#[local] Hint Resolve sim_dec_degree : irc_sim.
Lemma sim_add_simp_wl (ls : list N) : sim (@reg_alloc.add_simp_wl ls) (@add_simp_wl ls).
Proof.
 unfold reg_alloc.add_simp_wl,add_simp_wl.
 solve_sim.
Qed.
#[local] Hint Resolve sim_add_simp_wl : irc_sim.
Lemma sim_add_spill_wl (ls : list N) : sim (@reg_alloc.add_spill_wl ls) (@add_spill_wl ls).
Proof.
 unfold reg_alloc.add_spill_wl,add_spill_wl.
 solve_sim.
Qed.
#[local] Hint Resolve sim_add_spill_wl : irc_sim.
Lemma sim_add_freeze_wl (ls : list N) : sim (@reg_alloc.add_freeze_wl ls) (@add_freeze_wl ls).
Proof.
 unfold reg_alloc.add_freeze_wl,add_freeze_wl.
 solve_sim.
Qed.
#[local] Hint Resolve sim_add_freeze_wl : irc_sim.
Lemma sim_push_stack (x : N) : sim (@reg_alloc.push_stack x) (@push_stack x).
Proof.
 unfold reg_alloc.push_stack,push_stack.
 solve_sim.
Qed.
#[local] Hint Resolve sim_push_stack : irc_sim.
Lemma sim_add_unavail_moves_wl (ls : list (N * (N * N))) : sim (@reg_alloc.add_unavail_moves_wl ls) (@add_unavail_moves_wl ls).
Proof.
 unfold reg_alloc.add_unavail_moves_wl,add_unavail_moves_wl.
 solve_sim.
Qed.
#[local] Hint Resolve sim_add_unavail_moves_wl : irc_sim.
Lemma sim_is_not_coalesced (d : N) : sim (@reg_alloc.is_not_coalesced d) (@is_not_coalesced d).
Proof.
 unfold reg_alloc.is_not_coalesced,is_not_coalesced.
 solve_sim.
Qed.
#[local] Hint Resolve sim_is_not_coalesced : irc_sim.
Lemma sim_split_degree (d k v : N) : sim (@reg_alloc.split_degree d k v) (@split_degree d k v).
Proof.
 unfold reg_alloc.split_degree,split_degree.
 solve_sim.
Qed.
#[local] Hint Resolve sim_split_degree : irc_sim.
Lemma sim_partition_degree d k xs :
 sim (st_ex_PARTITION (reg_alloc.split_degree d k) xs [] []) (partition_degree d k xs).
Proof.
 unfold partition_degree. apply IRCBulk.partition_sim.
 apply sim_partition; intro i; apply sim_split_degree.
Qed.
#[local] Hint Resolve sim_partition_degree : irc_sim.
Lemma sim_revive_moves (vs : list N) : sim (@reg_alloc.revive_moves vs) (@revive_moves vs).
Proof.
 unfold reg_alloc.revive_moves,revive_moves.
 solve_sim.
Qed.
#[local] Hint Resolve sim_revive_moves : irc_sim.
Lemma sim_unspill (k : N) : sim (@reg_alloc.unspill k) (@unspill k).
Proof.
 unfold reg_alloc.unspill,unspill.
 solve_sim.
Qed.
#[local] Hint Resolve sim_unspill : irc_sim.
Lemma sim_do_simplify (k : N) : sim (@reg_alloc.do_simplify k) (@do_simplify k).
Proof.
 unfold reg_alloc.do_simplify,do_simplify.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_simplify : irc_sim.
Lemma sim_inc_deg (n d : N) : sim (@reg_alloc.inc_deg n d) (@inc_deg n d).
Proof.
 unfold reg_alloc.inc_deg,inc_deg.
 solve_sim.
Qed.
#[local] Hint Resolve sim_inc_deg : irc_sim.
Lemma sim_is_Fixed (x : N) : sim (@reg_alloc.is_Fixed x) (@is_Fixed x).
Proof.
 unfold reg_alloc.is_Fixed,is_Fixed.
 solve_sim.
Qed.
#[local] Hint Resolve sim_is_Fixed : irc_sim.
Lemma sim_do_coalesce_real (x y : N) (case1 case2 : list N) : sim (@reg_alloc.do_coalesce_real x y case1 case2) (@do_coalesce_real x y case1 case2).
Proof.
 unfold reg_alloc.do_coalesce_real,do_coalesce_real.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_coalesce_real : irc_sim.
Lemma sim_is_Atemp (d : N) : sim (@reg_alloc.is_Atemp d) (@is_Atemp d).
Proof.
 unfold reg_alloc.is_Atemp,is_Atemp.
 solve_sim.
Qed.
#[local] Hint Resolve sim_is_Atemp : irc_sim.
Lemma sim_is_Fixed_k (k x : N) : sim (@reg_alloc.is_Fixed_k k x) (@is_Fixed_k k x).
Proof.
 unfold reg_alloc.is_Fixed_k,is_Fixed_k.
 solve_sim.
Qed.
#[local] Hint Resolve sim_is_Fixed_k : irc_sim.
Lemma sim_considered_var (k x : N) : sim (@reg_alloc.considered_var k x) (@considered_var k x).
Proof.
 unfold reg_alloc.considered_var,considered_var.
 solve_sim.
Qed.
#[local] Hint Resolve sim_considered_var : irc_sim.
Lemma sim_deg_or_inf (k x : N) : sim (@reg_alloc.deg_or_inf k x) (@deg_or_inf k x).
Proof.
 unfold reg_alloc.deg_or_inf,deg_or_inf.
 solve_sim.
Qed.
#[local] Hint Resolve sim_deg_or_inf : irc_sim.
Lemma sim_bg_ok (k x y : N) : sim (@reg_alloc.bg_ok k x y) (@bg_ok k x y).
Proof.
 unfold reg_alloc.bg_ok,bg_ok.
 solve_sim.
Qed.
#[local] Hint Resolve sim_bg_ok : irc_sim.
Lemma sim_consistency_ok (x y : N) : sim (@reg_alloc.consistency_ok x y) (@consistency_ok x y).
Proof.
 unfold reg_alloc.consistency_ok,consistency_ok.
 solve_sim.
Qed.
#[local] Hint Resolve sim_consistency_ok : irc_sim.
Lemma sim_coalesce_parent_fuel fuel : forall x, x < N.of_nat fuel ->
 sim (reg_alloc.coalesce_parent x) (coalesce_parent_fuel fuel x).
Proof.
 induction fuel as [|fuel IH]; intros x Hbound; [lia|].
 rewrite reg_alloc.coalesce_parent_def.
 cbn [coalesce_parent_fuel].
 apply sim_bind; [apply sim_coalesced_sub|]. intro xt.
 apply sim_bind; [apply sim_is_Fixed|]. intros [].
 - apply sim_return.
 - destruct (N.leb_spec x xt) as [Hle|Hlt]; [apply sim_return|].
   apply sim_bind; [apply IH; lia|]. intro anc.
   apply sim_ignore; [apply sim_update_coalesced|apply sim_return].
Qed.
Lemma sim_coalesce_parent x : sim (reg_alloc.coalesce_parent x) (coalesce_parent x).
Proof. apply sim_coalesce_parent_fuel; lia. Qed.
#[local] Hint Resolve sim_coalesce_parent : irc_sim.
Lemma sim_canonize_move (x y : N) : sim (@reg_alloc.canonize_move x y) (@canonize_move x y).
Proof.
 unfold reg_alloc.canonize_move,canonize_move.
 solve_sim.
Qed.
#[local] Hint Resolve sim_canonize_move : irc_sim.
Lemma sim_st_ex_FIRST {A B} (p : N -> N -> RA bool) (p' : N -> N -> IM bool)
 (q : N -> N -> RA (option B)) (q' : N -> N -> IM (option B)) ls :
 (forall x y, sim (p x y) (p' x y)) ->
 (forall x y, sim (q x y) (q' x y)) -> forall unavail : list (A*(N*N)),
 sim (reg_alloc.st_ex_FIRST p q ls unavail) (st_ex_FIRST p' q' ls unavail).
Proof.
 intros Hp Hq; induction ls as [|[pri [x y]] xs IH]; intro unavail;
 cbn [reg_alloc.st_ex_FIRST st_ex_FIRST]; solve_sim.
Qed.
#[local] Hint Resolve sim_st_ex_FIRST : irc_sim.
Lemma sim_respill (k x : N) : sim (@reg_alloc.respill k x) (@respill k x).
Proof.
 unfold reg_alloc.respill,respill.
 solve_sim.
Qed.
#[local] Hint Resolve sim_respill : irc_sim.
Lemma sim_do_coalesce (k : N) : sim (@reg_alloc.do_coalesce k) (@do_coalesce k).
Proof.
 unfold reg_alloc.do_coalesce,do_coalesce.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_coalesce : irc_sim.
Lemma sim_reset_move_related {A} (ls : list (A * (N * N))) : sim (@reg_alloc.reset_move_related A ls) (@reset_move_related A ls).
Proof.
 unfold reg_alloc.reset_move_related,reset_move_related.
 solve_sim.
Qed.
#[local] Hint Resolve sim_reset_move_related : irc_sim.
Lemma sim_do_prefreeze (k : N) : sim (@reg_alloc.do_prefreeze k) (@do_prefreeze k).
Proof.
 unfold reg_alloc.do_prefreeze,do_prefreeze.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_prefreeze : irc_sim.
Lemma sim_do_freeze (k : N) : sim (@reg_alloc.do_freeze k) (@do_freeze k).
Proof.
 unfold reg_alloc.do_freeze,do_freeze.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_freeze : irc_sim.
Lemma sim_st_ex_list_MIN_cost scost ls : forall d k v acc,
 sim (reg_alloc.st_ex_list_MIN_cost scost ls d k v acc) (st_ex_list_MIN_cost scost ls d k v acc).
Proof. induction ls as [|x xs IH]; intros d k v acc;
  cbn [reg_alloc.st_ex_list_MIN_cost st_ex_list_MIN_cost];
  rewrite ?fast_lookup_any_exact; solve_sim. Qed.
#[local] Hint Resolve sim_st_ex_list_MIN_cost : irc_sim.
Lemma sim_st_ex_list_MAX_deg ls : forall d k v acc,
 sim (reg_alloc.st_ex_list_MAX_deg ls d k v acc) (st_ex_list_MAX_deg ls d k v acc).
Proof. induction ls as [|x xs IH]; intros d k v acc; cbn [reg_alloc.st_ex_list_MAX_deg st_ex_list_MAX_deg]; solve_sim. Qed.
#[local] Hint Resolve sim_st_ex_list_MAX_deg : irc_sim.
Lemma sim_do_spill (scostopt : option (num_map N)) (k : N) : sim (@reg_alloc.do_spill scostopt k) (@do_spill scostopt k).
Proof.
 unfold reg_alloc.do_spill,do_spill.
 rewrite ?fast_lookup_any_exact.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_spill : irc_sim.
Lemma sim_do_step (scost : option (num_map N)) (k : N) : sim (@reg_alloc.do_step scost k) (@do_step scost k).
Proof.
 unfold reg_alloc.do_step,do_step.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_step : irc_sim.
Lemma sim_rpt_do_step scost k c : sim (reg_alloc.rpt_do_step scost k c) (rpt_do_step scost k c).
Proof.
 unfold reg_alloc.rpt_do_step,rpt_do_step.
 induction c using N.peano_ind; [apply sim_return|].
 rewrite !num_rec_SUC. solve_sim.
Qed.
#[local] Hint Resolve sim_rpt_do_step : irc_sim.
Lemma sim_do_upd_coalesce (i : N) : sim (@reg_alloc.do_upd_coalesce i) (@do_upd_coalesce i).
Proof.
 unfold reg_alloc.do_upd_coalesce,do_upd_coalesce.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_upd_coalesce : irc_sim.
Lemma sim_init_alloc1_heu (moves : list (N * (N * N))) (d k : N) : sim (@reg_alloc.init_alloc1_heu moves d k) (@init_alloc1_heu moves d k).
Proof.
 unfold reg_alloc.init_alloc1_heu,init_alloc1_heu.
 solve_sim.
Qed.
#[local] Hint Resolve sim_init_alloc1_heu : irc_sim.
Lemma sim_do_alloc1 (moves : list (N * (N * N))) (scost : option (num_map N)) (k : N) : sim (@reg_alloc.do_alloc1 moves scost k) (@do_alloc1 moves scost k).
Proof.
 unfold reg_alloc.do_alloc1,do_alloc1.
 solve_sim.
Qed.
#[local] Hint Resolve sim_do_alloc1 : irc_sim.

Definition initialize_fast moves k (s : ra_state) :=
 execute (init_alloc1_heu moves (dim s) k) s.
Theorem initialize_fast_exact moves k s :
 initialize_fast moves k s = reg_alloc.init_alloc1_heu moves (dim s) k s.
Proof. apply execute_exact,sim_init_alloc1_heu. Qed.
Definition repeat_fast scost k count := execute (rpt_do_step scost k count).
Theorem repeat_fast_exact scost k count s :
 repeat_fast scost k count s = reg_alloc.rpt_do_step scost k count s.
Proof. apply execute_exact,sim_rpt_do_step. Qed.
Definition allocate_fast moves scost k := execute (do_alloc1 moves scost k).
Theorem allocate_fast_exact moves scost k s :
 allocate_fast moves scost k s = reg_alloc.do_alloc1 moves scost k s.
Proof. apply execute_exact,sim_do_alloc1. Qed.
Definition step_fast scost k := execute (do_step scost k).
Theorem step_fast_exact scost k s : step_fast scost k s = reg_alloc.do_step scost k s.
Proof. apply execute_exact,sim_do_step. Qed.

Theorem advance_initialize_fast_exact (r : exc (list (N*(N*N))) state_exn * ra_state) k :
 Allocation.advance r (fun moves => initialize_fast moves k) =
 Allocation.advance r (fun moves s => reg_alloc.init_alloc1_heu moves (dim s) k s).
Proof.
 destruct r as [[moves|e] s]; cbn [Allocation.advance]; [apply initialize_fast_exact|reflexivity].
Qed.
Theorem advance_repeat_fast_exact (r : exc N state_exn * ra_state) scost k :
 Allocation.advance r (fun count => repeat_fast scost k count) =
 Allocation.advance r (fun count => reg_alloc.rpt_do_step scost k count).
Proof.
 destruct r as [[count|e] s]; cbn [Allocation.advance]; [apply repeat_fast_exact|reflexivity].
Qed.
Theorem advance_allocate_fast_exact {A} (r : exc A state_exn * ra_state)
 (moves : A -> list (N*(N*N))) scost k :
 Allocation.advance r (fun v => allocate_fast (moves v) scost k) =
 Allocation.advance r (fun v => reg_alloc.do_alloc1 (moves v) scost k).
Proof.
 destruct r as [[v|e] s]; cbn [Allocation.advance]; [apply allocate_fast_exact|reflexivity].
Qed.
