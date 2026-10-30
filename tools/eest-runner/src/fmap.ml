(* Realization of Galette's [fmap] for extraction.  A map is a base lookup
   function with persistent overrides, bucketed by the structural hash of
   the key.  Each override keeps the key's equality test from the Rocq
   decider; the trusted assumption is that keys the decider calls equal
   have equal [Hashtbl.hash], which holds for the strings and words used. *)
module IM = Map.Make (Int)

type ('k, 'v) entry = { key : 'k; same : 'k -> bool; value : 'v option }
type ('k, 'v) t = { base : 'k -> 'v option; over : ('k, 'v) entry list IM.t }

let of_fun base = { base; over = IM.empty }
let empty = { base = (fun _ -> None); over = IM.empty }

let lookup m a =
  match IM.find_opt (Hashtbl.hash a) m.over with
  | None -> m.base a
  | Some bucket ->
    let rec go = function
      | [] -> m.base a
      | e :: rest -> if e.same a then e.value else go rest in
    go bucket

let case k m = k (lookup m)

let set same key value m =
  let h = Hashtbl.hash key in
  let bucket = match IM.find_opt h m.over with None -> [] | Some b -> b in
  let bucket = List.filter (fun e -> not (same e.key)) bucket in
  { m with over = IM.add h ({ key; same; value } :: bucket) m.over }

(* [FUPDATE f (k, v)]: [decide (k = a)]. *)
let update dec m (k, v) = set (fun a -> dec k a) k (Some v) m
(* [fdomsub f k0]: [decide (a = k0)]. *)
let domsub dec m k0 = set (fun a -> dec a k0) k0 None m
