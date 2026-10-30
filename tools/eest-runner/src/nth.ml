(* Realization of [InitE.Guest.Basic.nthN] for extraction: the same
   function, indexing an array made from the last list it was called with. *)
let last_list : Obj.t ref = ref (Obj.repr [])
let last_array : Obj.t array ref = ref [||]

let nthN (i : Z.t) (xs : 'a list) (default : 'a) : 'a =
  if Obj.repr xs != !last_list then begin
    last_list := Obj.repr xs;
    last_array := Array.of_list (List.map Obj.repr xs)
  end;
  let a = !last_array in
  if Z.sign i >= 0 && Z.lt i (Z.of_int (Array.length a)) then Obj.obj a.(Z.to_int i)
  else default
