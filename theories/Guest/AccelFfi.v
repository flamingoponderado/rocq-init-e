(** Original Guest/AccelFfi.lean: complete byte-level accelerator oracle. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From Galette.HOL.src.string Require Import string.
From Galette.cakeml.basis.pure Require Import mlstring.
From InitE.Guest Require Import ByteCodec Accel.
Open Scope N_scope.
Open Scope hol_string_scope.
Definition keccakfBytes (configuration bytes : list word8) : option (list word8) :=
 option_map (fun state => leBytesOfWords (keccakF state)) (exactWords configuration bytes 25).
Definition sha256fBytes (configuration bytes : list word8) : option (list word8) :=
 option_map (fun ws => leBytesOfWords (u32sToDwords (sha256Compress
   (dwordsToU32s (TAKE 4 ws)) (dwordsToU32sBE (DROP 4 ws)))) ++ DROP 32 bytes)
   (exactWords configuration bytes 12).
Definition arithModBytes (limbs : N) (configuration bytes : list word8) : option (list word8) :=
 match exactWords configuration bytes (5*limbs) with
 | None => None
 | Some ws =>
   let a := TAKE limbs ws in let b := TAKE limbs (DROP limbs ws) in
   let c := TAKE limbs (DROP (2*limbs) ws) in let m := TAKE limbs (DROP (3*limbs) ws) in
   let modulus := leLimbsToNat m in
   if modulus =? 0 then None else
   Some (leBytesOfWords (TAKE (4*limbs) ws ++ natToLeLimbs limbs
     (arith256Mod (leLimbsToNat a) (leLimbsToNat b) (leLimbsToNat c) modulus)))
 end.
Definition curveAddBytes (prime limbs : N) (configuration bytes : list word8) : option (list word8) :=
 match exactWords configuration bytes (4*limbs) with
 | None => None
 | Some ws =>
   let pt1 := TAKE (2*limbs) ws in let pt2 := DROP (2*limbs) ws in
   if ptValid prime limbs pt1 && ptValid prime limbs pt2 &&
     negb (leLimbsToNat (TAKE limbs pt1) =? leLimbsToNat (TAKE limbs pt2))
   then Some (leBytesOfWords (curveAddL prime limbs pt1 pt2 ++ pt2)) else None
 end.
Definition curveDblBytes (prime limbs : N) (configuration bytes : list word8) : option (list word8) :=
 match exactWords configuration bytes (2*limbs) with
 | None => None
 | Some pt => if ptValid prime limbs pt && negb (leLimbsToNat (DROP limbs pt) =? 0)
   then Some (leBytesOfWords (curveDblL prime limbs pt)) else None
 end.
Definition complexBytes (op : N -> N -> list (word 64) -> list (word 64) -> list (word 64))
 (prime limbs : N) (configuration bytes : list word8) : option (list word8) :=
 match exactWords configuration bytes (4*limbs) with
 | None => None
 | Some ws => let a := TAKE (2*limbs) ws in let b := DROP (2*limbs) ws in
   if ptValid prime limbs a && ptValid prime limbs b
   then Some (leBytesOfWords (op prime limbs a b ++ b)) else None
 end.
Definition blake2bBytes (configuration bytes : list word8) : option (list word8) :=
 match exactWords configuration bytes 33 with
 | Some (index::rest) =>
   let state := TAKE 16 rest in let input := DROP 16 rest in
   if w2n index <? 10 then Some (leBytesOfWords (index :: blake2bRound (w2n index) state input ++ input)) else None
 | _ => None
 end.
Definition acceleratorBytes (name : mlstring) (configuration bytes : list word8) : option (list word8) :=
 if bool_decide (name = strlit "keccakf") then keccakfBytes configuration bytes else
 if bool_decide (name = strlit "sha256f") then sha256fBytes configuration bytes else
 if bool_decide (name = strlit "arith256mod") then arithModBytes 4 configuration bytes else
 if bool_decide (name = strlit "bn_arith256") then arithModBytes 4 configuration bytes else
 if bool_decide (name = strlit "bls_arith384") then arithModBytes 6 configuration bytes else
 if bool_decide (name = strlit "secpadd") then curveAddBytes secpP 4 configuration bytes else
 if bool_decide (name = strlit "secpdbl") then curveDblBytes secpP 4 configuration bytes else
 if bool_decide (name = strlit "bn_g1_add") then curveAddBytes bn254P 4 configuration bytes else
 if bool_decide (name = strlit "bn_g1_dbl") then curveDblBytes bn254P 4 configuration bytes else
 if bool_decide (name = strlit "bn_fp2_add") then complexBytes complexAddL bn254P 4 configuration bytes else
 if bool_decide (name = strlit "bn_fp2_sub") then complexBytes complexSubL bn254P 4 configuration bytes else
 if bool_decide (name = strlit "bn_fp2_mul") then complexBytes complexMulL bn254P 4 configuration bytes else
 if bool_decide (name = strlit "bls_g1_add") then curveAddBytes bls12P 6 configuration bytes else
 if bool_decide (name = strlit "bls_g1_dbl") then curveDblBytes bls12P 6 configuration bytes else
 if bool_decide (name = strlit "bls_fp2_add") then complexBytes complexAddL bls12P 6 configuration bytes else
 if bool_decide (name = strlit "bls_fp2_sub") then complexBytes complexSubL bls12P 6 configuration bytes else
 if bool_decide (name = strlit "bls_fp2_mul") then complexBytes complexMulL bls12P 6 configuration bytes else
 if bool_decide (name = strlit "blake2bround") then blake2bBytes configuration bytes else
 None.
