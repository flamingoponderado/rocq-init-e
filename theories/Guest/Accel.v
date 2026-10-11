(** Computational port of the pure accelerator definitions in pinned
    RiscvZkvm/Rv64/ZiskAccel.lean. No oracle axioms or extracted callbacks. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
Open Scope N_scope.
Definition getW {a : N} (ws : list (word a)) (i : N) : word a :=
 nth (N.to_nat i) ws (n2w 0).
Fixpoint setAt {A} (i : nat) (x : A) (xs : list A) : list A :=
 match xs, i with [],_ => [] | _::rest,O => x::rest | y::rest,S j => y::setAt j x rest end.
Definition keccakRC : list (word 64) := [(n2w 1); (n2w 32898); (n2w 9223372036854808714);
   (n2w 9223372039002292224); (n2w 32907); (n2w 2147483649);
   (n2w 9223372039002292353); (n2w 9223372036854808585); (n2w 138);
   (n2w 136); (n2w 2147516425); (n2w 2147483658);
   (n2w 2147516555); (n2w 9223372036854775947); (n2w 9223372036854808713);
   (n2w 9223372036854808579); (n2w 9223372036854808578); (n2w 9223372036854775936);
   (n2w 32778); (n2w 9223372039002259466); (n2w 9223372039002292353);
   (n2w 9223372036854808704); (n2w 2147483649); (n2w 9223372039002292232)].
Definition sha256K : list (word 32) := [(n2w 1116352408); (n2w 1899447441); (n2w 3049323471); (n2w 3921009573);
   (n2w 961987163); (n2w 1508970993); (n2w 2453635748); (n2w 2870763221);
   (n2w 3624381080); (n2w 310598401); (n2w 607225278); (n2w 1426881987);
   (n2w 1925078388); (n2w 2162078206); (n2w 2614888103); (n2w 3248222580);
   (n2w 3835390401); (n2w 4022224774); (n2w 264347078); (n2w 604807628);
   (n2w 770255983); (n2w 1249150122); (n2w 1555081692); (n2w 1996064986);
   (n2w 2554220882); (n2w 2821834349); (n2w 2952996808); (n2w 3210313671);
   (n2w 3336571891); (n2w 3584528711); (n2w 113926993); (n2w 338241895);
   (n2w 666307205); (n2w 773529912); (n2w 1294757372); (n2w 1396182291);
   (n2w 1695183700); (n2w 1986661051); (n2w 2177026350); (n2w 2456956037);
   (n2w 2730485921); (n2w 2820302411); (n2w 3259730800); (n2w 3345764771);
   (n2w 3516065817); (n2w 3600352804); (n2w 4094571909); (n2w 275423344);
   (n2w 430227734); (n2w 506948616); (n2w 659060556); (n2w 883997877);
   (n2w 958139571); (n2w 1322822218); (n2w 1537002063); (n2w 1747873779);
   (n2w 1955562222); (n2w 2024104815); (n2w 2227730452); (n2w 2361852424);
   (n2w 2428436474); (n2w 2756734187); (n2w 3204031479); (n2w 3329325298)].
Definition blake2Sigma : list (list N) := [[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15];
   [14; 10; 4; 8; 9; 15; 13; 6; 1; 12; 0; 2; 11; 7; 5; 3];
   [11; 8; 12; 0; 5; 2; 15; 13; 10; 14; 3; 6; 7; 1; 9; 4];
   [7; 9; 3; 1; 13; 12; 11; 14; 2; 6; 5; 10; 4; 0; 15; 8];
   [9; 0; 5; 7; 2; 4; 10; 15; 14; 1; 11; 12; 6; 8; 3; 13];
   [2; 12; 6; 10; 0; 11; 8; 3; 4; 13; 7; 5; 15; 14; 1; 9];
   [12; 5; 1; 15; 14; 13; 4; 10; 0; 7; 6; 3; 9; 2; 8; 11];
   [13; 11; 7; 14; 12; 1; 3; 9; 5; 0; 15; 4; 8; 6; 2; 10];
   [6; 15; 14; 9; 11; 3; 0; 8; 12; 2; 13; 7; 1; 4; 10; 5];
   [10; 2; 8; 4; 7; 6; 1; 5; 15; 11; 9; 14; 3; 12; 13; 0]].
Definition rhoOff (x y : N) : N :=
 nth (N.to_nat (y mod 5))
  (nth (N.to_nat (x mod 5))
   [[0;36;3;41;18];[1;44;10;45;2];[62;6;43;15;61];[28;55;25;21;56];[27;20;39;8;14]] []) 0.
Definition keccakRound (rc : word 64) (st : list (word 64)) : list (word 64) :=
 let A := fun x y => getW st (x mod 5 + 5*(y mod 5)) in
 let C := fun x => word_xor (word_xor (word_xor (word_xor (A x 0) (A x 1)) (A x 2)) (A x 3)) (A x 4) in
 let D := fun x => word_xor (C (x+4)) (word_rol (C (x+1)) 1) in
 let B := fun X Y => let xs := (X+3*Y) mod 5 in let ys := X mod 5 in
   word_rol (word_xor (A xs ys) (D xs)) (rhoOff xs ys) in
 let chi := fun j => let X := j mod 5 in let Y := j/5 in
   word_xor (B X Y) (word_and (word_1comp (B (X+1) Y)) (B (X+2) Y)) in
 MAP (fun j => if j =? 0 then word_xor (chi 0) rc else chi j) (COUNT_LIST 25).
Definition keccakF (st : list (word 64)) : list (word 64) :=
 fold_left (fun s rc => keccakRound rc s) keccakRC st.
Definition sha256W (w : list (word 32)) : list (word 32) :=
 fold_left (fun acc t =>
   if t <? 16 then acc ++ [getW w t] else
   let s0 := word_xor (word_xor (word_ror (getW acc (t-15)) 7) (word_ror (getW acc (t-15)) 18)) (word_lsr (getW acc (t-15)) 3) in
   let s1 := word_xor (word_xor (word_ror (getW acc (t-2)) 17) (word_ror (getW acc (t-2)) 19)) (word_lsr (getW acc (t-2)) 10) in
   acc ++ [(getW acc (t-16)+s0+getW acc (t-7)+s1)%w]) (COUNT_LIST 64) [].
Definition sha256Compress (hs w : list (word 32)) : list (word 32) :=
 let W := sha256W w in
 let fin := fold_left (fun st t =>
   let a := getW st 0 in let b := getW st 1 in let c := getW st 2 in let d := getW st 3 in
   let e := getW st 4 in let f := getW st 5 in let g := getW st 6 in let h := getW st 7 in
   let S1 := word_xor (word_xor (word_ror e 6) (word_ror e 11)) (word_ror e 25) in
   let ch := word_xor (word_and e f) (word_and (word_1comp e) g) in
   let T1 := (h+S1+ch+getW sha256K t+getW W t)%w in
   let S0 := word_xor (word_xor (word_ror a 2) (word_ror a 13)) (word_ror a 22) in
   let maj := word_xor (word_xor (word_and a b) (word_and a c)) (word_and b c) in
   let T2 := (S0+maj)%w in
   [(T1+T2)%w;a;b;c;(d+T1)%w;e;f;g]) (COUNT_LIST 64) (TAKE 8 hs) in
 MAP (fun xy => (fst xy+snd xy)%w) (combine (TAKE 8 hs) fin).
Definition leLimbsToNat (ws : list (word 64)) : N :=
 fold_right (fun w acc => acc*2^64+w2n w) 0 ws.
Definition natToLeLimbs (n x : N) : list (word 64) :=
 MAP (fun i => n2w (N.shiftr x (64*i))) (COUNT_LIST n).
Definition arith256Mod (a b c m : N) : N := (a*b+c) mod m.
Fixpoint powModAux (m : N) (fuel : nat) (b e : N) : N :=
 match fuel with
 | O => 1 mod m
 | S f => if e =? 0 then 1 mod m else
   let h := powModAux m f ((b*b) mod m) (e/2) in
   if e mod 2 =? 1 then (h*(b mod m)) mod m else h
 end.
Definition powMod (b e m : N) : N := powModAux m 512 (b mod m) e.
Definition invMod (x m : N) : N := powMod x (m-2) m.
Definition curveAdd (p x1 y1 x2 y2 : N) : N*N :=
 let lam := ((y2+p-y1)*invMod ((x2+p-x1) mod p) p) mod p in
 let x3 := (lam*lam+2*p-x1-x2) mod p in
 (x3,(lam*((x1+p-x3) mod p)+p-y1) mod p).
Definition curveDbl (p x1 y1 : N) : N*N :=
 let lam := ((3*x1*x1) mod p * invMod ((2*y1) mod p) p) mod p in
 let x3 := (lam*lam+2*p-x1-x1) mod p in
 (x3,(lam*((x1+p-x3) mod p)+p-y1) mod p).
Definition curveAddL (p nl : N) (pt1 pt2 : list (word 64)) : list (word 64) :=
 let r := curveAdd p (leLimbsToNat (TAKE nl pt1)) (leLimbsToNat (DROP nl pt1))
  (leLimbsToNat (TAKE nl pt2)) (leLimbsToNat (DROP nl pt2)) in
 natToLeLimbs nl (fst r) ++ natToLeLimbs nl (snd r).
Definition curveDblL (p nl : N) (pt : list (word 64)) : list (word 64) :=
 let r := curveDbl p (leLimbsToNat (TAKE nl pt)) (leLimbsToNat (DROP nl pt)) in
 natToLeLimbs nl (fst r) ++ natToLeLimbs nl (snd r).
Definition ptValid (p nl : N) (pt : list (word 64)) : bool :=
 (leLimbsToNat (TAKE nl pt) <? p) && (leLimbsToNat (DROP nl pt) <? p).
Definition complexAddL (p nl : N) (f1 f2 : list (word 64)) : list (word 64) :=
 natToLeLimbs nl ((leLimbsToNat (TAKE nl f1)+leLimbsToNat (TAKE nl f2)) mod p) ++
 natToLeLimbs nl ((leLimbsToNat (DROP nl f1)+leLimbsToNat (DROP nl f2)) mod p).
Definition complexSubL (p nl : N) (f1 f2 : list (word 64)) : list (word 64) :=
 natToLeLimbs nl ((leLimbsToNat (TAKE nl f1)+p-leLimbsToNat (TAKE nl f2)) mod p) ++
 natToLeLimbs nl ((leLimbsToNat (DROP nl f1)+p-leLimbsToNat (DROP nl f2)) mod p).
Definition complexMulL (p nl : N) (f1 f2 : list (word 64)) : list (word 64) :=
 let x0 := leLimbsToNat (TAKE nl f1) in let x1 := leLimbsToNat (DROP nl f1) in
 let y0 := leLimbsToNat (TAKE nl f2) in let y1 := leLimbsToNat (DROP nl f2) in
 natToLeLimbs nl ((x0*y0+p*p-x1*y1) mod p) ++ natToLeLimbs nl ((x0*y1+x1*y0) mod p).
Definition blakeG (v : list (word 64)) (a b c d : N) (x y : word 64) : list (word 64) :=
 let va := (getW v a+getW v b+x)%w in
 let vd := word_ror (word_xor (getW v d) va) 32 in
 let vc := (getW v c+vd)%w in
 let vb := word_ror (word_xor (getW v b) vc) 24 in
 let va' := (va+vb+y)%w in
 let vd' := word_ror (word_xor vd va') 16 in
 let vc' := (vc+vd')%w in
 let vb' := word_ror (word_xor vb vc') 63 in
 setAt (N.to_nat d) vd' (setAt (N.to_nat c) vc' (setAt (N.to_nat b) vb' (setAt (N.to_nat a) va' v))).
Definition blake2bRound (idx : N) (v m : list (word 64)) : list (word 64) :=
 let s := nth (N.to_nat (idx mod 10)) blake2Sigma [] in
 let mi := fun i => getW m (nth (N.to_nat i) s 0) in
 let v1 := blakeG v 0 4 8 12 (mi 0) (mi 1) in
 let v2 := blakeG v1 1 5 9 13 (mi 2) (mi 3) in
 let v3 := blakeG v2 2 6 10 14 (mi 4) (mi 5) in
 let v4 := blakeG v3 3 7 11 15 (mi 6) (mi 7) in
 let v5 := blakeG v4 0 5 10 15 (mi 8) (mi 9) in
 let v6 := blakeG v5 1 6 11 12 (mi 10) (mi 11) in
 let v7 := blakeG v6 2 7 8 13 (mi 12) (mi 13) in
 blakeG v7 3 4 9 14 (mi 14) (mi 15).
Definition dwordsToU32s (ws : list (word 64)) : list (word 32) :=
 flat_map (fun w => [w2w w;w2w (word_lsr w 32)]) ws.
Definition byteSwap32 (x : word 32) : word 32 :=
 word_or (word_or (word_or (word_lsl (word_and x (n2w 255)) 24)
  (word_lsl (word_and x (n2w 65280)) 8))
  (word_lsr (word_and x (n2w 16711680)) 8))
  (word_lsr (word_and x (n2w 4278190080)) 24).
Definition dwordBE (w : word 64) : word 64 :=
 word_or (w2w (byteSwap32 (w2w w))) (word_lsl (w2w (byteSwap32 (w2w (word_lsr w 32)))) 32).
Definition dwordsToU32sBE (ws : list (word 64)) : list (word 32) := dwordsToU32s (MAP dwordBE ws).
Fixpoint u32sToDwords (ws : list (word 32)) : list (word 64) :=
 match ws with lo::hi::rest => word_or (word_lsl (w2w hi) 32) (w2w lo)::u32sToDwords rest | _ => [] end.
Definition secpP : N := 115792089237316195423570985008687907853269984665640564039457584007908834671663.
Definition bn254P : N := 21888242871839275222246405745257275088696311157297823662689037894645226208583.
Definition bls12P : N := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.
