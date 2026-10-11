(** Known-answer tests copied from pinned original ZiskAccel.lean.
    vm_compute produces proof terms checked by the Rocq kernel. *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Galette.HOL.src.list.src Require Import list rich_list.
From InitE.Guest Require Import Accel AccelFfi ByteCodec.
Open Scope N_scope.
Example sha256Compress_kat_empty :
 sha256Compress
      [n2w 1779033703; n2w 3144134277; n2w 1013904242; n2w 2773480762;
       n2w 1359893119; n2w 2600822924; n2w 528734635; n2w 1541459225]
      [n2w 2147483648; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0]
    = [n2w 3820012610; n2w 2566659092; n2w 2600203464; n2w 2574235940;
       n2w 665731556; n2w 1687917388; n2w 2761267483; n2w 2018687061].
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example blake2bRound_kat_abc :
 blake2bRound 0
      [n2w 7640891576939301192; n2w 13503953896175478587; n2w 4354685564936845355;
       n2w 11912009170470909681; n2w 5840696475078001361; n2w 11170449401992604703;
       n2w 2270897969802886507; n2w 6620516959819538809; n2w 7640891576956012808;
       n2w 13503953896175478587; n2w 4354685564936845355; n2w 11912009170470909681;
       n2w 5840696475078001362; n2w 11170449401992604703; n2w 16175846103906665108;
       n2w 6620516959819538809]
      [n2w 6513249; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0; n2w 0]
    = [n2w 9707440099081960313; n2w 13919708115642571251; n2w 14313883604204833422;
       n2w 902916003658517597; n2w 4967013240145357303; n2w 11837650394348604030;
       n2w 15999054287854434379; n2w 6439224605934397036; n2w 13746022367454054535;
       n2w 7090913738691013329; n2w 18052591224639614398; n2w 5916165702131158410;
       n2w 16153577839664528003; n2w 2052363037506523539; n2w 10342616010177476862;
       n2w 2528949647217589348].
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example secp_curveDbl_kat :
 curveDbl secpP
      55066263022277343669578718895168534326250603453777594175500187360389116729240
      32670510020758816978083085130507043184471273380659243275938904335757337482424
    = (89565891926547004231252920425935692360644145829622209833684329913297188986597,
       12158399299693830322967808612713398636155367887041628176798871954788371653930).
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example secp_curveAdd_kat :
 curveAdd secpP
      55066263022277343669578718895168534326250603453777594175500187360389116729240
      32670510020758816978083085130507043184471273380659243275938904335757337482424
      89565891926547004231252920425935692360644145829622209833684329913297188986597
      12158399299693830322967808612713398636155367887041628176798871954788371653930
    = (112711660439710606056748659173929673102114977341539408544630613555209775888121,
       25583027980570883691656905877401976406448868254816295069919888960541586679410).
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example sha_wire_padding : dwordsToU32sBE [n2w 128] = [n2w 2147483648;n2w 0].
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example nonempty_configuration_rejected : keccakfBytes [n2w 0] [] = None.
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example zero_modulus_rejected : arithModBytes 4 [] (leBytesOfWords (REPLICATE 20 (n2w 0))) = None.
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example bn254_complexMul_kat :
 complexMulL bn254P 4 (natToLeLimbs 4 1 ++ natToLeLimbs 4 2)
 (natToLeLimbs 4 3 ++ natToLeLimbs 4 4) =
 natToLeLimbs 4 (bn254P-5) ++ natToLeLimbs 4 10.
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
Example keccakF_kat_empty :
 TAKE 4 (keccakF (MAP (fun j => if j =? 0 then n2w 1 else if j =? 16
 then n2w 9223372036854775808 else n2w 0) (COUNT_LIST 25))) =
 [n2w 4333579421379646149;n2w 13836122230913597074;n2w 4262519377828905189;n2w 8116759062988257915].
Proof. apply (proj1 (bool_decide_spec _)); vm_compute; reflexivity. Qed.
