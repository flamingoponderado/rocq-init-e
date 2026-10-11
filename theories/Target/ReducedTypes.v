(* Generated from original reduced Types.lean; do not edit. *)
(* SHA256: a48508a93122656a67d2bdb65c9b5405abb1aa5cdbb1d4b5257b34ed195cc558 *)
From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From Stdlib Require Import Strings.Ascii.
Open Scope N_scope.
Inductive rawInstType : Type :=
 | Half : word 16 -> rawInstType
 | Word : word 32 -> rawInstType.
#[global] Instance rawInstType_inhabited : Inhabited rawInstType := Half (inhabitant _).
#[global] Instance rawInstType_eq_dec : EqDecision rawInstType.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive accessType : Type :=
 | Read : accessType
 | Write : accessType.
#[global] Instance accessType_inhabited : Inhabited accessType := Read.
#[global] Instance accessType_eq_dec : EqDecision accessType.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive fetchType : Type :=
 | Instruction : fetchType
 | Data : fetchType.
#[global] Instance fetchType_inhabited : Inhabited fetchType := Instruction.
#[global] Instance fetchType_eq_dec : EqDecision fetchType.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Architecture : Type :=
 | RV32I : Architecture
 | RV64I : Architecture
 | RV128I : Architecture.
#[global] Instance Architecture_inhabited : Inhabited Architecture := RV32I.
#[global] Instance Architecture_eq_dec : EqDecision Architecture.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Privilege : Type :=
 | User : Privilege
 | Supervisor : Privilege
 | Hypervisor : Privilege
 | Machine : Privilege.
#[global] Instance Privilege_inhabited : Inhabited Privilege := User.
#[global] Instance Privilege_eq_dec : EqDecision Privilege.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive VM_Mode : Type :=
 | Mbare : VM_Mode
 | Mbb : VM_Mode
 | Mbbid : VM_Mode
 | Sv32 : VM_Mode
 | Sv39 : VM_Mode
 | Sv48 : VM_Mode
 | Sv57 : VM_Mode
 | Sv64 : VM_Mode.
#[global] Instance VM_Mode_inhabited : Inhabited VM_Mode := Mbare.
#[global] Instance VM_Mode_eq_dec : EqDecision VM_Mode.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive ExtStatus : Type :=
 | Off : ExtStatus
 | Initial : ExtStatus
 | Clean : ExtStatus
 | Dirty : ExtStatus.
#[global] Instance ExtStatus_inhabited : Inhabited ExtStatus := Off.
#[global] Instance ExtStatus_eq_dec : EqDecision ExtStatus.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive ExceptionType : Type :=
 | Fetch_Misaligned : ExceptionType
 | Fetch_Fault : ExceptionType
 | Illegal_Instr : ExceptionType
 | Breakpoint : ExceptionType
 | Load_Fault : ExceptionType
 | AMO_Misaligned : ExceptionType
 | Store_AMO_Fault : ExceptionType
 | UMode_Env_Call : ExceptionType
 | SMode_Env_Call : ExceptionType
 | HMode_Env_Call : ExceptionType
 | MMode_Env_Call : ExceptionType.
#[global] Instance ExceptionType_inhabited : Inhabited ExceptionType := Fetch_Misaligned.
#[global] Instance ExceptionType_eq_dec : EqDecision ExceptionType.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mcpuid : Type := {
 mcpuid_ArchBase : word 2;
 mcpuid_I : bool;
 mcpuid_M : bool;
 mcpuid_S : bool;
 mcpuid_U : bool;
 mcpuid_mcpuid'rst : word 58
}.
#[global] Instance mcpuid_inhabited : Inhabited mcpuid :=
 {| mcpuid_ArchBase := inhabitant _;
    mcpuid_I := inhabitant _;
    mcpuid_M := inhabitant _;
    mcpuid_S := inhabitant _;
    mcpuid_U := inhabitant _;
    mcpuid_mcpuid'rst := inhabitant _ |}.
Definition mcpuid_ArchBase_fupd (update : word 2 -> word 2) (x : mcpuid) : mcpuid :=
 {| mcpuid_ArchBase := update (mcpuid_ArchBase x);
    mcpuid_I := mcpuid_I x;
    mcpuid_M := mcpuid_M x;
    mcpuid_S := mcpuid_S x;
    mcpuid_U := mcpuid_U x;
    mcpuid_mcpuid'rst := mcpuid_mcpuid'rst x |}.
Definition mcpuid_I_fupd (update : bool -> bool) (x : mcpuid) : mcpuid :=
 {| mcpuid_ArchBase := mcpuid_ArchBase x;
    mcpuid_I := update (mcpuid_I x);
    mcpuid_M := mcpuid_M x;
    mcpuid_S := mcpuid_S x;
    mcpuid_U := mcpuid_U x;
    mcpuid_mcpuid'rst := mcpuid_mcpuid'rst x |}.
Definition mcpuid_M_fupd (update : bool -> bool) (x : mcpuid) : mcpuid :=
 {| mcpuid_ArchBase := mcpuid_ArchBase x;
    mcpuid_I := mcpuid_I x;
    mcpuid_M := update (mcpuid_M x);
    mcpuid_S := mcpuid_S x;
    mcpuid_U := mcpuid_U x;
    mcpuid_mcpuid'rst := mcpuid_mcpuid'rst x |}.
Definition mcpuid_S_fupd (update : bool -> bool) (x : mcpuid) : mcpuid :=
 {| mcpuid_ArchBase := mcpuid_ArchBase x;
    mcpuid_I := mcpuid_I x;
    mcpuid_M := mcpuid_M x;
    mcpuid_S := update (mcpuid_S x);
    mcpuid_U := mcpuid_U x;
    mcpuid_mcpuid'rst := mcpuid_mcpuid'rst x |}.
Definition mcpuid_U_fupd (update : bool -> bool) (x : mcpuid) : mcpuid :=
 {| mcpuid_ArchBase := mcpuid_ArchBase x;
    mcpuid_I := mcpuid_I x;
    mcpuid_M := mcpuid_M x;
    mcpuid_S := mcpuid_S x;
    mcpuid_U := update (mcpuid_U x);
    mcpuid_mcpuid'rst := mcpuid_mcpuid'rst x |}.
Definition mcpuid_mcpuid'rst_fupd (update : word 58 -> word 58) (x : mcpuid) : mcpuid :=
 {| mcpuid_ArchBase := mcpuid_ArchBase x;
    mcpuid_I := mcpuid_I x;
    mcpuid_M := mcpuid_M x;
    mcpuid_S := mcpuid_S x;
    mcpuid_U := mcpuid_U x;
    mcpuid_mcpuid'rst := update (mcpuid_mcpuid'rst x) |}.
#[global] Instance mcpuid_eq_dec : EqDecision mcpuid.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mimpid : Type := {
 mimpid_RVImpl : word 48;
 mimpid_RVSource : word 16
}.
#[global] Instance mimpid_inhabited : Inhabited mimpid :=
 {| mimpid_RVImpl := inhabitant _;
    mimpid_RVSource := inhabitant _ |}.
Definition mimpid_RVImpl_fupd (update : word 48 -> word 48) (x : mimpid) : mimpid :=
 {| mimpid_RVImpl := update (mimpid_RVImpl x);
    mimpid_RVSource := mimpid_RVSource x |}.
Definition mimpid_RVSource_fupd (update : word 16 -> word 16) (x : mimpid) : mimpid :=
 {| mimpid_RVImpl := mimpid_RVImpl x;
    mimpid_RVSource := update (mimpid_RVSource x) |}.
#[global] Instance mimpid_eq_dec : EqDecision mimpid.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mstatus : Type := {
 mstatus_MFS : word 2;
 mstatus_MIE : bool;
 mstatus_MIE1 : bool;
 mstatus_MIE2 : bool;
 mstatus_MIE3 : bool;
 mstatus_MMPRV : bool;
 mstatus_MPRV : word 2;
 mstatus_MPRV1 : word 2;
 mstatus_MPRV2 : word 2;
 mstatus_MPRV3 : word 2;
 mstatus_MSD : bool;
 mstatus_MXS : word 2;
 mstatus_VM : word 5;
 mstatus_mstatus'rst : word 41
}.
#[global] Instance mstatus_inhabited : Inhabited mstatus :=
 {| mstatus_MFS := inhabitant _;
    mstatus_MIE := inhabitant _;
    mstatus_MIE1 := inhabitant _;
    mstatus_MIE2 := inhabitant _;
    mstatus_MIE3 := inhabitant _;
    mstatus_MMPRV := inhabitant _;
    mstatus_MPRV := inhabitant _;
    mstatus_MPRV1 := inhabitant _;
    mstatus_MPRV2 := inhabitant _;
    mstatus_MPRV3 := inhabitant _;
    mstatus_MSD := inhabitant _;
    mstatus_MXS := inhabitant _;
    mstatus_VM := inhabitant _;
    mstatus_mstatus'rst := inhabitant _ |}.
Definition mstatus_MFS_fupd (update : word 2 -> word 2) (x : mstatus) : mstatus :=
 {| mstatus_MFS := update (mstatus_MFS x);
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MIE_fupd (update : bool -> bool) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := update (mstatus_MIE x);
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MIE1_fupd (update : bool -> bool) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := update (mstatus_MIE1 x);
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MIE2_fupd (update : bool -> bool) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := update (mstatus_MIE2 x);
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MIE3_fupd (update : bool -> bool) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := update (mstatus_MIE3 x);
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MMPRV_fupd (update : bool -> bool) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := update (mstatus_MMPRV x);
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MPRV_fupd (update : word 2 -> word 2) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := update (mstatus_MPRV x);
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MPRV1_fupd (update : word 2 -> word 2) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := update (mstatus_MPRV1 x);
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MPRV2_fupd (update : word 2 -> word 2) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := update (mstatus_MPRV2 x);
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MPRV3_fupd (update : word 2 -> word 2) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := update (mstatus_MPRV3 x);
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MSD_fupd (update : bool -> bool) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := update (mstatus_MSD x);
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_MXS_fupd (update : word 2 -> word 2) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := update (mstatus_MXS x);
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_VM_fupd (update : word 5 -> word 5) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := update (mstatus_VM x);
    mstatus_mstatus'rst := mstatus_mstatus'rst x |}.
Definition mstatus_mstatus'rst_fupd (update : word 41 -> word 41) (x : mstatus) : mstatus :=
 {| mstatus_MFS := mstatus_MFS x;
    mstatus_MIE := mstatus_MIE x;
    mstatus_MIE1 := mstatus_MIE1 x;
    mstatus_MIE2 := mstatus_MIE2 x;
    mstatus_MIE3 := mstatus_MIE3 x;
    mstatus_MMPRV := mstatus_MMPRV x;
    mstatus_MPRV := mstatus_MPRV x;
    mstatus_MPRV1 := mstatus_MPRV1 x;
    mstatus_MPRV2 := mstatus_MPRV2 x;
    mstatus_MPRV3 := mstatus_MPRV3 x;
    mstatus_MSD := mstatus_MSD x;
    mstatus_MXS := mstatus_MXS x;
    mstatus_VM := mstatus_VM x;
    mstatus_mstatus'rst := update (mstatus_mstatus'rst x) |}.
#[global] Instance mstatus_eq_dec : EqDecision mstatus.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mtdeleg : Type := {
 mtdeleg_Exc_deleg : word 16;
 mtdeleg_Intr_deleg : word 48
}.
#[global] Instance mtdeleg_inhabited : Inhabited mtdeleg :=
 {| mtdeleg_Exc_deleg := inhabitant _;
    mtdeleg_Intr_deleg := inhabitant _ |}.
Definition mtdeleg_Exc_deleg_fupd (update : word 16 -> word 16) (x : mtdeleg) : mtdeleg :=
 {| mtdeleg_Exc_deleg := update (mtdeleg_Exc_deleg x);
    mtdeleg_Intr_deleg := mtdeleg_Intr_deleg x |}.
Definition mtdeleg_Intr_deleg_fupd (update : word 48 -> word 48) (x : mtdeleg) : mtdeleg :=
 {| mtdeleg_Exc_deleg := mtdeleg_Exc_deleg x;
    mtdeleg_Intr_deleg := update (mtdeleg_Intr_deleg x) |}.
#[global] Instance mtdeleg_eq_dec : EqDecision mtdeleg.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mip : Type := {
 mip_HSIP : bool;
 mip_HTIP : bool;
 mip_MSIP : bool;
 mip_MTIP : bool;
 mip_SSIP : bool;
 mip_STIP : bool;
 mip_mip'rst : word 58
}.
#[global] Instance mip_inhabited : Inhabited mip :=
 {| mip_HSIP := inhabitant _;
    mip_HTIP := inhabitant _;
    mip_MSIP := inhabitant _;
    mip_MTIP := inhabitant _;
    mip_SSIP := inhabitant _;
    mip_STIP := inhabitant _;
    mip_mip'rst := inhabitant _ |}.
Definition mip_HSIP_fupd (update : bool -> bool) (x : mip) : mip :=
 {| mip_HSIP := update (mip_HSIP x);
    mip_HTIP := mip_HTIP x;
    mip_MSIP := mip_MSIP x;
    mip_MTIP := mip_MTIP x;
    mip_SSIP := mip_SSIP x;
    mip_STIP := mip_STIP x;
    mip_mip'rst := mip_mip'rst x |}.
Definition mip_HTIP_fupd (update : bool -> bool) (x : mip) : mip :=
 {| mip_HSIP := mip_HSIP x;
    mip_HTIP := update (mip_HTIP x);
    mip_MSIP := mip_MSIP x;
    mip_MTIP := mip_MTIP x;
    mip_SSIP := mip_SSIP x;
    mip_STIP := mip_STIP x;
    mip_mip'rst := mip_mip'rst x |}.
Definition mip_MSIP_fupd (update : bool -> bool) (x : mip) : mip :=
 {| mip_HSIP := mip_HSIP x;
    mip_HTIP := mip_HTIP x;
    mip_MSIP := update (mip_MSIP x);
    mip_MTIP := mip_MTIP x;
    mip_SSIP := mip_SSIP x;
    mip_STIP := mip_STIP x;
    mip_mip'rst := mip_mip'rst x |}.
Definition mip_MTIP_fupd (update : bool -> bool) (x : mip) : mip :=
 {| mip_HSIP := mip_HSIP x;
    mip_HTIP := mip_HTIP x;
    mip_MSIP := mip_MSIP x;
    mip_MTIP := update (mip_MTIP x);
    mip_SSIP := mip_SSIP x;
    mip_STIP := mip_STIP x;
    mip_mip'rst := mip_mip'rst x |}.
Definition mip_SSIP_fupd (update : bool -> bool) (x : mip) : mip :=
 {| mip_HSIP := mip_HSIP x;
    mip_HTIP := mip_HTIP x;
    mip_MSIP := mip_MSIP x;
    mip_MTIP := mip_MTIP x;
    mip_SSIP := update (mip_SSIP x);
    mip_STIP := mip_STIP x;
    mip_mip'rst := mip_mip'rst x |}.
Definition mip_STIP_fupd (update : bool -> bool) (x : mip) : mip :=
 {| mip_HSIP := mip_HSIP x;
    mip_HTIP := mip_HTIP x;
    mip_MSIP := mip_MSIP x;
    mip_MTIP := mip_MTIP x;
    mip_SSIP := mip_SSIP x;
    mip_STIP := update (mip_STIP x);
    mip_mip'rst := mip_mip'rst x |}.
Definition mip_mip'rst_fupd (update : word 58 -> word 58) (x : mip) : mip :=
 {| mip_HSIP := mip_HSIP x;
    mip_HTIP := mip_HTIP x;
    mip_MSIP := mip_MSIP x;
    mip_MTIP := mip_MTIP x;
    mip_SSIP := mip_SSIP x;
    mip_STIP := mip_STIP x;
    mip_mip'rst := update (mip_mip'rst x) |}.
#[global] Instance mip_eq_dec : EqDecision mip.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mie : Type := {
 mie_HSIE : bool;
 mie_HTIE : bool;
 mie_MSIE : bool;
 mie_MTIE : bool;
 mie_SSIE : bool;
 mie_STIE : bool;
 mie_mie'rst : word 58
}.
#[global] Instance mie_inhabited : Inhabited mie :=
 {| mie_HSIE := inhabitant _;
    mie_HTIE := inhabitant _;
    mie_MSIE := inhabitant _;
    mie_MTIE := inhabitant _;
    mie_SSIE := inhabitant _;
    mie_STIE := inhabitant _;
    mie_mie'rst := inhabitant _ |}.
Definition mie_HSIE_fupd (update : bool -> bool) (x : mie) : mie :=
 {| mie_HSIE := update (mie_HSIE x);
    mie_HTIE := mie_HTIE x;
    mie_MSIE := mie_MSIE x;
    mie_MTIE := mie_MTIE x;
    mie_SSIE := mie_SSIE x;
    mie_STIE := mie_STIE x;
    mie_mie'rst := mie_mie'rst x |}.
Definition mie_HTIE_fupd (update : bool -> bool) (x : mie) : mie :=
 {| mie_HSIE := mie_HSIE x;
    mie_HTIE := update (mie_HTIE x);
    mie_MSIE := mie_MSIE x;
    mie_MTIE := mie_MTIE x;
    mie_SSIE := mie_SSIE x;
    mie_STIE := mie_STIE x;
    mie_mie'rst := mie_mie'rst x |}.
Definition mie_MSIE_fupd (update : bool -> bool) (x : mie) : mie :=
 {| mie_HSIE := mie_HSIE x;
    mie_HTIE := mie_HTIE x;
    mie_MSIE := update (mie_MSIE x);
    mie_MTIE := mie_MTIE x;
    mie_SSIE := mie_SSIE x;
    mie_STIE := mie_STIE x;
    mie_mie'rst := mie_mie'rst x |}.
Definition mie_MTIE_fupd (update : bool -> bool) (x : mie) : mie :=
 {| mie_HSIE := mie_HSIE x;
    mie_HTIE := mie_HTIE x;
    mie_MSIE := mie_MSIE x;
    mie_MTIE := update (mie_MTIE x);
    mie_SSIE := mie_SSIE x;
    mie_STIE := mie_STIE x;
    mie_mie'rst := mie_mie'rst x |}.
Definition mie_SSIE_fupd (update : bool -> bool) (x : mie) : mie :=
 {| mie_HSIE := mie_HSIE x;
    mie_HTIE := mie_HTIE x;
    mie_MSIE := mie_MSIE x;
    mie_MTIE := mie_MTIE x;
    mie_SSIE := update (mie_SSIE x);
    mie_STIE := mie_STIE x;
    mie_mie'rst := mie_mie'rst x |}.
Definition mie_STIE_fupd (update : bool -> bool) (x : mie) : mie :=
 {| mie_HSIE := mie_HSIE x;
    mie_HTIE := mie_HTIE x;
    mie_MSIE := mie_MSIE x;
    mie_MTIE := mie_MTIE x;
    mie_SSIE := mie_SSIE x;
    mie_STIE := update (mie_STIE x);
    mie_mie'rst := mie_mie'rst x |}.
Definition mie_mie'rst_fupd (update : word 58 -> word 58) (x : mie) : mie :=
 {| mie_HSIE := mie_HSIE x;
    mie_HTIE := mie_HTIE x;
    mie_MSIE := mie_MSIE x;
    mie_MTIE := mie_MTIE x;
    mie_SSIE := mie_SSIE x;
    mie_STIE := mie_STIE x;
    mie_mie'rst := update (mie_mie'rst x) |}.
#[global] Instance mie_eq_dec : EqDecision mie.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record mcause : Type := {
 mcause_EC : word 4;
 mcause_Int : bool;
 mcause_mcause'rst : word 59
}.
#[global] Instance mcause_inhabited : Inhabited mcause :=
 {| mcause_EC := inhabitant _;
    mcause_Int := inhabitant _;
    mcause_mcause'rst := inhabitant _ |}.
Definition mcause_EC_fupd (update : word 4 -> word 4) (x : mcause) : mcause :=
 {| mcause_EC := update (mcause_EC x);
    mcause_Int := mcause_Int x;
    mcause_mcause'rst := mcause_mcause'rst x |}.
Definition mcause_Int_fupd (update : bool -> bool) (x : mcause) : mcause :=
 {| mcause_EC := mcause_EC x;
    mcause_Int := update (mcause_Int x);
    mcause_mcause'rst := mcause_mcause'rst x |}.
Definition mcause_mcause'rst_fupd (update : word 59 -> word 59) (x : mcause) : mcause :=
 {| mcause_EC := mcause_EC x;
    mcause_Int := mcause_Int x;
    mcause_mcause'rst := update (mcause_mcause'rst x) |}.
#[global] Instance mcause_eq_dec : EqDecision mcause.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record MachineCSR : Type := {
 MachineCSR_mbadaddr : word 64;
 MachineCSR_mbase : word 64;
 MachineCSR_mbound : word 64;
 MachineCSR_mcause : mcause;
 MachineCSR_mcpuid : mcpuid;
 MachineCSR_mdbase : word 64;
 MachineCSR_mdbound : word 64;
 MachineCSR_mepc : word 64;
 MachineCSR_mfromhost : word 64;
 MachineCSR_mhartid : word 64;
 MachineCSR_mibase : word 64;
 MachineCSR_mibound : word 64;
 MachineCSR_mie : mie;
 MachineCSR_mimpid : mimpid;
 MachineCSR_mip : mip;
 MachineCSR_mscratch : word 64;
 MachineCSR_mstatus : mstatus;
 MachineCSR_mtdeleg : mtdeleg;
 MachineCSR_mtohost : word 64;
 MachineCSR_mtvec : word 64
}.
#[global] Instance MachineCSR_inhabited : Inhabited MachineCSR :=
 {| MachineCSR_mbadaddr := inhabitant _;
    MachineCSR_mbase := inhabitant _;
    MachineCSR_mbound := inhabitant _;
    MachineCSR_mcause := inhabitant _;
    MachineCSR_mcpuid := inhabitant _;
    MachineCSR_mdbase := inhabitant _;
    MachineCSR_mdbound := inhabitant _;
    MachineCSR_mepc := inhabitant _;
    MachineCSR_mfromhost := inhabitant _;
    MachineCSR_mhartid := inhabitant _;
    MachineCSR_mibase := inhabitant _;
    MachineCSR_mibound := inhabitant _;
    MachineCSR_mie := inhabitant _;
    MachineCSR_mimpid := inhabitant _;
    MachineCSR_mip := inhabitant _;
    MachineCSR_mscratch := inhabitant _;
    MachineCSR_mstatus := inhabitant _;
    MachineCSR_mtdeleg := inhabitant _;
    MachineCSR_mtohost := inhabitant _;
    MachineCSR_mtvec := inhabitant _ |}.
Definition MachineCSR_mbadaddr_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := update (MachineCSR_mbadaddr x);
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mbase_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := update (MachineCSR_mbase x);
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mbound_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := update (MachineCSR_mbound x);
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mcause_fupd (update : mcause -> mcause) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := update (MachineCSR_mcause x);
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mcpuid_fupd (update : mcpuid -> mcpuid) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := update (MachineCSR_mcpuid x);
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mdbase_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := update (MachineCSR_mdbase x);
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mdbound_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := update (MachineCSR_mdbound x);
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mepc_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := update (MachineCSR_mepc x);
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mfromhost_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := update (MachineCSR_mfromhost x);
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mhartid_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := update (MachineCSR_mhartid x);
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mibase_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := update (MachineCSR_mibase x);
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mibound_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := update (MachineCSR_mibound x);
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mie_fupd (update : mie -> mie) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := update (MachineCSR_mie x);
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mimpid_fupd (update : mimpid -> mimpid) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := update (MachineCSR_mimpid x);
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mip_fupd (update : mip -> mip) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := update (MachineCSR_mip x);
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mscratch_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := update (MachineCSR_mscratch x);
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mstatus_fupd (update : mstatus -> mstatus) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := update (MachineCSR_mstatus x);
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mtdeleg_fupd (update : mtdeleg -> mtdeleg) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := update (MachineCSR_mtdeleg x);
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mtohost_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := update (MachineCSR_mtohost x);
    MachineCSR_mtvec := MachineCSR_mtvec x |}.
Definition MachineCSR_mtvec_fupd (update : word 64 -> word 64) (x : MachineCSR) : MachineCSR :=
 {| MachineCSR_mbadaddr := MachineCSR_mbadaddr x;
    MachineCSR_mbase := MachineCSR_mbase x;
    MachineCSR_mbound := MachineCSR_mbound x;
    MachineCSR_mcause := MachineCSR_mcause x;
    MachineCSR_mcpuid := MachineCSR_mcpuid x;
    MachineCSR_mdbase := MachineCSR_mdbase x;
    MachineCSR_mdbound := MachineCSR_mdbound x;
    MachineCSR_mepc := MachineCSR_mepc x;
    MachineCSR_mfromhost := MachineCSR_mfromhost x;
    MachineCSR_mhartid := MachineCSR_mhartid x;
    MachineCSR_mibase := MachineCSR_mibase x;
    MachineCSR_mibound := MachineCSR_mibound x;
    MachineCSR_mie := MachineCSR_mie x;
    MachineCSR_mimpid := MachineCSR_mimpid x;
    MachineCSR_mip := MachineCSR_mip x;
    MachineCSR_mscratch := MachineCSR_mscratch x;
    MachineCSR_mstatus := MachineCSR_mstatus x;
    MachineCSR_mtdeleg := MachineCSR_mtdeleg x;
    MachineCSR_mtohost := MachineCSR_mtohost x;
    MachineCSR_mtvec := update (MachineCSR_mtvec x) |}.
#[global] Instance MachineCSR_eq_dec : EqDecision MachineCSR.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record HypervisorCSR : Type := {
 HypervisorCSR_hbadaddr : word 64;
 HypervisorCSR_hcause : mcause;
 HypervisorCSR_hepc : word 64;
 HypervisorCSR_hscratch : word 64;
 HypervisorCSR_hstatus : mstatus;
 HypervisorCSR_htdeleg : mtdeleg;
 HypervisorCSR_htvec : word 64
}.
#[global] Instance HypervisorCSR_inhabited : Inhabited HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := inhabitant _;
    HypervisorCSR_hcause := inhabitant _;
    HypervisorCSR_hepc := inhabitant _;
    HypervisorCSR_hscratch := inhabitant _;
    HypervisorCSR_hstatus := inhabitant _;
    HypervisorCSR_htdeleg := inhabitant _;
    HypervisorCSR_htvec := inhabitant _ |}.
Definition HypervisorCSR_hbadaddr_fupd (update : word 64 -> word 64) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := update (HypervisorCSR_hbadaddr x);
    HypervisorCSR_hcause := HypervisorCSR_hcause x;
    HypervisorCSR_hepc := HypervisorCSR_hepc x;
    HypervisorCSR_hscratch := HypervisorCSR_hscratch x;
    HypervisorCSR_hstatus := HypervisorCSR_hstatus x;
    HypervisorCSR_htdeleg := HypervisorCSR_htdeleg x;
    HypervisorCSR_htvec := HypervisorCSR_htvec x |}.
Definition HypervisorCSR_hcause_fupd (update : mcause -> mcause) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := HypervisorCSR_hbadaddr x;
    HypervisorCSR_hcause := update (HypervisorCSR_hcause x);
    HypervisorCSR_hepc := HypervisorCSR_hepc x;
    HypervisorCSR_hscratch := HypervisorCSR_hscratch x;
    HypervisorCSR_hstatus := HypervisorCSR_hstatus x;
    HypervisorCSR_htdeleg := HypervisorCSR_htdeleg x;
    HypervisorCSR_htvec := HypervisorCSR_htvec x |}.
Definition HypervisorCSR_hepc_fupd (update : word 64 -> word 64) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := HypervisorCSR_hbadaddr x;
    HypervisorCSR_hcause := HypervisorCSR_hcause x;
    HypervisorCSR_hepc := update (HypervisorCSR_hepc x);
    HypervisorCSR_hscratch := HypervisorCSR_hscratch x;
    HypervisorCSR_hstatus := HypervisorCSR_hstatus x;
    HypervisorCSR_htdeleg := HypervisorCSR_htdeleg x;
    HypervisorCSR_htvec := HypervisorCSR_htvec x |}.
Definition HypervisorCSR_hscratch_fupd (update : word 64 -> word 64) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := HypervisorCSR_hbadaddr x;
    HypervisorCSR_hcause := HypervisorCSR_hcause x;
    HypervisorCSR_hepc := HypervisorCSR_hepc x;
    HypervisorCSR_hscratch := update (HypervisorCSR_hscratch x);
    HypervisorCSR_hstatus := HypervisorCSR_hstatus x;
    HypervisorCSR_htdeleg := HypervisorCSR_htdeleg x;
    HypervisorCSR_htvec := HypervisorCSR_htvec x |}.
Definition HypervisorCSR_hstatus_fupd (update : mstatus -> mstatus) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := HypervisorCSR_hbadaddr x;
    HypervisorCSR_hcause := HypervisorCSR_hcause x;
    HypervisorCSR_hepc := HypervisorCSR_hepc x;
    HypervisorCSR_hscratch := HypervisorCSR_hscratch x;
    HypervisorCSR_hstatus := update (HypervisorCSR_hstatus x);
    HypervisorCSR_htdeleg := HypervisorCSR_htdeleg x;
    HypervisorCSR_htvec := HypervisorCSR_htvec x |}.
Definition HypervisorCSR_htdeleg_fupd (update : mtdeleg -> mtdeleg) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := HypervisorCSR_hbadaddr x;
    HypervisorCSR_hcause := HypervisorCSR_hcause x;
    HypervisorCSR_hepc := HypervisorCSR_hepc x;
    HypervisorCSR_hscratch := HypervisorCSR_hscratch x;
    HypervisorCSR_hstatus := HypervisorCSR_hstatus x;
    HypervisorCSR_htdeleg := update (HypervisorCSR_htdeleg x);
    HypervisorCSR_htvec := HypervisorCSR_htvec x |}.
Definition HypervisorCSR_htvec_fupd (update : word 64 -> word 64) (x : HypervisorCSR) : HypervisorCSR :=
 {| HypervisorCSR_hbadaddr := HypervisorCSR_hbadaddr x;
    HypervisorCSR_hcause := HypervisorCSR_hcause x;
    HypervisorCSR_hepc := HypervisorCSR_hepc x;
    HypervisorCSR_hscratch := HypervisorCSR_hscratch x;
    HypervisorCSR_hstatus := HypervisorCSR_hstatus x;
    HypervisorCSR_htdeleg := HypervisorCSR_htdeleg x;
    HypervisorCSR_htvec := update (HypervisorCSR_htvec x) |}.
#[global] Instance HypervisorCSR_eq_dec : EqDecision HypervisorCSR.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record sstatus : Type := {
 sstatus_SFS : word 2;
 sstatus_SIE : bool;
 sstatus_SMPRV : bool;
 sstatus_SPIE : bool;
 sstatus_SPS : bool;
 sstatus_SSD : bool;
 sstatus_SXS : word 2;
 sstatus_sstatus'rst : word 55
}.
#[global] Instance sstatus_inhabited : Inhabited sstatus :=
 {| sstatus_SFS := inhabitant _;
    sstatus_SIE := inhabitant _;
    sstatus_SMPRV := inhabitant _;
    sstatus_SPIE := inhabitant _;
    sstatus_SPS := inhabitant _;
    sstatus_SSD := inhabitant _;
    sstatus_SXS := inhabitant _;
    sstatus_sstatus'rst := inhabitant _ |}.
Definition sstatus_SFS_fupd (update : word 2 -> word 2) (x : sstatus) : sstatus :=
 {| sstatus_SFS := update (sstatus_SFS x);
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_SIE_fupd (update : bool -> bool) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := update (sstatus_SIE x);
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_SMPRV_fupd (update : bool -> bool) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := update (sstatus_SMPRV x);
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_SPIE_fupd (update : bool -> bool) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := update (sstatus_SPIE x);
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_SPS_fupd (update : bool -> bool) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := update (sstatus_SPS x);
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_SSD_fupd (update : bool -> bool) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := update (sstatus_SSD x);
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_SXS_fupd (update : word 2 -> word 2) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := update (sstatus_SXS x);
    sstatus_sstatus'rst := sstatus_sstatus'rst x |}.
Definition sstatus_sstatus'rst_fupd (update : word 55 -> word 55) (x : sstatus) : sstatus :=
 {| sstatus_SFS := sstatus_SFS x;
    sstatus_SIE := sstatus_SIE x;
    sstatus_SMPRV := sstatus_SMPRV x;
    sstatus_SPIE := sstatus_SPIE x;
    sstatus_SPS := sstatus_SPS x;
    sstatus_SSD := sstatus_SSD x;
    sstatus_SXS := sstatus_SXS x;
    sstatus_sstatus'rst := update (sstatus_sstatus'rst x) |}.
#[global] Instance sstatus_eq_dec : EqDecision sstatus.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record sip : Type := {
 sip_SSIP : bool;
 sip_STIP : bool;
 sip_sip'rst : word 62
}.
#[global] Instance sip_inhabited : Inhabited sip :=
 {| sip_SSIP := inhabitant _;
    sip_STIP := inhabitant _;
    sip_sip'rst := inhabitant _ |}.
Definition sip_SSIP_fupd (update : bool -> bool) (x : sip) : sip :=
 {| sip_SSIP := update (sip_SSIP x);
    sip_STIP := sip_STIP x;
    sip_sip'rst := sip_sip'rst x |}.
Definition sip_STIP_fupd (update : bool -> bool) (x : sip) : sip :=
 {| sip_SSIP := sip_SSIP x;
    sip_STIP := update (sip_STIP x);
    sip_sip'rst := sip_sip'rst x |}.
Definition sip_sip'rst_fupd (update : word 62 -> word 62) (x : sip) : sip :=
 {| sip_SSIP := sip_SSIP x;
    sip_STIP := sip_STIP x;
    sip_sip'rst := update (sip_sip'rst x) |}.
#[global] Instance sip_eq_dec : EqDecision sip.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record sie : Type := {
 sie_SSIE : bool;
 sie_STIE : bool;
 sie_sie'rst : word 62
}.
#[global] Instance sie_inhabited : Inhabited sie :=
 {| sie_SSIE := inhabitant _;
    sie_STIE := inhabitant _;
    sie_sie'rst := inhabitant _ |}.
Definition sie_SSIE_fupd (update : bool -> bool) (x : sie) : sie :=
 {| sie_SSIE := update (sie_SSIE x);
    sie_STIE := sie_STIE x;
    sie_sie'rst := sie_sie'rst x |}.
Definition sie_STIE_fupd (update : bool -> bool) (x : sie) : sie :=
 {| sie_SSIE := sie_SSIE x;
    sie_STIE := update (sie_STIE x);
    sie_sie'rst := sie_sie'rst x |}.
Definition sie_sie'rst_fupd (update : word 62 -> word 62) (x : sie) : sie :=
 {| sie_SSIE := sie_SSIE x;
    sie_STIE := sie_STIE x;
    sie_sie'rst := update (sie_sie'rst x) |}.
#[global] Instance sie_eq_dec : EqDecision sie.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record SupervisorCSR : Type := {
 SupervisorCSR_sasid : word 64;
 SupervisorCSR_sbadaddr : word 64;
 SupervisorCSR_scause : mcause;
 SupervisorCSR_sepc : word 64;
 SupervisorCSR_sptbr : word 64;
 SupervisorCSR_sscratch : word 64;
 SupervisorCSR_stvec : word 64
}.
#[global] Instance SupervisorCSR_inhabited : Inhabited SupervisorCSR :=
 {| SupervisorCSR_sasid := inhabitant _;
    SupervisorCSR_sbadaddr := inhabitant _;
    SupervisorCSR_scause := inhabitant _;
    SupervisorCSR_sepc := inhabitant _;
    SupervisorCSR_sptbr := inhabitant _;
    SupervisorCSR_sscratch := inhabitant _;
    SupervisorCSR_stvec := inhabitant _ |}.
Definition SupervisorCSR_sasid_fupd (update : word 64 -> word 64) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := update (SupervisorCSR_sasid x);
    SupervisorCSR_sbadaddr := SupervisorCSR_sbadaddr x;
    SupervisorCSR_scause := SupervisorCSR_scause x;
    SupervisorCSR_sepc := SupervisorCSR_sepc x;
    SupervisorCSR_sptbr := SupervisorCSR_sptbr x;
    SupervisorCSR_sscratch := SupervisorCSR_sscratch x;
    SupervisorCSR_stvec := SupervisorCSR_stvec x |}.
Definition SupervisorCSR_sbadaddr_fupd (update : word 64 -> word 64) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := SupervisorCSR_sasid x;
    SupervisorCSR_sbadaddr := update (SupervisorCSR_sbadaddr x);
    SupervisorCSR_scause := SupervisorCSR_scause x;
    SupervisorCSR_sepc := SupervisorCSR_sepc x;
    SupervisorCSR_sptbr := SupervisorCSR_sptbr x;
    SupervisorCSR_sscratch := SupervisorCSR_sscratch x;
    SupervisorCSR_stvec := SupervisorCSR_stvec x |}.
Definition SupervisorCSR_scause_fupd (update : mcause -> mcause) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := SupervisorCSR_sasid x;
    SupervisorCSR_sbadaddr := SupervisorCSR_sbadaddr x;
    SupervisorCSR_scause := update (SupervisorCSR_scause x);
    SupervisorCSR_sepc := SupervisorCSR_sepc x;
    SupervisorCSR_sptbr := SupervisorCSR_sptbr x;
    SupervisorCSR_sscratch := SupervisorCSR_sscratch x;
    SupervisorCSR_stvec := SupervisorCSR_stvec x |}.
Definition SupervisorCSR_sepc_fupd (update : word 64 -> word 64) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := SupervisorCSR_sasid x;
    SupervisorCSR_sbadaddr := SupervisorCSR_sbadaddr x;
    SupervisorCSR_scause := SupervisorCSR_scause x;
    SupervisorCSR_sepc := update (SupervisorCSR_sepc x);
    SupervisorCSR_sptbr := SupervisorCSR_sptbr x;
    SupervisorCSR_sscratch := SupervisorCSR_sscratch x;
    SupervisorCSR_stvec := SupervisorCSR_stvec x |}.
Definition SupervisorCSR_sptbr_fupd (update : word 64 -> word 64) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := SupervisorCSR_sasid x;
    SupervisorCSR_sbadaddr := SupervisorCSR_sbadaddr x;
    SupervisorCSR_scause := SupervisorCSR_scause x;
    SupervisorCSR_sepc := SupervisorCSR_sepc x;
    SupervisorCSR_sptbr := update (SupervisorCSR_sptbr x);
    SupervisorCSR_sscratch := SupervisorCSR_sscratch x;
    SupervisorCSR_stvec := SupervisorCSR_stvec x |}.
Definition SupervisorCSR_sscratch_fupd (update : word 64 -> word 64) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := SupervisorCSR_sasid x;
    SupervisorCSR_sbadaddr := SupervisorCSR_sbadaddr x;
    SupervisorCSR_scause := SupervisorCSR_scause x;
    SupervisorCSR_sepc := SupervisorCSR_sepc x;
    SupervisorCSR_sptbr := SupervisorCSR_sptbr x;
    SupervisorCSR_sscratch := update (SupervisorCSR_sscratch x);
    SupervisorCSR_stvec := SupervisorCSR_stvec x |}.
Definition SupervisorCSR_stvec_fupd (update : word 64 -> word 64) (x : SupervisorCSR) : SupervisorCSR :=
 {| SupervisorCSR_sasid := SupervisorCSR_sasid x;
    SupervisorCSR_sbadaddr := SupervisorCSR_sbadaddr x;
    SupervisorCSR_scause := SupervisorCSR_scause x;
    SupervisorCSR_sepc := SupervisorCSR_sepc x;
    SupervisorCSR_sptbr := SupervisorCSR_sptbr x;
    SupervisorCSR_sscratch := SupervisorCSR_sscratch x;
    SupervisorCSR_stvec := update (SupervisorCSR_stvec x) |}.
#[global] Instance SupervisorCSR_eq_dec : EqDecision SupervisorCSR.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record SynchronousTrap : Type := {
 SynchronousTrap_badaddr : option (word 64);
 SynchronousTrap_trap : ExceptionType
}.
#[global] Instance SynchronousTrap_inhabited : Inhabited SynchronousTrap :=
 {| SynchronousTrap_badaddr := inhabitant _;
    SynchronousTrap_trap := inhabitant _ |}.
Definition SynchronousTrap_badaddr_fupd (update : option (word 64) -> option (word 64)) (x : SynchronousTrap) : SynchronousTrap :=
 {| SynchronousTrap_badaddr := update (SynchronousTrap_badaddr x);
    SynchronousTrap_trap := SynchronousTrap_trap x |}.
Definition SynchronousTrap_trap_fupd (update : ExceptionType -> ExceptionType) (x : SynchronousTrap) : SynchronousTrap :=
 {| SynchronousTrap_badaddr := SynchronousTrap_badaddr x;
    SynchronousTrap_trap := update (SynchronousTrap_trap x) |}.
#[global] Instance SynchronousTrap_eq_dec : EqDecision SynchronousTrap.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive TransferControl : Type :=
 | BranchTo : word 64 -> TransferControl
 | Trap : SynchronousTrap -> TransferControl.
#[global] Instance TransferControl_inhabited : Inhabited TransferControl := BranchTo (inhabitant _).
#[global] Instance TransferControl_eq_dec : EqDecision TransferControl.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record StateDelta : Type := {
 StateDelta_addr : option (word 64);
 StateDelta_data1 : option (word 64);
 StateDelta_data2 : option (word 64);
 StateDelta_exc_taken : bool;
 StateDelta_fetch_exc : bool;
 StateDelta_pc : word 64;
 StateDelta_rinstr : rawInstType;
 StateDelta_st_width : option (word 32)
}.
#[global] Instance StateDelta_inhabited : Inhabited StateDelta :=
 {| StateDelta_addr := inhabitant _;
    StateDelta_data1 := inhabitant _;
    StateDelta_data2 := inhabitant _;
    StateDelta_exc_taken := inhabitant _;
    StateDelta_fetch_exc := inhabitant _;
    StateDelta_pc := inhabitant _;
    StateDelta_rinstr := inhabitant _;
    StateDelta_st_width := inhabitant _ |}.
Definition StateDelta_addr_fupd (update : option (word 64) -> option (word 64)) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := update (StateDelta_addr x);
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_data1_fupd (update : option (word 64) -> option (word 64)) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := update (StateDelta_data1 x);
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_data2_fupd (update : option (word 64) -> option (word 64)) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := update (StateDelta_data2 x);
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_exc_taken_fupd (update : bool -> bool) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := update (StateDelta_exc_taken x);
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_fetch_exc_fupd (update : bool -> bool) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := update (StateDelta_fetch_exc x);
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_pc_fupd (update : word 64 -> word 64) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := update (StateDelta_pc x);
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_rinstr_fupd (update : rawInstType -> rawInstType) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := update (StateDelta_rinstr x);
    StateDelta_st_width := StateDelta_st_width x |}.
Definition StateDelta_st_width_fupd (update : option (word 32) -> option (word 32)) (x : StateDelta) : StateDelta :=
 {| StateDelta_addr := StateDelta_addr x;
    StateDelta_data1 := StateDelta_data1 x;
    StateDelta_data2 := StateDelta_data2 x;
    StateDelta_exc_taken := StateDelta_exc_taken x;
    StateDelta_fetch_exc := StateDelta_fetch_exc x;
    StateDelta_pc := StateDelta_pc x;
    StateDelta_rinstr := StateDelta_rinstr x;
    StateDelta_st_width := update (StateDelta_st_width x) |}.
#[global] Instance StateDelta_eq_dec : EqDecision StateDelta.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Internal_ty : Type :=
 | FETCH_FAULT : word 64 -> Internal_ty
 | FETCH_MISALIGNED : word 64 -> Internal_ty.
#[global] Instance Internal_inhabited : Inhabited Internal_ty := FETCH_FAULT (inhabitant _).
#[global] Instance Internal_eq_dec : EqDecision Internal_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive System_ty : Type :=
 | EBREAK : System_ty
 | ECALL : System_ty.
#[global] Instance System_inhabited : Inhabited System_ty := EBREAK.
#[global] Instance System_eq_dec : EqDecision System_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Store_ty : Type :=
 | SB : (word 5 * (word 5 * word 12)%type)%type -> Store_ty
 | SD : (word 5 * (word 5 * word 12)%type)%type -> Store_ty
 | SH : (word 5 * (word 5 * word 12)%type)%type -> Store_ty
 | SW : (word 5 * (word 5 * word 12)%type)%type -> Store_ty.
#[global] Instance Store_inhabited : Inhabited Store_ty := SB (inhabitant _).
#[global] Instance Store_eq_dec : EqDecision Store_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Load_ty : Type :=
 | LB : (word 5 * (word 5 * word 12)%type)%type -> Load_ty
 | LBU : (word 5 * (word 5 * word 12)%type)%type -> Load_ty
 | LD : (word 5 * (word 5 * word 12)%type)%type -> Load_ty
 | LH : (word 5 * (word 5 * word 12)%type)%type -> Load_ty
 | LHU : (word 5 * (word 5 * word 12)%type)%type -> Load_ty
 | LW : (word 5 * (word 5 * word 12)%type)%type -> Load_ty
 | LWU : (word 5 * (word 5 * word 12)%type)%type -> Load_ty.
#[global] Instance Load_inhabited : Inhabited Load_ty := LB (inhabitant _).
#[global] Instance Load_eq_dec : EqDecision Load_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Branch_ty : Type :=
 | BEQ : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty
 | BGE : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty
 | BGEU : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty
 | BLT : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty
 | BLTU : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty
 | BNE : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty
 | JAL : (word 5 * word 20)%type -> Branch_ty
 | JALR : (word 5 * (word 5 * word 12)%type)%type -> Branch_ty.
#[global] Instance Branch_inhabited : Inhabited Branch_ty := BEQ (inhabitant _).
#[global] Instance Branch_eq_dec : EqDecision Branch_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive MulDiv_ty : Type :=
 | DIV : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | DIVU : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | MUL : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | MULH : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | MULHSU : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | MULHU : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | REM : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty
 | REMU : (word 5 * (word 5 * word 5)%type)%type -> MulDiv_ty.
#[global] Instance MulDiv_inhabited : Inhabited MulDiv_ty := DIV (inhabitant _).
#[global] Instance MulDiv_eq_dec : EqDecision MulDiv_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive Shift_ty : Type :=
 | SLL : (word 5 * (word 5 * word 5)%type)%type -> Shift_ty
 | SLLI : (word 5 * (word 5 * word 6)%type)%type -> Shift_ty
 | SRA : (word 5 * (word 5 * word 5)%type)%type -> Shift_ty
 | SRAI : (word 5 * (word 5 * word 6)%type)%type -> Shift_ty
 | SRL : (word 5 * (word 5 * word 5)%type)%type -> Shift_ty
 | SRLI : (word 5 * (word 5 * word 6)%type)%type -> Shift_ty.
#[global] Instance Shift_inhabited : Inhabited Shift_ty := SLL (inhabitant _).
#[global] Instance Shift_eq_dec : EqDecision Shift_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive ArithR_ty : Type :=
 | ADD : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty
 | AND : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty
 | OR : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty
 | SLT : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty
 | SLTU : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty
 | SUB : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty
 | XOR : (word 5 * (word 5 * word 5)%type)%type -> ArithR_ty.
#[global] Instance ArithR_inhabited : Inhabited ArithR_ty := ADD (inhabitant _).
#[global] Instance ArithR_eq_dec : EqDecision ArithR_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive ArithI_ty : Type :=
 | ADDI : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty
 | ADDIW : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty
 | ANDI : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty
 | AUIPC : (word 5 * word 20)%type -> ArithI_ty
 | LUI : (word 5 * word 20)%type -> ArithI_ty
 | ORI : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty
 | SLTI : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty
 | SLTIU : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty
 | XORI : (word 5 * (word 5 * word 12)%type)%type -> ArithI_ty.
#[global] Instance ArithI_inhabited : Inhabited ArithI_ty := ADDI (inhabitant _).
#[global] Instance ArithI_eq_dec : EqDecision ArithI_ty.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive instruction : Type :=
 | ArithI : ArithI_ty -> instruction
 | ArithR : ArithR_ty -> instruction
 | Branch : Branch_ty -> instruction
 | FENCE : (word 5 * (word 5 * (word 4 * word 4)%type)%type)%type -> instruction
 | Internal : Internal_ty -> instruction
 | Load : Load_ty -> instruction
 | MulDiv : MulDiv_ty -> instruction
 | Shift : Shift_ty -> instruction
 | Store : Store_ty -> instruction
 | System : System_ty -> instruction
 | UnknownInstruction : instruction.
#[global] Instance instruction_inhabited : Inhabited instruction := ArithI (inhabitant _).
#[global] Instance instruction_eq_dec : EqDecision instruction.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive FetchResult : Type :=
 | F_Error : instruction -> FetchResult
 | F_Result : rawInstType -> FetchResult.
#[global] Instance FetchResult_inhabited : Inhabited FetchResult := F_Error (inhabitant _).
#[global] Instance FetchResult_eq_dec : EqDecision FetchResult.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive rvc : Type :=
 | Comp : word 16 -> rvc
 | Full : word 32 -> rvc.
#[global] Instance rvc_inhabited : Inhabited rvc := Comp (inhabitant _).
#[global] Instance rvc_eq_dec : EqDecision rvc.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Inductive exception : Type :=
 | INTERNAL_ERROR : list (ascii) -> exception
 | NoException : exception
 | UNDEFINED : list (ascii) -> exception.
#[global] Instance exception_inhabited : Inhabited exception := INTERNAL_ERROR (inhabitant _).
#[global] Instance exception_eq_dec : EqDecision exception.
Proof. intros x y; unfold Decision; decide equality; apply decide; exact _. Defined.

Record riscv_state : Type := {
 riscv_state_MEM8 : (word 64 -> word 8);
 riscv_state_c_ExitCode : (word 8 -> word 64);
 riscv_state_c_HCSR : (word 8 -> HypervisorCSR);
 riscv_state_c_MCSR : (word 8 -> MachineCSR);
 riscv_state_c_NextFetch : (word 8 -> option (TransferControl));
 riscv_state_c_PC : (word 8 -> word 64);
 riscv_state_c_SCSR : (word 8 -> SupervisorCSR);
 riscv_state_c_Skip : (word 8 -> word 64);
 riscv_state_c_gpr : (word 8 -> (word 5 -> word 64));
 riscv_state_c_update : (word 8 -> StateDelta);
 riscv_state_done : bool;
 riscv_state_exception : exception;
 riscv_state_log : list ((N * list (ascii))%type);
 riscv_state_procID : word 8;
 riscv_state_totalCore : N
}.
#[global] Instance riscv_state_inhabited : Inhabited riscv_state :=
 {| riscv_state_MEM8 := inhabitant _;
    riscv_state_c_ExitCode := inhabitant _;
    riscv_state_c_HCSR := inhabitant _;
    riscv_state_c_MCSR := inhabitant _;
    riscv_state_c_NextFetch := inhabitant _;
    riscv_state_c_PC := inhabitant _;
    riscv_state_c_SCSR := inhabitant _;
    riscv_state_c_Skip := inhabitant _;
    riscv_state_c_gpr := inhabitant _;
    riscv_state_c_update := inhabitant _;
    riscv_state_done := inhabitant _;
    riscv_state_exception := inhabitant _;
    riscv_state_log := inhabitant _;
    riscv_state_procID := inhabitant _;
    riscv_state_totalCore := inhabitant _ |}.
Definition riscv_state_MEM8_fupd (update : (word 64 -> word 8) -> (word 64 -> word 8)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := update (riscv_state_MEM8 x);
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_ExitCode_fupd (update : (word 8 -> word 64) -> (word 8 -> word 64)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := update (riscv_state_c_ExitCode x);
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_HCSR_fupd (update : (word 8 -> HypervisorCSR) -> (word 8 -> HypervisorCSR)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := update (riscv_state_c_HCSR x);
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_MCSR_fupd (update : (word 8 -> MachineCSR) -> (word 8 -> MachineCSR)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := update (riscv_state_c_MCSR x);
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_NextFetch_fupd (update : (word 8 -> option (TransferControl)) -> (word 8 -> option (TransferControl))) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := update (riscv_state_c_NextFetch x);
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_PC_fupd (update : (word 8 -> word 64) -> (word 8 -> word 64)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := update (riscv_state_c_PC x);
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_SCSR_fupd (update : (word 8 -> SupervisorCSR) -> (word 8 -> SupervisorCSR)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := update (riscv_state_c_SCSR x);
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_Skip_fupd (update : (word 8 -> word 64) -> (word 8 -> word 64)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := update (riscv_state_c_Skip x);
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_gpr_fupd (update : (word 8 -> (word 5 -> word 64)) -> (word 8 -> (word 5 -> word 64))) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := update (riscv_state_c_gpr x);
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_c_update_fupd (update : (word 8 -> StateDelta) -> (word 8 -> StateDelta)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := update (riscv_state_c_update x);
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_done_fupd (update : bool -> bool) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := update (riscv_state_done x);
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_exception_fupd (update : exception -> exception) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := update (riscv_state_exception x);
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_log_fupd (update : list ((N * list (ascii))%type) -> list ((N * list (ascii))%type)) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := update (riscv_state_log x);
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_procID_fupd (update : word 8 -> word 8) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := update (riscv_state_procID x);
    riscv_state_totalCore := riscv_state_totalCore x |}.
Definition riscv_state_totalCore_fupd (update : N -> N) (x : riscv_state) : riscv_state :=
 {| riscv_state_MEM8 := riscv_state_MEM8 x;
    riscv_state_c_ExitCode := riscv_state_c_ExitCode x;
    riscv_state_c_HCSR := riscv_state_c_HCSR x;
    riscv_state_c_MCSR := riscv_state_c_MCSR x;
    riscv_state_c_NextFetch := riscv_state_c_NextFetch x;
    riscv_state_c_PC := riscv_state_c_PC x;
    riscv_state_c_SCSR := riscv_state_c_SCSR x;
    riscv_state_c_Skip := riscv_state_c_Skip x;
    riscv_state_c_gpr := riscv_state_c_gpr x;
    riscv_state_c_update := riscv_state_c_update x;
    riscv_state_done := riscv_state_done x;
    riscv_state_exception := riscv_state_exception x;
    riscv_state_log := riscv_state_log x;
    riscv_state_procID := riscv_state_procID x;
    riscv_state_totalCore := update (riscv_state_totalCore x) |}.
