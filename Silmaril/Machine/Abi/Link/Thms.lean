module

public import Silmaril.Machine.Abi.Link.Defs
public import Silmaril.Machine.Abi.Infer.Thms
public import Silmaril.Machine.Abi.Win64.Thms
/-! # Link compatibility: soundness

* `check_direct_agree`: a `direct` verdict makes the interpreted conventions
  `Agree`, for every `Interp`.
* `compatible_translate_eq`: so the importer's translated contract equals the
  exporter's, for every C contract.
* `link_sound`: whatever the verdict, an exporter verified against its own
  convention's translated contract, called through the edge's `Bridge`, meets
  the importer's translated contract. For `direct` the bridge is nothing; for
  `thunk` it is a correct thunk (`Convention.Thunk.sound`); `reject` has no
  bridge.
* `check_reject_iff`: `check` rejects exactly on a prototype mismatch;
  `check_proto`: otherwise the prototypes are equal.
* `sysv_compatible`: LP64 System V endpoints of one prototype are compatible
  unless a no-red-zone importer meets a red-zone exporter.
* `toTag_sysv`: the C1 tag of `sysv o.options` is the link tag's.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Link

open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options CallSite)
open Silmaril.Machine.SystemV.Abi (VectorLevel Ffi.State)
open Silmaril.Logic.Institution.Bridges

theorem Proto.ext {p q : Proto} (h : p.signature = q.signature) : p = q := by
  cases p; cases q; cases h; rfl

theorem agree_refl (A : Convention vocab Ffi.State CallSite) (p : Proto) : A.Agree A p :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem checkTags_ne_reject (p : Proto) (a b : AbiTag) : checkTags p a b ≠ .reject := by
  unfold checkTags
  split
  · simp
  · split
    · split <;> simp
    · simp

theorem checkTags_direct_agree (I : Interp) (p : Proto) {a b : AbiTag}
    (direct : checkTags p a b = .direct) {A B : Convention vocab Ffi.State CallSite}
    (hA : I.conv a = some A) (hB : I.conv b = some B) : A.Agree B p := by
  unfold checkTags at direct
  by_cases same : a = b
  · subst same
    rw [hA] at hB
    cases hB
    exact agree_refl A p
  · simp only [same, ↓reduceIte] at direct
    cases a with
    | sysv64 i =>
      cases b with
      | sysv64 e =>
        simp only at direct
        split at direct
        · rename_i cond
          simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at cond
          obtain ⟨⟨hi, he⟩, -⟩ := cond
          rw [I.sysv i hi] at hA
          rw [I.sysv e he] at hB
          cases hA; cases hB
          exact SystemV.sysv_agree _ _ p
        · cases direct
      | _ => cases direct
    | _ => cases b <;> cases direct

theorem check_reject_iff (imp exp : Endpoint) :
    check imp exp = .reject ↔ imp.proto.signature ≠ exp.proto.signature := by
  unfold check
  split
  · rename_i h
    simp only [h, ne_eq, not_true_eq_false, iff_false]
    exact checkTags_ne_reject _ _ _
  · rename_i h
    simp [h]

theorem check_proto {imp exp : Endpoint} (ok : check imp exp ≠ .reject) :
    imp.proto = exp.proto :=
  Proto.ext (by simpa [check_reject_iff] using ok)

theorem check_eq_checkTags {imp exp : Endpoint} (ok : check imp exp ≠ .reject) :
    check imp exp = checkTags imp.proto imp.abi exp.abi := by
  simp [check, check_proto ok]

/-- Soundness of direct compatibility: the conventions agree. -/
theorem check_direct_agree (I : Interp) {imp exp : Endpoint} (compatible : Compatible imp exp)
    {A B : Convention vocab Ffi.State CallSite}
    (hA : I.conv imp.abi = some A) (hB : I.conv exp.abi = some B) : A.Agree B imp.proto := by
  have ok : check imp exp ≠ .reject := by
    unfold Compatible at compatible; rw [compatible]; decide
  exact checkTags_direct_agree I imp.proto
    ((check_eq_checkTags ok).symm.trans compatible) hA hB

/-- Linking a compatible pair preserves contracts: the importer's translated
contract is the exporter's. -/
theorem compatible_translate_eq (I : Interp) {imp exp : Endpoint}
    (compatible : Compatible imp exp) {A B : Convention vocab Ffi.State CallSite}
    (hA : I.conv imp.abi = some A) (hB : I.conv exp.abi = some B)
    (c : Contracts.Contract (vocab.Args imp.proto) (Option (vocab.Ret imp.proto))) :
    A.translate imp.proto c = B.translate imp.proto c :=
  (check_direct_agree I compatible hA hB).translate_eq c

/-- Soundness of a link edge: the exporter's verified machine contract, adapted by
the bridge the verdict requires, gives the importer's machine contract. -/
theorem link_sound (I : Interp) {imp exp : Endpoint}
    {A B : Convention vocab Ffi.State CallSite}
    (hA : I.conv imp.abi = some A) (hB : I.conv exp.abi = some B)
    (bridge : Bridge A B imp.proto (check imp exp))
    {model : Contracts.Model Ffi.State Ffi.State}
    {c : Contracts.Contract (vocab.Args imp.proto) (Option (vocab.Ret imp.proto))}
    (callee : Contracts.Sat model (B.translate imp.proto c)) :
    Contracts.Sat (Bridge.wrap _ bridge model) (A.translate imp.proto c) := by
  generalize hv : check imp exp = v at bridge
  cases v with
  | direct =>
    exact ((check_direct_agree I hv hA hB).sat_iff model c).2 callee
  | thunk => exact Convention.Thunk.sound bridge.2 callee
  | reject => exact bridge.elim

/-- A compatible edge also admits the empty thunk, if a linker prefers to treat
every edge uniformly. -/
theorem compatible_direct_thunk (I : Interp) {imp exp : Endpoint}
    (compatible : Compatible imp exp) {A B : Convention vocab Ffi.State CallSite}
    (hA : I.conv imp.abi = some A) (hB : I.conv exp.abi = some B) :
    (Convention.Thunk.direct A B imp.proto).Correct :=
  (check_direct_agree I compatible hA hB).direct_correct

/-- LP64 System V endpoints of one prototype are compatible unless a
no-red-zone importer meets a red-zone exporter. -/
theorem sysv_compatible {p q : Proto} (same : p.signature = q.signature) {i e : SysvOptions}
    (hi : i.x32 = false) (he : e.x32 = false) (redZone : e.redZone = true → i.redZone = true) :
    Compatible ⟨p, .sysv64 i⟩ ⟨q, .sysv64 e⟩ := by
  unfold Compatible check checkTags
  simp only [same, ite_true]
  split
  · rfl
  · cases h : e.redZone <;> simp_all

theorem toTag_sysv (o : SysvOptions) (h : o.x32 = false) :
    (sysv o.options).tag = (AbiTag.sysv64 o).toTag := by
  simp [AbiTag.toTag, h, sysv, SystemV.convention]

/-! ## Integration with the Win64 comorphism -/

/-- The inference data for Microsoft x64 is the Win64 package's data. -/
theorem infer_ms64_eq : Infer.ms64 = Win64.ms64 := rfl

/-- The multi-ABI interpretation: LP64 System V tags as in `Interp.standard`,
and `.ms64` as the Microsoft x64 comorphism `Win64.win64`. x32 and inferred
tags remain uninterpreted. -/
def Interp.multi : Interp where
  conv
    | .sysv64 o => if o.x32 then none else some (SystemV.sysv o.options)
    | .ms64 => some Win64.win64
    | .inferred _ => none
  sysv o h := by simp [h]

theorem Interp.multi_ms64 : Interp.multi.conv .ms64 = some Win64.win64 := rfl

/-- An `ms_abi` importer and an LP64 System V exporter of the same prototype
never link directly: the check asks for a thunk. -/
theorem check_ms64_sysv {p : Proto} {o : SysvOptions} :
    check ⟨p, .ms64⟩ ⟨p, .sysv64 o⟩ = .thunk := by
  simp [check, checkTags]

/-- Likewise for a System V importer and an `ms_abi` exporter. -/
theorem check_sysv_ms64 {p : Proto} {o : SysvOptions} :
    check ⟨p, .sysv64 o⟩ ⟨p, .ms64⟩ = .thunk := by
  simp [check, checkTags]

end Silmaril.Machine.Abi.Link
