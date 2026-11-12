module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Sem
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Fwd

/-!
# Round 6: SpecTec's `Ref_ok` on Core types is Core's `RefOk`

On a Core-valid store (`StoreOk`) and a Core-valid closed reference type (`TyOk {}`), `RefOkS`
(SpecTec's `Ref_ok`, transcribed onto Core types, `Defs.lean`) is Core's `RefOk`:

* `refOkS_of_refOk`: Core → SpecTec, unconditionally (`tyOkS_empty`, `subS_empty`);
* `principal_of_refOkS`: every `RefOkS` derivation starts at a Core-valid type `p` that Core
  assigns to the reference without `sub`, and reaches its type by one `SubS {}` step from `p`
  (chains of `Ref_ok/sub` compose through `Heaptype_sub/trans`, whose middle is `TyOkS {}`);
* `refOk_of_refOkS`: SpecTec → Core, on a valid store and a Core-valid target type
  (`sub_of_subS_ref`: the `SubS {}` step lands in Core's `Sub {}` between coherent types).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **Core's `RefOk` is SpecTec's `Ref_ok`** (on Core types, `RefOkS`). -/
theorem refOkS_of_refOk {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    RefOkS s r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h => exact .func h
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih (tyOkS_empty hok) (subS_empty hs)

/-- `SubS` composes at the reference sort through a `TyOkS` middle heap type. -/
theorem SubS.ref_trans {Δ : TypeCtx} {n₁ n₂ n₃ : Bool} {h₁ h₂ h₃ : CHeapType}
    (a : SubS Δ (.ref n₁ h₁) (.ref n₂ h₂)) (b : SubS Δ (.ref n₂ h₂) (.ref n₃ h₃))
    (hm : TyOkS Δ h₂) : SubS Δ (.ref n₁ h₁) (.ref n₃ h₃) := by
  cases b with
  | refNull hb =>
    cases a with
    | refNonNull ha => exact .refNull (.heapTrans hm ha hb)
    | refNull ha => exact .refNull (.heapTrans hm ha hb)
  | refNonNull hb =>
    cases a with
    | refNonNull ha => exact .refNonNull (.heapTrans hm ha hb)

theorem tyOkS_refHeap {Δ : TypeCtx} {rt : CRefType} (h : TyOkS Δ rt) : TyOkS Δ (refHeap rt) := by
  cases h with
  | ref hh => exact hh

theorem cohH_refHeap {rt : CRefType} (h : TyOk {} rt) : CohH (refHeap rt) := by
  cases h with
  | ref hh => exact cohH_of_tyOk hh

/-- `SubS {}` from a `RefOkS` type that is either the principal type or `SubS`-above it. -/
theorem subS_compose {p rt' rt : CRefType}
    (h : p = rt' ∨ (TyOkS {} rt' ∧ SubS {} p rt')) (hs : SubS {} rt' rt) : SubS {} p rt := by
  rcases h with rfl | ⟨hok, hp⟩
  · exact hs
  · obtain ⟨n₁, h₁⟩ := p
    obtain ⟨n₂, h₂⟩ := rt'
    obtain ⟨n₃, h₃⟩ := rt
    exact hp.ref_trans hs (tyOkS_refHeap hok)

/-- From `SubS {}` above a Core-valid type to a Core-valid type, Core's `Sub {}`. -/
theorem sub_of_subS_valid {p rt : CRefType} (hp : TyOk {} p) (hrt : TyOk {} rt)
    (hs : SubS {} p rt) : Sub {} p rt := by
  obtain ⟨n₁, h₁⟩ := p
  obtain ⟨n₂, h₂⟩ := rt
  exact sub_of_subS_ref hs (cohH_refHeap hp) (cohH_refHeap hrt)

/-- `RefOk` at a Core-valid type from a Core-valid type below it, in `SubS {}` or equal. -/
theorem refOk_lift {s : Store H} {r : Ref} {p rt : CRefType} (hr : RefOk s r p) (hp : TyOk {} p)
    (hrt : TyOk {} rt) (h : p = rt ∨ (TyOkS {} rt ∧ SubS {} p rt)) : RefOk s r rt := by
  rcases h with rfl | ⟨-, hs⟩
  · exact hr
  · exact .sub hr hrt (sub_of_subS_valid hp hrt hs)

/-- The function types of a valid store are Core-valid. -/
theorem tyOk_func_type {s : Store H} (hS : StoreOk s) {a : Nat} {fi : FuncInst H}
    (h : s.funcs[a]? = some fi) : TyOk {} fi.type := by
  cases hS.funcs fi (List.mem_of_getElem? h) with
  | wasm hdt => exact hdt
  | host hdt => exact hdt

/-- A Core-valid defined type as a non-null reference type. -/
theorem tyOk_defRef {d : DefType} (h : TyOk {} d) : TyOk {} (Ty.ref false (Ty.defHeap d)) :=
  .ref (.use (.dt h))

/-- **Principal types**: a `RefOkS` derivation on a valid store starts at a Core-valid type
Core assigns to the reference, and its type is that type or `SubS {}`-above it (through a
`TyOkS {}` type). -/
theorem principal_of_refOkS {s : Store H} (hS : StoreOk s) {r : Ref} {rt : CRefType}
    (h : RefOkS s r rt) :
    ∃ p, RefOk s r p ∧ TyOk {} p ∧ (p = rt ∨ (TyOkS {} rt ∧ SubS {} p rt)) := by
  induction h with
  | null => exact ⟨_, .null, .ref .bot, .inl rfl⟩
  | i31 b => exact ⟨_, .i31 b, .ref (.abs _), .inl rfl⟩
  | struct h =>
    exact ⟨_, .struct h, tyOk_defRef (hS.structsClosed _ (List.mem_of_getElem? h)), .inl rfl⟩
  | array h =>
    exact ⟨_, .array h, tyOk_defRef (hS.arraysClosed _ (List.mem_of_getElem? h)), .inl rfl⟩
  | func h => exact ⟨_, .func h, tyOk_defRef (tyOk_func_type hS h), .inl rfl⟩
  | exn h => exact ⟨_, .exn h, .ref (.abs _), .inl rfl⟩
  | host a => exact ⟨_, .host a, .ref (.abs _), .inl rfl⟩
  | extern _ hn ih =>
    obtain ⟨p, hr, hp, hc⟩ := ih
    exact ⟨_, .extern (refOk_lift hr hp (.ref (.abs _)) hc) hn, .ref (.abs _), .inl rfl⟩
  | sub _ hok hs ih =>
    obtain ⟨p, hr, hp, hc⟩ := ih
    exact ⟨p, hr, hp, .inr ⟨hok, subS_compose hc hs⟩⟩

/-- **SpecTec's `Ref_ok` (on Core types) is Core's `RefOk`**, on a valid store and a
Core-valid closed reference type. -/
theorem refOk_of_refOkS {s : Store H} (hS : StoreOk s) {r : Ref} {rt : CRefType}
    (hrt : TyOk {} rt) (h : RefOkS s r rt) : RefOk s r rt := by
  obtain ⟨p, hr, hp, hc⟩ := principal_of_refOkS hS h
  exact refOk_lift hr hp hrt hc

/-- **`RefOkS` and `RefOk` agree** on a valid store and a Core-valid closed reference type. -/
theorem refOkS_iff {s : Store H} (hS : StoreOk s) {r : Ref} {rt : CRefType}
    (hrt : TyOk {} rt) : RefOkS s r rt ↔ RefOk s r rt :=
  ⟨refOk_of_refOkS hS hrt, refOkS_of_refOk⟩

/-! ## The elimination-side reading `RefOkE` -/

/-- `SubE` composes at the reference sort through a coherent middle heap type. -/
theorem SubE.ref_trans {n₁ n₂ n₃ : Bool} {h₁ h₂ h₃ : CHeapType}
    (a : SubE (.ref n₁ h₁) (.ref n₂ h₂)) (b : SubE (.ref n₂ h₂) (.ref n₃ h₃))
    (hm : CohH h₂) : SubE (.ref n₁ h₁) (.ref n₃ h₃) := by
  cases b with
  | refNull hb =>
    cases a with
    | refNonNull ha => exact .refNull (.heapTrans hm ha hb)
    | refNull ha => exact .refNull (.heapTrans hm ha hb)
  | refNonNull hb =>
    cases a with
    | refNonNull ha => exact .refNonNull (.heapTrans hm ha hb)

/-- `SubE` from a `RefOkE` type that is either the principal type or `SubE`-above it. -/
theorem subE_compose {p rt' rt : CRefType}
    (h : p = rt' ∨ (CohH (refHeap rt') ∧ SubE p rt')) (hs : SubE rt' rt) : SubE p rt := by
  rcases h with rfl | ⟨hok, hp⟩
  · exact hs
  · obtain ⟨n₁, h₁⟩ := p
    obtain ⟨n₂, h₂⟩ := rt'
    obtain ⟨n₃, h₃⟩ := rt
    exact hp.ref_trans hs hok

/-- `RefOk` at a Core-valid type from a Core-valid type below it, in `SubE` or equal. -/
theorem refOk_liftE {s : Store H} {r : Ref} {p rt : CRefType} (hr : RefOk s r p)
    (hp : TyOk {} p) (hrt : TyOk {} rt) (h : p = rt ∨ (CohH (refHeap rt) ∧ SubE p rt)) :
    RefOk s r rt := by
  rcases h with rfl | ⟨-, hs⟩
  · exact hr
  · obtain ⟨n₁, h₁⟩ := p
    obtain ⟨n₂, h₂⟩ := rt
    exact .sub hr hrt (sub_of_subE_ref hs (cohH_refHeap hp) (cohH_refHeap hrt))

/-- **Principal types for `RefOkE`**, on a valid store. -/
theorem principal_of_refOkE {s : Store H} (hS : StoreOk s) {r : Ref} {rt : CRefType}
    (h : RefOkE s r rt) :
    ∃ p, RefOk s r p ∧ TyOk {} p ∧ (p = rt ∨ (CohH (refHeap rt) ∧ SubE p rt)) := by
  induction h with
  | null => exact ⟨_, .null, .ref .bot, .inl rfl⟩
  | i31 b => exact ⟨_, .i31 b, .ref (.abs _), .inl rfl⟩
  | struct h =>
    exact ⟨_, .struct h, tyOk_defRef (hS.structsClosed _ (List.mem_of_getElem? h)), .inl rfl⟩
  | array h =>
    exact ⟨_, .array h, tyOk_defRef (hS.arraysClosed _ (List.mem_of_getElem? h)), .inl rfl⟩
  | func h => exact ⟨_, .func h, tyOk_defRef (tyOk_func_type hS h), .inl rfl⟩
  | exn h => exact ⟨_, .exn h, .ref (.abs _), .inl rfl⟩
  | host a => exact ⟨_, .host a, .ref (.abs _), .inl rfl⟩
  | extern _ hn ih =>
    obtain ⟨p, hr, hp, hc⟩ := ih
    exact ⟨_, .extern (refOk_liftE hr hp (.ref (.abs _)) hc) hn, .ref (.abs _), .inl rfl⟩
  | sub _ hok hs ih =>
    obtain ⟨p, hr, hp, hc⟩ := ih
    exact ⟨p, hr, hp, .inr ⟨hok, subE_compose hc hs⟩⟩

/-- **`RefOkE` is Core's `RefOk`** at a Core-valid closed type, on a valid store. -/
theorem refOk_of_refOkE {s : Store H} (hS : StoreOk s) {r : Ref} {rt : CRefType}
    (hrt : TyOk {} rt) (h : RefOkE s r rt) : RefOk s r rt := by
  obtain ⟨p, hr, hp, hc⟩ := principal_of_refOkE hS h
  exact refOk_liftE hr hp hrt hc

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV
