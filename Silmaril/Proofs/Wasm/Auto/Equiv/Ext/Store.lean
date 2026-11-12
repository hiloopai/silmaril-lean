module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Ext.Canon

/-!
# Concrete states of the extended executor

How the frame, store and stack of a symbolic state (`XCtx.frameOf`, `XCtx.storeOf`,
`XCtx.stackOf`) change with the symbolic state, and what `local.get`, `global.get` and the
memory lookup see in them: `setGlobals` with distinct addresses, `setMem`, and the locals.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## `setGlobals` -/

theorem mems_setGlobals : ∀ (s : Store H) (ga : List Nat) (vs : List Val),
    (setGlobals s ga vs).mems = s.mems
  | _, _ :: _, _ :: _ => by rw [setGlobals]; exact mems_setGlobals _ _ _
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl

theorem globals_length_setGlobals : ∀ (s : Store H) (ga : List Nat) (vs : List Val),
    (setGlobals s ga vs).globals.length = s.globals.length
  | s, _ :: _, _ :: _ => by
    rw [setGlobals, globals_length_setGlobals]; simp [Store.setGlobal]
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl

theorem getElem?_setGlobals_not_mem : ∀ (s : Store H) (ga : List Nat) (vs : List Val) (b : Nat),
    b ∉ ga → (setGlobals s ga vs).globals[b]? = s.globals[b]?
  | s, a :: as, v :: vs, b, hb => by
    rw [setGlobals, getElem?_setGlobals_not_mem _ _ _ _ (fun h => hb (List.mem_cons_of_mem _ h))]
    have hab : a ≠ b := fun h => hb (h ▸ List.mem_cons_self)
    simp [Store.setGlobal, hab]
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, _ => rfl

theorem getElem?_setGlobals : ∀ (s : Store H) (ga : List Nat) (vs : List Val) (k : Nat)
    (hk : k < ga.length), ga.Nodup → vs.length = ga.length →
    (setGlobals s ga vs).globals[ga[k]]? = (s.globals[ga[k]]?).map fun g => { g with value := vs.getD k (.i32 0) }
  | s, a :: as, v :: vs, 0, _, hnd, _ => by
    rw [setGlobals]
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    simp only [List.getElem_cons_zero]
    rw [getElem?_setGlobals_not_mem _ _ _ _ ha]
    simp [Store.setGlobal]
  | s, a :: as, v :: vs, k + 1, hk, hnd, hl => by
    rw [setGlobals]
    have hnd' := (List.nodup_cons.mp hnd)
    have hk' : k < as.length := by simpa using hk
    have hne : a ≠ as[k] := fun h => hnd'.1 (h ▸ List.getElem_mem hk')
    simp only [List.getElem_cons_succ]
    rw [getElem?_setGlobals _ as vs k hk' hnd'.2 (by simpa using hl)]
    simp [Store.setGlobal, hne]
  | _, [], _, _, hk, _, _ => absurd hk (by simp)
  | _, _ :: _, [], _, _, _, hl => by simp at hl

theorem setGlobal_comm (s : Store H) {a b : Nat} (v w : Val) (h : a ≠ b) :
    (s.setGlobal a v).setGlobal b w = (s.setGlobal b w).setGlobal a v := by
  simp only [Store.setGlobal, Store.mk.injEq]
  rw [List.modify_modify_ne _ _ _ h.symm]
  simp

theorem setGlobal_setGlobal (s : Store H) (a : Nat) (v w : Val) :
    (s.setGlobal a v).setGlobal a w = s.setGlobal a w := by
  simp only [Store.setGlobal, List.modify_modify_eq]
  rfl

theorem setGlobals_setGlobal_not_mem : ∀ (s : Store H) (ga : List Nat) (vs : List Val) (a : Nat)
    (v : Val), a ∉ ga → (setGlobals s ga vs).setGlobal a v = setGlobals (s.setGlobal a v) ga vs
  | s, b :: bs, w :: ws, a, v, ha => by
    rw [setGlobals, setGlobals, setGlobals_setGlobal_not_mem _ _ _ _ _
      (fun h => ha (List.mem_cons_of_mem _ h))]
    have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
    rw [setGlobal_comm _ _ _ hab]
  | _, [], _, _, _, _ => rfl
  | _, _ :: _, [], _, _, _ => rfl

theorem setGlobals_set : ∀ (s : Store H) (ga : List Nat) (vs : List Val) (k : Nat)
    (hk : k < ga.length) (v : Val), ga.Nodup → vs.length = ga.length →
    (setGlobals s ga vs).setGlobal ga[k] v = setGlobals s ga (vs.set k v)
  | s, a :: as, w :: ws, 0, _, v, hnd, _ => by
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    simp only [List.getElem_cons_zero, List.set_cons_zero, setGlobals]
    rw [setGlobals_setGlobal_not_mem _ _ _ _ _ ha, setGlobal_setGlobal]
  | s, a :: as, w :: ws, k + 1, hk, v, hnd, hl => by
    simp only [List.getElem_cons_succ, List.set_cons_succ, setGlobals]
    exact setGlobals_set _ as ws k (by simpa using hk) v (List.nodup_cons.mp hnd).2 (by simpa using hl)
  | _, [], _, _, hk, _, _, _ => absurd hk (by simp)
  | s, _ :: _, [], _, _, v, _, hl => by simp at hl

/-! ## Context invariants -/

theorem XCtx.Ok.good {lt st gt : List IntType} {mem : Bool} {c : XCtx H}
    (h : c.Ok lt st gt mem) : c.Good mem :=
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ## Frames -/

theorem frameOf_congr (c : XCtx H) {S S' : XState} (h : S.locals = S'.locals) :
    c.frameOf S = c.frameOf S' := by
  simp [XCtx.frameOf, h]

theorem frameOf_module (c : XCtx H) (S : XState) : (c.frameOf S).module = c.f.module := rfl

theorem local?_frameOf (c : XCtx H) (S : XState) (x : LocalIdx) :
    (c.frameOf S).local? x = (S.locals[x.toNat]?).map fun p => some (denX c.ρ c.mi.bytes p) := by
  simp [XCtx.frameOf, Frame.local?]

theorem frameOf_setLocal (c : XCtx H) (S : XState) (x : LocalIdx) (p : IntType × XT)
    (st : List (IntType × XT)) :
    c.frameOf { S with locals := S.locals.set x.toNat p, stack := st } =
      (c.frameOf S).setLocal x (denX c.ρ c.mi.bytes p) := by
  simp [XCtx.frameOf, Frame.setLocal, List.map_set]

theorem locals_length_frameOf (c : XCtx H) (S : XState) : (c.frameOf S).locals.length = S.locals.length := by
  simp [XCtx.frameOf]

/-! ## Stores -/

theorem storeOf_congr (c : XCtx H) (mem : Bool) {S S' : XState} (hg : S.globs = S'.globs)
    (hm : S.mem = S'.mem) : c.storeOf mem S = c.storeOf mem S' := by
  simp [XCtx.storeOf, hg, hm]

theorem global?_storeOf {mem : Bool} {c : XCtx H} (hc : c.Good mem) (S : XState)
    (hl : S.globs.length = c.ga.length) (x : GlobalIdx) (hx : x.toNat < c.ga.length) :
    ∃ g, (c.storeOf mem S).global? (c.frameOf S) x = some (c.ga[x.toNat], g) ∧
      g.value = denX c.ρ c.mi.bytes S.globs[x.toNat] := by
  obtain ⟨hnd, hga, -⟩ := hc
  obtain ⟨hmod, hlt⟩ := hga x.toNat hx
  have hglob : (c.storeOf mem S).globals = (setGlobals c.s c.ga (S.globs.map (denX c.ρ c.mi.bytes))).globals := by
    unfold XCtx.storeOf; split <;> rfl
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, c.s.globals[c.ga[x.toNat]]? = some g₀ :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have := getElem?_setGlobals c.s c.ga (S.globs.map (denX c.ρ c.mi.bytes)) x.toNat hx hnd (by simp [hl])
  rw [hg₀] at this
  refine ⟨{ g₀ with value := (S.globs.map (denX c.ρ c.mi.bytes)).getD x.toNat (.i32 0) }, ?_, ?_⟩
  · simp only [Store.global?, frameOf_module, hmod, Option.bind_eq_bind, Option.bind_some, hglob, this]
    rfl
  · have hx' : x.toNat < S.globs.length := by omega
    simp [List.getD_eq_getElem?_getD, hx']

theorem setGlobal_storeOf {mem : Bool} {c : XCtx H} (hc : c.Good mem) (S : XState)
    (hl : S.globs.length = c.ga.length) (x : GlobalIdx) (hx : x.toNat < c.ga.length)
    (p : IntType × XT) (st : List (IntType × XT)) :
    (c.storeOf mem S).setGlobal c.ga[x.toNat] (denX c.ρ c.mi.bytes p) =
      c.storeOf mem { S with globs := S.globs.set x.toNat p, stack := st } := by
  obtain ⟨hnd, -, -⟩ := hc
  have key := setGlobals_set c.s c.ga (S.globs.map (denX c.ρ c.mi.bytes)) x.toNat hx
    (denX c.ρ c.mi.bytes p) hnd (by simp [hl])
  unfold XCtx.storeOf
  cases mem
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_set]
    exact key
  · simp only [↓reduceIte, List.map_set]
    rw [← key]
    rfl

theorem mem?_storeOf {c : XCtx H} (hc : c.Good true) (S : XState) {x : MemIdx} (hx : x.toNat = 0) :
    (c.storeOf true S).mem? (c.frameOf S) x = some (c.ma, { c.mi with bytes := evM c.ρ c.mi.bytes S.mem }) := by
  obtain ⟨-, -, hm⟩ := hc
  have h0 := hm rfl
  have hx' : x.toNat = (⟨0⟩ : MemIdx).toNat := hx
  simp only [Store.mem?, frameOf_module, hx'] at h0 ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h0
  obtain ⟨a, ha, b, hb, hab⟩ := h0
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
  obtain ⟨rfl, rfl⟩ := hab
  have hlt : c.ma < c.s.mems.length := (List.getElem?_eq_some_iff.mp hb).1
  simp [XCtx.storeOf, ha, Store.setMem, mems_setGlobals, hlt]

theorem setMem_storeOf (c : XCtx H) (S : XState) (m' : XT) (B : ByteArray)
    (hB : evM c.ρ c.mi.bytes m' = B) (st : List (IntType × XT)) (G : List (Guard × XState)) :
    (c.storeOf true S).setMem c.ma { c.mi with bytes := B } =
      c.storeOf true { S with mem := m', stack := st, guards := G } := by
  simp [XCtx.storeOf, Store.setMem, hB, List.set_set]

theorem size_storeM (B : ByteArray) (t : IntType) (p : Option PackSize) (i : BitVec 32)
    (arg : MemArg) (v : BitVec t.width) : (storeM B t p i arg v).size = B.size := by
  unfold storeM
  split
  · cases h : Memory.store B (effAddr i.toNat arg) (count := t.width / 8) (v.setWidth _) with
    | none => rfl
    | some B' => simpa [h] using Silmaril.Wasm.Logic.Core.size_store h
  · rename_i sz
    cases h : Memory.store B (effAddr i.toNat arg) (count := sz.width / 8) (v.setWidth _) with
    | none => rfl
    | some B' => simpa [h] using Silmaril.Wasm.Logic.Core.size_store h

/-- Stores keep the size of memory. -/
theorem size_evM (ρ : Env) (B0 : ByteArray) : ∀ e : XT, (evM ρ B0 e).size = B0.size
  | .mstore m t p a arg v => by
    rw [evM]
    exact (size_storeM _ t p _ arg _).trans (size_evM ρ B0 m)
  | .minit => rfl
  | .var _ | .const _ | .un .. | .bin .. | .rel .. | .wrap _ | .ext .. | .sel .. | .load .. => rfl

end Silmaril.Proofs.Wasm.Auto.Equiv