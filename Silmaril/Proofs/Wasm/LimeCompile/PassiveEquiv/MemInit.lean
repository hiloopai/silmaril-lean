module

public import Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.Basic
public import Silmaril.Wasm.LimeCompile.PassiveData.Thms

/-!
# The passive-data store relation: `memory.init` against a call frame

`memoryInit_rel` is the local step of the module-level simulation, stated with the store
relation `SRel`. A source frame of the source module runs `memory.init 0 y`, and the related
target frame (`FRel`) runs `call (helperBase m + y)`. In bounds, both return, and the final
stores are again `SRel`-related. Out of bounds, both trap on unchanged stores. The proof
discharges the premises of `memoryInit_emulation` from `SRel` and `Ctx.Ok`: the data instance of
`y` holds `effBytes`, the target holds the helper of `y` at address `N + y` (`helperAt_of_srel`),
the memories are equal, and `memoryInitLoop` changes only the memories (`memoryInitLoop_eq`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.PassiveData Silmaril.Wasm.LimeCompile.PassiveEquiv
open Silmaril.Proofs.Wasm.LimeCompile.PassiveData (I32 MemOk HelperAt)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `memoryInitLoop` changes only the memories. -/
theorem memoryInitLoop_eq {x : MemIdx} {y : DataIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32},
      memoryInitLoop s f x y a i j n = some s' → s' = { s with mems := s'.mems } := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f i j hl
  rw [memoryInitLoop] at hl
  split at hl
  · split at hl
    · split at hl
      · cases hl
        rfl
      · rename_i hn
        split at hl
        · split at hl
          · rename_i ma mi _ _ _ _ _ _ _ b _
            have := ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl hl
            rw [this]
            rfl
          · cases hl
        · cases hl
    · cases hl
  · cases hl

/-- `SRel` is kept when both sides set the same memories. -/
theorem SRel.withMems {K : Ctx} {s t : Store H} (h : SRel K s t) (ms : List MemInst) :
    SRel K { s with mems := ms } { t with mems := ms } := by
  refine ⟨?_, h.nfuncs, h.funcs, h.ndatas, h.seg, h.datas, h.exportsNum⟩
  have ho := h.other
  cases s
  cases t
  simp only [Store.mk.injEq] at ho ⊢
  tauto

theorem idx_toNat_of_lt {k : Nat} (hk : k < 2 ^ 32) : (idx k : FuncIdx).toNat = k := by
  show (Fin.ofNat (2 ^ 32) k).val = k
  simp only [Fin.ofNat]
  exact Nat.mod_eq_of_lt hk

/-- The target instance resolves the helper index of segment `y` to address `N + y`. -/
theorem mi'_helper {K : Ctx} (hK : K.Ok) {y : Nat} (hy : y < K.m.data.length) :
    K.mi'.funcs[(idx (helperBase K.m + y) : FuncIdx).toNat]? = some (K.N + y) := by
  rw [idx_toNat_of_lt (by have := hK.bound; omega)]
  simp only [Ctx.mi', Ctx.helperAddrs]
  rw [List.getElem?_append_right (by rw [hK.funcs]; omega)]
  simp [hK.funcs, hy]

/-- A related target store holds the helper of segment `y` at address `N + y`. -/
theorem helperAt_of_srel {K : Ctx} (hK : K.Ok) {s t : Store H} (h : SRel K s t) {y : Nat}
    {d : Data} (hd : K.m.data[y]? = some d) {ma : Nat}
    (hma : K.mi.mems[(idx 0 : MemIdx).toNat]? = some ma) :
    HelperAt t (K.N + y) (helperBase K.m + y) ma (effBytes d) := by
  obtain ⟨ps, rs, he, hps, hrs⟩ := hK.hd
  have hy : y < K.m.data.length := (List.getElem?_eq_some_iff.mp hd).1
  refine ⟨K.helperInst y d, helperFunc K.m y d, ps, rs, ?_, he, hps, hrs, rfl, rfl, rfl,
    mi'_helper hK hy, hma⟩
  rw [SRel.helper h y, hd]
  rfl

/-- **`memory.init` against a call of its helper, on related stores.** -/
theorem memoryInit_rel {K : Ctx} (hK : K.Ok) {s t : Store H} (hS : SRel K s t) {f g : Frame}
    (hf : f.module = K.mi) (hg : g.module = K.mi') {y : DataIdx} {d : Data}
    (hd : K.m.data[y.toNat]? = some d) {ma : Nat} {mi : MemInst}
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hmi : MemOk mi) {i j n : BitVec 32} :
    ∃ di : DataInst, di.bytes.data.toList = effBytes d ∧
    (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size →
      ∃ s' t', Steps P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s', f, []⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n,
          .plain (.call (idx (helperBase K.m + y.toNat)))]⟩ ⟨t', g, []⟩ ∧ SRel K s' t') ∧
    (¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size) →
      Step P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s, f, [.trap]⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n,
          .plain (.call (idx (helperBase K.m + y.toNat)))]⟩ ⟨t, g, [.trap]⟩) := by
  obtain ⟨a, hya, hsa, -⟩ := hS.seg y.toNat d hd
  obtain ⟨di, hdi, hdb⟩ : ∃ di, s.datas[a]? = some di ∧ di.bytes.data.toList = effBytes d := by
    cases hx : s.datas[a]? with
    | none => rw [hx] at hsa; cases hsa
    | some di => rw [hx] at hsa; exact ⟨di, rfl, Option.some.inj hsa⟩
  have hsd : s.data? f y = some (a, di) := by simp [Store.data?, hf, hya, hdi]
  have hma : K.mi.mems[(idx 0 : MemIdx).toNat]? = some ma := by
    have := (Silmaril.Proofs.Wasm.LimeCompile.PassiveData.mem?_inv hm).1
    rwa [hf] at this
  have hH := helperAt_of_srel hK hS hd hma
  have hy : y.toNat < K.m.data.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgf : g.module.funcs[(idx (helperBase K.m + y.toNat) : FuncIdx).toNat]? =
      some (K.N + y.toNat) := by
    rw [hg]
    exact mi'_helper hK hy
  have htm : t.mems = s.mems := by
    have := congrArg Store.mems hS.other
    exact this.symm
  have hbs : (effBytes d).length ≤ 2 ^ 32 := hK.segs d (List.mem_of_getElem? hd)
  obtain ⟨-, hoob⟩ := memoryInit_emulation (P := P) (host := host) hm hmi hsd hdb hbs htm hH hgf
    (i := i) (j := j) (n := n)
  refine ⟨di, hdb, fun hb => ?_, hoob⟩
  obtain ⟨s', hl⟩ := Silmaril.Proofs.Wasm.LimeCompile.PassiveData.memoryInitLoop_some
    (H := H) n hm hsd hb.1 hb.2
  have hsm : s.mems[ma]? = some mi :=
    (Silmaril.Proofs.Wasm.LimeCompile.PassiveData.mem?_inv hm).2
  have ht' := Silmaril.Proofs.Wasm.LimeCompile.PassiveData.emu_ok (P := P) (host := host) hbs hdb n
    hl hsd (by rw [hf]; exact hma) (fun mi' h' => by rw [hsm] at h'; cases h'; exact hmi) htm hH hgf
  refine ⟨s', { t with mems := s'.mems }, memoryInitLoop_steps n hl, ?_, ?_⟩
  · simpa [constI32, Val.i32] using ht'
  · rw [memoryInitLoop_eq n hl]
    exact SRel.withMems hS s'.mems

/-- Memory 0 of the source instance is valid in a store with the session invariants. -/
theorem memOk_of_sinv {K : Ctx} {s : Store H} (h : SInv K s) {f : Frame} (hf : f.module = K.mi)
    {ma : Nat} {mi : MemInst} (hm : s.mem? f (idx 0) = some (ma, mi)) : MemOk mi := by
  have hinv := Silmaril.Proofs.Wasm.LimeCompile.PassiveData.mem?_inv hm
  have h0 : K.mi.mems[0]? = some ma := by
    have e : f.module.mems[(idx 0 : MemIdx).toNat]? = some ma := hinv.1
    rw [hf] at e
    exact e
  exact h.mem0 ma mi h0 hinv.2

end Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv
