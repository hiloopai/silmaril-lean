module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Expr
public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Thms

/-!
# `Rel` is kept by the state changes of the fragment

`rel_setL` (`local.set`), `rel_setG` (`global.set`, with the global's address), `rel_mem` (a
store whose memory holds the new bytes and whose globals and functions are unchanged: after
`i32.store8`, `memory.copy` and the built-ins).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E Bin BI M32 upd)
open Silmaril.Wasm.JcoTool.KDrop (DSt)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA GlobalsAre gidx)

variable {H : Type} {hb : BI → H} {ma nl : Nat}

theorem loc_lt {F : Frame} {i : Nat} {v : Option Val} (h : F.locals[i]? = some v) :
    i < F.locals.length := (List.getElem?_eq_some_iff.mp h).1

/-- `local.set i` keeps `Rel`. -/
theorem rel_setL {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) {i v : Nat}
    (hi : i < nl) (hv : v < M32) :
    (ix i : LocalIdx).toNat < F.locals.length ∧
      Rel hb nl ma cs (F.setLocal (ix i) (Val.i32 (w v))) { s with l := upd s.l i v } := by
  have hi32 : i < M32 := Nat.lt_of_lt_of_le hi h.nl32
  have hlen : i < F.locals.length := loc_lt (h.loc i hi).1
  refine ⟨by rw [ix_toNat hi32]; exact hlen, h.nl32, fun j hj => ?_, h.glob, h.glt, h.mem, h.imp⟩
  show (F.locals.set (ix i : LocalIdx).toNat (some (Val.i32 (w v))))[j]? = _ ∧ upd s.l i v j < M32
  rw [ix_toNat hi32]
  by_cases hji : j = i
  · subst hji
    simp [hlen, upd, hv]
  · rw [List.getElem?_set_ne (Ne.symm hji)]
    simp only [upd, hji, ↓reduceIte]
    exact h.loc j hj

theorem gsOf_set (g : Nat → Nat) {i : Nat} (v : Nat) :
    (gsOf g).set i (w v) = gsOf (upd g i v) := by
  apply List.ext_getElem
  · simp [gsOf]
  · intro j h1 h2
    simp only [gsOf, List.getElem_set, List.getElem_map, List.getElem_range, upd]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji, Ne.symm hji]

/-- `global.set i` keeps `Rel`, in the store with the global at its address set. -/
theorem rel_setG (Pf : Profile) {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) {i v : Nat}
    (hi : i < NG) (hv : v < M32) :
    ∃ a gi, cs.global? F (ix i) = some (a, gi) ∧
      Rel hb nl ma (cs.setGlobal a (Val.i32 (w v))) F { s with g := upd s.g i v } := by
  have hi32 : i < 2 ^ 32 := by unfold NG at hi; omega
  have hlt : (gidx i).value.val < (gsOf s.g).length := by
    show i % 2 ^ 32 < _
    rw [Nat.mod_eq_of_lt hi32]; simp [gsOf, hi]
  obtain ⟨a, gi, hga, hgs, -⟩ := Silmaril.Wasm.FX.Asyncify.Tool.global_set_core (Pf := Pf)
    (host := fun _ _ _ _ => False) cs F [] (ls := []) (ops := []) h.glob (gidx i) (w v) hlt
  have hval : (gidx i).value.val = i := Nat.mod_eq_of_lt hi32
  rw [hval, gsOf_set] at hgs
  refine ⟨a, gi, hga, h.nl32, h.loc, hgs, fun j hj => ?_, ?_, ?_⟩
  · simp only [upd]; split
    · exact hv
    · exact h.glt j hj
  · obtain ⟨mi, h0, h1, hs, hb'⟩ := h.mem
    exact ⟨mi, h0, h1, hs, hb'⟩
  · intro b
    obtain ⟨a', fi, ps, rs, h1, h2, h3, h4, h5⟩ := h.imp b
    exact ⟨a', fi, ps, rs, h1, h2, h3, h4, h5⟩

/-- A store with the new memory and the same globals and functions keeps `Rel`. -/
theorem rel_mem {cs cs' : Store H} {F : Frame} {s s' : DSt} (h : Rel hb nl ma cs F s)
    (hm : MemR cs' F ma s'.m) (hg : cs'.globals = cs.globals) (hf : cs'.funcs = cs.funcs)
    (hl : s'.l = s.l) (hgg : s'.g = s.g) : Rel hb nl ma cs' F s' := by
  refine ⟨h.nl32, ?_, ?_, ?_, hm, ?_⟩
  · rw [hl]; exact h.loc
  · have e : ∀ x, cs'.global? F x = cs.global? F x := global?_of_globals hg F
    obtain ⟨h1, h2, h3⟩ := h.glob
    rw [hgg]
    refine ⟨h1, fun g hg' => ?_, fun g g' a a' gi gi' ha ha' => ?_⟩
    · rw [e]; exact h2 g hg'
    · rw [e] at ha ha'; exact h3 g g' a a' gi gi' ha ha'
  · rw [hgg]; exact h.glt
  · intro b
    obtain ⟨a', fi, ps, rs, h1, h2, h3, h4, h5⟩ := h.imp b
    exact ⟨a', fi, ps, rs, h1, by rw [hf]; exact h2, h3, h4, h5⟩

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
