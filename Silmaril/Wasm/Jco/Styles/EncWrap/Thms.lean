module

public import Silmaril.Wasm.Jco.Styles.EncWrap.Defs
public import Silmaril.Wasm.Jco.Styles.Enc.Thms
public import Silmaril.Wasm.Jco.Styles.Realloc.Thms
public import Silmaril.Wasm.Jco.Styles.Retptr.Thms

/-!
# FFI styles with a string encoding: results

* **`wrapE_correct`**: for a conforming module, the wrapper `wrapE md enc` behaves as the C
  convention with encoding `enc`, `md.specE M enc`, on every export.
* `specE_utf8`, **`wrapE_utf8`**: with `utf8` this is `Meta.spec`, and `wrapE md .utf8` behaves as
  `wrap md`. The copying `realloc` shim is then never called with a nonzero old pointer.
* `thinE_callExport`, `canonSpecE_eq_specE`, **`recognizeThinE_agrees`**: the thin wrapper with
  encoding `enc` follows the canonical convention. On worlds without results in memory it agrees
  with `wrapE md enc` when the module's `realloc` behaves as the emulated one (`ReallocEmulates`).
* **`specCallE_exact`**: when no string argument needs a second allocation (`NoShrinkArgs`), the
  C convention with encoding `enc` is the exact-copy convention `Meta.specCallExact`. In general
  they differ: the canonical algorithm allocates the worst case and then shrinks or grows, which
  calls `alloc` again and leaks a block (`reallocEmu`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)
open Silmaril.Proofs.Wasm.Jco (run_plain run_out find_liftsFrom)

variable (M : CoreInst) (md : Meta)

/-! ## Adaptor functions -/

theorem execX_map_base : ∀ (is : List AInstr) (f : Frame),
    execX M (is.map .base) f = exec M is f
  | [], _ => rfl
  | i :: is, f => by
    rw [List.map_cons, execX_cons, exec_cons]
    exact RM.bind_congr fun f' => execX_map_base is f'

theorem AFn.toX_run (fn : AFn) : fn.toX.run M = fn.run M := by
  funext xs
  simp only [XFn.run, AFn.run, AFn.toX, execX_map_base]

theorem wrapE_realloc (hC : md.Conforms M) (a b c d : Nat) :
    (wrapE md .utf8).callRef M (.adapt 0) [i32n a, i32n b, i32n c, i32n d] =
      reallocEmuF M md.alloc [i32n a, i32n b, i32n c, i32n d] :=
  reallocShimX_run M md.alloc _ _ _ _ (hC.alloc _)

theorem wrapE_callRef0 (enc : StrEnc) :
    (wrapE md enc).callRef M (.adapt 0) = (wrapE md .utf8).callRef M (.adapt 0) := rfl

theorem wrapE_shim (enc : StrEnc) (i : Nat) (s : Sig) (hi : md.world[i]? = some s) :
    (wrapE md enc).callRef M (.adapt (i + 1)) = (exportShim md s).run M := by
  funext xs
  simp [XComp.callRef, wrapE, adaptorXOf, hi, AFn.toX_run]

theorem wrapE_find (enc : StrEnc) (name : String) :
    (wrapE md enc).lifts.find? (·.sig.name == name) =
      ((liftsFrom 0 md.world).find? (·.sig.name == name)).map (Lift.withEnc enc) := by
  simp only [wrapE, List.find?_map]
  rfl

/-! ## The wrapper -/

/-- One export of the encoded wrapper. -/
theorem canonCallE_wrapE (hC : md.Conforms M) (enc : StrEnc) (i : Nat) (s : Sig)
    (hi : md.world[i]? = some s) (vs : List PVal) :
    canonCallE M enc ((wrapE md enc).callRef M (.adapt 0)) ((wrapE md enc).callRef M (.adapt (i + 1)))
      s vs = md.specCallE M enc s vs := by
  have hs : s ∈ md.world := List.mem_of_getElem? hi
  rw [wrapE_shim M md enc i s hi, wrapE_callRef0]
  unfold canonCallE Meta.specCallE
  rw [lowerParamsE_congr M (wrapE_realloc M md hC)]
  refine RM.bind_congr_returns (lowerParamsE_length M enc _ _ _) ?_
  intro xs hx
  cases h : inMem s.result
  · rw [run_plain M md s h xs hx]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [run_out M md hC s hs h xs hx]
    simp only [↓reduceIte, RM.bind_assoc, RM.pure_bind]

/-- **The encoded wrapper behaves as the C convention with encoding `enc`.** -/
theorem wrapE_correct (hC : md.Conforms M) (enc : StrEnc) (name : String) (vs : List PVal) :
    (wrapE md enc).callExportWith M (canonCallE M) name vs = md.specE M enc name vs := by
  unfold XComp.callExportWith Meta.specE
  rw [wrapE_find]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]; rfl
  | some s =>
    obtain ⟨i, hi, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    have hidx : 0 + i + 1 = i + 1 := by omega
    rw [hfind]
    simp only [hidx, Option.map_some]
    exact canonCallE_wrapE M md hC enc i s hi vs

/-! ## UTF-8 -/

theorem reallocEmuF_zero (n : Nat) :
    reallocEmuF M md.alloc [i32n 0, i32n 0, i32n 1, i32n n] = M.call md.alloc [i32n n, i32n 1] := by
  simp [reallocEmuF, reallocEmu]

theorem specE_utf8 : md.specE M .utf8 = md.spec M := by
  funext name vs
  unfold Meta.specE Meta.spec
  cases md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    show md.specCallE M .utf8 s vs = md.specCall M s vs
    unfold Meta.specCallE Meta.specCall
    rw [lowerParamsE_utf8, lowerParams_agree M md (reallocEmuF_zero M md)]
    simp only [liftResultE_utf8]

/-- **With `utf8`, the encoded wrapper is `wrap`.** -/
theorem wrapE_utf8 (hC : md.Conforms M) :
    (wrapE md .utf8).callExportWith M (canonCallE M) = (wrap md).callExport M := by
  funext name vs
  rw [wrapE_correct M md hC, specE_utf8, wrap_correct M md hC]

/-! ## The thin wrapper -/

theorem thinE_callExport (r : String) (enc : StrEnc) (name : String) (vs : List PVal) :
    (thinE md r enc).callExportWith M (canonCallE M) name vs =
      canonSpecE M md.world r enc name vs := by
  unfold XComp.callExportWith canonSpecE
  simp only [thinE, List.find?_map]
  have hp : ((fun x : XLift => x.sig.name == name) ∘
      fun s : Sig => ({ sig := s, callee := .core s.name, realloc := .core r, enc := enc } : XLift)) =
      fun s : Sig => s.name == name := rfl
  rw [hp]
  cases md.world.find? (·.name == name) <;> rfl

theorem canonSpecE_eq_specE {r : String} (h : md.thinOk = true) (hR : ReallocEmulates M md r)
    (enc : StrEnc) : canonSpecE M md.world r enc = md.specE M enc := by
  funext name vs
  unfold canonSpecE Meta.specE
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    have hs : inMem s.result = false := thinOk_mem md h (find?_mem md hf)
    show canonCallE M enc (M.call r) (M.call s.name) s vs = md.specCallE M enc s vs
    unfold canonCallE Meta.specCallE
    rw [lowerParamsE_congr M hR]
    simp only [hs, Bool.false_eq_true, ↓reduceIte]

/-- Thin-wrapper recognition with a string encoding. -/
def recognizeThinE (md : Meta) (r : String) (enc : StrEnc) : Option XComp :=
  if md.thinOk then some (thinE md r enc) else none

/-- **A recognized encoded thin wrapper agrees with the encoded wrapper.** -/
theorem recognizeThinE_agrees {r : String} {enc : StrEnc} {c : XComp}
    (h : recognizeThinE md r enc = some c) (hC : md.Conforms M) (hR : ReallocEmulates M md r) :
    c.callExportWith M (canonCallE M) = (wrapE md enc).callExportWith M (canonCallE M) := by
  unfold recognizeThinE at h
  split at h
  · next hk =>
    have hc : c = thinE md r enc := (Option.some.inj h).symm
    funext name vs
    rw [hc, thinE_callExport, canonSpecE_eq_specE M md hk hR, wrapE_correct M md hC]
  · cases h

end Silmaril.Wasm.Jco
