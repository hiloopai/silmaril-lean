module

public import Silmaril.Wasm.Jco.Styles.Unified.Imports.Defs
public import Silmaril.Wasm.Jco.Styles.Imports.Thms
public import Silmaril.Proofs.Wasm.Jco.Styles.Unified

/-!
# The unified wrapper with world imports: proofs

Proofs of `Silmaril.Wasm.Jco.Styles.Unified.Imports.Thms`.

* `canonCallU_congr`: the unified `canon lift` calls its `realloc` only on `i32` arguments.
* `realloc_inst`: when the allocator does not depend on the imports, the `cabi_realloc` of
  `wrapU` behaves the same without imports and with any imports.
* `callExport_wrapUI`: so `wrapUI` is `wrapU` over the instance with the lowered imports.
* `imps_wrapUI`: the lowered imports are the C convention's imports.
* `specCall_inst`: the C convention with imports is `Meta.specCall` over the instance with the C
  convention's imports.
-/

public section

namespace Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat)
open Silmaril.Proofs.Wasm.Jco (find_liftsFrom)
open Silmaril.Proofs.Wasm.Jco.Styles.Unified (wrapU_realloc0 wrapU_realloc_zero wrapU_find
  lowerSpill_congr)

/-- The unified `canon lift` depends on its `realloc` only on `i32` arguments. -/
theorem canonCallU_congr (N : CoreInst) (enc : StrEnc) {R R' : List Flat → RM N.St (List Flat)}
    (h : ∀ a b c d : Nat, R [i32n a, i32n b, i32n c, i32n d] = R' [i32n a, i32n b, i32n c, i32n d])
    (callee : List Flat → RM N.St (List Flat)) (sig : Sig) (vs : List PVal) :
    canonCallU N enc R callee sig vs = canonCallU N enc R' callee sig vs := by
  unfold canonCallU
  cases hsp : spillOf sig.params with
  | some p =>
    have h0 : ∀ a n : Nat, R [i32n 0, i32n 0, i32n a, i32n n] = R' [i32n 0, i32n 0, i32n a, i32n n] :=
      fun a n => h 0 0 a n
    show canonCallS N R callee sig vs = canonCallS N R' callee sig vs
    unfold canonCallS
    simp only [hsp]
    exact RM.bind_congr fun vals => by rw [lowerSpill_congr N h0]
  | none =>
    cases wideOf sig.result with
    | some p =>
      show canonCallWE N enc R callee sig vs = canonCallWE N enc R' callee sig vs
      simp only [canonCallWE, lowerParamsE_congr N h enc]
    | none =>
      show canonCallE N enc R callee sig vs = canonCallE N enc R' callee sig vs
      simp only [canonCallE, lowerParamsE_congr N h enc]

variable (M : ICoreInst) (H : Host M.St) (md : IMeta)

theorem reallocEmuF_inst (a b : Imports M.St)
    (h : ∀ xs, (M.inst a).call md.alloc xs = (M.inst b).call md.alloc xs) :
    reallocEmuF (M.inst a) md.alloc = reallocEmuF (M.inst b) md.alloc := by
  have h' : ∀ xs, M.call a md.alloc xs = M.call b md.alloc xs := h
  funext xs
  unfold reallocEmuF reallocEmu copyBytes
  simp only [h']
  rfl

/-- Without imports and with any imports, the `cabi_realloc` of `wrapU` agrees on `i32`
arguments. -/
theorem realloc_inst (hA : md.AllocIndep M) (hC : md.Conforms M) (enc : StrEnc)
    (imps : Imports M.St) (a b c d : Nat) :
    (wrapU md.toMeta enc).callRef (M.inst noImports) (.adapt 0) [i32n a, i32n b, i32n c, i32n d] =
      (wrapU md.toMeta enc).callRef (M.inst imps) (.adapt 0) [i32n a, i32n b, i32n c, i32n d] := by
  rw [wrapU_realloc0, wrapE_realloc _ md.toMeta (hC noImports) a b c d, wrapU_realloc0,
    wrapE_realloc _ md.toMeta (hC imps) a b c d, reallocEmuF_inst M md imps noImports (hA imps)]

/-- **`wrapUI` is `wrapU` over the instance with the lowered imports.** -/
theorem callExport_wrapUI (hA : md.AllocIndep M) (hC : md.Conforms M) (enc : StrEnc)
    (name : String) (vs : List PVal) :
    (wrapUI md enc).callExport M H name vs =
      (wrapU md.toMeta enc).callExportWith (M.inst ((wrapUI md enc).imps M H))
        (canonCallU (M.inst ((wrapUI md enc).imps M H))) name vs := by
  have hl : (wrapUI md enc).comp = wrapU md.toMeta enc := rfl
  unfold UIComp.callExport XComp.callExportWith
  rw [hl, wrapU_find]
  cases hf : md.world.find? (·.name == name) with
  | none => rw [(find_liftsFrom name 0 md.world).2 hf]; rfl
  | some s =>
    obtain ⟨i, -, hfind⟩ := (find_liftsFrom name 0 md.world).1 s hf
    rw [hfind]
    simp only [Option.map_some]
    exact canonCallU_congr (M.inst ((wrapUI md enc).imps M H)) enc
      (R := (wrapU md.toMeta enc).callRef (M.inst noImports) (.adapt 0))
      (R' := (wrapU md.toMeta enc).callRef (M.inst ((wrapUI md enc).imps M H)) (.adapt 0))
      (realloc_inst M md hA hC enc _) _ s vs

theorem find?_lowersU (n : String) :
    (md.imports.map fun s => (⟨s, .adapt 0⟩ : Lower)).find? (·.sig.name == n) =
      (md.imports.find? (·.name == n)).map fun s => ⟨s, .adapt 0⟩ := by
  rw [List.find?_map]
  rfl

/-- The lowered imports of `wrapUI` are the C convention's imports. -/
theorem imps_wrapUI (hC : md.Conforms M) (enc : StrEnc) :
    (wrapUI md enc).imps M H = md.specImports M H := by
  funext n
  unfold UIComp.imps IMeta.specImports
  simp only [wrapUI, find?_lowersU]
  cases md.imports.find? (·.name == n) with
  | none => rfl
  | some s =>
    show canonLowerWith (M.inst noImports) (lowerBytes (M.inst noImports)
      ((wrapU md.toMeta enc).callRef (M.inst noImports) (.adapt 0))) (H n) s = _
    rw [funext₂ (lowerBytes_agree _ md.toMeta
      (fun n => wrapU_realloc_zero _ md.toMeta (hC noImports) enc 1 n))]

/-! ## The C convention with imports -/

theorem specBytes_inst (a b : Imports M.St)
    (h : ∀ xs, (M.inst a).call md.alloc xs = (M.inst b).call md.alloc xs) (lim : Nat)
    (bs : List UInt8) :
    md.toMeta.specBytes (M.inst a) lim bs = md.toMeta.specBytes (M.inst b) lim bs := by
  have h' : ∀ xs, M.call a md.alloc xs = M.call b md.alloc xs := h
  simp only [Meta.specBytes, h']
  rfl

theorem specParams_inst (a b : Imports M.St)
    (h : ∀ xs, (M.inst a).call md.alloc xs = (M.inst b).call md.alloc xs) :
    ∀ (ps : List PTy) (vs : List PVal),
      md.toMeta.specParams (M.inst a) ps vs = md.toMeta.specParams (M.inst b) ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    have hp : md.toMeta.specParam (M.inst a) t v = md.toMeta.specParam (M.inst b) t v := by
      cases t <;> cases v <;> simp only [Meta.specParam, specBytes_inst M md a b h]
    simp only [Meta.specParams, hp, specParams_inst a b h ts vs]

/-- The C convention with imports is `Meta.specCall` over the instance with its imports. -/
theorem specCall_inst (hA : md.AllocIndep M) (sig : Sig) (vs : List PVal) :
    md.specCall M H sig vs = md.toMeta.specCall (M.inst (md.specImports M H)) sig vs := by
  unfold IMeta.specCall Meta.specCall
  rw [specParams_inst M md noImports (md.specImports M H) (fun xs => (hA (md.specImports M H) xs).symm)]

theorem spec_inst (hA : md.AllocIndep M) :
    md.spec M H = md.toMeta.spec (M.inst (md.specImports M H)) := by
  funext name vs
  unfold IMeta.spec Meta.spec
  cases md.world.find? (·.name == name) with
  | none => rfl
  | some sig => exact specCall_inst M H md hA sig vs

end Silmaril.Proofs.Wasm.Jco.Styles.UnifiedImports
