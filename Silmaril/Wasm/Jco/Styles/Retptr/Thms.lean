module

public import Silmaril.Wasm.Jco.Styles.Retptr.Defs
public import Silmaril.Wasm.Jco.Thin.Canon.Thms

/-!
# The retptr style: behaviour, and its relation to the out-pointer and canonical styles

* `lowerParams_agree`: canonical lowering through any `realloc` that answers `realloc(0, 0, 1,
  n)` as `alloc(n, 1)` is the C convention's copying. `reallocShim_run` says the `cabi_realloc`
  shim is such a `realloc`.
* **`retComp_callExport`**: the retptr wrapper `retComp md` behaves as the retptr style
  `md.retSpec M`, for every module.
* **`retSpec_retView`**: the retptr style of the out-pointer to retptr view of a conforming
  module is its C convention, `md.spec M`. **`retComp_retView`**: so the retptr wrapper over the
  view behaves as `wrap md` over the module. The export shims of `wrap` are exactly the view.
* **`retSpec_eq_canonSpec`**: for a module with a canonical `realloc` export `r` that agrees with
  its allocator (`ReallocAgrees`), the retptr style **is** the canonical convention, on every
  world (results in memory included). So the thin wrapper `thinComp md r` applies to retptr
  modules on every world (`thinComp_retSpec`), not only where `Meta.thinOk` holds, and agrees with
  the retptr wrapper (`recognizeRet_thin`).
* `retSpec_eq_spec`: where no result is in memory, the retptr style is the C convention.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (md : Meta)

/-! ## Lowering through an agreeing `realloc` -/

theorem lowerParam_agree {R : List Flat → RM M.St (List Flat)}
    (hR : ∀ n : Nat, R [i32n 0, i32n 0, i32n 1, i32n n] = M.call md.alloc [i32n n, i32n 1])
    (t : PTy) (v : PVal) : lowerParam M R t v = md.specParam M t v := by
  cases t <;> cases v <;> simp only [lowerParam, Meta.specParam, lowerBytes, Meta.specBytes]
  all_goals
    congr 1
    funext _
    rw [hR]

/-- Canonical lowering through an agreeing `realloc` is the C convention. -/
theorem lowerParams_agree {R : List Flat → RM M.St (List Flat)}
    (hR : ∀ n : Nat, R [i32n 0, i32n 0, i32n 1, i32n n] = M.call md.alloc [i32n n, i32n 1]) :
    ∀ (ps : List PTy) (vs : List PVal), lowerParams M R ps vs = md.specParams M ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    simp only [lowerParams, Meta.specParams, lowerParam_agree M md hR,
      lowerParams_agree hR ts vs]

/-- The `cabi_realloc` shim calls `alloc(size, align)`. -/
theorem reallocShim_run (alloc : String) (a b c d : Flat) :
    (reallocShim alloc).run M [a, b, c, d] = M.call alloc [d, c] := by
  simp [AFn.run, reallocShim, exec_cons, AInstr.step, RM.bind_assoc]

theorem retComp_realloc (n : Nat) :
    (retComp md).callRef M (.adapt 0) [i32n 0, i32n 0, i32n 1, i32n n] =
      M.call md.alloc [i32n n, i32n 1] := by
  simp only [Comp.callRef, retComp]
  exact reallocShim_run M md.alloc _ _ _ _

/-! ## The retptr wrapper -/

theorem retComp_find (name : String) :
    (retComp md).lifts.find? (·.sig.name == name) =
      (md.world.find? (·.name == name)).map fun s => ⟨s, .core s.name, .adapt 0⟩ := by
  simp only [retComp, List.find?_map]
  rfl

/-- **The retptr wrapper behaves as the retptr style**, for every module. -/
theorem retComp_callExport (name : String) (vs : List PVal) :
    (retComp md).callExport M name vs = md.retSpec M name vs := by
  unfold Comp.callExport Meta.retSpec
  rw [retComp_find]
  cases md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    show canonCall M ((retComp md).callRef M (.adapt 0)) (M.call s.name) s vs = md.retCall M s vs
    unfold canonCall Meta.retCall
    rw [lowerParams_agree M md (retComp_realloc M md)]

/-! ## The out-pointer to retptr view -/

theorem retViewCall_plain {n : String}
    (h : ∀ s, md.world.find? (·.name == n) = some s → inMem s.result = false) :
    retViewCall M md n = M.call n := by
  funext xs
  unfold retViewCall
  cases hf : md.world.find? (·.name == n) with
  | none => rfl
  | some s => simp only [h s hf, Bool.false_eq_true, ↓reduceIte]

theorem noClash_mem {r : String} (h : md.NoClash r = true) {s : Sig} (hs : s ∈ md.world)
    (hn : s.name = md.alloc ∨ s.name = r) : inMem s.result = false := by
  have hall := List.all_eq_true.mp h s hs
  have hb : (s.name == md.alloc || s.name == r) = true := by
    rcases hn with hn | hn <;> simp [hn]
  simpa [hb] using hall

theorem find?_name {n : String} {s : Sig} (h : md.world.find? (·.name == n) = some s) :
    s ∈ md.world ∧ s.name = n :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem retView_alloc {r : String} (h : md.NoClash r = true) :
    (retView M md).call md.alloc = M.call md.alloc :=
  retViewCall_plain M md fun _ hf =>
    noClash_mem md h (find?_name md hf).1 (.inl (find?_name md hf).2)

theorem retView_realloc {r : String} (h : md.NoClash r = true) :
    (retView M md).call r = M.call r :=
  retViewCall_plain M md fun _ hf =>
    noClash_mem md h (find?_name md hf).1 (.inr (find?_name md hf).2)

theorem specParams_retView {r : String} (h : md.NoClash r = true) :
    ∀ (ps : List PTy) (vs : List PVal), md.specParams (retView M md) ps vs = md.specParams M ps vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by
    have hp : md.specParam (retView M md) t v = md.specParam M t v := by
      cases t <;> cases v <;> simp only [Meta.specParam, Meta.specBytes, retView_alloc M md h] <;>
        rfl
    simp only [Meta.specParams, hp, specParams_retView h ts vs]
    rfl

theorem retView_call_of_find {name : String} {s : Sig}
    (hf : md.world.find? (·.name == name) = some s) :
    (retView M md).call s.name =
      if inMem s.result then outAsRet M md s.name else M.call s.name := by
  funext xs
  have hn : s.name = name := (find?_name md hf).2
  show retViewCall M md s.name xs = _
  unfold retViewCall
  rw [hn, hf]
  show (if inMem s.result then outAsRet M md name xs else M.call name xs) =
    (if inMem s.result then outAsRet M md name else M.call name) xs
  cases inMem s.result <;> rfl

/-- **The retptr style of the view is the C convention.** -/
theorem retSpec_retView {r : String} (h : md.NoClash r = true) :
    md.retSpec (retView M md) = md.spec M := by
  funext name vs
  unfold Meta.retSpec Meta.spec
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    show md.retCall (retView M md) s vs = md.specCall M s vs
    unfold Meta.retCall Meta.specCall
    rw [specParams_retView M md h, retView_call_of_find M md hf]
    cases inMem s.result
    · rfl
    · refine RM.bind_congr fun xs => ?_
      show (outAsRet M md s.name xs >>= liftResult M s.result) = _
      simp only [outAsRet, RM.bind_assoc, RM.pure_bind, ↓reduceIte]

/-- **The retptr wrapper over the view is `wrap`**: the export shims of the monadic construction
are the out-pointer to retptr view. -/
theorem retComp_retView {r : String} (h : md.NoClash r = true) (hC : md.Conforms M) :
    (retComp md).callExport (retView M md) = (wrap md).callExport M := by
  funext name vs
  rw [retComp_callExport, retSpec_retView M md h, wrap_correct M md hC]

/-! ## The retptr style is the canonical convention -/

theorem retSpec_eq_canonSpec {r : String} (hR : ReallocAgrees M md r) :
    md.retSpec M = canonSpec M md.world r := by
  funext name vs
  unfold Meta.retSpec canonSpec
  cases md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    show md.retCall M s vs = canonCall M (M.call r) (M.call s.name) s vs
    unfold Meta.retCall canonCall
    rw [lowerParams_agree M md hR]

/-- The thin wrapper of a retptr module with an agreeing `realloc` follows the retptr style, on
every world. -/
theorem thinComp_retSpec {r : String} (hR : ReallocAgrees M md r) :
    (thinComp md r).callExport M = md.retSpec M := by
  funext name vs
  rw [thinComp_callExport, retSpec_eq_canonSpec M md hR]

/-- Recognized retptr wrappers agree with the thin wrapper when the `realloc` agrees. -/
theorem recognizeRet_thin {r : String} {c : Comp} (h : recognizeRet md true = some c)
    (hR : ReallocAgrees M md r) : c.callExport M = (thinComp md r).callExport M := by
  have hc : c = retComp md := (Option.some.inj h).symm
  funext name vs
  rw [hc, retComp_callExport, thinComp_retSpec M md hR]

/-- Without results in memory, the retptr style is the C convention. -/
theorem retSpec_eq_spec (h : md.thinOk = true) : md.retSpec M = md.spec M := by
  funext name vs
  unfold Meta.retSpec Meta.spec
  cases hf : md.world.find? (·.name == name) with
  | none => rfl
  | some s =>
    show md.retCall M s vs = md.specCall M s vs
    have hs : inMem s.result = false := thinOk_mem md h (find?_mem md hf)
    unfold Meta.retCall Meta.specCall
    simp only [hs, Bool.false_eq_true, ↓reduceIte]

end Silmaril.Wasm.Jco
