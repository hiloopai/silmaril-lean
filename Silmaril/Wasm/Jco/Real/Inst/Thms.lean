module

public import Silmaril.Wasm.Jco.Real.Inst.Defs

/-!
# A real Core 3.0 module instance as a `CoreInst`: theorems

* `mapM_ofVal?_iff`: the flat values read back from Core values are exactly the flat values
  they came from.
* **`call_ok_iff`**: a returned call of `realInst` is exactly a reference-semantics run of the
  export, from `$invoke` on the arguments to the result values, in the final store.
* `call_trap_of_run`: a run reducing to a trap is a trapping call.
* **`session_of_call_ok`**: a returned call followed by a session of further invocations is a
  session of `Binaryen.Session` (the observation that `Binaryen.ExportRefines` and so the 3.0 →
  Lime compiler's `compile_correct` are stated with). So the states of `realInst` are those of
  the module's export sessions, and the instance is stateful in exactly that sense.
* **`wrap_correct_real`**, `wrap_correct_seq_real`: `wrap_correct` and `wrap_correct_seq` for the
  instance of a real Core 3.0 module (assuming `Meta.Conforms` of that instance).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc? Session)

variable {H : Type}

theorem ofVal?_toVal (v : Flat) : ofVal? (toVal v) = some v := by
  rcases v with ⟨t, b⟩
  rfl

theorem toVal_of_ofVal? {v : Val} {x : Flat} (h : ofVal? v = some x) : v = toVal x := by
  rcases v with ⟨⟨t, b⟩⟩ | _ | _ <;> simp [ofVal?] at h
  subst h
  rfl

theorem mapM_ofVal?_iff : ∀ (vs : List Val) (xs : List Flat),
    vs.mapM ofVal? = some xs ↔ vs = xs.map toVal
  | [], xs => by
    cases xs <;> simp
  | v :: vs, xs => by
    constructor
    · intro h
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨x, hx, ys, hys, rfl⟩ := h
      rw [List.map_cons, ← (mapM_ofVal?_iff vs ys).mp hys, toVal_of_ofVal? hx]
    · intro h
      cases xs with
      | nil => simp at h
      | cons x xs =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ofVal?_toVal, (mapM_ofVal?_iff (xs.map toVal) xs).mpr rfl]

theorem resultOut_ok {r : Result} {s s' : Store H} {ys : List Flat}
    (h : resultOut r s = .ok ys s') : r = .values (ys.map toVal) ∧ s = s' := by
  cases r with
  | values vs =>
    simp only [resultOut] at h
    split at h
    · rename_i xs hxs
      cases h
      exact ⟨by rw [(mapM_ofVal?_iff vs ys).mp hxs], rfl⟩
    · cases h
  | throw _ => cases h
  | trap => cases h

theorem resultOut_values (ys : List Flat) (s : Store H) :
    resultOut (.values (ys.map toVal)) s = .ok ys s := by
  simp [resultOut, (mapM_ofVal?_iff (ys.map toVal) ys).mpr rfl]

variable (P : Profile) (host : HostSemantics H) (mi : ModuleInst) (ma : Nat)

/-- **A returned call is a reference-semantics run of the export to values.** -/
theorem call_ok_iff (name : String) (xs ys : List Flat) (s s' : Store H) :
    (realInst H P host mi ma).call name xs s (.ok ys s') ↔
      ∃ a c, exportFunc? mi name = some a ∧ InvokeOk s a (xs.map toVal) ∧
        Steps P host (invoke s a (xs.map toVal)) c ∧ c.code = vals (ys.map toVal) ∧
          c.store = s' := by
  show coreCall P host mi name xs s (.ok ys s') ↔ _
  unfold coreCall
  constructor
  · intro h
    split at h
    · rename_i a ha
      rcases h with ⟨hok, c, r, hrun, hc, ho⟩ | ⟨_, h⟩
      · obtain ⟨rfl, hs⟩ := resultOut_ok ho.symm
        exact ⟨a, c, ha, hok, hrun, hc, hs⟩
      · cases h
    · cases h
  · rintro ⟨a, c, ha, hok, hrun, hc, rfl⟩
    rw [ha]
    exact Or.inl ⟨hok, c, .values (ys.map toVal), hrun, hc, (resultOut_values ys _).symm⟩

/-- A well-typed run reducing to a trap is a trapping call. -/
theorem call_trap_of_run (name : String) (xs : List Flat) (s : Store H) {a : Nat}
    (ha : exportFunc? mi name = some a) (hok : InvokeOk s a (xs.map toVal)) {c : Config H}
    (hrun : Steps P host (invoke s a (xs.map toVal)) c) (hc : c.code = [.trap]) :
    (realInst H P host mi ma).call name xs s .trap := by
  show coreCall P host mi name xs s .trap
  unfold coreCall
  rw [ha]
  exact Or.inl ⟨hok, c, .trap, hrun, hc, rfl⟩

/-- **A returned call extends to an export session** of the module instance. -/
theorem session_of_call_ok {name : String} {xs ys : List Flat} {s s' : Store H}
    (h : (realInst H P host mi ma).call name xs s (.ok ys s'))
    {rest : List Silmaril.Wasm.Binaryen.Call} {bs : List (Silmaril.Wasm.Behaviour Val)}
    (tail : Session P host mi s' rest bs) :
    Session P host mi s ((name, xs.map toVal) :: rest)
      ((Result.values (ys.map toVal)).toBehaviour :: bs) := by
  obtain ⟨a, c, ha, hok, hrun, hc, rfl⟩ := (call_ok_iff P host mi ma name xs ys s s').mp h
  exact Session.done ha hok hrun hc tail

/-- **`wrap_correct` for a real Core 3.0 module instance.** -/
theorem wrap_correct_real (md : Meta) (hC : md.Conforms (realInst H P host mi ma))
    (name : String) (vs : List PVal) :
    (wrap md).callExport (realInst H P host mi ma) name vs =
      md.spec (realInst H P host mi ma) name vs :=
  wrap_correct _ md hC name vs

/-- `wrap_correct_seq` for a real Core 3.0 module instance: the wrapper's state is the Core
store, shared by the calls. -/
theorem wrap_correct_seq_real (md : Meta) (hC : md.Conforms (realInst H P host mi ma))
    (calls : List (String × List PVal)) :
    runCalls ((wrap md).callExport (realInst H P host mi ma)) calls =
      runCalls (md.spec (realInst H P host mi ma)) calls :=
  wrap_correct_seq _ md hC calls

end Silmaril.Wasm.Jco.Real
