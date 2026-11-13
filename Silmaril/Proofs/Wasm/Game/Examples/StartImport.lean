module

public import Silmaril.Wasm.Game.Examples.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms

/-!
# A module whose start function calls an import: proofs

The allocation and the instantiation configuration of `exStart` are computed by
kernel evaluation of silmaril-lean's `validate?` and `prepare?`
(`decide +kernel` on Boolean summaries; no compiled evaluation). The runs are then
built from Core 3.0 `Step` rules, for an arbitrary profile:

* `run_to_callout`: `call 1` enters the start function, whose body `call 0`
  reaches the host-call redex of the import;
* `run_answer`: an answer `values []` of the host returns through the label and
  the frame;
* `loop_silent`: a host that never answers makes the redex stutter
  (`call_ref-hostfunc-div`), so the run diverges.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Examples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Examples Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The host function of import `0`. -/
def isHost0 (fi : FuncInst Nat) : Bool := match fi.code with | .host 0 => true | _ => false
/-- A Wasm function without locals whose body is `call 0`. -/
def isBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.call x]⟩ => x.toNat == 0 | _ => false

/-- `exStart` validates (kernel evaluation of `validate?`). -/
theorem exStart_valid : (validate? exStart).isSome = true := by decide +kernel
/-- The spec's allocation of `exStart` succeeds (kernel evaluation of `prepare?`). -/
theorem exPrepSome : (prepare? evalConst? (importStore (CExternType.funcs exMT.imports)) exStart (importAddrs exMT)).isSome = true
    := by decide +kernel
/-- Kernel-checked facts about the prepared configuration: no segment code, start
function `1`, the instance's functions `0, 1`, its export, and the two functions of the store. -/
theorem t_code : exPrep.1.code.isEmpty = true := by decide +kernel
theorem t_start : exPrep.2 = some ⟨1⟩ := by decide +kernel
theorem t_funcs : exPrep.1.frame.module.funcs = [0, 1] := by decide +kernel
theorem t_addrs : exportFuncAddrs exPrep.1.frame.module = [1] := by decide +kernel
theorem t_len : exPrep.1.store.funcs.length = 2 := by decide +kernel
theorem t_ty : exPrep.1.store.funcs.map (fun fi => FnType.ofDefType? fi.type) = [some ⟨[], []⟩, some ⟨[], []⟩]
    := by decide +kernel
theorem t_mod : exPrep.1.store.funcs.map (fun fi => fi.module.funcs) = [[], [0, 1]]
    := by decide +kernel
theorem t_host : exPrep.1.store.funcs.map isHost0 = [true, false] := by decide +kernel
theorem t_body : exPrep.1.store.funcs.map isBody = [false, true] := by decide +kernel
theorem t_imp : exMT.imports.all (fun xt => match xt with | .func _ => true | _ => false) = true
    := by decide +kernel
theorem t_impT : (CExternType.funcs exMT.imports).map FnType.ofDefType? = [some ⟨[], []⟩]
    := by decide +kernel

/-- Reading `isHost0`. -/
theorem isHost0_code {fi : FuncInst Nat} (h : isHost0 fi = true) : fi.code = .host 0 := by
  unfold isHost0 at h
  split at h
  · assumption
  · cases h

/-- Reading `isBody`. -/
theorem isBody_code {fi : FuncInst Nat} (h : isBody fi = true) :
    ∃ code : Func, ∃ x : FuncIdx, fi.code = .wasm code ∧ code.locals = [] ∧ code.body = [.call x] ∧ x.toNat = 0 := by
  unfold isBody at h
  split at h
  · rename_i t x hc
    exact ⟨_, x, hc, rfl, rfl, by simpa using h⟩
  · cases h

/-- The prepared store has two functions. -/
theorem exFuncs : ∃ fi₀ fi₁ : FuncInst Nat, exPrep.1.store.funcs = [fi₀, fi₁] := by
  obtain ⟨a, b, h⟩ := List.length_eq_two.mp t_len
  exact ⟨a, b, h⟩

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}

/-- A defined type of scalar type `[] → []` expands to `func [] []`. -/
theorem ty_nil {d : DefType} (h : FnType.ofDefType? d = some ⟨[], []⟩) :
    Expand d (.func (Ty.ofList []) (Ty.ofList [])) := FnType.expand_of_ofDefType? h

/-- **The start call reaches the import call**: `call 1` enters the start function, whose
body `call 0` reaches the host-call redex of the import. -/
theorem run_to_callout {s : Store Nat} {f : Frame} {fi₀ fi₁ : FuncInst Nat} {code : Func} {x : FuncIdx}
    (hfuncs : s.funcs = [fi₀, fi₁]) (hmod : f.module.funcs = [0, 1]) (h1 : fi₁.code = .wasm code)
    (hloc : code.locals = []) (hbody : code.body = [.call x]) (hx : x.toNat = 0)
    (hty₁ : FnType.ofDefType? fi₁.type = some ⟨[], []⟩) (hmod₁ : fi₁.module.funcs = [0, 1]) :
    Steps P host ⟨s, f, [.plain (.call ⟨1⟩)]⟩
      ⟨s, f, [.frame 0 (Frame.forCall fi₁.module [] []) [.label 0 []
        [.ref (.func 0), .callRefType fi₀.type]]]⟩ := by
  have h₁ : Step P host ⟨s, f, [.plain (.call ⟨1⟩)]⟩ ⟨s, f, [.ref (.func 1), .callRefType fi₁.type]⟩ :=
    Step.call (by rw [hmod]; rfl) (by rw [hfuncs]; rfl)
  have h₂ : Step P host ⟨s, f, [.ref (.func 1), .callRefType fi₁.type]⟩
      ⟨s, f, [.frame 0 (Frame.forCall fi₁.module [] []) [.label 0 [] [.plain (.call x)]]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := host) (s := s) (f := f) (c := .callRefType fi₁.type)
      (vs := []) (a := 1) (fi := fi₁) (code := code) trivial (by rw [hfuncs]; rfl) (ty_nil hty₁)
      (by simp [Ty.length]) h1
    simpa [vals, hloc, hbody, expression, Ty.length] using h
  have h₃ : Step P host ⟨s, Frame.forCall fi₁.module [] [], [.plain (.call x)]⟩
      ⟨s, Frame.forCall fi₁.module [] [], [.ref (.func 0), .callRefType fi₀.type]⟩ :=
    Step.call (by simp [Frame.forCall, hmod₁, hx]) (by rw [hfuncs]; rfl)
  exact (h₁.steps.trans h₂.steps).trans (Step.ctxtFrame (Step.ctxtLabel h₃)).steps

/-- An answer `values []` returns through the label and the frame. -/
theorem run_answer {s : Store Nat} {f f' : Frame} {fi₀ : FuncInst Nat} (hfuncs : s.funcs[0]? = some fi₀)
    (h0 : fi₀.code = .host 0) (hty₀ : FnType.ofDefType? fi₀.type = some ⟨[], []⟩)
    (hh : host 0 s [] (.returned s (.values []))) :
    Steps P host ⟨s, f, [.frame 0 f' [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]]]⟩
      ⟨s, f, []⟩ := by
  have h₁ : Step P host ⟨s, f', [.ref (.func 0), .callRefType fi₀.type]⟩ ⟨s, f', []⟩ := by
    have h := Step.callRefHost (P := P) (host := host) (s := s) (f := f') (c := .callRefType fi₀.type)
      (vs := []) (a := 0) (fi := fi₀) trivial hfuncs (ty_nil hty₀) (by simp [Ty.length]) h0 hh
    simpa [vals, Result.toAdmin] using h
  have h₂ : Step P host ⟨s, f', [.label 0 [] []]⟩ ⟨s, f', []⟩ :=
    Step.labelVals (vs := [])
  have h₃ : Step P host ⟨s, f, [.frame 0 f' []]⟩ ⟨s, f, []⟩ :=
    Step.frameVals (vs := []) rfl
  exact ((Step.ctxtFrame (Step.ctxtLabel h₁)).steps.trans (Step.ctxtFrame h₂).steps).trans h₃.steps

/-- A host that never answers makes the redex stutter forever. -/
theorem loop_silent {s : Store Nat} {f f' : Frame} {fi₀ : FuncInst Nat} (hfuncs : s.funcs[0]? = some fi₀)
    (h0 : fi₀.code = .host 0) (hty₀ : FnType.ofDefType? fi₀.type = some ⟨[], []⟩)
    (hh : host 0 s [] .diverged) :
    Diverges P host ⟨s, f, [.frame 0 f' [.label 0 [] [.ref (.func 0), .callRefType fi₀.type]]]⟩ := by
  have h₁ : Step P host ⟨s, f', [.ref (.func 0), .callRefType fi₀.type]⟩
      ⟨s, f', [.ref (.func 0), .callRefType fi₀.type]⟩ := by
    have h := Step.callRefHostDiv (P := P) (host := host) (s := s) (f := f') (c := .callRefType fi₀.type)
      (vs := []) (a := 0) (fi := fi₀) trivial hfuncs (ty_nil hty₀) (by simp [Ty.length]) h0 hh
    simpa [vals] using h
  exact ⟨fun _ => _, rfl, fun _ => Step.ctxtFrame (Step.ctxtLabel h₁)⟩

/-- The host induced by `exAnswer` answers import `0` with `values []`. -/
theorem hostOf_answer {s : Store Nat} :
    hostOf exI.imports exAnswer 0 s [] (.returned s (.values [])) := by
  refine ⟨⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩, ?_, .inl ⟨_, rfl, rfl⟩⟩
  simp [ifaceOp?, exI]

/-- The host induced by the silent environment diverges on import `0`. -/
theorem hostOf_silent {s : Store Nat} :
    hostOf exI.imports (Env.silent _) 0 s [] .diverged := by
  refine ⟨⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩, ?_, .inr ⟨fun _ h => (by cases h), rfl⟩⟩
  simp [ifaceOp?, exI]

/-- The shape of the prepared store: the import, then the start function. -/
theorem exShape : ∃ (fi₀ fi₁ : FuncInst Nat) (code : Func) (x : FuncIdx),
    exPrep.1.store.funcs = [fi₀, fi₁] ∧ fi₀.code = .host 0 ∧ fi₁.code = .wasm code ∧
    code.locals = [] ∧ code.body = [.call x] ∧ x.toNat = 0 ∧
    FnType.ofDefType? fi₀.type = some ⟨[], []⟩ ∧ FnType.ofDefType? fi₁.type = some ⟨[], []⟩ ∧
    fi₁.module.funcs = [0, 1] := by
  obtain ⟨fi₀, fi₁, hl⟩ := exFuncs
  have hh : [isHost0 fi₀, isHost0 fi₁] = [true, false] := by simpa [hl] using t_host
  have hb : [isBody fi₀, isBody fi₁] = [false, true] := by simpa [hl] using t_body
  have ht : [FnType.ofDefType? fi₀.type, FnType.ofDefType? fi₁.type] =
      [some ⟨[], []⟩, some ⟨[], []⟩] := by simpa [hl] using t_ty
  have hm : [fi₀.module.funcs, fi₁.module.funcs] = [[], [0, 1]] := by simpa [hl] using t_mod
  obtain ⟨code, x, h1, hloc, hbody, hx⟩ := isBody_code (List.cons.inj (List.cons.inj hb).2).1
  exact ⟨fi₀, fi₁, code, x, hl, isHost0_code (List.cons.inj hh).1, h1, hloc, hbody, hx,
    (List.cons.inj ht).1, (List.cons.inj (List.cons.inj ht).2).1,
    (List.cons.inj (List.cons.inj hm).2).1⟩

/-- The configuration of `$instantiate` is `call 1` in the module's frame. -/
theorem exC₀_eq : exC₀ = ⟨exPrep.1.store, exPrep.1.frame, [.plain (.call ⟨1⟩)]⟩ := by
  have hc : exPrep.1.code = [] := List.isEmpty_iff.mp t_code
  simp only [exC₀, t_start, Config.withStart, hc, List.nil_append]

/-- **Instantiation against `exAnswer` succeeds**, for every profile. -/
theorem ex_ready : (exI.closedSpec P exC₀ exAnswer).InstReady := by
  obtain ⟨fi₀, fi₁, code, x, hl, h0, h1, hloc, hbody, hx, ht₀, ht₁, hm₁⟩ := exShape
  have hrun := (run_to_callout (P := P) (host := hostOf exI.imports exAnswer) hl t_funcs h1 hloc
    hbody hx ht₁ hm₁).trans (run_answer (f := exPrep.1.frame) (by rw [hl]; rfl) h0 ht₀ hostOf_answer)
  refine (closedSpec_instReady_iff P exAnswer).2 ⟨_, ⟨exPrep.1.store, exPrep.1.frame, []⟩, ?_, rfl, rfl⟩
  rw [exC₀_eq]
  exact hrun

/-- **Instantiation against the silent environment diverges** (the start function waits for
the import forever), for every profile. -/
theorem ex_diverges : (exI.closedSpec P exC₀ (Env.silent _)).InstDiverges := by
  obtain ⟨fi₀, fi₁, code, x, hl, h0, h1, hloc, hbody, hx, ht₀, ht₁, hm₁⟩ := exShape
  have hrun := run_to_callout (P := P) (host := hostOf exI.imports (Env.silent _)) hl t_funcs h1 hloc
    hbody hx ht₁ hm₁
  refine (closedSpec_instDiverges_iff P (Env.silent _)).2 ?_
  rw [exC₀_eq]
  exact Silmaril.InfiniteTrace.of_steps hrun (loop_silent (by rw [hl]; rfl) h0 ht₀ hostOf_silent)

/-- The validated type. -/
theorem exStart_valid' : validate? exStart = some exMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp exStart_valid
  simp [exMT, hmt]

/-- The allocation. -/
theorem exPrep' : prepare? evalConst? (importStore (CExternType.funcs exMT.imports)) exStart
    (importAddrs exMT) = some exPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp exPrepSome
  simp [exPrep, hp]

/-- The only import is a function. -/
theorem ex_funcImports : ∀ xt ∈ exMT.imports, ∃ d, xt = .func d := by
  intro xt hxt
  have h := List.all_eq_true.mp t_imp xt hxt
  cases xt with
  | func d => exact ⟨d, rfl⟩
  | _ => cases h

/-- The import has scalar type `[] → []`. -/
theorem ex_importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs exMT.imports) exI.imports := by
  have hlen : (CExternType.funcs exMT.imports).length = 1 := by
    simpa using congrArg List.length t_impT
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp hlen
  have h : FnType.ofDefType? d = some ⟨[], []⟩ := by simpa [hd] using t_impT
  rw [hd]
  exact .cons h .nil

/-- The export has scalar type `[] → []`. -/
theorem ex_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, exI.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) exI.addrs exI.exports := by
  obtain ⟨fi₀, fi₁, code, x, hl, -, -, -, -, -, -, ht₁, -⟩ := exShape
  have ha : exI.addrs = [1] := t_addrs
  rw [ha]
  exact .cons ⟨fi₁, by simp [exI, hl], ht₁⟩ .nil

/-- **`exI` is the spec instance of `exStart`, with configuration `exC₀`.** -/
theorem ex_isSpecInstance : IsSpecInstance exStart exMT exI exC₀ where
  valid := exStart_valid'
  funcImports := ex_funcImports
  importTypes := ex_importTypes
  prepared := ⟨exPrep.1, exPrep.2, exPrep', rfl, rfl, rfl⟩
  exportTypes := ex_exportTypes

end Silmaril.Proofs.Wasm.Game.Examples
