module

public import Silmaril.Wasm.Spec.Joint.Wrap.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Thms
public import Silmaril.Wasm.Spec.Component.Ground.Thms

@[expose] public section

/-!
# Wrapping core modules as components: proofs

* the canonical ABI at the wrapping types: lowering numeric Core values typed by `t` at
  `numVT t` checks and gives the values back (`checkList_numToIR`, `lowerList_numToIR`), lifting
  numeric results gives their IR images (`liftList_numToIR`), and the reference images are the
  wrapped values (`toRefVal_numToIR`);
* the wrapping component is a simple component of the soundness fragment
  (`wrapSimple_good`) whose interface is the image interface (`cface_wrapSimple`);
* `wrap_spec`, `wrap_sound`: **soundness of wrapping w.r.t. the boundary adapters**.

Summary in `Silmaril.Wasm.Spec.Joint.Wrap.Thms`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Component (CoreFuncTy ValTy FuncTy checkLower lowerArgs liftArgs)
open Silmaril.Wasm.Component.Reference (fnOf NumModule Simple SimpleExport toRefVal exportSpec
  coreOut liftOutcome modSem)
open Silmaril.Wasm.Spec.Component
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Execution.Core (Val Result Steps invoke)
open Silmaril.Wasm.SingleThreaded (toFlat? ofFlat)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Values at the wrapping types -/

/-- A numeric Core value of type `t`. -/
theorem num_of_hasVal {t : NumType} {v : Val} (h : (ScalarType.num t).HasVal v) :
    ∃ b, v = .num ⟨t, b⟩ := h

/-- The IR image of a numeric value has the wrapping type, and lowers to the value. -/
theorem numToIR_check_lower {t : NumType} {v : Val} (h : (ScalarType.num t).HasVal v) :
    (numVT t).check (numToIR v) = true ∧ ((numVT t).lower (numToIR v)).map ofFlat = [v] := by
  obtain ⟨b, rfl⟩ := num_of_hasVal h
  rcases t with (_ | _) | (_ | _) <;> exact ⟨rfl, rfl⟩

/-- Lifting at the wrapping type reads the value back. -/
theorem numToIR_lift {t : NumType} {v : Val} (h : (ScalarType.num t).HasVal v) :
    ∃ y, toFlat? v = some y ∧
      ∀ r : List Silmaril.Wasm.Component.Flat, (numVT t).lift (y :: r) = some (numToIR v, r) := by
  obtain ⟨b, rfl⟩ := num_of_hasVal h
  rcases t with (_ | _) | (_ | _) <;> exact ⟨_, rfl, fun _ => rfl⟩

/-- The reference image of the IR image is the wrapped value. -/
theorem toRefVal_numToIR {t : NumType} {v : Val} (h : (ScalarType.num t).HasVal v) :
    toRefVal (numToIR v) = wrapVal v := by
  obtain ⟨b, rfl⟩ := num_of_hasVal h
  rcases t with (_ | _) | (_ | _) <;> rfl

theorem checkList_numToIR :
    ∀ {ps : List NumType} {a : List Val}, List.Forall₂ ScalarType.HasVal (ps.map .num) a →
      ValTy.checkList (ps.map numVT) (a.map numToIR) = true
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, ValTy.checkList, Bool.and_eq_true]
    exact ⟨(numToIR_check_lower h).1, checkList_numToIR hs⟩

theorem lowerList_numToIR :
    ∀ {ps : List NumType} {a : List Val}, List.Forall₂ ScalarType.HasVal (ps.map .num) a →
      (ValTy.lowerList (ps.map numVT) (a.map numToIR)).map ofFlat = a
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, ValTy.lowerList, List.map_append, (numToIR_check_lower h).2,
      lowerList_numToIR hs, List.singleton_append]

theorem liftList_numToIR :
    ∀ {rs : List NumType} {vs : List Val}, List.Forall₂ ScalarType.HasVal (rs.map .num) vs →
      ∃ ys, vs.mapM toFlat? = some ys ∧
        ∀ r, ValTy.liftList (rs.map numVT) (ys ++ r) = some (vs.map numToIR, r)
  | [], [], _ => ⟨[], rfl, fun _ => rfl⟩
  | _ :: _, v :: _, .cons h hs => by
    obtain ⟨y, hy, hlift⟩ := numToIR_lift h
    obtain ⟨ys, hys, hrest⟩ := liftList_numToIR hs
    refine ⟨y :: ys, by simp [List.mapM_cons, hy, hys], fun r => ?_⟩
    simp only [List.map_cons, ValTy.liftList, List.cons_append, hlift, hrest, Option.map_some]

/-- Lowering checks and gives back the arguments. -/
theorem checkLower_numToIR {ps : List NumType} {a : List Val}
    (h : List.Forall₂ ScalarType.HasVal (ps.map .num) a) :
    ∃ xs, checkLower (ps.map numVT) (a.map numToIR) = some xs ∧ xs.map ofFlat = a :=
  ⟨lowerArgs (ps.map numVT) (a.map numToIR),
    by simp only [checkLower, checkList_numToIR h, ite_true], lowerList_numToIR h⟩

/-- Lifting numeric results gives their IR images. -/
theorem liftArgs_numToIR {rs : List NumType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal (rs.map .num) vs) :
    ∃ ys, vs.mapM toFlat? = some ys ∧ liftArgs (rs.map numVT) ys = some (vs.map numToIR) := by
  obtain ⟨ys, hys, hlift⟩ := liftList_numToIR h
  refine ⟨ys, hys, ?_⟩
  have h₀ := hlift []
  rw [List.append_nil] at h₀
  simp only [liftArgs, h₀]

theorem map_toRefVal_numToIR :
    ∀ {ps : List NumType} {a : List Val}, List.Forall₂ ScalarType.HasVal (ps.map .num) a →
      (a.map numToIR).map toRefVal = a.map wrapVal
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, toRefVal_numToIR h, map_toRefVal_numToIR hs]

/-! ## The wrapping component -/

theorem flatList_numVT : ∀ ps : List NumType, ValTy.flatList (ps.map numVT) = ps
  | [] => rfl
  | t :: ps => by
    have ht : (numVT t).flat = [t] := by rcases t with (_ | _) | (_ | _) <;> rfl
    simp only [List.map_cons, ValTy.flatList, ht, flatList_numVT ps, List.singleton_append]

theorem irTys_numVT : ∀ ps : List NumType, irTys (ps.map numVT) = ps.map wrapNum
  | [] => rfl
  | t :: ps => by
    have ht : irTy (numVT t) = wrapNum t := by rcases t with (_ | _) | (_ | _) <;> rfl
    simp only [List.map_cons, irTys, ht, irTys_numVT ps]

/-- The IR function type of a wrapped core function type is its wrapping. -/
theorem irFn_liftTy (ft : CoreFuncTy) : irFn (liftTy ft) = wrapFn ft := by
  simp only [irFn, liftTy, wrapFn, irTys_numVT]

/-- An export of the wrapping component. -/
theorem wrapSimple_getElem (m : NumModule) (j : Fin m.exports.length) :
    (wrapSimple m).exports[wrapExp m j] =
      ⟨m.exports[j].1, liftTy m.exports[j].2, j⟩ := by
  simp [wrapSimple, wrapExp]

/-- **The wrapping component is in the soundness fragment** (given distinct export names). -/
theorem wrapSimple_good (m : NumModule) (hn : (m.exports.map Prod.fst).Nodup) :
    (wrapSimple m).Good where
  names := by
    have he : ((wrapSimple m).exports.map (·.name)) = m.exports.map Prod.fst :=
      List.ext_getElem (by simp [wrapSimple]) fun i _ _ => by simp [wrapSimple]
    rw [he]
    exact hn
  core := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.exists_of_mem_mapIdx hx
    refine ⟨m.exports[k].1, ?_⟩
    show m.exports[k]? = some (m.exports[k].1, ⟨ValTy.flatList (m.exports[k].2.params.map numVT),
      ValTy.flatList (m.exports[k].2.results.map numVT)⟩)
    rw [flatList_numVT, flatList_numVT, List.getElem?_eq_getElem hk]

/-- **The interface of the wrapping component is the image interface.** -/
theorem cface_wrapSimple (m : NumModule) :
    cface (wrapSimple m).toComp = (numIface m).map wrapFn := by
  have he : (cface (wrapSimple m).toComp).exports = ((numIface m).map wrapFn).exports :=
    List.ext_getElem (by simp [cface, Simple.toComp, wrapSimple, numIface])
      fun i _ _ => by simp [cface, Simple.toComp, wrapSimple, numIface, irFn_liftTy]
  exact congrArg₂ Iface.mk rfl he

/-! ## Module traces -/

/-- Reading back an event recast to the source interface. -/
theorem mapP_unmapIdx {Ty Ty' A R : Type} (τ : Ty → Ty') {X : Iface Ty}
    (e : Event A R (X.map τ)) : Event.mapP τ id id (Event.unmapIdx τ e) = e := by
  rcases e with (⟨i, a⟩ | ⟨i, r⟩) | (⟨i, a⟩ | ⟨i, r⟩) <;> rfl

/-- A two-event trace of the restricted semantics is a trace of the original one. -/
theorem restrict_pair {Ty Ty' A R : Type} {S : Semantics Ty' A R} {τ : Ty → Ty'} {X : Iface Ty}
    {p : (S.restrict τ).Prog X} {x y : Event A R X} (h : [x, y] ∈ (S.restrict τ).traces p) :
    [Event.mapP τ id id x, Event.mapP τ id id y] ∈ S.traces p := by
  obtain ⟨u, hu, hmap⟩ := h
  have hu' : u = [Event.mapP τ id id x, Event.mapP τ id id y] := by
    calc u = (u.map (Event.unmapIdx τ)).map (Event.mapP τ id id) := by
          simp only [List.map_map, Function.comp_def, mapP_unmapIdx, List.map_id']
      _ = _ := by rw [hmap]; rfl
  exact hu' ▸ hu

/-- The arguments of an export call in a trace of a Core 3.0 instance are typed. -/
theorem typed_of_call_mem {P : Profile} {X : WIface} {p : WasmProg X} {j : X.Exp}
    {a : List Val} {b : Silmaril.Wasm.Behaviour Val}
    (h : [Event.call j a, Event.ret j b] ∈ (wasmSem P).traces p) :
    ∃ a' : Typed (X.exports.get j).params, a'.1 = a := by
  obtain ⟨t, -, hmap⟩ := h
  obtain ⟨m₁, -, -, h₁, -⟩ := map_eq_pair hmap
  rcases m₁ with (e | e) | (⟨⟨j', a'⟩⟩ | ⟨f, w⟩)
  · cases h₁
  · cases h₁
  · simp only [moveEvent, Sum.map_inr, evOf, Event.call, Sum.inr.injEq, SideEv.ask.injEq] at h₁
    obtain ⟨rfl, ha⟩ := h₁
    exact ⟨a', ha⟩
  · cases h₁

/-- The outcome of a Core result, as `coreOut` reports it. -/
def resOut : Result → Option (List Silmaril.Wasm.Component.Flat)
  | .values vs => vs.mapM toFlat?
  | _ => none

/-- **Wrapping and the canonical ABI agree on outcomes.** The canonical-ABI outcome of a typed
Core result of a wrapped export is the wrapping of the result's behaviour. -/
theorem liftOutcome_resOut {ft : CoreFuncTy} {F : FnType} (hF : F = fnOf ft) {r : Result}
    {w : Answer F} (hw : Answer.ofResult? F r = some w) :
    liftOutcome (liftTy ft) (resOut r) = wrapOut w.toBehaviour := by
  subst hF
  have hbeh : w.toBehaviour = r.toBehaviour := by
    rw [Answer.toBehaviour, Answer.toResult_of_ofResult? hw]
  rw [hbeh]
  cases r with
  | values vs =>
    have hty : List.Forall₂ ScalarType.HasVal (ft.results.map .num) vs := by
      simp only [Answer.ofResult?] at hw
      split at hw
      · next h => exact h
      · cases hw
    obtain ⟨ys, hys, hlift⟩ := liftArgs_numToIR hty
    simp only [resOut, hys, liftOutcome, liftTy, hlift, map_toRefVal_numToIR hty]
    rfl
  | trap => rfl
  | throw _ => rfl

/-! ## Soundness of wrapping -/

/-- The type of export `j` of the module program. -/
theorem numProg_export_ty (m : NumModule) (j : Fin m.exports.length) :
    ((numIface m).map fnOf).exports.get (Iface.expTo fnOf _ (numExp m j)) =
      fnOf m.exports[j].2 := by
  rw [Iface.get_exports_map]
  simp [numIface, numExp]

/-- **Wrapping is sound w.r.t. the canonical-ABI specification.** A terminating first call of
export `j` of a Core 3.0 instance `I` of `m` (at any profile) is, wrapped, an outcome of the
canonical-ABI specification of the wrapping component on the IR images of the arguments. -/
theorem wrap_spec (P : Profile) (m : NumModule) {I : ScalarInstance} (hI : m.IsInst I)
    (j : Fin m.exports.length) (a : List Val) (b : Silmaril.Wasm.Behaviour Val)
    (ht : [Event.call (numExp m j) a, Event.ret (numExp m j) b] ∈
      (numSem P).traces (numProg P m I)) :
    wrapOut b ∈ exportSpec P (wrapSimple m) (wrapSimple m).exports[wrapExp m j]
      (a.map numToIR) := by
  have hw := restrict_pair ht
  obtain ⟨a', ha'⟩ := typed_of_call_mem hw
  subst ha'
  obtain ⟨d, r, w, hrun, hcode, hres, hwb⟩ := (call_ret_mem_iff _ _ a' b).1 hw
  have hty : List.Forall₂ ScalarType.HasVal (m.exports[j].2.params.map .num) a'.1 :=
    (congrArg (fun F : FnType => List.Forall₂ ScalarType.HasVal F.params a'.1)
      (numProg_export_ty m j)).mp a'.2
  obtain ⟨xs, hcl, hxs⟩ := checkLower_numToIR hty
  have hcore : resOut r ∈ coreOut P m j xs := ⟨I, hI, d, r, hxs ▸ hrun, hcode, rfl⟩
  have hout : wrapOut b = liftOutcome (liftTy m.exports[j].2) (resOut r) := by
    rw [liftOutcome_resOut (numProg_export_ty m j) hres, hwb]
  have hcl' : checkLower (liftTy m.exports[j].2).params (a'.1.map numToIR) = some xs := hcl
  rw [wrapSimple_getElem]
  simp only [exportSpec, hcl']
  exact .inl ⟨resOut r, hcore, hout⟩

/-- The arguments of a call in a module trace are typed by the export's parameters. -/
theorem numArgs_typed {P : Profile} {m : NumModule} {I : ScalarInstance}
    {j : Fin m.exports.length} {a : List Val} {b : Silmaril.Wasm.Behaviour Val}
    (ht : [Event.call (numExp m j) a, Event.ret (numExp m j) b] ∈
      (numSem P).traces (numProg P m I)) :
    List.Forall₂ ScalarType.HasVal (m.exports[j].2.params.map .num) a := by
  obtain ⟨a', ha'⟩ := typed_of_call_mem (restrict_pair ht)
  subst ha'
  exact (congrArg (fun F : FnType => List.Forall₂ ScalarType.HasVal F.params a'.1)
    (numProg_export_ty m j)).mp a'.2

/-- Wrapped behaviours other than divergence are observable by the IR. -/
theorem terminates_wrapOut {b : Silmaril.Wasm.Behaviour Val} (hb : b ≠ .diverges) :
    Terminates (wrapOut b) := by
  cases b with
  | returns _ => trivial
  | traps => trivial
  | throws _ => trivial
  | diverges => exact absurd rfl hb

/-- **Soundness of wrapping w.r.t. the boundary adapters.** Every terminating first call of a
Core 3.0 instance of `m` (at any profile), translated by the change of base of `wrapSem`, is a
trace of the wrapping component in Silmaril's IR over `modSem P`, whose boundary is the
canonical-ABI `canon lift` adapters. -/
theorem wrap_sound (P : Profile) (m : NumModule) (hn : (m.exports.map Prod.fst).Nodup)
    {I : ScalarInstance} (hI : m.IsInst I) (j : Fin m.exports.length) (a : List Val)
    (b : Silmaril.Wasm.Behaviour Val) (hb : b ≠ .diverges)
    (ht : [Event.call (numExp m j) a, Event.ret (numExp m j) b] ∈
      (numSem P).traces (numProg P m I)) :
    [Event.call (Simple.expIdx (wrapSimple m) (wrapExp m j)) (a.map wrapVal),
      Event.ret (Simple.expIdx (wrapSimple m) (wrapExp m j)) (wrapOut b)] ∈
      (irSem (modSem P)).traces (Simple.irProg (wrapSimple m)) := by
  have hspec := wrap_spec P m hI j a b ht
  have hir := Simple.ir_of_spec P (wrapSimple m) (wrapSimple_good m hn) (wrapExp m j)
    (a.map numToIR) _ hspec (terminates_wrapOut hb)
  rw [map_toRefVal_numToIR (numArgs_typed ht)] at hir
  exact hir

/-- **Component contracts verified on the wrapping component hold of the module**: for every
terminating first call of a Core 3.0 instance of `m`, the wrapped arguments and outcome satisfy
the contract. -/
theorem wrap_contract (P : Profile) (m : NumModule) (hn : (m.exports.map Prod.fst).Nodup)
    {I : ScalarInstance} (hI : m.IsInst I) (j : Fin m.exports.length)
    {pre : List RVal → Prop} {post : List RVal → Outcome → Prop}
    (hM : Models (contract CFn (List RVal) Outcome) (irSem (modSem P))
      (Simple.irProg (wrapSimple m)) ⟨Simple.expIdx (wrapSimple m) (wrapExp m j), pre, post⟩)
    (a : List Val) (b : Silmaril.Wasm.Behaviour Val) (hb : b ≠ .diverges)
    (ht : [Event.call (numExp m j) a, Event.ret (numExp m j) b] ∈
      (numSem P).traces (numProg P m I))
    (hpre : pre (a.map wrapVal)) : post (a.map wrapVal) (wrapOut b) := by
  have htr := (models_iff _ _ _ _).1 hM _ (wrap_sound P m hn hI j a b hb ht)
  exact (contract_pair_iff _ _ _ _).1 htr rfl hpre

end Silmaril.Wasm.Spec
