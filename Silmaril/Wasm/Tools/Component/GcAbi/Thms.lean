module

public import Silmaril.Wasm.Tools.Component.GcAbi.Defs
import Silmaril.Wasm.Component.Reference.Validation.Laws.Thms

/-!
# Soundness of the 🛸 GC canonical ABI checks

* `ok_sound`: the executable `lower_gc` is sound for `Lowers`;
* `funcOk_sound`: the function check is sound for `FuncLowers`;
* `liftProblem_sound`, `lowerCheck_sound`: the checks of a 🛸 `lift`/`lower` give `LiftOk` /
  `LowerOk`;
* `gDefs?_sound`, `check?_sound`: the fold is sound for `GValidDefs`, the validator for
  `GValid`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.GcAbi

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Validation (Ty DefType CValType CStorageType CCompType CHeapType)

variable {enc : ABI.StringEncoding}

theorem primOk_sound {p : WIT.Primitive} {s : Slot} (h : primOk enc p s = true) :
    Lowers enc (.prim p) s := by
  unfold primOk at h
  split at h
  · next k _ hk => exact .small hk (of_decide_eq_true h)
  · next n hk hn => exact .num hn (of_decide_eq_true h)
  · split at h
    · rename_i hc _ _
      exact .string ((of_decide_eq_true h) ▸ hc)
    · cases h

theorem onArray_true {c : Option CCompType} {k : CStorageType → Bool} (h : onArray c k = true) :
    ∃ m st, c = some (.array (.field m st)) ∧ k st = true := by
  unfold onArray at h
  split at h
  · next m st => exact ⟨m, st, rfl, h⟩
  · cases h

theorem onStruct_true {c : Option CCompType} {k : List (Silmaril.Wasm.Validation.Ty .field) → Bool}
    (h : onStruct c k = true) : ∃ cs, c = some (.struct cs) ∧ k cs.toList = true := by
  unfold onStruct at h
  split at h
  · next cs => exact ⟨cs, rfl, h⟩
  · cases h

mutual
theorem ok_sound : ∀ (t : VT) (s : Slot), ok enc t s = true → Lowers enc t s
  | .prim p, s, h => primOk_sound (by simpa only [ok] using h)
  | .list e, s, h =>
    have ⟨_, _, hc, hk⟩ := onArray_true (by simpa only [ok] using h)
    .list hc (ok_sound e _ hk)
  | .fixedList e _, s, h =>
    have ⟨_, _, hc, hk⟩ := onArray_true (by simpa only [ok] using h)
    .fixedList hc (ok_sound e _ hk)
  | .record fs, s, h =>
    have ⟨_, hc, hk⟩ := onStruct_true (by simpa only [ok] using h)
    .record hc (recOk_sound fs _ hk)
  | .tuple ts, s, h =>
    have ⟨_, hc, hk⟩ := onStruct_true (by simpa only [ok] using h)
    .tuple hc (tupOk_sound ts _ hk)
  | .variant _, s, h => .sum trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .option _, s, h => .sum trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .result _ _, s, h => .sum trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .enum _, s, h => .bits trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .flags _, s, h => .bits trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .own _, s, h => .handle trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .borrow _, s, h => .handle trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .future _, s, h => .handle trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .stream _, s, h => .handle trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .errorContext, s, h => .handle trivial (of_decide_eq_true (by simpa only [ok] using h))
  | .map _ _, s, h => by simp only [ok] at h; cases h
  | .ref r, _, _ => nomatch r

theorem recOk_sound : ∀ (fs : List (String × VT)) (cs : List (Silmaril.Wasm.Validation.Ty .field)),
    recOk enc fs cs = true → Fields enc (fs.map (·.2)) cs
  | [], [], _ => .nil
  | (_, t) :: fs, .field _ _ :: cs, h =>
    have h' := Bool.and_eq_true_iff.mp (by simpa only [recOk] using h)
    .cons (ok_sound t _ h'.1) (recOk_sound fs cs h'.2)
  | [], _ :: _, h => by simp only [recOk] at h; cases h
  | _ :: _, [], h => by simp only [recOk] at h; cases h

theorem tupOk_sound : ∀ (ts : List VT) (cs : List (Silmaril.Wasm.Validation.Ty .field)),
    tupOk enc ts cs = true → Fields enc ts cs
  | [], [], _ => .nil
  | t :: ts, .field _ _ :: cs, h =>
    have h' := Bool.and_eq_true_iff.mp (by simpa only [tupOk] using h)
    .cons (ok_sound t _ h'.1) (tupOk_sound ts cs h'.2)
  | [], _ :: _, h => by simp only [tupOk] at h; cases h
  | _ :: _, [], h => by simp only [tupOk] at h; cases h
end

theorem resultOk_sound {r : Option VT} {rs : List CValType}
    (h : (match r, rs with
      | none, [] => true
      | some t, [x] => ok enc t (.arg x)
      | _, _ => false) = true) : ResultLowers enc r rs := by
  split at h
  · exact trivial
  · exact ok_sound _ _ h
  · cases h

theorem funcOk_sound {ft : FT} {d : DefType} (h : funcOk enc ft d = true) :
    FuncLowers enc ft d := by
  unfold funcOk at h
  split at h
  · next ps rs hsig =>
    have h1 := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp h1.1
    have hall := List.all_eq_true.mp h2.2
    exact ⟨⟨ps, rs, hsig, beq_iff_eq.mp h2.1, fun p hp => ok_sound _ _ (hall p hp),
      resultOk_sound h1.2⟩⟩
  · cases h

variable {feat : Features} {Γ : Ctx Core3Extern} {os : List BinaryGC.CanonOpt} {ft : FT}

theorem postReturn_sound {d : DefType} {p : Option Nat}
    (h : (match p with
      | none => none
      | some p =>
        match funcSig? d, (coreFuncDef? Γ p).bind funcSig? with
        | some (_, rs), some pr =>
          if pr = (rs, []) then none
          else some "canonical option `post-return` uses a core function with an incorrect \
            signature"
        | _, _ => some "canonical option `post-return` uses a core function with an incorrect \
            signature") = (none : Option String)) :
    OptAll p fun p => ∃ dp rs, funcSig? d = some (dp, rs) ∧
      (coreFuncDef? Γ p).bind funcSig? = some (rs, []) := by
  split at h
  · exact trivial
  · split at h
    · next dp rs pr hd hp =>
      split at h
      · next he => exact ⟨dp, rs, hd, hp.trans (congrArg some he)⟩
      · cases h
    · cases h

theorem liftCallee_sound {callee : Nat}
    (h : (match coreFuncDef? Γ callee with
      | none => some s!"core function index {callee} out of bounds"
      | some d =>
        if !funcOk (CanonOpts.encoding (v0 os)) ft d then
          some "lowered component function type does not match the core function type of the \
            `gc` lifting"
        else match CanonOpts.postReturnIdx? (v0 os) with
          | none => none
          | some p =>
            match funcSig? d, (coreFuncDef? Γ p).bind funcSig? with
            | some (_, rs), some pr =>
              if pr = (rs, []) then none
              else some "canonical option `post-return` uses a core function with an incorrect \
                signature"
            | _, _ => some "canonical option `post-return` uses a core function with an \
                incorrect signature") = none) :
    ∃ d, coreFuncDef? Γ callee = some d ∧ FuncLowers (CanonOpts.encoding (v0 os)) ft d ∧
      OptAll (CanonOpts.postReturnIdx? (v0 os)) fun p => ∃ dp rs,
        funcSig? d = some (dp, rs) ∧ (coreFuncDef? Γ p).bind funcSig? = some (rs, []) := by
  split at h
  · cases h
  · next d hd =>
    split at h
    · cases h
    · next hf =>
      have hok : funcOk (CanonOpts.encoding (v0 os)) ft d = true := by simpa using hf
      exact ⟨d, hd, funcOk_sound hok, postReturn_sound h⟩

/-- **The checks of a 🛸 `lift`** give `LiftOk`. -/
theorem liftProblem_sound {callee : Nat} (h : liftProblem feat Γ callee os ft = none) :
    LiftOk feat Γ callee os ft := by
  unfold liftProblem at h
  split at h
  · cases h
  · next hgc =>
    split at h
    · cases h
    · next hct =>
      split at h
      · cases h
      · next hv => exact ⟨Classical.not_not.mp hgc, Classical.not_not.mp hct,
          Classical.not_not.mp hv, liftCallee_sound h⟩

theorem lowerType_sound {i : Nat} {x : Core3Extern}
    (h : (match coreTypeFunc? Γ i with
      | none => .error "canonical option `core type` must reference a core function type"
      | some d =>
        if ¬ ValidCanonOpts feat V3 Γ .lower ft (v0 os) then
          .error (CanonOpts.explainCanonOpts feat V3 Γ .lower ft (v0 os)).message
        else if !funcOk (CanonOpts.encoding (v0 os)) ft d then
          .error "declared `core-type` does not match the GC lowering of the component \
            function type"
        else match core3Ext? (.func d) with
          | some x => .ok x
          | none => .error "declared `core-type` is not a valid core function type") =
      (Except.ok x : Except String Core3Extern)) :
    ValidCanonOpts feat V3 Γ .lower ft (v0 os) ∧ ∃ d, coreTypeFunc? Γ i = some d ∧
      FuncLowers (CanonOpts.encoding (v0 os)) ft d ∧ core3Ext? (.func d) = some x := by
  split at h
  · cases h
  · next d hd =>
    split at h
    · cases h
    · next hv =>
      split at h
      · cases h
      · next hf =>
        split at h
        · next y hy => cases h; exact ⟨Classical.not_not.mp hv, d, hd, funcOk_sound (by simpa using hf), hy⟩
        · cases h

/-- **The checks of a 🛸 `lower`** give `LowerOk` with the new core function's type. -/
theorem lowerCheck_sound {x : Core3Extern} (h : lowerCheck feat Γ os ft = .ok x) :
    LowerOk feat Γ os ft x := by
  unfold lowerCheck at h
  split at h
  · cases h
  · next hgc =>
    split at h
    · cases h
    · next i hi =>
      have ⟨hv, d, hd, hf, hx⟩ := lowerType_sound h
      exact ⟨Classical.not_not.mp hgc, ⟨i, d, hi, hd, hf, hx⟩, hv⟩
    · cases h

theorem gLift_sound {sc : Scopes Core3Extern} {s s' : DefState Core3Extern} {callee t : Nat}
    (h : gDef? feat sc s (.lift callee os t) = .ok s') : GValidDef feat sc s (.lift callee os t) s' := by
  simp only [gDef?] at h
  split at h
  · next ft hty =>
    split at h
    · cases h
    · next hp => cases h; exact .lift hty (liftProblem_sound hp)
  · cases h

theorem gLower_sound {sc : Scopes Core3Extern} {s s' : DefState Core3Extern} {f : Nat}
    (h : gDef? feat sc s (.lower f os) = .ok s') : GValidDef feat sc s (.lower f os) s' := by
  simp only [gDef?] at h
  split at h
  · next ft hty =>
    split at h
    · cases h
    · next x hx => cases h; exact .lower hty (lowerCheck_sound hx)
  · cases h

mutual
/-- **Soundness of one step of the fold.** -/
theorem gDef?_sound : ∀ (d : GDef) {sc : Scopes Core3Extern} {s s' : DefState Core3Extern},
    gDef? feat sc s d = .ok s' → GValidDef feat sc s d s'
  | .ref d, sc, s, s', h => by
    simp only [gDef?] at h
    cases hs : step feat sc s d with
    | error e => rw [hs] at h; cases h
    | ok s1 => rw [hs] at h; cases h; exact .ref (checkDef?_sound d hs)
  | .lift _ _ _, _, _, _, h => gLift_sound h
  | .lower _ _, _, _, _, h => gLower_sound h
  | .comp ds, sc, s, s', h => by
    simp only [gDef?] at h
    split at h
    · cases h
    · next ch hch =>
      split at h
      · next hd => cases h; exact .comp (gDefs?_sound ds hch) hd
      · cases h

/-- **Soundness of the fold.** -/
theorem gDefs?_sound : ∀ (ds : List GDef) {sc : Scopes Core3Extern} {s s' : DefState Core3Extern},
    gDefs? feat sc s ds = .ok s' → GValidDefs feat sc s ds s'
  | [], _, _, _, h => by cases h; exact .nil
  | d :: ds, sc, s, s', h => by
    simp only [gDefs?] at h
    split at h
    · next s1 hs1 => exact .cons (gDef?_sound d hs1) (gDefs?_sound ds h)
    · cases h
end

/-- **Soundness of the validator** of components with 🛸 definitions. -/
theorem check?_sound {ds : List GDef} {ct : Types.ComponentType Nat Core3Extern}
    (h : check? feat ds = .ok ct) : GValid feat ds ct := by
  unfold check? at h
  split at h
  · cases h
  · next s hs =>
    split at h
    · next hd => cases h; exact ⟨s, gDefs?_sound ds hs, hd, rfl⟩
    · cases h

end Silmaril.Wasm.Tools.Component.GcAbi
