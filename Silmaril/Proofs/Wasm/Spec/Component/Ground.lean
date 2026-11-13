module

public import Silmaril.Wasm.Spec.Component.Ground.Defs
public import Silmaril.Wasm.Spec.Temporal.Thms
public import Silmaril.Wasm.Component.Reference.Sound.Thms

@[expose] public section

/-!
# Component specification institutions: grounding proofs

* positions of traces (`everyPos_nil`, `everyPos_cons`, `everyPos_single`, `everyPos_pair`);
* plays of the IR as traces (`irTraces_call_ret`, `irTraces_call_trap`);
* the reference semantics: `refSem_retPost_iff`, `refSem_contract_iff`;
* simple components: specification outcomes are IR traces (`Simple.ir_of_spec`, from
  `Reference.specToIR`), hence contracts and return postconditions verified on the IR hold of
  the canonical-ABI specification over Core 3.0 (`Simple.contract_spec`, `Simple.retPost_spec`)
  and of the reference machine (`Simple.contract_ref`, `Simple.retPost_ref`), unconditionally
  within the flat arities (`Simple.refSound_of_arity`, from the proved
  `Reference.refToSpec_of_arity`);
* the IR's types are at most aggregates (`irTy_level`, `cface_level`).

Summary in `Silmaril.Wasm.Spec.Component.IR.Thms` and `Silmaril.Wasm.Spec.Component.Ref.Thms`.
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Games
open Silmaril.Wasm.Component (Payload sigN Comp CoreSem CoreModule ValTy)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-! ## Positions of short traces -/

theorem everyPos_nil {α : Type} {P : List α → α → Prop} : EveryPos P [] ↔ True :=
  ⟨fun _ => trivial, fun _ h e r hl => by simp at hl⟩

/-- An action invariant on `x :: l`: at the head, and on `l` with `x` prepended to histories. -/
theorem everyPos_cons {α : Type} {P : List α → α → Prop} {x : α} {l : List α} :
    EveryPos P (x :: l) ↔ P [] x ∧ EveryPos (fun h e => P (x :: h) e) l := by
  constructor
  · intro h
    exact ⟨h [] x l rfl, fun h' e r hl => h (x :: h') e r (by rw [hl]; rfl)⟩
  · rintro ⟨h0, hl⟩ (_ | ⟨y, h'⟩) e r heq
    · have hx : x = e := (List.cons.inj heq).1
      exact hx ▸ h0
    · obtain ⟨rfl, hl'⟩ := List.cons.inj heq
      exact hl h' e r hl'

theorem everyPos_single {α : Type} {P : List α → α → Prop} {x : α} :
    EveryPos P [x] ↔ P [] x := by
  rw [everyPos_iff_get]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h k hk
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact h

theorem everyPos_pair {α : Type} {P : List α → α → Prop} {x y : α} :
    EveryPos P [x, y] ↔ P [] x ∧ P [x] y := by
  rw [everyPos_iff_get]
  constructor
  · intro h
    exact ⟨h 0 (by simp), h 1 (by simp)⟩
  · rintro ⟨h0, h1⟩ k hk
    rcases k with _ | _ | k
    · exact h0
    · exact h1
    · have hk2 : k + 1 + 1 < 2 := hk
      omega

/-! ## Plays of the IR as traces -/

variable {n k : ℕ} {X : CIface}

/-- A returning export call of the IR is a trace. -/
theorem irTraces_call_ret (hi : n = X.imports.length) (he : k = X.exports.length)
    (σ : Strategy (sigN n) (sigN k)) (j : Fin k) (vs ws : List Silmaril.Wasm.Component.Val)
    (h : [.inr (.ask (j, .vals vs)), .inr (.ans (j, .vals vs) (some (.vals ws)))] ∈ σ) :
    [Event.call (Fin.cast he j) (vs.map toRefVal),
      Event.ret (Fin.cast he j) (.returns (some (ws.map toRefVal)))] ∈ irTraces hi he σ :=
  ⟨_, h, rfl⟩

/-- A trapping export call of the IR is a trace. -/
theorem irTraces_call_trap (hi : n = X.imports.length) (he : k = X.exports.length)
    (σ : Strategy (sigN n) (sigN k)) (j : Fin k) (vs : List Silmaril.Wasm.Component.Val)
    (h : [.inr (.ask (j, .vals vs)), .inr (.ans (j, .vals vs) none)] ∈ σ) :
    [Event.call (Fin.cast he j) (vs.map toRefVal), Event.ret (Fin.cast he j) .traps] ∈
      irTraces hi he σ :=
  ⟨_, h, rfl⟩

/-! ## The reference semantics -/

section Ref

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}
  (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)

/-- The return events of a trace of a reference component. -/
theorem mem_refTraces_ret {p : RefProg E X} {t : List (CEvent X)}
    (ht : t ∈ refTraces prof h σ0 p) {j : X.Exp} {b : Outcome} (hb : Event.ret j b ∈ t) :
    ∃ a, b ∈ exportBehaviours prof h σ0 p.comp p.args (p.names j) a ∧
      t = [Event.call j a, Event.ret j b] := by
  rcases ht with rfl | ⟨j', a, rfl⟩ | ⟨j', a, b', hb', rfl⟩
  · simp at hb
  · simp at hb
  · have he : j = j' ∧ b = b' := by simpa using hb
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨a, hb', rfl⟩

/-- **Return postconditions of the reference semantics are statements about
`exportBehaviours`.** -/
theorem refSem_retPost_iff (p : RefProg E X) (j : X.Exp) (Q : Outcome → Prop) :
    Models (retPost CFn (List RVal) Outcome) (refSem prof h σ0) p ⟨j, Q⟩ ↔
      ∀ a b, b ∈ exportBehaviours prof h σ0 p.comp p.args (p.names j) a → Q b := by
  rw [models_iff]
  constructor
  · intro hM a b hb
    exact hM _ (.inr (.inr ⟨j, a, b, hb, rfl⟩)) b (by simp)
  · intro hQ t ht b hb
    obtain ⟨a, hb', -⟩ := mem_refTraces_ret prof h σ0 ht hb
    exact hQ a b hb'

/-- The contract position predicate on a call followed by its return. -/
theorem contract_pair_iff (φ : Contract.Fm (List RVal) Outcome X) (j : X.Exp) (a : List RVal)
    (b : Outcome) :
    EveryPos (Contract.pos φ) [Event.call j a, Event.ret j b] ↔
      (j = φ.exp → φ.pre a → φ.post a b) := by
  rw [everyPos_pair]
  constructor
  · rintro ⟨-, h1⟩ rfl hpre
    exact h1 b rfl a rfl hpre
  · intro hj
    refine ⟨fun r hr => by simp at hr, fun r hr a' ha' hpre => ?_⟩
    have hjr : j = φ.exp ∧ b = r := by simpa using hr
    obtain ⟨rfl, rfl⟩ := hjr
    have ha : a = a' := by simpa [pendingCall, callStep] using ha'
    subst ha
    exact hj rfl hpre

/-- **Contracts of the reference semantics are statements about `exportBehaviours`.** -/
theorem refSem_contract_iff (p : RefProg E X) (φ : Contract.Fm (List RVal) Outcome X) :
    Models (contract CFn (List RVal) Outcome) (refSem prof h σ0) p φ ↔
      ∀ a b, b ∈ exportBehaviours prof h σ0 p.comp p.args (p.names φ.exp) a → φ.pre a →
        φ.post a b := by
  rw [models_iff]
  constructor
  · intro hM a b hb
    exact (contract_pair_iff φ φ.exp a b).1 (hM _ (.inr (.inr ⟨φ.exp, a, b, hb, rfl⟩))) rfl
  · rintro hQ t (rfl | ⟨j, a, rfl⟩ | ⟨j, a, b, hb, rfl⟩)
    · intro h e r hr
      simp at hr
    · exact everyPos_single.2 fun r hr => by simp at hr
    · refine (contract_pair_iff φ j a b).2 ?_
      rintro rfl
      exact hQ a b hb

end Ref

/-! ## Simple components: grounding in the reference -/

namespace Simple

/-- **Terminating specification outcomes are IR traces.** -/
theorem ir_of_spec (P : Profile) (c : Simple) (hc : c.Good) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (b : Outcome) (hb : b ∈ exportSpec P c c.exports[j] vs)
    (ht : Terminates b) :
    [Event.call (Simple.expIdx c j) (vs.map toRefVal), Event.ret (Simple.expIdx c j) b] ∈
      (irSem (modSem P)).traces (Simple.irProg c) := by
  have hobs := specToIR P c hc j vs b hb
  match b, ht, hobs with
  | .returns (some _), _, ⟨ws, hws, hplay⟩ =>
    rw [hws]
    exact irTraces_call_ret (Simple.irProg c).hi (Simple.irProg c).he _ _ vs ws hplay
  | .traps, _, hplay =>
    exact irTraces_call_trap (Simple.irProg c).hi (Simple.irProg c).he _ _ vs hplay

/-- **Contracts verified on the IR hold of the canonical-ABI specification over Core 3.0**, for
terminating outcomes, at every profile. -/
theorem contract_spec (P : Profile) (c : Simple) (hc : c.Good) (j : Fin c.exports.length)
    {pre : List RVal → Prop} {post : List RVal → Outcome → Prop}
    (hM : Models (contract CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg c)
      ⟨Simple.expIdx c j, pre, post⟩)
    (vs : List Silmaril.Wasm.Component.Val) (b : Outcome) (hb : b ∈ exportSpec P c c.exports[j] vs)
    (ht : Terminates b) (hpre : pre (vs.map toRefVal)) : post (vs.map toRefVal) b := by
  have htr := (models_iff _ _ _ _).1 hM _ (Simple.ir_of_spec P c hc j vs b hb ht)
  exact (contract_pair_iff ⟨Simple.expIdx c j, pre, post⟩ _ _ b).1 htr rfl hpre

/-- **Return postconditions verified on the IR hold of the canonical-ABI specification.** -/
theorem retPost_spec (P : Profile) (c : Simple) (hc : c.Good) (j : Fin c.exports.length)
    {Q : Outcome → Prop}
    (hM : Models (retPost CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg c)
      ⟨Simple.expIdx c j, Q⟩)
    (vs : List Silmaril.Wasm.Component.Val) (b : Outcome) (hb : b ∈ exportSpec P c c.exports[j] vs)
    (ht : Terminates b) : Q b :=
  (models_iff _ _ _ _).1 hM _ (Simple.ir_of_spec P c hc j vs b hb ht) b (by simp)

/-- **The reference-machine half holds unconditionally within the flat arities**
(`Reference.refToSpec_of_arity`, proved; no validity hypothesis). -/
theorem refSound_of_arity (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) {c : Simple}
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) : RefSound P prof c :=
  refToSpec_of_arity P prof c hc hf hi ha

/-- Contracts verified on the IR hold of the reference machine, given the reference-machine
half `RefSound` (for any component for which it is known). -/
theorem contract_of_refSound {P : Profile} {prof : Silmaril.Wasm.Component.ProfileKind}
    {c : Simple} (hR : RefSound P prof c) (hc : c.Good) (j : Fin c.exports.length)
    {pre : List RVal → Prop} {post : List RVal → Outcome → Prop}
    (hM : Models (contract CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg c)
      ⟨Simple.expIdx c j, pre, post⟩) :
    Models (contract CFn (List RVal) Outcome) (refSem prof (refHost P) ()) (Simple.refProg P c)
      ⟨Simple.expIdx c j, Simple.refPre c j pre, fun a b => Terminates b → post a b⟩ := by
  rw [refSem_contract_iff]
  rintro a b hb ⟨vs, rfl, hty, hpre⟩ ht
  have hspec : b ∈ exportSpec P c c.exports[j] vs :=
    hR _ (List.getElem_mem j.isLt) vs hty hb
  exact Simple.contract_spec P c hc j hM vs b hspec ht hpre

/-- **Contracts verified on the IR hold of the reference machine** over `core3P P`, at every
profile and component choice profile, for terminating outcomes of well-typed calls, for every
simple component within the flat arities (unconditional, through `refSound_of_arity`). -/
theorem contract_ref {P : Profile} {prof : Silmaril.Wasm.Component.ProfileKind} {c : Simple}
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    {pre : List RVal → Prop} {post : List RVal → Outcome → Prop}
    (hM : Models (contract CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg c)
      ⟨Simple.expIdx c j, pre, post⟩) :
    Models (contract CFn (List RVal) Outcome) (refSem prof (refHost P) ()) (Simple.refProg P c)
      ⟨Simple.expIdx c j, Simple.refPre c j pre, fun a b => Terminates b → post a b⟩ :=
  contract_of_refSound (refSound_of_arity P prof hc hf hi ha) hc j hM

/-- Return postconditions verified on the IR hold of the reference machine, given
`RefSound`. -/
theorem retPost_of_refSound {P : Profile} {prof : Silmaril.Wasm.Component.ProfileKind}
    {c : Simple} (hR : RefSound P prof c) (hc : c.Good) (j : Fin c.exports.length)
    {Q : Outcome → Prop}
    (hM : Models (retPost CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg c)
      ⟨Simple.expIdx c j, Q⟩)
    (vs : List Silmaril.Wasm.Component.Val) (hty : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Outcome) (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal))
    (ht : Terminates b) : Q b :=
  Simple.retPost_spec P c hc j hM vs b (hR _ (List.getElem_mem j.isLt) vs hty hb) ht

/-- **Return postconditions verified on the IR hold of the reference machine**, for every
simple component within the flat arities (unconditional). -/
theorem retPost_ref {P : Profile} {prof : Silmaril.Wasm.Component.ProfileKind} {c : Simple}
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    {Q : Outcome → Prop}
    (hM : Models (retPost CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg c)
      ⟨Simple.expIdx c j, Q⟩)
    (vs : List Silmaril.Wasm.Component.Val) (hty : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Outcome) (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal))
    (ht : Terminates b) : Q b :=
  retPost_of_refSound (refSound_of_arity P prof hc hf hi ha) hc j hM vs hty b hb ht

end Simple

/-! ## Levels of the IR's types -/

mutual
theorem irTy_level : ∀ t : ValTy, CTy.level (irTy t) ≤ Level.aggregate
  | .bool | .s8 | .u8 | .s16 | .u16 | .s32 | .u32 | .s64 | .u64 | .f32 | .f64 | .char => by
    decide
  | .record ts => by
    have h := irFields_level 0 ts
    simp only [irTy, CTy.level]
    omega
  | .variant cs => by
    have h := irCases_level 0 cs
    simp only [irTy, CTy.level]
    omega

theorem irTys_level : ∀ ts : List ValTy, CTy.levelList (irTys ts) ≤ Level.aggregate
  | [] => by decide
  | t :: ts => by
    have h₁ := irTy_level t
    have h₂ := irTys_level ts
    simp only [irTys, CTy.levelList]
    omega

theorem irFields_level :
    ∀ (n : ℕ) (ts : List ValTy), CTy.levelFields (irFields n ts) ≤ Level.aggregate
  | _, [] => by simp [irFields, CTy.levelFields]
  | n, t :: ts => by
    have h₁ := irTy_level t
    have h₂ := irFields_level (n + 1) ts
    simp only [irFields, CTy.levelFields]
    omega

theorem irCases_level :
    ∀ (n : ℕ) (cs : List (Option ValTy)), CTy.levelCases (irCases n cs) ≤ Level.aggregate
  | _, [] => by simp [irCases, CTy.levelCases]
  | n, c :: cs => by
    have h₁ := irOpt_level c
    have h₂ := irCases_level (n + 1) cs
    simp only [irCases, CTy.levelCases]
    omega

theorem irOpt_level : ∀ o : Option ValTy, CTy.levelOpt (irOpt o) ≤ Level.aggregate
  | none => by decide
  | some t => irTy_level t
end

/-- IR function types are at most aggregates. -/
theorem irFn_level (ft : Silmaril.Wasm.Component.FuncTy) : (irFn ft).level ≤ Level.aggregate :=
  max_le (irTys_level _) (irTys_level _)

/-- Function types at most aggregates, listed. -/
theorem levelList_le {fs : List CFn} (h : ∀ f ∈ fs, f.level ≤ Level.aggregate) :
    CFn.levelList fs ≤ Level.aggregate := by
  induction fs with
  | nil => exact Nat.zero_le _
  | cons f fs ih =>
    exact max_le (h f (by simp)) (ih fun g hg => h g (by simp [hg]))

/-- **The interfaces of IR components are at most aggregates**: Silmaril's IR has no strings,
lists, handles, streams or futures. -/
theorem cface_level {M : Type} (c : Comp M) : (cface c).level ≤ Level.aggregate := by
  refine max_le (levelList_le ?_) (levelList_le ?_)
  · intro f hf
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hf
    exact irFn_level _
  · intro f hf
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hf
    exact irFn_level _

/-- Every program of the IR semantics is at an interface of level at most `aggregate`. -/
theorem irSem_level {M : Type} [CoreModule M] (C : CoreSem M) {X : CIface}
    (p : (irSem C).Prog X) : X.level ≤ Level.aggregate := by
  rw [← p.cface_eq]
  exact cface_level _

/-! ## Typing: IR values are reference values of the reference types -/

open Silmaril.Wasm.Component.Value (IntKind)
open Silmaril.Wasm.Component.Value.Val (HasType HasFields HasCase HasOpt)

/-- Signed bit patterns are in range. -/
theorem inRange_signed {k : IntKind} (hk : k.signed = true) (x : BitVec k.width) :
    k.inRange x.toInt = true := by
  simp only [IntKind.inRange, IntKind.minValue, IntKind.bound, hk, ite_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

/-- Unsigned bit patterns are in range. -/
theorem inRange_unsigned {k : IntKind} (hk : k.signed = false) (x : BitVec k.width) :
    k.inRange (x.toNat : ℤ) = true := by
  simp only [IntKind.inRange, IntKind.minValue, IntKind.bound, hk, Bool.false_eq_true, ite_false,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast x.isLt⟩

mutual
/-- **IR typing is reference typing**: an IR value of IR type `t` is, read through `toRefVal`, a
reference value of the reference type `irTy t`. -/
theorem hasType_irTy : ∀ (t : ValTy) (v : Silmaril.Wasm.Component.Val), t.check v = true →
    HasType (R := ℕ) (toRefVal v) (irTy t)
  | .bool, v, h => by
    cases v with
    | bool b => exact .bool b
    | _ => simp [ValTy.check] at h
  | .s8, v, h => by
    cases v with
    | s8 x => exact .int rfl (inRange_signed (k := .s8) rfl x)
    | _ => simp [ValTy.check] at h
  | .u8, v, h => by
    cases v with
    | u8 x => exact .int rfl (inRange_unsigned (k := .u8) rfl x)
    | _ => simp [ValTy.check] at h
  | .s16, v, h => by
    cases v with
    | s16 x => exact .int rfl (inRange_signed (k := .s16) rfl x)
    | _ => simp [ValTy.check] at h
  | .u16, v, h => by
    cases v with
    | u16 x => exact .int rfl (inRange_unsigned (k := .u16) rfl x)
    | _ => simp [ValTy.check] at h
  | .s32, v, h => by
    cases v with
    | s32 x => exact .int rfl (inRange_signed (k := .s32) rfl x)
    | _ => simp [ValTy.check] at h
  | .u32, v, h => by
    cases v with
    | u32 x => exact .int rfl (inRange_unsigned (k := .u32) rfl x)
    | _ => simp [ValTy.check] at h
  | .s64, v, h => by
    cases v with
    | s64 x => exact .int rfl (inRange_signed (k := .s64) rfl x)
    | _ => simp [ValTy.check] at h
  | .u64, v, h => by
    cases v with
    | u64 x => exact .int rfl (inRange_unsigned (k := .u64) rfl x)
    | _ => simp [ValTy.check] at h
  | .f32, v, h => by
    cases v with
    | f32 x => exact .f32 x
    | _ => simp [ValTy.check] at h
  | .f64, v, h => by
    cases v with
    | f64 x => exact .f64 x
    | _ => simp [ValTy.check] at h
  | .char, v, h => by
    cases v with
    | char c => exact .char c
    | _ => simp [ValTy.check] at h
  | .record ts, v, h => by
    cases v with
    | record vs => exact .record (hasFields_irFields 0 ts vs h)
    | _ => simp [ValTy.check] at h
  | .variant cs, v, h => by
    cases v with
    | variant i p =>
      have h' : ValTy.checkCase cs i p = true := by
        simp only [ValTy.check, Bool.and_eq_true] at h
        exact h.2
      exact .variant (hasCase_irCases 0 cs i p h')
    | _ => simp [ValTy.check] at h

/-- Record fields. -/
theorem hasFields_irFields : ∀ (n : ℕ) (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val),
    ValTy.checkList ts vs = true → HasFields (R := ℕ) (toRefVals vs) (irFields n ts)
  | _, [], [], _ => .nil
  | n, t :: ts, v :: vs, h => by
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    exact .cons (hasType_irTy t v h'.1) (hasFields_irFields (n + 1) ts vs h'.2)
  | _, [], _ :: _, h => by simp [ValTy.checkList] at h
  | _, _ :: _, [], h => by simp [ValTy.checkList] at h

/-- Variant cases. -/
theorem hasCase_irCases : ∀ (n : ℕ) (cs : List (Option ValTy)) (i : ℕ)
    (p : Option Silmaril.Wasm.Component.Val), ValTy.checkCase cs i p = true →
    HasCase (R := ℕ) i (toRefOpt p) (irCases n cs)
  | _, [], _, _, h => by simp [ValTy.checkCase] at h
  | _, c :: _, 0, p, h => .here (hasOpt_irOpt c p h)
  | n, _ :: cs, i + 1, p, h => .there (hasCase_irCases (n + 1) cs i p h)

/-- Optional payloads. -/
theorem hasOpt_irOpt : ∀ (o : Option ValTy) (p : Option Silmaril.Wasm.Component.Val),
    ValTy.checkOpt o p = true → HasOpt (R := ℕ) (toRefOpt p) (irOpt o)
  | none, none, _ => .none
  | some t, some v, h => .some (hasType_irTy t v h)
  | none, some _, h => by simp [ValTy.checkOpt] at h
  | some _, none, h => by simp [ValTy.checkOpt] at h
end

/-- **Well-typed IR argument lists are reference-typed** at the reference function type. -/
theorem typed_irTys : ∀ (ts : List ValTy) (vs : List Silmaril.Wasm.Component.Val),
    ValTy.checkList ts vs = true → Typed (irTys ts) (vs.map toRefVal)
  | [], [], _ => .nil
  | t :: ts, v :: vs, h => by
    have h' : t.check v = true ∧ ValTy.checkList ts vs = true := by
      simpa only [ValTy.checkList, Bool.and_eq_true] using h
    exact .cons (hasType_irTy t v h'.1) (typed_irTys ts vs h'.2)
  | [], _ :: _, h => by simp [ValTy.checkList] at h
  | _ :: _, [], h => by simp [ValTy.checkList] at h

/-- The precondition of a transferred contract implies reference typing of the arguments. -/
theorem Simple.refPre_typed {c : Simple} {j : Fin c.exports.length} {pre : List RVal → Prop}
    {a : List RVal} (h : Simple.refPre c j pre a) : Typed (irFn c.exports[j].ty).params a := by
  obtain ⟨vs, rfl, hty, -⟩ := h
  exact typed_irTys _ vs hty

end Silmaril.Wasm.Spec.Component
