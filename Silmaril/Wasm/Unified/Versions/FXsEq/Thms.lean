module

public import Silmaril.Wasm.Unified.Versions.FXEq.Thms
public import Silmaril.Wasm.Unified.Versions.FXSim.Thms
public import Silmaril.Wasm.Unified.Core30Faithful.Thms

/-!
# Core 3.0 and the repaired WasmFX model agree on 3.0 code

`algFXs` (`Silmaril.Wasm.Unified.Versions.FXEq`) interprets the 3.0 opcodes `block`, `loop` and `if`
also by the FX structured forms, so the FX meaning of 3.0 code holds FX code in which some
structured instructions are FX ones, and the frozen `Task.fxs_obsEq_core` asked whether Core 3.0
and the reduct of `fxModelNs` still observe the same.

* `mem_evFXs` (mutual induction through blocks): **the FX meanings of 3.0 code are exactly the
  FX programs that read as a Core meaning** (`LiftIs`, `Silmaril.Wasm.Unified.Versions.FXSim`).
* **`not_fxs_obsEq_core`: `Task.fxs_obsEq_core` is refuted as stated.** Its hypothesis
  constrains the FX validation `okcFX` only on embedded Core code, and the FX meaning of
  `block` also contains the FX form: with `okc` rejecting everything and `okcFX` accepting only
  the FX `block` with an empty body, Core observes nothing on `block` and WasmFX observes
  `returns []`.
* **`core_obsEq_fxs`: the repaired statement is proved**: if FX validation of FX code that reads
  as a Core program is Core validation of that program (`hok`), Core 3.0 and the reduct of
  `fxModelNs` have the same observations on every call. The behaviours agree by the CoreFX
  simulation `behavioursFX_liftIs`. `okcLift okc` (FX code reading as a valid Core program) is
  such a validation (`okcLift_lift`), and it also satisfies the old hypothesis
  (`okcLift_core`).
* `fxsEmb_obsEq`, `fxsEmb_sat_iff`: at the image point of `fxEmb` (`fxModelNsAt`), every
  sentence transfers; `fxs_obsEq_fx`: on 3.0 code `fxModelNs` and `fxModelN` (the pass-1 algebra,
  whose structured forms are dead) observe the same.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FX Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

/-! ## The FX meanings of 3.0 code -/

section Eval

/-- The FX meaning of an instruction in the reduct of `algFXs` along `σ`. -/
def evFXsI (σ : sig30 ⟶ sigFX) (u : UInstr sig30.Op) : Set InstrFX :=
  (algFXs.comap σ.f).evalInstr u

/-- The FX meaning of code in the reduct of `algFXs` along `σ`. -/
def evFXs (σ : sig30 ⟶ sigFX) (c : sig30.Code) : Set (List InstrFX) :=
  (algFXs.comap σ.f).evalCode c

/-- The FX meanings of blocks in the reduct of `algFXs` along `σ`. -/
def evFXsB (σ : sig30 ⟶ sigFX) (bs : List sig30.Code) : List (Set (List InstrFX)) :=
  (algFXs.comap σ.f).evalBlocks bs

/-- An FX block meaning holds the FX programs that read as a program of the Core meaning. -/
def BlockRel (DF : Set (List InstrFX)) (D : Set (List Instr)) : Prop :=
  ∀ l, l ∈ DF ↔ ∃ is ∈ D, LiftIs l is

theorem bodies_of_core {bodies : List (List Instr)} {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))}
    (h : List.Forall₂ (fun b D => b.map InstrFX.core ∈ D) bodies DsF)
    (hB : List.Forall₂ BlockRel DsF Ds) : List.Forall₂ (· ∈ ·) bodies Ds := by
  induction h generalizing Ds with
  | nil =>
    cases hB
    exact .nil
  | cons hb _ ih =>
    cases hB with
    | cons hR hB' =>
      obtain ⟨is, his, hl⟩ := (hR _).1 hb
      exact .cons (LiftIs.map_core_iff.1 hl ▸ his) (ih hB')

theorem core_of_bodies {bodies : List (List Instr)} {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))} (h : List.Forall₂ (· ∈ ·) bodies Ds)
    (hB : List.Forall₂ BlockRel DsF Ds) :
    List.Forall₂ (fun b D => b.map InstrFX.core ∈ D) bodies DsF := by
  induction h generalizing DsF with
  | nil =>
    cases hB
    exact .nil
  | cons hb _ ih =>
    cases hB with
    | cons hR hB' => exact .cons ((hR _).2 ⟨_, hb, liftIs_map_core _⟩) (ih hB')

/-- One FX body read from one Core body. -/
theorem one_body {b : List InstrFX} {is : List Instr} {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))} (h : List.Forall₂ (· ∈ ·) [is] Ds)
    (hB : List.Forall₂ BlockRel DsF Ds) (hl : LiftIs b is) : List.Forall₂ (· ∈ ·) [b] DsF := by
  obtain ⟨D, rfl, hD⟩ : ∃ D, Ds = [D] ∧ is ∈ D := by
    cases h with
    | cons hD hn =>
      cases hn
      exact ⟨_, rfl, hD⟩
  cases hB with
  | cons hR hn =>
    cases hn
    exact .cons ((hR b).2 ⟨is, hD, hl⟩) .nil

/-- One Core body read from one FX body. -/
theorem one_body' {b : List InstrFX} {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))} (h : List.Forall₂ (· ∈ ·) [b] DsF)
    (hB : List.Forall₂ BlockRel DsF Ds) :
    ∃ is, List.Forall₂ (· ∈ ·) [is] Ds ∧ LiftIs b is := by
  cases h with
  | cons hb hn =>
    cases hn
    cases hB with
    | cons hR hn' =>
      cases hn'
      obtain ⟨is, his, hl⟩ := (hR b).1 hb
      exact ⟨is, .cons his .nil, hl⟩

/-- Two FX bodies read from two Core bodies. -/
theorem two_bodies {b₁ b₂ : List InstrFX} {is₁ is₂ : List Instr}
    {DsF : List (Set (List InstrFX))} {Ds : List (Set (List Instr))}
    (h : List.Forall₂ (· ∈ ·) [is₁, is₂] Ds) (hB : List.Forall₂ BlockRel DsF Ds)
    (hl₁ : LiftIs b₁ is₁) (hl₂ : LiftIs b₂ is₂) : List.Forall₂ (· ∈ ·) [b₁, b₂] DsF := by
  cases h with
  | cons h₁ h' =>
    cases h' with
    | cons h₂ hn =>
      cases hn
      cases hB with
      | cons hR₁ hB' =>
        cases hB' with
        | cons hR₂ hn' =>
          cases hn'
          exact .cons ((hR₁ _).2 ⟨_, h₁, hl₁⟩) (.cons ((hR₂ _).2 ⟨_, h₂, hl₂⟩) .nil)

/-- Two Core bodies read from two FX bodies. -/
theorem two_bodies' {b₁ b₂ : List InstrFX} {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))} (h : List.Forall₂ (· ∈ ·) [b₁, b₂] DsF)
    (hB : List.Forall₂ BlockRel DsF Ds) :
    ∃ is₁ is₂, List.Forall₂ (· ∈ ·) [is₁, is₂] Ds ∧ LiftIs b₁ is₁ ∧ LiftIs b₂ is₂ := by
  cases h with
  | cons h₁ h' =>
    cases h' with
    | cons h₂ hn =>
      cases hn
      cases hB with
      | cons hR₁ hB' =>
        cases hB' with
        | cons hR₂ hn' =>
          cases hn'
          obtain ⟨is₁, hi₁, hl₁⟩ := (hR₁ _).1 h₁
          obtain ⟨is₂, hi₂, hl₂⟩ := (hR₂ _).1 h₂
          exact ⟨is₁, is₂, .cons hi₁ (.cons hi₂ .nil), hl₁, hl₂⟩

theorem liftIs_cons_iff {x : InstrFX} {t : List InstrFX} {is : List Instr} :
    LiftIs (x :: t) is ↔ ∃ i t', is = i :: t' ∧ LiftI x i ∧ LiftIs t t' := by
  constructor
  · intro h
    cases h with
    | cons hx ht => exact ⟨_, _, rfl, hx, ht⟩
  · rintro ⟨i, t', rfl, hx, ht⟩
    exact .cons hx ht

theorem liftIs_nil_iff {l : List InstrFX} : LiftIs l [] ↔ l = [] := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .nil

/-- An FX structured form of a 3.0 opcode reads as a Core instruction of that opcode. -/
theorem shape_core (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) {o : sig30.Op} {imms : List Imm} {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))} {hs : List Handler} (hB : List.Forall₂ BlockRel DsF Ds)
    {x : InstrFX} {bs : List (List InstrFX)} (hb : shapeFXs x = some ((σ.f o).1, imms, bs))
    (hh : hs = []) (hbs : List.Forall₂ (· ∈ ·) bs DsF) :
    ∃ i ∈ @id (Set Instr) (alg30.op o imms Ds hs), LiftI x i := by
  subst hh
  cases x with
  | block bt b =>
    obtain ⟨ho, rfl, rfl⟩ : head (.block bt []) = (σ.f o).1 ∧ [e bt] = imms ∧ [b] = bs := by
      simpa [shapeFXs] using hb
    obtain ⟨is, hD, hl⟩ := one_body' hbs hB
    exact ⟨.block bt is, ⟨(ho.trans (hσ o) : head (.block bt is) = o.1), rfl, rfl, hD⟩, .block hl⟩
  | loop bt b =>
    obtain ⟨ho, rfl, rfl⟩ : head (.loop bt []) = (σ.f o).1 ∧ [e bt] = imms ∧ [b] = bs := by
      simpa [shapeFXs] using hb
    obtain ⟨is, hD, hl⟩ := one_body' hbs hB
    exact ⟨.loop bt is, ⟨(ho.trans (hσ o) : head (.loop bt is) = o.1), rfl, rfl, hD⟩, .loop hl⟩
  | if_ bt b₁ b₂ =>
    obtain ⟨ho, rfl, rfl⟩ :
        head (.if_ bt [] []) = (σ.f o).1 ∧ [e bt] = imms ∧ [b₁, b₂] = bs := by
      simpa [shapeFXs] using hb
    obtain ⟨is₁, is₂, hD, hl₁, hl₂⟩ := two_bodies' hbs hB
    exact ⟨.if_ bt is₁ is₂, ⟨(ho.trans (hσ o) : head (.if_ bt is₁ is₂) = o.1), rfl, rfl, hD⟩,
      .if_ hl₁ hl₂⟩
  | core i => simp [shapeFXs] at hb
  | fx j => simp [shapeFXs] at hb

/-- A Core instruction of a 3.0 opcode, read as FX, is in the FX meaning of the opcode. -/
theorem core_shape (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) {o : sig30.Op}
    {imms : List Imm} {DsF : List (Set (List InstrFX))} {Ds : List (Set (List Instr))}
    {hs : List Handler} (hB : List.Forall₂ BlockRel DsF Ds) {x : InstrFX} {i : Instr}
    (h₁ : head i = o.1) (h₂ : immsOf i = imms) (h₃ : hdlOf i = hs)
    (h₄ : List.Forall₂ (· ∈ ·) i.bodies Ds) (hx : LiftI x i) :
    x ∈ @id (Set InstrFX) (algFXs.op (σ.f o) imms DsF hs) := by
  cases hx with
  | core => exact Or.inl ⟨i, rfl, h₁.trans (hσ o).symm, h₂, h₃, core_of_bodies h₄ hB⟩
  | @block bt b is hl =>
    exact Or.inr (Or.inr ⟨[b], by rw [hσ o, ← h₁, ← h₂]; rfl, h₃.symm, one_body h₄ hB hl⟩)
  | @loop bt b is hl =>
    exact Or.inr (Or.inr ⟨[b], by rw [hσ o, ← h₁, ← h₂]; rfl, h₃.symm, one_body h₄ hB hl⟩)
  | @if_ bt b₁ b₂ is₁ is₂ hl₁ hl₂ =>
    exact Or.inr (Or.inr ⟨[b₁, b₂], by rw [hσ o, ← h₁, ← h₂]; rfl, h₃.symm,
      two_bodies h₄ hB hl₁ hl₂⟩)

/-- **The FX meaning of an opcode is read from its Core meaning.** -/
theorem op_iff (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) (o : sig30.Op) (imms : List Imm) {DsF : List (Set (List InstrFX))}
    {Ds : List (Set (List Instr))} (hs : List Handler) (hB : List.Forall₂ BlockRel DsF Ds)
    (x : InstrFX) :
    x ∈ @id (Set InstrFX) (algFXs.op (σ.f o) imms DsF hs) ↔
      ∃ i ∈ @id (Set Instr) (alg30.op o imms Ds hs), LiftI x i := by
  constructor
  · rintro (⟨i, rfl, h₁, h₂, h₃, h₄⟩ | ⟨j, -, hj, -⟩ | ⟨bs, hb, hh, hbs⟩)
    · exact ⟨i, ⟨h₁.trans (hσ o), h₂, h₃, bodies_of_core h₄ hB⟩, .core i⟩
    · obtain ⟨i, hi⟩ := o.2
      exact absurd (hi.trans ((hσ o).symm.trans hj.symm)) (head_ne_headFX i j)
    · exact shape_core σ hσ hB hb hh hbs
  · rintro ⟨i, ⟨h₁, h₂, h₃, h₄⟩, hx⟩
    exact core_shape σ hσ hB h₁ h₂ h₃ h₄ hx

mutual
/-- FX meanings of an instruction, read from Core meanings. -/
theorem mem_evFXsI (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) : (u : UInstr sig30.Op) → ∀ x, x ∈ evFXsI σ u ↔ ∃ i ∈ evalI30 u, LiftI x i
  | .op o imms bs hs => by
    intro x
    rw [evFXsI, Alg.evalInstr, evalI30, Alg.evalInstr]
    exact op_iff σ hσ o imms hs (evFXsB_rel σ hσ bs) x
/-- **The FX meanings of 3.0 code are the FX programs reading as a Core meaning.** -/
theorem mem_evFXs (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) : (c : sig30.Code) → ∀ l, l ∈ evFXs σ c ↔ ∃ is ∈ evalC30 c, LiftIs l is
  | [] => by
    intro l
    rw [evFXs, Alg.evalCode, evalC30, Alg.evalCode]
    show l = [] ↔ ∃ is, is = [] ∧ LiftIs l is
    rw [← liftIs_nil_iff]
    exact ⟨fun h => ⟨[], rfl, h⟩, fun ⟨is, his, h⟩ => his ▸ h⟩
  | u :: c => by
    intro l
    rw [evFXs, Alg.evalCode, evalC30, Alg.evalCode]
    show (∃ x t, l = x :: t ∧ x ∈ evFXsI σ u ∧ t ∈ evFXs σ c) ↔
      ∃ is, (∃ i t', is = i :: t' ∧ i ∈ evalI30 u ∧ t' ∈ evalC30 c) ∧ LiftIs l is
    constructor
    · rintro ⟨x, t, rfl, hx, ht⟩
      obtain ⟨i, hi, hxi⟩ := (mem_evFXsI σ hσ u x).1 hx
      obtain ⟨t', ht', htt⟩ := (mem_evFXs σ hσ c t).1 ht
      exact ⟨i :: t', ⟨i, t', rfl, hi, ht'⟩, .cons hxi htt⟩
    · rintro ⟨_, ⟨i, t', rfl, hi, ht'⟩, hl⟩
      obtain ⟨x, t, rfl, hxi, htt⟩ : ∃ x t, l = x :: t ∧ LiftI x i ∧ LiftIs t t' := by
        cases hl with
        | cons hx ht => exact ⟨_, _, rfl, hx, ht⟩
      exact ⟨x, t, rfl, (mem_evFXsI σ hσ u x).2 ⟨i, hi, hxi⟩, (mem_evFXs σ hσ c t).2 ⟨t', ht', htt⟩⟩
/-- FX block meanings, read from Core block meanings. -/
theorem evFXsB_rel (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) : (bs : List sig30.Code) → List.Forall₂ BlockRel (evFXsB σ bs) (evB30 bs)
  | [] => by
    rw [evFXsB, Alg.evalBlocks, evB30, Alg.evalBlocks]
    exact .nil
  | b :: bs => by
    rw [evFXsB, Alg.evalBlocks, evB30, Alg.evalBlocks]
    exact .cons (fun l => mem_evFXs σ hσ b l) (evFXsB_rel σ hσ bs)
end

end Eval

/-! ## The repaired equation -/

variable {H : Type}

/-- FX code that reads as a valid Core program. -/
def okcLift (okc : List Instr → Prop) (l : List InstrFX) : Prop := ∃ is, LiftIs l is ∧ okc is

theorem okcLift_lift (okc : List Instr → Prop) {l : List InstrFX} {is : List Instr}
    (h : LiftIs l is) : okcLift okc l ↔ okc is :=
  ⟨fun ⟨_, hj, hok⟩ => LiftIs.functional hj h ▸ hok, fun hok => ⟨is, h, hok⟩⟩

theorem okcLift_core (okc : List Instr → Prop) (is : List Instr) :
    okcLift okc (is.map InstrFX.core) ↔ okc is :=
  okcLift_lift okc (liftIs_map_core is)

/-- **Core 3.0 and the reduct of the repaired WasmFX model observe the same**, when FX validation
of FX code reading as a Core program is Core validation of that program. -/
theorem core_obsEq_fxs (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (okcFX : List InstrFX → Prop)
    (hok : ∀ l is, LiftIs l is → (okcFX l ↔ okc is)) :
    ObsEq ((fxModelNs P host s noFX f okcFX).reduct (FSig.incl sub30FX))
      (model30 P host s f okc) := by
  have hσ : ∀ o, ((FSig.incl sub30FX).f o).1 = o.1 := fun _ => rfl
  have hbeh : ∀ {l is}, LiftIs l is → ∀ vs,
      behavioursFX P host noFX (cfgFX s f l vs) = behCode P host s f is vs :=
    fun hl vs => behavioursFX_liftIs P host s [] f vs hl
  rintro ⟨c, vs⟩
  ext b
  show ((∃ l ∈ evFXs _ c, okcFX l) ∧
      ∃ l ∈ evFXs _ c, okcFX l ∧ b ∈ behavioursFX P host noFX (cfgFX s f l vs)) ↔
    ((∃ is ∈ evalC30 c, okc is) ∧ ∃ is ∈ evalC30 c, okc is ∧ b ∈ behCode P host s f is vs)
  constructor
  · rintro ⟨⟨l, hl, hk⟩, l', hl', hk', hb⟩
    obtain ⟨is, his, hli⟩ := (mem_evFXs _ hσ c l).1 hl
    obtain ⟨is', his', hli'⟩ := (mem_evFXs _ hσ c l').1 hl'
    exact ⟨⟨is, his, (hok l is hli).1 hk⟩, is', his', (hok l' is' hli').1 hk',
      hbeh hli' vs ▸ hb⟩
  · rintro ⟨⟨is, his, hk⟩, is', his', hk', hb⟩
    have hm : ∀ js ∈ evalC30 c, js.map InstrFX.core ∈ evFXs (FSig.incl sub30FX) c :=
      fun js hjs => (mem_evFXs _ hσ c _).2 ⟨js, hjs, liftIs_map_core js⟩
    exact ⟨⟨_, hm is his, (hok _ is (liftIs_map_core is)).2 hk⟩, _, hm is' his',
      (hok _ is' (liftIs_map_core is')).2 hk', (hbeh (liftIs_map_core is') vs).symm ▸ hb⟩

/-- On 3.0 code the repaired and the pass-1 WasmFX models observe the same. -/
theorem fxs_obsEq_fx (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) :
    ObsEq ((fxModelNs P host s noFX f (okcLift okc)).reduct (FSig.incl sub30FX))
      ((fxModelN P host s noFX f (okcLift okc)).reduct (FSig.incl sub30FX)) := fun x =>
  (core_obsEq_fxs P host s f okc _ (fun _ _ h => okcLift_lift okc h) x).trans
    (core_obsEq_fx P host s f okc _ (okcLift_core okc) x).symm

/-! ## The refutation of the frozen statement -/

/-- **`Task.fxs_obsEq_core` is false as stated**: its hypothesis does not constrain FX validation
of the FX structured forms. -/
theorem not_fxs_obsEq_core : ¬ Task.fxs_obsEq_core := by
  intro hT
  have hok : ∀ is : List Instr,
      (fun l : List InstrFX => l = [InstrFX.block .empty []]) (is.map InstrFX.core) ↔
        (fun _ : List Instr => False) is := by
    intro is
    constructor
    · intro h
      cases is with
      | nil => cases h
      | cons i t =>
        have h' := (List.cons.inj h).1
        cases h'
    · exact False.elim
  have hE := hT Empty Profile.spec (fun _ _ _ _ => False) {} {} (fun _ => False)
    (fun l => l = [InstrFX.block .empty []]) hok (encCode [.block .empty []], [])
  have hσ : ∀ o, ((FSig.incl sub30FX).f o).1 = o.1 := fun _ => rfl
  have hmem : [InstrFX.block .empty []] ∈ evFXs (FSig.incl sub30FX) (encCode [.block .empty []]) :=
    (mem_evFXs _ hσ _ _).2 ⟨_, mem_evalCode_encCode _, .cons (.block .nil) .nil⟩
  have hrun : Behaviour.returns [] ∈ behavioursFX Profile.spec (fun _ _ _ _ => False) noFX
      (cfgFX ({} : Store Empty) {} [InstrFX.block .empty []] []) := by
    refine Or.inl ⟨⟨{}, [], {}, cvals []⟩, .values [], ?_, rfl, rfl⟩
    exact (Relation.ReflTransGen.single (StepFX.block (vs := []) (bt := .empty) (body := [])
      (t₁ := []) (t₂ := []) rfl rfl)).tail (StepFX.labelVals (vs := []))
  have hfx : Behaviour.returns [] ∈
      ((fxModelNs Profile.spec (fun _ _ _ _ => False) ({} : Store Empty) noFX {}
        (fun l => l = [InstrFX.block .empty []])).reduct (FSig.incl sub30FX)).obs
        (encCode [.block .empty []], []) :=
    ⟨⟨_, hmem, rfl⟩, _, hmem, rfl, hrun⟩
  rw [hE] at hfx
  exact hfx.1.elim fun _ h => h.2

/-! ## At the image point of `fxEmb` -/

/-- The repaired WasmFX model at a CoreFX point. -/
def fxModelNsAt (P : Profile) (f : Frame) (okc : List InstrFX → Prop) (x : FX.Pt H) :
    Model UIn UObs sigFX :=
  fxModelNs P x.2.1 x.1 x.2.2 f okc

variable (f : Frame) (okc : List Instr → Prop)

/-- **`fxEmb` into the repaired WasmFX model, as an equation of observations.** -/
theorem fxsEmb_obsEq (P : Profile) (x : Core.Pt H) :
    ObsEq ((fxModelNsAt P f (okcLift okc) ((FX.fxEmb P H).pt x)).reduct (FSig.incl nsub_30_FX))
      (coreSAt v30 P f okc x) :=
  (core_obsEq_fxs P x.2 x.1 f okc _ (fun _ _ h => okcLift_lift okc h)).reduct
    (FSig.incl (nsig_sub30 v30))

/-- **Transfer along `fxEmb` into the repaired model: every sentence.** -/
theorem fxsEmb_sat_iff (P : Profile) (x : Core.Pt H) (φ : Sen UIn UObs (nsig v30)) :
    Sat (fxModelNsAt P f (okcLift okc) ((FX.fxEmb P H).pt x)) (φ.map (FSig.incl nsub_30_FX)) ↔
      Sat (coreSAt v30 P f okc x) φ := by
  rw [sat_map_iff]
  exact (fxsEmb_obsEq f okc P x).sat_iff φ

end Silmaril.Wasm.Unified.Versions
