module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30YSub
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30YFloat
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms

/-!
# Instruction typing of the wasm-3.0 script, the comorphism in `{locals, globals}`

The model is `stepModel BI`, as in `Instr30`. The sentences are Core typing judgements in the
context `ctxLoc L G = {locals := L, globals := G}`, translated to `Instr_ok`/`Instrs_ok` facts in
its image `ctxLGV L G`.

* `numeric_preserves`: every Core typing of an integer or float numeric instruction other than a
  conversion is an `Instr_ok` fact in every typed context value.
* `instrY_preserves`: on `fragY` (parametric, numeric, variable), at bounded types and under
  `ParamOk`, every Core typing in `ctxLoc L G` is an `Instr_ok` fact in `ctxLGV L G`, in every
  `simEnv B` and under every reading of `otherwise`.
* `fragOkY_dd`, `instrsY_preserves`: the same for `Instrs_ok` on `FragOkY` derivations
  (`empty`, `instr`, `seq` without initialised locals, `frame` at flat types).
* `globalAddF64`: non-vacuity: `global.get 0; f64.const 1; f64.add; global.set 0` at `[] -> []`
  in a context with one mutable `f64` global, through `seq` at the stacks `[f64]`, `[f64, f64]`
  and `[f64]`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Y

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV instrtypeV idxV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV ItBnd)

variable {B : Builtins}

/-! ## Single instructions -/

/-- **The numeric instructions are preserved, in any context**: every Core typing of an integer or
float instruction other than a conversion is an `Instr_ok` fact in every typed context value. -/
theorem numeric_preserves (O : ElseI) {C : Context} {c : Value} (hc : CtxT B c) {i : Instr}
    {it : InstrType} (hn : numY i = true) (h : NumericInstrOk C i it) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, instrToV i, instrtypeV it]) := by
  cases h with
  | intConst t b => exact Instr30X.dd_intConst O hc t b
  | floatConst t b => exact dd_floatConst O hc t b
  | intUnOp hv => exact Instr30X.dd_intUnOp O hc hv
  | floatUnOp t op => exact dd_floatUnOp O hc t op
  | intBinOp t op => exact Instr30X.dd_intBinOp O hc t op
  | floatBinOp t op => exact dd_floatBinOp O hc t op
  | intTestOp t op => exact Instr30X.dd_intTestOp O hc t op
  | intRelOp t op => exact Instr30X.dd_intRelOp O hc t op
  | floatRelOp t op => exact dd_floatRelOp O hc t op
  | convert op => simp [numY] at hn

/-- **`fragY` in `{locals, globals}`**: a Core typing in `ctxLoc L G` of a reached instruction,
under `ParamOk`, is an `Instr_ok` fact of `simEnv B` in `ctxLGV L G`, under every reading of
`otherwise`. -/
theorem instrY_preserves (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hb : CtxBnd L G)
    {i : Instr} {it : InstrType} (hf : fragY i = true) (hp : ParamOk i it)
    (h : InstrOk (ctxLoc L G) i it) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [ctxLGV L G, instrToV i, instrtypeV it]) := by
  have hc : CtxT B (ctxLGV L G) := ctxT_lg hb
  cases h with
  | parametric h =>
    have hpi : param i = true := by cases h <;> rfl
    exact parametric_preserves O hc h (hp hpi).1 (hp hpi).2
  | numeric h =>
    have hn : numY i = true := by
      cases h <;> simp_all [fragY, param, numY, var]
    exact numeric_preserves O hc hn h
  | «variable» h => exact variable_preserves O hb h
  | vector h => cases h <;> simp [fragY, param, numY, var] at hf
  | memory h => cases h <;> simp [fragY, param, numY, var] at hf
  | table h => cases h <;> simp [fragY, param, numY, var] at hf
  | reference h => cases h <;> simp [fragY, param, numY, var] at hf
  | _ => simp [fragY, param, numY, var] at hf

/-! ## Sequences -/

/-- A valid instruction of `fragY` has a typed image. -/
theorem typedV_fragY {C : Context} {i : Instr} {it : InstrType} (hf : fragY i = true)
    (h : InstrOk C i it) : TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  have hb : Round4.instrBnd i = true := by
    cases i <;> simp [fragY, param, numY, var] at hf <;> rfl
  have hs : Round5.Target.instrSel i = true := by
    cases i <;> simp [fragY, param, numY, var] at hf <;> rfl
  exact Round5.Target.instrTypingSel_aux (Round5.SimdTy.simdTypingSel B) i C it h hb hs

/-- A `FragOkY` derivation is a Core derivation. -/
theorem fragOkY_sound {L : List LocalType} {G : List CGlobalType} {is : List Instr}
    {it : InstrType} (h : FragOkY L G is it) : InstrsOk (ctxLoc L G) is it := by
  induction h with
  | nil => exact .nil
  | instr _ _ _ h => exact .instr h
  | seq _ _ _ ih₁ ih₂ => exact .seq ih₁ (fun _ hx => absurd hx List.not_mem_nil) ih₂
  | frame _ hok _ ih => exact .frame ih hok
  | sub _ hs hok _ _ _ ih => exact .sub ih hs hok

/-- The initialised locals of a reached instruction's typing are local indices. -/
theorem inits_fragY {C : Context} {i : Instr} {it : InstrType} (hf : fragY i = true)
    (h : InstrOk C i it) : ∀ n ∈ it.inits, ∃ x : LocalIdx, n = x.toNat := by
  cases h with
  | parametric h => cases h <;> simp
  | numeric h => cases h <;> simp
  | «variable» h =>
    cases h with
    | @localSet x _ _ _ => exact fun n hn => ⟨x, List.mem_singleton.1 hn⟩
    | @localTee x _ _ _ => exact fun n hn => ⟨x, List.mem_singleton.1 hn⟩
    | _ => simp
  | vector h => cases h <;> simp [fragY, param, numY, var] at hf
  | memory h => cases h <;> simp [fragY, param, numY, var] at hf
  | table h => cases h <;> simp [fragY, param, numY, var] at hf
  | reference h => cases h <;> simp [fragY, param, numY, var] at hf
  | _ => simp [fragY, param, numY, var] at hf

/-- An element on the left of a pointwise relation is related to one on the right. -/
theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr hl, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hab⟩ := forall₂_mem_left hl h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- The parameters of a supertype of a type with number or vector parameters are flat. -/
theorem flatSub_params {C : Context} {ps rs ps' rs' : List CValType}
    (hs : InstrTypeSub C (.plain ps rs) (.plain ps' rs')) (hp : ∀ t ∈ ps, t.IsNumOrVec) :
    ∀ t ∈ ps', Flat t = true := by
  intro t ht
  obtain ⟨u, hu, hsub⟩ := forall₂_mem_left hs.1 ht
  exact flat_of_sub hsub (hp u hu)

/-- The results of a subtype of a type with number or vector results are flat. -/
theorem flatSub_results {C : Context} {ps rs ps' rs' : List CValType}
    (hs : InstrTypeSub C (.plain ps rs) (.plain ps' rs')) (hr : ∀ t ∈ rs', t.IsNumOrVec) :
    ∀ t ∈ rs, Flat t = true := by
  intro t ht
  obtain ⟨u, hu, hsub⟩ := forall₂_mem_left hs.2.1 ht
  exact flat_of_sub hsub (hr u hu)

/-- A `FragOkY` derivation has bounded types. -/
theorem fragOkY_bnd {L : List LocalType} {G : List CGlobalType} {is : List Instr} {it : InstrType}
    (h : FragOkY L G is it) : ItBnd it := by
  induction h with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | instr _ hb _ _ => exact hb
  | seq _ _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | frame hf _ _ ih =>
    exact ⟨fun t ht => (List.mem_append.1 ht).elim (fun h => tyBnd_flat (hf t h)) (ih.1 t),
      fun t ht => (List.mem_append.1 ht).elim (fun h => tyBnd_flat (hf t h)) (ih.2 t)⟩
  | sub _ hs _ hp hr _ _ =>
    exact ⟨fun t ht => tyBnd_flat (flatSub_params hs hp t ht),
      fun t ht => tyBnd_flat (flat_numVec (hr t ht))⟩

/-- The instructions of a `FragOkY` derivation have typed images. -/
theorem fragOkY_typed {L : List LocalType} {G : List CGlobalType} {is : List Instr}
    {it : InstrType} (h : FragOkY L G is it) :
    ∀ v ∈ instrsToV is, TypedV (simEnv B) (.varT "instr" []) v := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | instr hf _ _ h =>
    intro v hv
    rw [Exn.instrsToV_eq_map] at hv
    obtain rfl := List.mem_singleton.1 hv
    exact typedV_fragY hf h
  | seq _ _ _ ih₁ ih₂ =>
    intro v hv
    rw [Instr30.instrsToV_append] at hv
    exact (List.mem_append.1 hv).elim (ih₁ v) (ih₂ v)
  | frame _ _ _ ih => exact ih
  | sub _ _ _ _ _ _ ih => exact ih

/-- Typed images of bounded value types. -/
theorem typedV_tys {ts : List CValType} (hb : ∀ t ∈ ts, Round4.tyBnd t = true) :
    ∀ v ∈ ts.map tyV, TypedV (simEnv B) (.varT "valtype" []) v := Instr30.typedV_vals hb

/-- `Instrs_ok/sub` towards number and vector types, from Core's premises. -/
theorem dd_subY (O : ElseI) {c : Value} (hc : CtxT B c) {C : Context} {is : List Value}
    {ps rs ps' rs' : List CValType} (hi : ∀ i ∈ is, TypedV (simEnv B) (.varT "instr" []) i)
    (hs : InstrTypeSub C (.plain ps rs) (.plain ps' rs')) (hp : ∀ t ∈ ps, t.IsNumOrVec)
    (hr : ∀ t ∈ rs', t.IsNumOrVec) (hlen : ps.length < 2 ^ 32 ∧ rs.length < 2 ^ 32)
    (h : DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, instrtypeV (.plain ps rs)])) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, instrtypeV (.plain ps' rs')]) := by
  have hfp : ∀ t ∈ ps, Flat t = true := fun t ht => flat_numVec (hp t ht)
  have hfr' : ∀ t ∈ rs', Flat t = true := fun t ht => flat_numVec (hr t ht)
  have hfp' : ∀ t ∈ ps', Flat t = true := flatSub_params hs hp
  have hfr : ∀ t ∈ rs, Flat t = true := flatSub_results hs hr
  have hl₁ : ps'.length = ps.length := (List.Forall₂.length_eq hs.1)
  have hl₂ : rs.length = rs'.length := (List.Forall₂.length_eq hs.2.1)
  have ty {ts : List CValType} (hf : ∀ t ∈ ts, Flat t = true) :
      ∀ v ∈ ts.map tyV, TypedV (simEnv B) (.varT "valtype" []) v :=
    typedV_tys fun t ht => tyBnd_flat (hf t ht)
  exact dd_instrsSub O hc hi
    (typedV_itV (by simpa using hlen.1) (by simpa using hlen.2) (ty hfp) (ty hfr))
    (typedV_itV (by simpa [hl₁] using hlen.1) (by simpa [← hl₂] using hlen.2) (ty hfp') (ty hfr'))
    h
    (dd_instrtypeSub O hc (ty hfp) (ty hfr) (ty hfp') (ty hfr')
      (resulttypeSub_numVec O hc hs.1 hp) (resulttypeSub_numVec O hc hs.2.1 hr))
    (instrtypeOk_flat O hc hfp' hfr')

/-- **`FragOkY` derivations are read by `DDerivesB`**, in `ctxLGV L G`. -/
theorem fragOkY_dd (O : ElseI) {L : List LocalType} {G : List CGlobalType} (hcb : CtxBnd L G)
    {is : List Instr} {it : InstrType} (h : FragOkY L G is it) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" []
      (.tuple [ctxLGV L G, .list (instrsToV is), instrtypeV it]) := by
  have hc : CtxT B (ctxLGV L G) := ctxT_lg hcb
  induction h with
  | nil => exact Instr30.dd_instrsEmpty O hc
  | @instr i it hf hb hp h =>
    rw [Instr30.instrtypeV_eq]
    exact Instr30.dd_instrsInstr O hc (typedV_fragY hf h) (typedV_tys hb.1)
      (fun v hv => by
        obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hv
        obtain ⟨x, rfl⟩ := inits_fragY hf h n hn
        exact Typing.typedV_idx x)
      (typedV_tys hb.2) (instrY_preserves O hcb hf hp h)
  | @seq is₁ is₂ t₁ t₂ t₃ hb h₁ h₂ ih₁ ih₂ =>
    show DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [ctxLGV L G,
      .list (instrsToV (is₁ ++ is₂)), itV (t₁.map tyV) [] (t₃.map tyV)])
    rw [Instr30.instrsToV_append]
    exact Instr30.dd_instrsSeq O hc (fragOkY_typed h₁) (fragOkY_typed h₂)
      (typedV_tys (fragOkY_bnd h₁).1) (typedV_tys hb) (typedV_tys (fragOkY_bnd h₂).2) ih₁ ih₂
  | @frame is ts t₁ t₂ hf _ h ih =>
    show DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [ctxLGV L G,
      .list (instrsToV is), itV ((ts ++ t₁).map tyV) [] ((ts ++ t₂).map tyV)])
    rw [List.map_append, List.map_append]
    exact Instr30.dd_instrsFrame O hc (fragOkY_typed h) (typedV_tys fun t ht => tyBnd_flat (hf t ht))
      (typedV_tys (fragOkY_bnd h).1) (typedV_tys (fragOkY_bnd h).2) ih (resulttypeOk_flat O hc hf)
  | @sub is ps rs ps' rs' h hs _ hp hr hlen ih =>
    exact dd_subY O hc (fragOkY_typed h) hs hp hr hlen ih

/-! ## Non-vacuity -/

/-- The context with one mutable `f64` global. -/
def gF64 : List CGlobalType := [⟨.var, .num (.float .f64)⟩]

/-- `f64` as a value type. -/
abbrev f64T : CValType := .num (.float .f64)

/-- Global index `0`. -/
def g0 : GlobalIdx := ⟨0⟩

/-- The code `global.get 0; f64.const 1; f64.add; global.set 0`. -/
def globalAddCode (one : BitVec 64) : List Instr :=
  [.globalGet g0, .floatConst .f64 one, .floatBinOp .f64 .add, .globalSet g0]

/-- Number types are bounded. -/
theorem bnd_f64s {ts : List CValType} (h : ∀ t ∈ ts, t = f64T) : ∀ t ∈ ts, Round4.tyBnd t = true :=
  fun t ht => (h t ht) ▸ rfl

/-- `global.get 0; f64.const 1; f64.add; global.set 0` at `[] -> []`, in `{globals := [mut f64]}`:
the constant is framed under the global's value, the add is sequenced after both, and the store
after the add. -/
theorem fragOkY_globalAdd (one : BitVec 64) : FragOkY [] gF64 (globalAddCode one) (.plain [] []) := by
  have hg : InstrOk (ctxLoc [] gF64) (.globalGet g0) (.plain [] [f64T]) :=
    .variable (.globalGet (m := .var) rfl)
  have hs : InstrOk (ctxLoc [] gF64) (.globalSet g0) (.plain [f64T] []) := .variable (.globalSet rfl)
  have hp (i : Instr) (it : InstrType) (hi : param i = false) : ParamOk i it :=
    fun h => absurd h (by simp [hi])
  have h1 : FragOkY [] gF64 [.globalGet g0] (.plain [] [f64T]) :=
    .instr rfl ⟨bnd_f64s (by simp), bnd_f64s (by simp)⟩ (hp _ _ rfl) hg
  have h2 : FragOkY [] gF64 [.floatConst .f64 one] (.plain [f64T] [f64T, f64T]) :=
    .frame (ts := [f64T]) (t₁ := []) (fun _ ht => (List.mem_singleton.1 ht) ▸ rfl) (fun _ ht => (List.mem_singleton.1 ht) ▸ TyOk.num _)
      (.instr rfl ⟨bnd_f64s (by simp), bnd_f64s (by simp)⟩ (hp _ _ rfl)
        (.numeric (.floatConst .f64 one)))
  have h3 : FragOkY [] gF64 [.floatBinOp .f64 .add] (.plain [f64T, f64T] [f64T]) :=
    .instr rfl ⟨bnd_f64s (by simp), bnd_f64s (by simp)⟩ (hp _ _ rfl)
      (.numeric (.floatBinOp .f64 .add))
  have h4 : FragOkY [] gF64 [.globalSet g0] (.plain [f64T] []) :=
    .instr rfl ⟨bnd_f64s (by simp), bnd_f64s (by simp)⟩ (hp _ _ rfl) hs
  have h12 := FragOkY.seq (bnd_f64s (by simp)) h1 h2
  have h123 := FragOkY.seq (bnd_f64s (by simp)) h12 h3
  exact FragOkY.seq (bnd_f64s (by simp)) h123 h4

/-- The context `{globals := [mut f64]}` is bounded. -/
theorem ctxBnd_gF64 : CtxBnd [] gF64 :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ hg => (List.mem_singleton.1 hg) ▸ rfl⟩

/-- `unreachable` at `[] -> [i32]`, through `Instrs_ok/sub` from its typing `[] -> [BOT]`: the
result `BOT` is a subtype of `i32`. -/
theorem fragOkY_unreachableBot : FragOkY [] [] [.unreachable] (.plain [] [Silmaril.Wasm.Validation.Ty.i32]) := by
  have hbot : InstrOk (ctxLoc [] []) .unreachable (.plain [] [.botv]) :=
    .parametric (.unreachable ⟨fun _ h => absurd h List.not_mem_nil,
      fun t ht => (List.mem_singleton.1 ht) ▸ TyOk.botv, fun _ h => absurd h List.not_mem_nil⟩)
  have h₀ : FragOkY [] [] [.unreachable] (.plain [] [.botv]) :=
    .instr rfl ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ rfl⟩
      (fun _ => ⟨fun t ht => (List.mem_singleton.1 (by simpa using ht)) ▸ rfl,
        fun _ h _ _ => nomatch h⟩) hbot
  exact .sub h₀ ⟨.nil, .cons Sub.botv .nil, fun _ h => absurd h List.not_mem_nil⟩
    ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ TyOk.num _,
      fun _ h => absurd h List.not_mem_nil⟩
    (fun _ h => absurd h List.not_mem_nil) (fun t ht => (List.mem_singleton.1 ht) ▸ trivial)
    ⟨by decide, by decide⟩

/-- The empty context is bounded. -/
theorem ctxBnd_nil : CtxBnd [] [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-! ## In the model `stepModel BI` -/

section Model

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- The model of the comorphism: `stepModel` at the concrete primitives `BI`. -/
local notation "MB" => Wasm30.stepModel (Round4Int.BI P hn host)

/-- **Core validation of `fragY` in `{locals, globals}` is preserved** in `stepModel BI`. -/
theorem instrY_sat {L : List LocalType} {G : List CGlobalType} (hb : CtxBnd L G) {i : Instr}
    {it : InstrType} (hf : fragY i = true) (hp : ParamOk i it) (h : InstrOk (ctxLoc L G) i it) :
    (MB).D "Instr_ok" "%|-%:%" [] (.tuple [ctxLGV L G, instrToV i, instrtypeV it]) :=
  instrY_preserves _ hb hf hp h

/-- **`FragOkY` derivations are `Instrs_ok` facts** of `stepModel BI`. -/
theorem instrsY_sat {L : List LocalType} {G : List CGlobalType} (hb : CtxBnd L G) {is : List Instr}
    {it : InstrType} (h : FragOkY L G is it) :
    (MB).D "Instrs_ok" "%|-%:%" [] (.tuple [ctxLGV L G, .list (instrsToV is), instrtypeV it]) :=
  fragOkY_dd _ hb h

/-- **Non-vacuity**: `global.get 0; f64.const 1; f64.add; global.set 0` at `[] -> []` is an
`Instrs_ok` fact of `stepModel BI` in `{GLOBALS [MUT F64]}`, and Core validates it in
`{globals := [mut f64]}`. -/
theorem globalAdd (one : BitVec 64) :
    (MB).D "Instrs_ok" "%|-%:%" []
        (.tuple [ctxLGV [] gF64, .list (instrsToV (globalAddCode one)), instrtypeV (.plain [] [])]) ∧
      InstrsOk (ctxLoc [] gF64) (globalAddCode one) (.plain [] []) :=
  ⟨instrsY_sat P hn host ctxBnd_gF64 (fragOkY_globalAdd one), fragOkY_sound (fragOkY_globalAdd one)⟩

/-- **Non-vacuity of `Instrs_ok/sub`**: `unreachable` at `[] -> [i32]`, derived from its typing at
`[] -> [BOT]` by `Instrs_ok/sub`, is an `Instrs_ok` fact of `stepModel BI` and Core-valid. -/
theorem unreachableBot :
    (MB).D "Instrs_ok" "%|-%:%" []
        (.tuple [ctxLGV [] [], .list (instrsToV [.unreachable]), instrtypeV (.plain [] [Silmaril.Wasm.Validation.Ty.i32])]) ∧
      InstrsOk (ctxLoc [] []) [.unreachable] (.plain [] [Silmaril.Wasm.Validation.Ty.i32]) :=
  ⟨instrsY_sat P hn host ctxBnd_nil fragOkY_unreachableBot, fragOkY_sound fragOkY_unreachableBot⟩

end Model

end Silmaril.Wasm.SpecTec.Institution.Instr30Y
