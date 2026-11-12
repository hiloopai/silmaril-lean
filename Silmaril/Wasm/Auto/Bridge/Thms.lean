module

public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Wasm.Auto.Front.Defs
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Auto.EGraph.Thms
public import Silmaril.Wasm.Auto.ESeg.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Execution.Core.Typing.Store
import Silmaril.Proofs.Wasm.Auto.Bridge.Seg
import Silmaril.Proofs.Wasm.Auto.Bridge.Ext.Mod

/-!
# From segments to modules: results

## Function summaries

Proofs in `Silmaril.Proofs.Wasm.Auto.Bridge.{Beh,Func,Mod,EGraph,Lemmas,All,Partial,Exec}`. For the
function summaries of `Silmaril.Wasm.Auto.Bridge.Defs`:

* `behaviours_eq_of_tfspec`: a total specification (`TFSpecAt`, the every-run total-correctness
  logic) that pins the outcome to returning `rs` makes the host-free behaviour set of `$invoke`
  exactly `{returns rs}`;
* `twp_xexec`: the forward rule of the body executor `xexec` (straight-line integer code,
  `select`, `block` and `if` without branches) in the total reading, every profile and host;
* `tfspec_of_sumOf`, **`behaviours_of_fnSum`**: a summarised export terminates and returns
  `fnOut F vs` on every accepted argument list, at every profile;
* **`modEquiv_of_fnCheck`**, `modRefines_of_fnCheck`: equal normal forms of the results give
  `ModEquiv R P m₁ m₂ j` and `ModRefines R P m₁ m₂ j` for every reflexive `R` (both front-end
  relations, `rel_refl`) and **every profile** `P`;
* `modEquiv_of_fnResiduals`: the same when the residual bitvector goals are proved;
* `modEquiv_of_out`, `modRefines_of_out`: the general form (equal results on typed arguments);
* `modMeets_of_fnSum`: a reference function agreeing with the summary is met;
* `lemmaGoals_hold`, `modEquiv_of_discharged`: the lemma library of residual goals (the
  `div10` identity);
* **`modEquiv_of_egraph`**: an e-graph certificate (`Silmaril.Wasm.Auto.EGraph.SegEquiv`) on the
  bodies of two summarised exports with the same local types proves `ModEquiv` at every profile,
  under the decidable side conditions `egraphLiftOk` and the definitional equations naming the
  bodies (`kernel_rfl`);
* `modEquiv_of_checkAll`, `egraphLiftOk_of_liftAll`: the same read off one kernel evaluation of
  `checkAll`/`liftAll` over every export (certificates of whole optimizer passes);
* `meets_orDiv_of_fspecValid`: a partial-correctness specification (`FSpecValid`, e.g. the VC
  generator's `genFunc_sound`) gives `Equiv.Meets` up to divergence (`OrDiv R`).

## The extended summaries

Proofs in `Silmaril.Proofs.Wasm.Auto.Bridge.Ext.{Beh,Func,Mod}`. For the summaries of
`Silmaril.Wasm.Auto.Bridge.Defs` (the extended executor of the equivalence checker run on whole
bodies, from the call frame, the instance's globals and memory `0`):

* `behaviours_eq_trap_of_tfspec`, `behaviours_eq_res_of_tfspec`: a total specification that pins
  a trap (or a result that returns or traps) gives the exact host-free behaviour set;
* `tfspecX_of_sumOfX`: a summarised function has the total specification "its outcome is that of
  `fnOutX F vs`", every profile and host relation;
* **`behaviours_of_fnSumX`**: every accepted invocation of a summarised export terminates, and
  returns or traps as `fnOutX F vs` says, at every profile;
* `modEquiv_of_outX`: equal results give `ModEquiv` (both front-end relations, every profile);
* **`modEquiv_of_fnCheckX`**: the check `fnCheckX` (same parameters and global values, the same
  memory where it matters, the same guards up to the simplifier, equal simplified results)
  proves `ModEquiv`;
* **`modEquiv_of_checkAmong`**: entry `i` of `checkAmong m₁ m₂ js` (both summarisers, each
  module instantiated once) proves `ModEquiv` at export `js[i]`; certificates of optimizer runs
  evaluate it once per chunk of exports.

What the statements observe: one invocation of the export from the instantiated store, its
result or trap (silmaril-lean's behaviour sets). Changes to globals and memory are not part of a
behaviour, so two functions that return the same values but leave different globals are
`ModEquiv`; return the globals to compare them.

## Summaries with locals

Proofs in `Silmaril.Proofs.Wasm.Auto.Bridge.Seg`.

* **`modEquiv_of_funcEquiv`**: an e-graph certificate `Silmaril.Wasm.Auto.ESeg.FuncEquiv Γ da db a b`
  (from `wasm-egraph tv-seg --func`: bodies with parameters `Γ` and declared locals `da`, `db`,
  compared from function entry; covers renumbered, merged and retyped locals) on the bodies of
  export `j` proves `Silmaril.Wasm.Auto.Front.ModEquiv R P m₁ m₂ j` at every profile, for every
  reflexive `R`, under the decidable side conditions `egraphFuncOk` (both exports summarised by
  `Silmaril.Wasm.Auto.Bridge.fnSum?`, plain bodies). This is the `egraph-seg` stage of
  `wasm-check pass --egraph-tv-seg`.
* `entryFrame_fnInit`, `sameParams_fnInit`: the summaries' initial frames are entry frames with
  the same parameters.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Bridge

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.Bridge` -/

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Beh.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Auto.Front (ExportRefines)

/-- A result whose code is `vals rs` returns `rs`. -/
theorem result_eq_of_vals {r : Result} {rs : List Val} (h : r.toAdmin = vals rs) :
    r = .values rs :=
  Silmaril.Proofs.Wasm.Auto.Bridge.result_eq_of_vals (r := r) (rs := rs) (h := h)

/-- **The behaviour set of a function with a total specification that pins the result**
(host-free). -/
theorem behaviours_eq_of_tfspec {H : Type} {P : Profile} {a : Nat} {S : FSpec H} {s : Store H}
    {args rs : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal rs) :
    behaviours P SingleThreaded.Det.noHost s a args = {.returns rs} :=
  Silmaril.Proofs.Wasm.Auto.Bridge.behaviours_eq_of_tfspec (H := H) (P := P) (a := a) (S := S) (s := s)
    (args := args) (rs := rs) (h := h) (hpre := hpre) (hpost := hpost)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Exec.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)

theorem den_selT {ρ : Env} (t : IntType) (a b c : Term) :
    den ρ (t, selT a b c) = if ev ρ .i32 c ≠ 0 then den ρ (t, a) else den ρ (t, b) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.den_selT (ρ := ρ) (t := t) (a := a) (b := b) (c := c)

/-- A nested body from an empty stack, as `twp_block_vals` wants it. -/
theorem BodyOk.body {H : Type} {P : Profile} {host : HostSemantics H} {ρ : Env}
    {rec : SState → List Instr → Option SState} (ih : BodyOk P host ρ rec)
    {ls : List (IntType × Term)} {st : List (IntType × Term)} {A : SState} {body : List Instr}
    (h : rec ⟨ls, []⟩ body = some A) (s : Store H) (f : Frame) (Q' : Post H)
    (hw : TWP P host s (frameAt f ρ A) (vals (stackAt ρ A).reverse) Q') :
    TWP P host s (frameAt f ρ ⟨ls, st⟩) (expression body) Q' :=
  Silmaril.Proofs.Wasm.Auto.Bridge.BodyOk.body (H := H) (P := P) (host := host) (ρ := ρ) (rec := rec)
    (ih := ih) (ls := ls) (st := st) (A := A) (body := body) (h := h) (s := s) (f := f) (Q' := Q')
    (hw := hw)

/-- **The forward rule for symbolic execution of a body.** -/
theorem twp_xexec {H : Type} {P : Profile} {host : HostSemantics H} {ρ : Env}
    (n : Nat) : BodyOk P host ρ (xexec n) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.twp_xexec (H := H) (P := P) (host := host) (ρ := ρ) (n := n)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Func.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf isInstance_of_instance?)
open Silmaril.Wasm.Auto.Front (addrOf)

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length :=
  Silmaril.Proofs.Wasm.Auto.Bridge.mapM_length (α := α) (β := β) (f := f)

theorem typedVals_nil : TypedVals [] [] :=
  Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_nil

/-- **A summary is a total specification**, at every profile and host relation. -/
theorem tfspec_of_sumOf {H : Type} {P : Profile} {host : HostSemantics H} {ft : FnType}
    {fi : FuncInst H} {F : FnSum} (h : sumOf ft fi = some F)
    {s₀ : Store H} {a : Nat} (hfi : s₀.funcs[a]? = some fi) (he : Expand fi.type ft.toComp) :
    TFSpecAt P host a (sumSpec F s₀) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.tfspec_of_sumOf (H := H) (P := P) (host := host) (ft := ft)
    (fi := fi) (F := F) (h := h) (s₀ := s₀) (a := a) (hfi := hfi) (he := he)

/-- **The behaviour set of a summarised export**: every accepted invocation terminates and
returns `fnOut F vs`, at every profile. -/
theorem behaviours_of_fnSum {P : Profile} {m : Module} {j : Nat} {F : FnSum}
    (h : fnSum? m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs = {.returns (fnOut F vs)} :=
  Silmaril.Proofs.Wasm.Auto.Bridge.behaviours_of_fnSum (P := P) (m := m) (j := j) (F := F) (h := h)
    (vs := vs) (hvs := hvs)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Mod.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post exec)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf isInstance_of_instance?)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ModMeets Rel specOfFn)

/-- **Refinement from equal results.** -/
theorem modRefines_of_out {P : Profile} {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSum} (hA : fnSum? m₁ j = some A)
    (hB : fnSum? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOut A vs = fnOut B vs) :
    ModRefines R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modRefines_of_out (P := P) (R := R) (hR := hR) (m₁ := m₁) (m₂ := m₂)
    (j := j) (A := A) (B := B) (hA := hA) (hB := hB) (hp := hp) (hout := hout)

/-- **Equivalence from equal results.** -/
theorem modEquiv_of_out {P : Profile} {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSum} (hA : fnSum? m₁ j = some A)
    (hB : fnSum? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOut A vs = fnOut B vs) :
    ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_out (P := P) (R := R) (hR := hR) (m₁ := m₁) (m₂ := m₂)
    (j := j) (A := A) (B := B) (hA := hA) (hB := hB) (hp := hp) (hout := hout)

/-- **The function-level check proves module refinement**, every profile, every reflexive
relation. -/
theorem modRefines_of_fnCheck {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheck m₁ m₂ j = true) : ModRefines R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modRefines_of_fnCheck (P := P) (R := R) (hR := hR) (m₁ := m₁)
    (m₂ := m₂) (j := j) (h := h)

/-- **The function-level check proves module equivalence.** -/
theorem modEquiv_of_fnCheck {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheck m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_fnCheck (P := P) (R := R) (hR := hR) (m₁ := m₁)
    (m₂ := m₂) (j := j) (h := h)

/-- **Residual goals**: proofs of the remaining bitvector equations give module equivalence. -/
theorem modEquiv_of_fnResiduals {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {gs : List Goal} (h : fnResiduals m₁ m₂ j = some gs)
    (hg : ∀ g ∈ gs, g.Holds) : ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_fnResiduals (P := P) (R := R) (hR := hR) (m₁ := m₁)
    (m₂ := m₂) (j := j) (gs := gs) (h := h) (hg := hg)

/-- **Reference functions**: a summarised export meets `f` if `f` agrees with the summary (or
leaves the result open) on typed arguments. -/
theorem modMeets_of_fnSum {P : Profile} {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m : Module} {j : Nat} {F : FnSum} (h : fnSum? m j = some F) {f : List Val → Option Result}
    (hf : ∀ vs, TypedVals F.params vs → f vs = some (.values (fnOut F vs)) ∨ f vs = none) :
    ModMeets R P m j f :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modMeets_of_fnSum (P := P) (R := R) (hR := hR) (m := m) (j := j)
    (F := F) (h := h) (f := f) (hf := hf)

/-- Every front-end relation is reflexive. -/
theorem rel_refl (R : Rel) : ∀ b, R.toProp b b :=
  Silmaril.Proofs.Wasm.Auto.Bridge.rel_refl (R := R)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/EGraph.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Core (exec localVal?)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModEquiv)

/-- A frame denoted by a symbolic state with locals of types `Γ` is typed by `Γ`. -/
theorem frameOk_frameAt {Γ : List IntType} {S : SState} (hΓ : S.locals.map (·.1) = Γ)
    (hn : Γ.length < 2 ^ 32) (f : Frame) (ρ : Env) : EGraph.FrameOk Γ (frameAt f ρ S) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.frameOk_frameAt (Γ := Γ) (S := S) (hΓ := hΓ) (hn := hn) (f := f)
    (ρ := ρ)

/-- **An e-graph certificate on the bodies proves module equivalence**, at every profile, for
every reflexive relation, under the decidable side conditions `egraphLiftOk`. -/
theorem modEquiv_of_egraph {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Profile} {m₁ m₂ : Module} {j : Nat} {Γ : List IntType} {a b : List Instr}
    (hok : egraphLiftOk m₁ m₂ j Γ = true) (ha : fnBody? m₁ j = some (Γ, a))
    (hb : fnBody? m₂ j = some (Γ, b)) (h : EGraph.SegEquiv Γ a b) :
    ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_egraph (R := R) (hR := hR) (P := P) (m₁ := m₁)
    (m₂ := m₂) (j := j) (Γ := Γ) (a := a) (b := b) (hok := hok) (ha := ha) (hb := hb) (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Lemmas.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Front (ModEquiv)

/-- The `div10` goal of the lemma library holds. -/
theorem div10_goal : Goal.Holds (.i64, div10Lhs, .bin (.div .unsigned) (.var 0) (.const 10)) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.div10_goal

theorem lemmaGoals_hold : ∀ g ∈ lemmaGoals, g.Holds :=
  Silmaril.Proofs.Wasm.Auto.Bridge.lemmaGoals_hold

/-- **Residual goals in the lemma library prove module equivalence**, every profile. -/
theorem modEquiv_of_discharged {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Numerics.Profile} {m₁ m₂ : Module} {j : Nat} {gs : List Goal}
    (h : fnResiduals m₁ m₂ j = some gs) (hd : discharged gs = true) : ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_discharged (R := R) (hR := hR) (P := P) (m₁ := m₁)
    (m₂ := m₂) (j := j) (gs := gs) (h := h) (hd := hd)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/All.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Verify (instance?)
open Silmaril.Wasm.Auto.Front (ModEquiv)

/-- **Entry `j` of `checkAll` proves module equivalence at export `j`**, every profile. -/
theorem modEquiv_of_checkAll {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Profile} {m₁ m₂ : Module} {j : Nat} (h : (checkAll m₁ m₂)[j]? = some true) :
    ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_checkAll (R := R) (hR := hR) (P := P) (m₁ := m₁)
    (m₂ := m₂) (j := j) (h := h)

/-- **Entry `j` of `liftAll` gives the e-graph side conditions at export `j`.** -/
theorem egraphLiftOk_of_liftAll {m₁ m₂ : Module} {j : Nat} {Γ : List IntType}
    (h : (liftAll m₁ m₂)[j]? = some (some Γ)) : egraphLiftOk m₁ m₂ j Γ = true :=
  Silmaril.Proofs.Wasm.Auto.Bridge.egraphLiftOk_of_liftAll (m₁ := m₁) (m₂ := m₂) (j := j) (Γ := Γ)
    (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Partial.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- **Partial correctness against a reference specification** `σ`: every finite behaviour is
allowed by `σ` (`R`-related, `R` reflexive), divergence aside. -/
theorem meets_orDiv_of_fspecValid {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b)
    {s : Store Nat} {a : Nat} {S : FSpec Nat} {σ : Equiv.ImportSpec Val}
    (h : FSpecValid P SingleThreaded.Det.noHost a S)
    (hpre : ∀ vs, InvokeOk s a vs → S.pre s vs)
    (hpost : ∀ vs s' o, InvokeOk s a vs → S.post s vs s' o →
      ∃ res, o = .normal res ∧ Behaviour.returns res ∈ σ vs)
    (hne : ∀ vs, (σ vs).Nonempty) :
    Equiv.Meets (entryPoints P SingleThreaded.Det.noHost) (OrDiv R) s a σ :=
  Silmaril.Proofs.Wasm.Auto.Bridge.meets_orDiv_of_fspecValid (P := P) (R := R) (hR := hR) (s := s)
    (a := a) (S := S) (σ := σ) (h := h) (hpre := hpre) (hpost := hpost) (hne := hne)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Ext/Beh.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

theorem trap_not_mem_vals (vs : List Val) : Admin.trap ∉ vals vs :=
  Silmaril.Proofs.Wasm.Auto.Bridge.trap_not_mem_vals (vs := vs)

/-- A configuration that exits with a trap reaches the trapped configuration. -/
theorem steps_trap {H : Type} {P : Profile} {c : Config H} {vs : List Val} {rest : List Admin}
    (hc : c.code = vals vs ++ .trap :: rest) :
    ∃ c' : Config H, Steps P SingleThreaded.Det.noHost c c' ∧ c'.code = [.trap] :=
  Silmaril.Proofs.Wasm.Auto.Bridge.steps_trap (H := H) (P := P) (c := c) (vs := vs) (rest := rest)
    (hc := hc)

/-- **The behaviour set of a function with a total specification that pins a trap**
(host-free). -/
theorem behaviours_eq_trap_of_tfspec {H : Type} {P : Profile} {a : Nat} {S : FSpec H} {s : Store H}
    {args : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .trap) :
    behaviours P SingleThreaded.Det.noHost s a args = {.traps} :=
  Silmaril.Proofs.Wasm.Auto.Bridge.behaviours_eq_trap_of_tfspec (H := H) (P := P) (a := a) (S := S)
    (s := s) (args := args) (h := h) (hpre := hpre) (hpost := hpost)

/-- **The behaviour set of a function whose total specification pins a result** that returns
or traps. -/
theorem behaviours_eq_res_of_tfspec {H : Type} {P : Profile} {a : Nat} {S : FSpec H} {s : Store H}
    {args : List Val}
    {r : Result} (hr : ∀ x, r ≠ .throw x) (h : TFSpecAt P SingleThreaded.Det.noHost a S)
    (hpre : S.pre s args) (hpost : ∀ s' o, S.post s args s' o → o = resOutcome r) :
    behaviours P SingleThreaded.Det.noHost s a args = {r.toBehaviour} :=
  Silmaril.Proofs.Wasm.Auto.Bridge.behaviours_eq_res_of_tfspec (H := H) (P := P) (a := a) (S := S)
    (s := s) (args := args) (r := r) (hr := hr) (h := h) (hpre := hpre) (hpost := hpost)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Ext/Func.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals den)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf)

theorem setGlobal_self {H : Type} {s : Store H} {a : Nat} {v : Val}
    (h : s.globals[a]?.map (·.value) = some v) : s.setGlobal a v = s :=
  Silmaril.Proofs.Wasm.Auto.Bridge.setGlobal_self (H := H) (s := s) (a := a) (v := v) (h := h)

theorem setGlobals_self {H : Type} (s : Store H) :
    ∀ {ga : List Nat} {gv : List Val},
      ga.mapM (fun a => s.globals[a]?.map (·.value)) = some gv → setGlobals s ga gv = s :=
  Silmaril.Proofs.Wasm.Auto.Bridge.setGlobals_self (H := H) (s := s)

theorem setMem_self {H : Type} {s : Store H} {a : Nat} {mi : MemInst} (h : s.mems[a]? = some mi) :
    s.setMem a mi = s :=
  Silmaril.Proofs.Wasm.Auto.Bridge.setMem_self (H := H) (s := s) (a := a) (mi := mi) (h := h)

/-- **A summary is a total specification**, at every profile and host relation. -/
theorem tfspecX_of_sumOfX {H : Type} {P : Profile} {host : HostSemantics H} {s₀ : Store H}
    {ft : FnType} {fi : FuncInst H} {F : FnSumX}
    (h : sumOfX s₀ ft fi = some F) {a : Nat} (hfi : s₀.funcs[a]? = some fi)
    (he : Expand fi.type ft.toComp) : TFSpecAt P host a (sumSpecX F s₀) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.tfspecX_of_sumOfX (H := H) (P := P) (host := host) (s₀ := s₀)
    (ft := ft) (fi := fi) (F := F) (h := h) (a := a) (hfi := hfi) (he := he)

/-- **The behaviour set of a summarised export**: every accepted invocation terminates, and
returns or traps as `fnOutX F vs` says, at every profile. -/
theorem behaviours_of_fnSumX {P : Profile} {m : Module} {j : Nat} {F : FnSumX}
    (h : fnSumX? m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs =
      {(fnOutX F vs).toBehaviour} :=
  Silmaril.Proofs.Wasm.Auto.Bridge.behaviours_of_fnSumX (P := P) (m := m) (j := j) (F := F) (h := h)
    (vs := vs) (hvs := hvs)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Bridge/Ext/Mod.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ExportRefines)

/-- **Equivalence from equal results.** -/
theorem modEquiv_of_outX {P : Profile} {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumX? m₁ j = some A)
    (hB : fnSumX? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_outX (P := P) (R := R) (hR := hR) (m₁ := m₁) (m₂ := m₂)
    (j := j) (A := A) (B := B) (hA := hA) (hB := hB) (hp := hp) (hout := hout)

/-- **The check proves module equivalence**, every profile, every reflexive relation. -/
theorem modEquiv_of_fnCheckX {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheckX m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_fnCheckX (P := P) (R := R) (hR := hR) (m₁ := m₁)
    (m₂ := m₂) (j := j) (h := h)

/-- **Entry `i` of `checkAmong m₁ m₂ js` proves module equivalence at export `js[i]`**, every
profile. -/
theorem modEquiv_of_checkAmong {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {js : List Nat} {i j : Nat} (hj : js[i]? = some j)
    (h : (checkAmong m₁ m₂ js)[i]? = some true) : ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_checkAmong (P := P) (R := R) (hR := hR) (m₁ := m₁)
    (m₂ := m₂) (js := js) (i := i) (j := j) (hj := hj) (h := h)

/-- **Entry `i` of `liftAmong m₁ m₂ js` gives the e-graph side conditions at export `js[i]`.** -/
theorem egraphLiftOk_of_liftAmong {m₁ m₂ : Module} {js : List Nat} {i j : Nat}
    {Γ : List IntType} (hj : js[i]? = some j) (h : (liftAmong m₁ m₂ js)[i]? = some (some Γ)) :
    Bridge.egraphLiftOk m₁ m₂ j Γ = true :=
  Silmaril.Proofs.Wasm.Auto.Bridge.egraphLiftOk_of_liftAmong (m₁ := m₁) (m₂ := m₂) (js := js) (i := i)
    (j := j) (Γ := Γ) (hj := hj) (h := h)

end

end Silmaril.Wasm.Auto.Bridge

namespace Silmaril.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Core (exec localVal?)
open Silmaril.Wasm.Auto.Front (ModEquiv)

/-- The frame of `fnInit Γ ds` is an entry frame. -/
theorem entryFrame_fnInit {Γ ds : List IntType} (hn : (Γ ++ ds).length < 2 ^ 32) (ρ : Env) :
    ESeg.EntryFrame Γ ds (frameAt {} ρ (fnInit Γ ds)) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.entryFrame_fnInit hn ρ

/-- The frames of `fnInit Γ da` and `fnInit Γ db` hold the same parameters. -/
theorem sameParams_fnInit (Γ da db : List IntType) (hn : Γ.length < 2 ^ 32) (ρ : Env) :
    ESeg.SameParams Γ.length (frameAt {} ρ (fnInit Γ da)) (frameAt {} ρ (fnInit Γ db)) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.sameParams_fnInit Γ da db hn ρ

/-- **A function-entry certificate on the bodies proves module equivalence**, at every
profile, for every reflexive relation, under the decidable side conditions `egraphFuncOk`. -/
theorem modEquiv_of_funcEquiv {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Profile} {m₁ m₂ : Module} {j : Nat} {Γ da db : List IntType} {a b : List Instr}
    (hok : egraphFuncOk m₁ m₂ j Γ da db = true) (ha : fnBody? m₁ j = some (Γ ++ da, a))
    (hb : fnBody? m₂ j = some (Γ ++ db, b)) (h : ESeg.FuncEquiv Γ da db a b) :
    ModEquiv R P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Bridge.modEquiv_of_funcEquiv hR hok ha hb h

/-! ## Results used by `Silmaril.Wasm.Auto2` -/

section
-- Lemmas of `Silmaril.Proofs.Wasm.Auto.Bridge` that the proofs of `Silmaril.Wasm.Auto2` (summaries,
-- calls, kernel checks) use.

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals den)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post Outcome)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ExportRefines)
open Silmaril.Wasm.Validation

/-- Zero-initialised locals, as summary terms and as the call frame's default values. -/
theorem locals_zero (σ : List CTypeUse) :
    ∀ {lts : List ValType} {ls : List IntType} (ρ : Env), lts.mapM intTy? = some ls →
      (ls.map fun t => (t, Term.const 0)).map (fun p => some (den ρ p)) =
        lts.map fun t => defaultVal? ((liftVal t).substAll σ) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.locals_zero σ

/-- The type of an instantiated export expands to its signature. -/
theorem export_expand {mt : CModuleType} {I : ScalarInstance} {m : Module}
    (hI : instance? m = some (mt, I)) {j : Nat} {ft : FnType} {fi : FuncInst Nat}
    (hft : I.exports[j]? = some ft) (hfi : I.store.funcs[I.addrs.getD j 0]? = some fi) :
    Expand fi.type ft.toComp :=
  Silmaril.Proofs.Wasm.Auto.Bridge.export_expand hI hft hfi

/-- Well-typed scalar arguments are typed integer values. -/
theorem typedVals_of_forall₂ {H : Type} {s : Store H} :
    ∀ {ps : List ScalarType} {ts : List IntType} {vs : List Val},
      ps.mapM scalarInt? = some ts →
      List.Forall₂ (ValOk s) vs (ps.map ScalarType.toC) → TypedVals ts vs :=
  Silmaril.Proofs.Wasm.Auto.Bridge.typedVals_of_forall₂

theorem bytes_ctxOf {H : Type} (s : Store H) (mi : ModuleInst) (args : List Val)
    (lts : List ValType) (ρ : Env) : (ctxOf s mi args lts ρ).mi.bytes = bytesOf (memOf s mi) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.bytes_ctxOf s mi args lts ρ

theorem frameOf_init {H : Type} {ps ls gt : List IntType} {lts : List ValType}
    {args gv : List Val} (hargs : TypedVals ps args) (hls : lts.mapM intTy? = some ls)
    (s : Store H) (mi : ModuleInst) :
    (ctxOf s mi args lts (envOfVals (args ++ gv))).frameOf (fnInitX ps ls gt) =
      Frame.forCall mi args lts :=
  Silmaril.Proofs.Wasm.Auto.Bridge.frameOf_init hargs hls s mi

theorem globsUsed_ok {H : Type} (s : Store H) (mi : ModuleInst) :
    GlobsOk s mi (globsUsed s mi).1 (globsUsed s mi).2.1 (globsUsed s mi).2.2 :=
  Silmaril.Proofs.Wasm.Auto.Bridge.globsUsed_ok s mi

theorem good_ctxOf {H : Type} (s : Store H) (mi : ModuleInst) (args : List Val)
    (lts : List ValType) (ρ : Env) : (ctxOf s mi args lts ρ).Good (memOf s mi).isSome :=
  Silmaril.Proofs.Wasm.Auto.Bridge.good_ctxOf s mi args lts ρ

theorem map_denX_zeros (ρ : Env) (B0 : ByteArray) (ls : List IntType) :
    (ls.map fun t => (t, XT.const 0)).map (fun p => some (denX ρ B0 p)) =
      (ls.map fun t => (t, Silmaril.Wasm.Auto.Equiv.Term.const 0)).map (fun p => some (den ρ p)) :=
  Silmaril.Proofs.Wasm.Auto.Bridge.map_denX_zeros ρ B0 ls

theorem storeOf_init {H : Type} {ps ls : List IntType} {lts : List ValType} {args : List Val}
    (hargs : TypedVals ps args) (s : Store H) (mi : ModuleInst) :
    (ctxOf s mi args lts (envOfVals (args ++ (globsUsed s mi).2.1))).storeOf (memOf s mi).isSome
      (fnInitX ps ls (globsUsed s mi).2.2) = s :=
  Silmaril.Proofs.Wasm.Auto.Bridge.storeOf_init hargs s mi

/-- Two exports whose behaviour sets are the same singleton on every accepted argument list
refine each other (for a reflexive `R`). -/
theorem exportRefines_of_singletonB {P : Profile} {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b) {s₁ s₂ : Store Nat} {a₁ a₂ : Nat} (g : List Val → Behaviour Val)
    (h₁ : ∀ vs, InvokeOk s₁ a₁ vs → behaviours P SingleThreaded.Det.noHost s₁ a₁ vs = {g vs})
    (h₂ : ∀ vs, InvokeOk s₁ a₁ vs → behaviours P SingleThreaded.Det.noHost s₂ a₂ vs = {g vs}) :
    ExportRefines R P s₁ a₁ s₂ a₂ :=
  Silmaril.Proofs.Wasm.Auto.Bridge.exportRefines_of_singletonB hR g h₁ h₂

theorem outAt_indep {S : XState} (h : usesMem S = false) (ρ : Env) (B0 B1 : ByteArray) :
    outAt ρ B0 S = outAt ρ B1 S :=
  Silmaril.Proofs.Wasm.Auto.Bridge.outAt_indep h ρ B0 B1

/-- The `div10` goal as a `BitVec 64` identity (Granlund–Montgomery division by `10`). -/
theorem div10_bv64 (x : BitVec 64) :
    ((3435973836#64 * (x >>> 32) +
        ((((4294967295#64 &&& 3435973836#64 * (x &&& 4294967295#64)) +
              ((4294967295#64 &&& 3435973837#64 * (x >>> 32)) +
                (3435973837#64 * (x &&& 4294967295#64)) >>> 32)) >>> 32) +
          ((3435973836#64 * (x &&& 4294967295#64)) >>> 32 +
            (3435973837#64 * (x >>> 32)) >>> 32))) >>> 3) = x / 10#64 :=
  Silmaril.Proofs.Wasm.Auto.Bridge.div10_bv64 x

end

end Silmaril.Wasm.Auto.Bridge
