module

public import Silmaril.Wasm.SpecTec.Sim.Round4.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round4Read.Thms
public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Thms

/-!
# SpecTec ↔ Core 3.0, round 4 integration: definitions

Round 4 had three tracks (r4-validity, r4-read, r4-fwd), each stated against its own notion of
validity. This topic joins them. Nothing in the tracks is changed; everything here is new.

* `CtxRes s f C`: every table, memory, element and data index of the context `C` resolves in the
  store `s` through the frame `f`. Core's `StateOk s f C` gives it, and it depends only on
  `C.frameView`, so it survives labels, local initialisation and the `RETURN` update of a frame.
  It is how `ConfigOk` gives `ReadValid` (`Round4Int.readValid_of_configOk`).
* `FamBwdV`: the backward rules that rounds 1–3 proved from the family bundles `Bwd.BwdHyps`
  (`Step_pure` in `Bwd.pureDone`, `Step_read` 11 and `Bwd.readDone`, `Step` in `Bwd.stepDone`),
  restated **rule by rule under `ReadValid`**. `BwdHyps` is refuted as a bundle
  (`ConfigOk.not_ctrlCall`: its `CtrlCall.valtypes` field is false), so the round-4 dispatch
  `Round4Read.backward_valid` that takes it is vacuous. `FamBwdV` asks only for the rule
  statements, on valid sources; `BwdHyps` implies it (`Round4Int.famBwdV_of_hyps`), so it is no
  stronger, and no refutation of it is known.
* `Parts`: what the frozen `Round4.Task.wholeStepValid` is reduced to here, for the concrete
  `B := Prims.builtins`. Every field is an open obligation; see `Round4Int.wholeStepValid_of_parts`
  and `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Int

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round4Read (ReadValid RemainingV)

variable {H : Type}

/-- **The context's indices resolve**: every table, memory, element segment and data segment the
context `C` declares is found in `s` through the frame `f`. -/
structure CtxRes (s : Store H) (f : Frame) (C : Context) : Prop where
  /-- Tables. -/
  table : ∀ {x : TableIdx} {tt : CTableType}, C.tables[x.toNat]? = some tt → (s.table? f x).isSome
  /-- Memories. -/
  mem : ∀ {x : MemIdx} {mt : MemoryType}, C.mems[x.toNat]? = some mt → (s.mem? f x).isSome
  /-- Element segments. -/
  elem : ∀ {y : ElemIdx} {rt : CRefType}, C.elems[y.toNat]? = some rt → (s.elem? f y).isSome
  /-- Data segments. -/
  data : ∀ {y : DataIdx}, C.datas[y.toNat]? = some () → (s.data? f y).isSome

/-- **The family rules of rounds 1–3, backward, rule by rule under `ReadValid`**: the fields of
`Round4Read.BackwardUpToV ReadValid` that `Round4Read.backwardUpToV_dispatch` takes from
`Bwd.BwdHyps`. -/
structure FamBwdV (env : Env) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- `Step_pure` in `Bwd.pureDone`. -/
  pure : ∀ i, i ∈ Bwd.pureDone → ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ReadValid ⟨s, f, is⟩ → Typed env hn ⟨s, f, is⟩ →
    Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read` 11 (`return_call_ref-frame-addr`) and `Bwd.readDone`. -/
  read : ∀ i, i ∈ Bwd.readDoneUpTo → ∀ (c : Config H) (w : Value), ReadValid c →
    Typed env hn c → Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step` in `Bwd.stepDone`. -/
  step : ∀ i, i ∈ Bwd.stepDone → ∀ (c : Config H) (w : Value), ReadValid c → Typed env hn c →
    Fires env "Step" i (.tuple [configV hn c, w]) → Bwd.BwdUpTo hn P host c w

/-- The concrete builtins of the simulation. -/
noncomputable abbrev BI (P : Profile) (hn : H → String) (host : HostSemantics H) : Builtins :=
  Prims.builtins P hn host

/-- A valid, bounded configuration: the source predicate of `Round4.Task.wholeStepValid`. -/
def Valid (c : Config H) : Prop := (∃ ts, ConfigOk c ts) ∧ Round4.Bounded c

/-- **What `Round4.Task.wholeStepValid` is reduced to**, at one encoding, host and profile, for
`B := Prims.builtins P hn host`. All five fields are open.

* `pos`: track r4-validity's positive typing of the encoding's leaves.
* `succTyped`: the Core successor of a valid, bounded configuration, when bounded, is `Typed`.
  It follows from `pos` for every `HostOk` host (`Round4Int.succTyped_of_hostOk`, through Core's
  `Step.preservation`); for other hosts it is a genuine condition, since a host may return an
  ill-typed store.
* `fwd`: the forward conjunct on valid sources (`Forward`). Track r4-fwd's
  `forward_concrete4_valid` gives it from round 2's `Residue` and `Extra` and `Open4`; the first
  two are refuted, so that route is vacuous, and `fwd` stays a hypothesis.
* `fam`, `rem`: the backward rules, under `ReadValid`: `FamBwdV` (rounds 1–3's family rules) and
  `RemainingV` (the rules no track has dispatched). -/
structure Parts (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Positive typing of the leaves. -/
  pos : Round4.PosTyping (BI P hn host) hn
  /-- Bounded Core successors of valid, bounded configurations are typed. -/
  succTyped : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round4.Bounded c →
    Round4.Bounded c' → Step P host c c' → Typed (simEnv (BI P hn host)) hn c'
  /-- The forward conjunct on valid sources. -/
  fwd : R4Fwd.Forward (BI P hn host) hn P host Valid
  /-- The family rules of rounds 1–3, backward, under `ReadValid`. -/
  fam : FamBwdV (simEnv (BI P hn host)) hn P host
  /-- The backward rules no track has dispatched, under `ReadValid`. -/
  rem : RemainingV (simEnv (BI P hn host)) hn P host

end Silmaril.Wasm.SpecTec.Sim.Round4Int
