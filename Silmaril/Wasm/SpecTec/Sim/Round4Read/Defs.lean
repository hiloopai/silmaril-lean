module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs

/-!
# SpecTec ↔ Core 3.0, round 4, track r4-read: definitions

Round 3 left the backward rules of `Integrate.RemainingW` open and found that several of them are
false as stated: SpecTec fires where Core is stuck, at configurations Core validity rules out
(`docs/projects/spectec/README.md`). This track re-proves them **under validity**.

The validity facts are stated here explicitly, as `ReadValid`, because the round-4 definitions of
`ConfigOk`-based validity were not on `origin` when this track started:

* `Integrate.StoreOk c.store`: the store bounds (tables, segments and arrays below `2 ^ 32`
  entries; memories whole pages below `2 ^ 32` bytes). Core's `StoreOk` does not give them; they
  are the planned `Bounded` facts.
* `CodeIdx c.store c.frame c.code`: every table, memory, element and data index named by an
  instruction of the active code, at any depth of labels and handlers, and inside every frame
  against that frame's module, resolves in the store. This is what Core validation gives
  (`InstrOk` puts the index in the context, `FrameOk`/`ModuleInstOk` map the context's entries to
  store addresses), so it is the planned consequence of `ConfigOk`.

`ReadValid` is closed under the four context decompositions the backward recursion performs
(`Round4Read.readValid_mid`, `_label`, `_handler`, `_frame`), so the per-rule obligations may
assume it (`BackwardUpToV`, `RemainingV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The indices an instruction names resolve**, against the frame's module and the store. Only
the table, memory, element-segment and data-segment indices are constrained. -/
def Instr.IdxOk (s : Store H) (f : Frame) : Instr → Prop
  | .tableGet x | .tableSet x | .tableSize x | .tableGrow x | .tableFill x =>
      (s.table? f x).isSome
  | .tableCopy x y => (s.table? f x).isSome ∧ (s.table? f y).isSome
  | .tableInit x y => (s.table? f x).isSome ∧ (s.elem? f y).isSome
  | .elemDrop y => (s.elem? f y).isSome
  | .intLoad _ _ x _ | .floatLoad _ x _ | .intStore _ _ x _ | .floatStore _ x _
  | .vecLoad _ x _ | .vecLoadLane _ x _ _ | .vecStore x _ | .vecStoreLane _ x _ _
  | .memorySize x | .memoryGrow x | .memoryFill x => (s.mem? f x).isSome
  | .memoryCopy x y => (s.mem? f x).isSome ∧ (s.mem? f y).isSome
  | .memoryInit x y => (s.mem? f x).isSome ∧ (s.data? f y).isSome
  | .dataDrop y => (s.data? f y).isSome
  | _ => True

mutual
/-- `Instr.IdxOk` for every plain instruction of `a`, at any depth; a frame's body is checked
against the frame's own module. -/
def adminIdx (s : Store H) (f : Frame) : Admin → Prop
  | .plain i => Instr.IdxOk s f i
  | .label _ _ b => codeIdx s f b
  | .handler _ _ b => codeIdx s f b
  | .frame _ fi b => codeIdx s fi b
  | _ => True

/-- `adminIdx` along a code sequence. -/
def codeIdx (s : Store H) (f : Frame) : List Admin → Prop
  | [] => True
  | a :: l => adminIdx s f a ∧ codeIdx s f l
end

/-- **The validity facts the backward read rules use**: the store bounds and index resolution
(see the module doc for how they follow from `ConfigOk` and the planned bounds). -/
structure ReadValid (c : Config H) : Prop where
  /-- The store bounds. -/
  store : Integrate.StoreOk c.store
  /-- Every index of the active code resolves. -/
  idx : codeIdx c.store c.frame c.code

/-- **The per-rule backward obligations under a configuration predicate `V`**:
`Bwd.BackwardUpTo` with `V c` added to every field. `Bwd.BackwardUpTo` is the case `V := ⊤`. -/
structure BackwardUpToV (V : Config H → Prop) (env : Env) (hn : H → String)
    (P : Numerics.Profile) (host : HostSemantics H) : Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    V ⟨s, f, is⟩ → Typed env hn ⟨s, f, is⟩ →
    Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule. -/
  read : ∀ (i : Nat) (c : Config H) (w : Value), V c →
    Typed env hn c → Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule. -/
  step : ∀ (i : Nat), 6 ≤ i → ∀ (c : Config H) (w : Value), V c →
    Typed env hn c → Fires env "Step" i (.tuple [configV hn c, w]) → Bwd.BwdUpTo hn P host c w

/-- **A configuration predicate closed under the context decompositions** of the backward
recursion: the redex of a split, and the body of a label, a handler or a frame (in the frame's
own frame). -/
structure CtxClosed (V : Config H → Prop) : Prop where
  /-- `ctxt-instrs`. -/
  mid : ∀ (s : Store H) (f : Frame) (a b c : List Admin), V ⟨s, f, a ++ b ++ c⟩ → V ⟨s, f, b⟩
  /-- `ctxt-label`. -/
  label : ∀ (s : Store H) (f : Frame) n cont body, V ⟨s, f, [.label n cont body]⟩ → V ⟨s, f, body⟩
  /-- `ctxt-handler`. -/
  handler : ∀ (s : Store H) (f : Frame) n cs body,
    V ⟨s, f, [.handler n cs body]⟩ → V ⟨s, f, body⟩
  /-- `ctxt-frame`. -/
  frame : ∀ (s : Store H) (f fi : Frame) n body, V ⟨s, f, [.frame n fi body]⟩ → V ⟨s, fi, body⟩

/-- The `Step_read` rules this track dispatches under `ReadValid`: `table.size` (27), the
`table.fill`, `table.copy`, `table.init` rules 29–37 (`-oob` with index resolution, the
`otherwise` rules by firing the earlier rule), their `memory.*` counterparts `memory.size`
(52), 54–62, `array.len-array` (81), and the scalar trapping loads `load-num-oob` (38),
`load-pack-oob` (40), `ref.null` (63), `ref.func` (64) and `array.fill-oob` (83). -/
def readDoneV : List Nat :=
  [27, 29, 30, 31, 32, 33, 34, 35, 36, 37] ++ [52, 54, 55, 56, 57, 58, 59, 60, 61, 62] ++
    [81, 38, 40, 63, 64, 83]

/-- **The open backward rules, under validity**: `Integrate.RemainingW` with `ReadValid c`
added to every field and the rules of `readDoneV` removed from `read`. `RemainingW` implies it
(`remainingV_of_w`). -/
structure RemainingV (env : Env) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure` outside the dispatched lists. -/
  pure : ∀ i, i ∉ Bwd.pureDone → i ∉ Integrate.floatDone → i ∉ BwdPureStep.pureDone →
    ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), ReadValid ⟨s, f, is⟩ →
    Typed env hn ⟨s, f, is⟩ → Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read` outside the dispatched lists. -/
  read : ∀ i, i ∉ Bwd.readDoneUpTo → i ∉ BwdRead.readDone → i ∉ readDoneV →
    ∀ (c : Config H) (w : Value), ReadValid c → Typed env hn c →
    Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step` (index `≥ 6`) outside the dispatched lists. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
    ∀ (c : Config H) (w : Value), ReadValid c → Typed env hn c →
    Fires env "Step" i (.tuple [configV hn c, w]) → Bwd.BwdUpTo hn P host c w

/-- `RemainingW` (no validity) implies `RemainingV`. -/
theorem remainingV_of_w {env : Env} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (R : Integrate.RemainingW env hn P host) : RemainingV env hn P host where
  pure i h₁ h₂ h₃ s f is w _ hc hf := R.pure i h₁ h₂ h₃ s f is w hc hf
  read i h₁ h₂ _ c w _ hc hf := R.read i h₁ h₂ c w hc hf
  step i h6 h₁ h₂ c w _ hc hf := R.step i h6 h₁ h₂ c w hc hf

end Silmaril.Wasm.SpecTec.Sim.Round4Read
