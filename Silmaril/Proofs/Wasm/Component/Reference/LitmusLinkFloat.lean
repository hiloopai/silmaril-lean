module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusSoundI
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkConds
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkInst
public import Silmaril.Proofs.Wasm.Component.Reference.LinkWire
public import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatSeq
public import Silmaril.Wasm.Component.Reference.LinkFloat.Defs

/-!
# Litmus: a linked importer with an `f32` export

`dblFhL`: the doubler `dblS` answers the import `g` of `fhS`, which exports `f(x) = g(x)` and
the identity `h: func(f32) -> f32`. The importer's imports are float-free, its export `h` is
not, so `Linked2.sound` does not apply but `linked2_sound_floatV` and
`linked2_sound_seq_floatV` do. The instance of `fhCore3` is computed by kernel evaluation of a
Boolean summary (`fhSummary`), as for `fwdCore3`.

* `dblFh_sound_floatV`: a call `h(x)` is the linked IR call on an admissible lowering of `x`;
* `dblFh_sound_seq_floatV`: calls `h(xᵢ)` and then `h(x)` on one instance are the linked IR
  play of admissible lowerings, results reported canonicalised;
* `dblFh_sound_seq_floatV_deterministic`: under the deterministic component profile, the IR
  plays the canonicalised arguments.

Only the reference-to-IR direction is instantiated: the IR denotation of `dblFhL` is not
computed here.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Proofs.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## The instance of `fhCore3` -/

/-- The scalar type `(f32) -> (f32)`. -/
abbrev fhFn : FnType := ⟨[.num (.float .f32)], [.num (.float .f32)]⟩

/-- The closed import types of `fhCore3`. -/
def fhImports : List DefType :=
  match validate? fhCore3 with
  | some mt => CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `fhCore3` against one host function. -/
def fhStore : Store Nat :=
  match instantiateOnce? (importStore fhImports) fhCore3 [.func 0] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `fhCore3`. -/
def fhInst : ScalarInstance where
  imports := [fwdFn]
  exports := [fwdFn, fhFn]
  addrs := [0, 1]
  store := fhStore

/-- The checks on the instantiated store and frame. -/
def fhBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0, 1] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some fwdFn, some fhFn]

/-- The Boolean summary of the validation and instantiation of `fhCore3`. -/
def fhSummary : Bool :=
  match validate? fhCore3 with
  | some mt => decide (mt.imports = [.func (ofFlatType ⟨[.int .i32], [.int .i32]⟩)]) &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some fwdFn] &&
      runOk fhBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) fhCore3
        [.func 0])
  | none => false

theorem fhSummary_eq : fhSummary = true := by decide +kernel

/-- A list whose image is a pair is a pair. -/
theorem map_pair {α β : Type} {g : α → Option β} {b₁ b₂ : β} :
    ∀ {l : List α}, l.map g = [some b₁, some b₂] →
      ∃ a₁ a₂, l = [a₁, a₂] ∧ g a₁ = some b₁ ∧ g a₂ = some b₂
  | [a₁, a₂], h => ⟨a₁, a₂, rfl, by simp_all⟩
  | [], h => nomatch h
  | [_], h => by simp at h
  | _ :: _ :: _ :: _, h => by simp at h

/-- The facts the summary records. -/
theorem fhFacts : ∃ mt, validate? fhCore3 = some mt ∧
    mt.imports = [.func (ofFlatType ⟨[.int .i32], [.int .i32]⟩)] ∧
    (CExternType.funcs mt.imports).map FnType.ofDefType? = [some fwdFn] ∧
    ∃ f : Frame, instantiateOnce? (importStore (CExternType.funcs mt.imports)) fhCore3
      [.func 0] = some (fhStore, f, none) ∧ exportFuncAddrs f.module = [0, 1] ∧
      (fhStore.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
        [some fwdFn, some fhFn] := by
  have h : fhSummary = true := fhSummary_eq
  unfold fhSummary at h
  split at h
  next mt hmt =>
    have h' : (mt.imports = [.func (ofFlatType ⟨[.int .i32], [.int .i32]⟩)] ∧
        (CExternType.funcs mt.imports).map FnType.ofDefType? = [some fwdFn]) ∧
        runOk fhBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) fhCore3
          [.func 0]) = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h
    obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
    have himp : fhImports = CExternType.funcs mt.imports := by simp only [fhImports, hmt]
    have hs : fhStore = s := by simp only [fhStore, himp, hrun]
    have hb' : exportFuncAddrs f.module = [0, 1] ∧
        (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
          [some fwdFn, some fhFn] := by
      simpa only [fhBody, Bool.and_eq_true, beq_iff_eq] using hb
    exact ⟨mt, hmt, h'.1.1, h'.1.2, f, hs ▸ hrun, hb'.1, hs ▸ hb'.2⟩
  next => cases h

/-- `fhInst` is the instance of `fhMod`. -/
theorem fh_isInst : fhMod.IsInst fhInst := by
  obtain ⟨mt, hmt, himp, hty, f, hf, hfa, hfs⟩ := fhFacts
  obtain ⟨d, hd, hdt⟩ := forall₂_of_map_single hty
  obtain ⟨fi₀, fi₁, hfuncs, h₀, h₁⟩ := map_pair hfs
  have hr : (List.range mt.imports.length).map ExternAddr.func = [ExternAddr.func 0] := by
    rw [himp]
    rfl
  have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := by
    intro xt hxt
    rw [himp, List.mem_singleton] at hxt
    exact ⟨_, hxt⟩
  refine ⟨⟨mt, ⟨hmt, hfun, hd ▸ .cons hdt .nil, ⟨f, ?_, hfa⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hf
  · refine .cons ⟨fi₀, ?_, h₀⟩ (.cons ⟨fi₁, ?_, h₁⟩ .nil)
    · show fhStore.funcs[0]? = some fi₀
      rw [hfuncs]
      rfl
    · show fhStore.funcs[1]? = some fi₁
      rw [hfuncs]
      rfl

/-! ## The conditions -/

theorem fhS_good : fhS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [fhS, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"f", rfl⟩
    · exact ⟨"h", rfl⟩, rfl⟩

theorem fhS_inst : fhS.Inst := by
  obtain ⟨mt, hmt, himp, -⟩ := fhFacts
  exact ⟨⟨fhInst, fh_isInst⟩, rfl, by decide, rfl, ⟨mt, hmt, himp⟩⟩

theorem fhS_arity : fhS.Arity := by
  unfold SimpleI.Arity
  decide

theorem dblFhL_importsFloatFree : dblFhL.ImportsFloatFree := by
  unfold Linked2.ImportsFloatFree
  decide

/-- The importer exports a float: `Linked2.sound` does not apply. -/
theorem dblFhL_not_floatFree : ¬ dblFhL.imp.FloatFree := by
  intro h
  have := (h.1 ⟨"h", ⟨[.f32], [.f32]⟩, 1⟩ (by simp [dblFhL, fhS])).1
  exact absurd this (by decide)

theorem dblFhL_wireTy : dblFhL.WireTy := by
  refine ⟨rfl, fun k w hk => ?_⟩
  match k, hk with
  | 0, hk =>
    have hw : w = 0 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩

theorem dblFhL_namesOk : dblFhL.NamesOk := by
  refine ⟨fun x hx n => ?_, fun x hx n => ?_⟩
  · have hx' : x = ⟨"g", ⟨[.u32], [.u32]⟩, 0⟩ := List.mem_singleton.1 hx
    rw [hx']
    exact ne_tag_t rfl (by decide) n
  · simp only [dblFhL, fhS, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ne_tag_t rfl (by decide) n
    · exact ne_tag_t rfl (by decide) n

theorem dblFhL_wireNodup : dblFhL.WireNodup := List.nodup_singleton 0

theorem dblFhL_splitOk : dblFhL.SplitOk :=
  ⟨⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## The litmus theorems -/

/-- The export `h` of the importer. -/
abbrev hIdx : Fin dblFhL.imp.exports.length := ⟨1, by decide⟩

/-- **A call of the float export `h` of `dblFhL`** (every profile, component choice profile and
host functions): every behaviour of instantiating `dblFhL.toRef` and calling `h(x)` is the
linked IR call of `h` on an admissible lowering `[f32 y]` of `[f32 x]`, the returned value
reported canonicalised. -/
theorem dblFh_sound_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) (x : BitVec 32)
    (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHost impl) h₀ dblFhL.toRef [] "h"
      [toRefVal (.f32 x)]) :
    ∃ vs', NanAtVList prof [.f32] [.f32 x] vs' ∧ ValTy.checkList [.f32] vs' = true ∧
      Linked2.IRObsV P dblFhL hIdx vs' b :=
  linked2_sound_floatV P prof dblFhL dblS_good dblS_inst fhS_good fhS_inst fhS_arity
    dblFhL_importsFloatFree dblFhL_wireTy dblFhL_namesOk dblFhL_wireNodup dblFhL_splitOk impl h₀
    hIdx [.f32 x] rfl b hb

theorem dblFh_typedCalls (xs : List (BitVec 32)) :
    SimpleI.TypedCalls dblFhL.imp (xs.map fun a => (hIdx, [.f32 a])) := by
  intro q hq
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
  rfl

theorem dblFh_callNames (xs : List (BitVec 32)) :
    (xs.map fun a => (hIdx, [Silmaril.Wasm.Component.Val.f32 a])).map
      (fun q : Fin dblFhL.imp.exports.length × List Silmaril.Wasm.Component.Val =>
        (dblFhL.imp.exports[q.1].name, q.2.map toRefVal)) =
      xs.map fun a => ("h", [toRefVal (.f32 a)]) := by
  rw [List.map_map]
  rfl

/-- **Sequences of calls of the float export `h` of `dblFhL`** (every profile, component choice
profile and host functions): every behaviour of instantiating `dblFhL.toRef`, calling `h` on each
of `xs` (each resolving), then on `x`, is the linked IR play of admissible lowerings of the
calls, the results reported canonicalised. -/
theorem dblFh_sound_seq_floatV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    {σ : Type} (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (xs : List (BitVec 32)) (x : BitVec 32)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ dblFhL.toRef
      (xs.map fun a => ("h", [toRefVal (.f32 a)])) "h" [toRefVal (.f32 x)]) :
    ∃ (calls' : List (Fin dblFhL.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val),
      Linked2.NanCallsV prof dblFhL (xs.map fun a => (hIdx, [.f32 a])) calls' ∧
      SimpleI.TypedCalls dblFhL.imp calls' ∧ NanAtVList prof [.f32] [.f32 x] vs' ∧
      ValTy.checkList [.f32] vs' = true ∧ p.1 = Linked2.canonResultsV dblFhL calls' wss ∧
      Linked2.seqMoves dblFhL calls' wss ∈ dblFhL.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P dblFhL calls' wss hIdx vs' p.2 :=
  linked2_sound_seq_floatV P prof dblFhL dblS_good dblS_inst fhS_good fhS_inst fhS_arity
    dblFhL_importsFloatFree dblFhL_wireTy dblFhL_namesOk dblFhL_wireNodup dblFhL_splitOk impl h₀
    _ hIdx [.f32 x] (dblFh_typedCalls xs) rfl p (dblFh_callNames xs ▸ hp)

/-- **Sequences of calls of `h` under the deterministic component profile**: the linked IR plays
the canonicalised arguments. -/
theorem dblFh_sound_seq_floatV_deterministic (P : Profile) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    (xs : List (BitVec 32)) (x : BitVec 32)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours .deterministic (linkHost impl) h₀ dblFhL.toRef
      (xs.map fun a => ("h", [toRefVal (.f32 a)])) "h" [toRefVal (.f32 x)]) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val),
      p.1 = Linked2.canonResultsV dblFhL
        (Linked2.canonCallsV dblFhL (xs.map fun a => (hIdx, [.f32 a]))) wss ∧
      Linked2.seqMoves dblFhL (Linked2.canonCallsV dblFhL (xs.map fun a => (hIdx, [.f32 a])))
        wss ∈ dblFhL.toComp.den (impSem P) ∧
      Linked2.SeqIRObsV P dblFhL (Linked2.canonCallsV dblFhL (xs.map fun a => (hIdx, [.f32 a])))
        wss hIdx (canonAtVList [.f32] [.f32 x]) p.2 :=
  linked2_sound_seq_floatV_deterministic P dblFhL dblS_good dblS_inst fhS_good fhS_inst
    fhS_arity dblFhL_importsFloatFree dblFhL_wireTy dblFhL_namesOk dblFhL_wireNodup
    dblFhL_splitOk impl h₀ _ hIdx [.f32 x] (dblFh_typedCalls xs) rfl p (dblFh_callNames xs ▸ hp)

end Silmaril.Proofs.Wasm.Component.Reference
