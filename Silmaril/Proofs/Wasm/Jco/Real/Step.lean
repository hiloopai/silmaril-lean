module

public import Silmaril.Proofs.Wasm.Jco.Real.Mem
public import Silmaril.Proofs.Wasm.Jco.Real.Top
public import Silmaril.Wasm.Jco.Real.Inst.Thms

/-!
# Adaptor instructions against the reference engine: the instructions without memory

`XInstr.step` over `realInst` is simulated by the reference semantics of the Core 3.0 image of
the instruction (`Sim`): `local.get`, `local.set`, `i32.const`, `i32.eqz`, `i32.lt_u`,
`select`, and `call` (through `$invoke` and frame independence, `Steps.reframe`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc?)

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)

/-- **The simulation of one run**: from the Core frame `cf` (with the locals of `f`), the Core
code `code` after the operand stack of `f` runs to the operand stack of `f'` in a frame of the
same module with the locals of `f'`, from store `s` to store `s'`. -/
def Sim (f f' : Silmaril.Wasm.Jco.Frame) (s s' : Store H)
    (cf : Silmaril.Wasm.Execution.Core.Frame) (code : List Admin) : Prop :=
  ∃ cf' : Silmaril.Wasm.Execution.Core.Frame, cf'.module = cf.module ∧
    cf'.locals = localsOf f'.locals ∧
    Steps P host ⟨s, cf, stackCode f.stack ++ code⟩ ⟨s', cf', stackCode f'.stack⟩

theorem stackCode_cons (v : Flat) (st : List Flat) :
    stackCode (v :: st) = stackCode st ++ [(toVal v).toAdmin] := by
  simp [stackCode, vals]

theorem stackCode_append (xs st : List Flat) :
    stackCode (xs ++ st) = stackCode st ++ vals (xs.reverse.map toVal) := by
  simp [stackCode, vals]

theorem asI32?_eq {v : Flat} {x : BitVec 32} (h : asI32? v = some x) : v = Flat.i32 x := by
  rcases v with ⟨t, b⟩
  rcases t with (_ | _) | _ <;> simp [asI32?] at h
  cases h
  rfl

theorem toAdmin_i32 (x : BitVec 32) : (toVal (Flat.i32 x)).toAdmin = .plain (.intConst .i32 x) :=
  rfl

theorem constI32_eq (x : BitVec 32) : constI32 x = (toVal (Flat.i32 x)).toAdmin := rfl

theorem ltu_eq (a b : BitVec 32) :
    intRelOp .i32 (.lt .unsigned) a b = if a.toNat < b.toNat then 1 else 0 := by
  show bool32 (decide (a.toNat < b.toNat)) = _
  by_cases h : a.toNat < b.toNat <;> simp [bool32, h]

theorem mkIdx_toNat {k : Silmaril.Wasm.IndexKind} {i : Nat} (h : i < 2 ^ 32) :
    (mkIdx i : Silmaril.Wasm.Idx k).toNat = i := by
  have h' : i < 4294967296 := h
  simp [mkIdx, Silmaril.Wasm.Idx.toNat, Nat.mod_eq_of_lt h']

/-- Lift a run under an operand stack. -/
theorem lift (st : List Flat) {s s' : Store H} {cf cf' : Silmaril.Wasm.Execution.Core.Frame}
    {X Y : List Admin} (h : Steps P host ⟨s, cf, X⟩ ⟨s', cf', Y⟩) :
    Steps P host ⟨s, cf, stackCode st ++ X⟩ ⟨s', cf', stackCode st ++ Y⟩ := by
  have := Steps.ctxtInstrs (vs := st.reverse.map toVal) (rest := []) h
  simpa [stackCode] using this

theorem sim_localGet {i : Nat} (hi : i < 2 ^ 32) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) (.base (.localGet i)) f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi (.base (.localGet i)))] := by
  simp only [XInstr.step, AInstr.step] at h
  rcases hv : f.locals[i]? with _ | v <;> simp only [hv] at h
  · cases h
  · obtain ⟨rfl, rfl⟩ := ok_pure h
    refine ⟨cf, rfl, hl, ?_⟩
    have hx : cf.local? (mkIdx i : Silmaril.Wasm.LocalIdx) = some (some (toVal v)) := by
      simp [Frame.local?, hl, localsOf, mkIdx_toNat hi, hv]
    have hrun := lift P host f.stack (Step.variable (VariableStep.localGet (s := s') hx)).steps
    rw [stackCode_cons]
    exact hrun

theorem sim_localSet {i : Nat} (hi : i < 2 ^ 32) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) (.base (.localSet i)) f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi (.base (.localSet i)))] := by
  rcases f with ⟨ls, _ | ⟨v, st⟩⟩ <;> simp only [XInstr.step, AInstr.step] at h
  · cases h
  · by_cases hlt : i < ls.length
    · simp only [hlt, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := ok_pure h
      have hx : (mkIdx i : Silmaril.Wasm.LocalIdx).toNat < cf.locals.length := by
        simpa [mkIdx_toNat hi, hl, localsOf] using hlt
      refine ⟨cf.setLocal (mkIdx i) (toVal v), rfl, ?_, ?_⟩
      · simp [Frame.setLocal, hl, localsOf, mkIdx_toNat hi, List.map_set]
      · have hrun := lift P host st (Step.variable (VariableStep.localSet (s := s') (v := toVal v) hx)).steps
        rw [List.append_nil] at hrun
        rw [stackCode_cons, List.append_assoc]
        exact hrun
    · simp only [hlt, ↓reduceIte] at h
      cases h

theorem sim_i32Const (c : BitVec 32) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) (.base (.i32Const c)) f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi (.base (.i32Const c)))] := by
  simp only [XInstr.step, AInstr.step] at h
  obtain ⟨rfl, rfl⟩ := ok_pure h
  refine ⟨cf, rfl, hl, ?_⟩
  rw [stackCode_cons, toAdmin_i32]
  exact .refl

theorem sim_i32Eqz {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) .i32Eqz f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi .i32Eqz)] := by
  rcases f with ⟨ls, _ | ⟨v, st⟩⟩ <;> simp only [XInstr.step] at h
  · cases h
  · obtain ⟨x, s₁, hx, hp⟩ := ok_bind h
    obtain ⟨hx', rfl⟩ := ok_ofOption hx
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    refine ⟨cf, rfl, hl, ?_⟩
    have hs : Step P host ⟨s', cf, [.plain (.intConst .i32 x), .plain (.intTestOp .i32 .eqz)]⟩
        ⟨s', cf, [constI32 (intTestOp .i32 .eqz x)]⟩ :=
      Step.numeric NumericStep.intTestOp
    have hrun := lift P host st hs.steps
    rw [stackCode_cons, stackCode_cons, asI32?_eq hx', List.append_assoc]
    exact hrun

theorem sim_i32LtU {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) .i32LtU f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi .i32LtU)] := by
  rcases f with ⟨ls, _ | ⟨vb, _ | ⟨va, st⟩⟩⟩ <;> simp only [XInstr.step] at h
  · cases h
  · cases h
  · obtain ⟨b, s₁, hb, h₁⟩ := ok_bind h
    obtain ⟨hb', rfl⟩ := ok_ofOption hb
    obtain ⟨a, s₂, ha, hp⟩ := ok_bind h₁
    obtain ⟨ha', rfl⟩ := ok_ofOption ha
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    refine ⟨cf, rfl, hl, ?_⟩
    have hs : Step P host ⟨s', cf, [.plain (.intConst .i32 a), .plain (.intConst .i32 b),
        .plain (.intRelOp .i32 (.lt .unsigned))]⟩
        ⟨s', cf, [constI32 (intRelOp .i32 (.lt .unsigned) a b)]⟩ :=
      Step.numeric NumericStep.intRelOp
    have hrun := lift P host st hs.steps
    rw [ltu_eq, constI32_eq] at hrun
    rw [stackCode_cons, stackCode_cons, stackCode_cons, asI32?_eq hb', asI32?_eq ha']
    simp only [List.append_assoc, List.cons_append, List.nil_append, toAdmin_i32]
    exact hrun

/-- The Core `select` on the images of the operands. -/
theorem core_select {s : Store H} {cf : Silmaril.Wasm.Execution.Core.Frame} (c : BitVec 32)
    (va vb : Flat) :
    Step P host ⟨s, cf, [(toVal va).toAdmin, (toVal vb).toAdmin, (toVal (Flat.i32 c)).toAdmin,
      .plain (.select none)]⟩ ⟨s, cf, [(toVal (if c == 0 then vb else va)).toAdmin]⟩ := by
  by_cases h0 : c = 0
  · subst h0
    exact Step.parametric (ParametricStep.selectFalse _ _ _)
  · have hc0 : (c == 0) = false := by simpa using h0
    rw [hc0]
    exact Step.parametric (ParametricStep.selectTrue h0)

theorem sim_select {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) .select f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi .select)] := by
  rcases f with ⟨ls, _ | ⟨vc, _ | ⟨vb, _ | ⟨va, st⟩⟩⟩⟩ <;> simp only [XInstr.step] at h
  · cases h
  · cases h
  · cases h
  · obtain ⟨c, s₁, hc, hp⟩ := ok_bind h
    obtain ⟨hc', rfl⟩ := ok_ofOption hc
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    refine ⟨cf, rfl, hl, ?_⟩
    have hrun := lift P host st (core_select P host (s := s') (cf := cf) c va vb).steps
    rw [stackCode_cons, stackCode_cons, stackCode_cons, stackCode_cons, asI32?_eq hc']
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact hrun

/-- `call g` from the adaptor's frame: the function index of `g` reaches the function exported
under `g`, whose `$invoke` run replays in the adaptor's frame. -/
theorem core_call {g : String} (n : Nat) {args rs : List Flat} {s s' : Store H}
    (hc : (realInst H P host mi ma).call g args s (.ok rs s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf) :
    Steps P host ⟨s, cf, vals (args.map toVal) ++ [.plain (coreOf fi (.base (.call g n)))]⟩
      ⟨s', cf, vals (rs.map toVal)⟩ := by
  obtain ⟨a, c, ha, hok, hrun, hcode, hs⟩ := (call_ok_iff P host mi ma g args rs s s').mp hc
  obtain ⟨fn, ps, rts, hfn, -, -⟩ := hok
  have hx : cf.module.funcs[(mkIdx (fi g) : Silmaril.Wasm.FuncIdx).toNat]? = some a := by
    simpa [mkIdx, Silmaril.Wasm.Idx.toNat] using he.call g a ha
  have hcall : Step P host ⟨s, cf, [.plain (.call (mkIdx (fi g)))]⟩
      ⟨s, cf, [.ref (.func a), .callRefType fn.type]⟩ := Step.call hx hfn
  have hinv : (invoke s a (args.map toVal)).code =
      vals (args.map toVal) ++ [.ref (.func a), .callRefType fn.type] := by
    simp [invoke, hfn]
  obtain ⟨-, -, hre⟩ := Steps.reframe hrun (invoke_topOK s a _)
  have hre' : Steps P host ⟨s, cf, vals (args.map toVal) ++ [.ref (.func a), .callRefType fn.type]⟩
      ⟨s', cf, vals (rs.map toVal)⟩ := by
    rw [← hinv, ← hcode, ← hs]
    exact hre cf
  have hpre := Steps.ctxtInstrs (vs := args.map toVal) (rest := []) hcall.steps
  simp only [List.append_nil] at hpre
  exact hpre.trans hre'

theorem stackCode_split (n : Nat) (st : List Flat) :
    stackCode st = stackCode (st.drop n) ++ vals ((st.take n).reverse.map toVal) := by
  conv => lhs; rw [← List.take_append_drop n st]
  rw [stackCode_append]

theorem sim_call (g : String) (n : Nat) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) (.base (.call g n)) f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi (.base (.call g n)))] := by
  rcases f with ⟨ls, st⟩
  simp only [XInstr.step, AInstr.step] at h
  by_cases hn : n ≤ st.length
  · simp only [hn, ↓reduceIte] at h
    obtain ⟨rs, s₁, hc, hp⟩ := ok_bind h
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    refine ⟨cf, rfl, hl, ?_⟩
    have hall := lift P host (st.drop n) (core_call P host mi ma fi n hc he)
    rw [stackCode_split n st, stackCode_append, List.reverse_reverse, List.append_assoc]
    exact hall
  · simp only [hn, ↓reduceIte] at h
    cases h

end Silmaril.Proofs.Wasm.Jco.Real
