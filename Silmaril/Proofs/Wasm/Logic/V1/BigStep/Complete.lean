module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Compose

/-!
# Every terminating reduction has a big-step derivation

The other half of Theorem 1 of Watt et al. The proof is by closure of the
big-step relation under small steps taken backwards, which needs no determinism
or termination assumption and so survives the nondeterminism of NaN results,
memory growth and host calls.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- `BigStep.values_append_iff` with an empty code continuation. -/
private theorem BigStep.values_iff {s : Store H} {f : Frame} {vs ws : List Value}
    {o : Outcome H} : BigStep host s f vs (values ws) o ↔ BigStep host s f (vs ++ ws) [] o := by
  have h := @BigStep.values_append_iff H host s f vs ws [] o
  simpa using h

/-- Run a `Plain` instruction whose operands are still sitting in the code. -/
private theorem BigStep.plain_back {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {i : Silmaril.Wasm.V1.Instr} {us : List Value} {es : List Admin} {o : Outcome H}
    (step : Plain s f args i s' f' rets)
    (rest : BigStep host s' f' us (values rets ++ es) o) :
    BigStep host s f us (values args ++ .source i :: es) o :=
  BigStep.values_append_iff.mpr (BigStep.plain step (BigStep.values_append_iff.mp rest))

/-- Trap a `PlainTrap` instruction whose operands are still sitting in the code. -/
private theorem BigStep.plainTrap_back {s : Store H} {f : Frame} {args : List Value}
    {i : Silmaril.Wasm.V1.Instr} {us : List Value} {es : List Admin} (step : PlainTrap s f args i) :
    BigStep host s f us (values args ++ .source i :: es) ⟨s, f, .trap⟩ :=
  BigStep.values_append_iff.mpr (BigStep.plainTrap step)

/-- Inversion for a run whose first instruction is `local.set`. -/
private theorem BigStep.localSet_inv {s : Store H} {f : Frame} {i : LocalIdx}
    {ws : List Value} {es : List Admin} {o : Outcome H}
    (h : BigStep host s f ws (.source (.localSet i) :: es) o) :
    ∃ (us : List Value) (v old : Value), ws = us ++ [v] ∧ f.locals[i.toNat]? = some old ∧
      BigStep host s {f with locals := f.locals.set i.toNat v} us es o := by
  cases h with
  | plain step rest =>
      cases step with
      | localSet _ v old found => exact ⟨_, v, old, rfl, found, by simpa using rest⟩
  | plainTrap step => cases step

/-- Inversion for a run whose first instruction is `br`. -/
private theorem BigStep.br_inv {s : Store H} {f : Frame} {ws : List Value} {l : LabelIdx}
    {es : List Admin} {o : Outcome H} (h : BigStep host s f ws (.source (.br l) :: es) o) :
    o = ⟨s, f, .br l ws⟩ := by
  cases h with
  | br => rfl
  | plain step _ => cases step
  | plainTrap step => cases step

/-- Inversion for a run whose first instruction is `return`. -/
private theorem BigStep.return_inv {s : Store H} {f : Frame} {ws : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStep host s f ws (.source .return_ :: es) o) :
    o = ⟨s, f, .ret ws⟩ := by
  cases h with
  | return_ => rfl
  | plain step _ => cases step
  | plainTrap step => cases step

/-- The big-step relation is closed under taking a store-independent step backwards. -/
private theorem BigStep.pureBack {s : Store H} {f : Frame} {before after : List Admin}
    (h : PureStep before after) {us : List Value} {o : Outcome H}
    (rest : BigStep host s f us after o) : BigStep host s f us before o := by
  cases h with
  | nop => exact BigStep.plain_back (Plain.nop s f) rest
  | unreachable => cases rest; exact BigStep.plainTrap_back (PlainTrap.unreachable s f)
  | drop v => exact BigStep.plain_back (Plain.drop s f v) rest
  | selectZero a b sameType => exact BigStep.plain_back (Plain.selectZero s f a b sameType) rest
  | selectNonzero a b sameType c hc =>
      exact BigStep.plain_back (Plain.selectNonzero s f a b sameType c hc) rest
  | block bt body => exact BigStep.block rest
  | loop bt body => exact BigStep.loop rest
  | ifZero bt left right =>
      show BigStep host s f us (values [.int .i32 0] ++ [.source (.if_ bt left right)]) o
      exact BigStep.values_append_iff.mpr (BigStep.ifZero rest)
  | ifNonzero bt left right c hc =>
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.if_ bt left right)]) o
      exact BigStep.values_append_iff.mpr (BigStep.ifNonzero hc rest)
  | brIfZero l =>
      show BigStep host s f us (values [.int .i32 0] ++ [.source (.brIf l)]) o
      exact BigStep.values_append_iff.mpr (BigStep.brIfZero rest)
  | brIfNonzero l c hc =>
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.brIf l)]) o
      exact BigStep.values_append_iff.mpr (BigStep.brIfNonzero hc rest)
  | brTable ls dflt c =>
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.brTable ls dflt)]) o
      exact BigStep.values_append_iff.mpr (BigStep.brTable rest)
  | labelDone n cont vs =>
      exact BigStep.labelNormal (BigStep.values_iff.mpr (BigStep.nil s f ([] ++ vs)))
        (BigStep.values_iff.mp rest)
  | labelBranch n cont extra vs tail arity =>
      refine BigStep.labelBrZero (s' := s) (f' := f) (l := ⟨0⟩) (extra := extra) (ws := vs)
        ?_ rfl arity ?_
      · have inner : BigStep host s f []
            (values (extra ++ vs) ++ (.source (.br ⟨0⟩) :: tail)) ⟨s, f, .br ⟨0⟩ (extra ++ vs)⟩ :=
          BigStep.values_append_iff.mpr (BigStep.br s f (extra ++ vs) ⟨0⟩ tail)
        simpa [List.append_assoc] using inner
      · simpa using BigStep.values_append_iff.mp rest
  | labelBranchOuter n cont vs tail l outer =>
      obtain rfl : o = ⟨s, f, .br (lowerLabel l) (us ++ vs)⟩ :=
        BigStep.br_inv (BigStep.values_append_iff.mp rest)
      have inner : BigStep host s f [] (values vs ++ (.source (.br l) :: tail))
          ⟨s, f, .br l vs⟩ := BigStep.values_append_iff.mpr (BigStep.br s f vs l tail)
      exact BigStep.labelBrSucc (s' := s) (f' := f) (ws := vs)
        (by simpa [List.append_assoc] using inner) outer
  | labelReturn n cont vs tail =>
      obtain rfl : o = ⟨s, f, .ret (us ++ vs)⟩ :=
        BigStep.return_inv (BigStep.values_append_iff.mp rest)
      have inner : BigStep host s f [] (values vs ++ (.source .return_ :: tail))
          ⟨s, f, .ret vs⟩ := BigStep.values_append_iff.mpr (BigStep.return_ s f vs tail)
      exact BigStep.labelRet (s' := s) (f' := f) (ws := vs)
        (by simpa [List.append_assoc] using inner)
  | frameDone n fr vs arity =>
      exact BigStep.frameNormal (BigStep.values_iff.mpr (BigStep.nil s fr ([] ++ vs))) arity
        (BigStep.values_iff.mp rest)
  | frameReturn n fr extra vs tail arity =>
      refine BigStep.frameRet (s' := s) (fr' := fr) (extra := extra) (ws := vs) ?_ arity
        (BigStep.values_iff.mp rest)
      have inner : BigStep host s fr []
          (values (extra ++ vs) ++ (.source .return_ :: tail)) ⟨s, fr, .ret (extra ++ vs)⟩ :=
        BigStep.values_append_iff.mpr (BigStep.return_ s fr (extra ++ vs) tail)
      simpa [List.append_assoc] using inner
  | trapValues v vs tail =>
      cases rest
      rw [List.append_assoc]
      exact BigStep.values_append_iff.mpr (BigStep.trap s f (us ++ (v :: vs)) tail)
  | trapTail i tail => cases rest; exact BigStep.trap s f us (i :: tail)
  | labelTrap n cont => cases rest; exact BigStep.labelTrap (BigStep.trap s f [] [])
  | frameTrap n fr => cases rest; exact BigStep.frameTrap (BigStep.trap s fr [] [])
  | localTee i v =>
      show BigStep host s f us [value v, .source (.localTee i)] o
      have h1 : BigStep host s f (us ++ [v, v]) [.source (.localSet i)] o :=
        BigStep.values_append_iff.mp rest
      obtain ⟨us', v', old, heq, found, h2⟩ := BigStep.localSet_inv h1
      have h3 : (us ++ [v]) ++ [v] = us' ++ [v'] := by simpa using heq
      obtain ⟨rfl, rfl⟩ : us ++ [v] = us' ∧ v = v' := by
        simpa using List.append_inj' h3 rfl
      exact BigStep.plain_back (Plain.localTee s f i v old found)
        (BigStep.values_append_iff.mpr h2)
  | intUnary t op x => exact BigStep.plain_back (Plain.intUnary s f t op x) rest
  | intBinary t op x y z hz => exact BigStep.plain_back (Plain.intBinary s f t op x y z hz) rest
  | intBinaryTrap t op x y err herr =>
      cases rest; exact BigStep.plainTrap_back (PlainTrap.intBinary s f t op x y err herr)
  | intTest t op x => exact BigStep.plain_back (Plain.intTest s f t op x) rest
  | intRel t op x y => exact BigStep.plain_back (Plain.intRel s f t op x y) rest
  | floatUnary t op x y hr => exact BigStep.plain_back (Plain.floatUnary s f t op x y hr) rest
  | floatBinary t op x y z hr =>
      exact BigStep.plain_back (Plain.floatBinary s f t op x y z hr) rest
  | floatRel t op x y => exact BigStep.plain_back (Plain.floatRel s f t op x y) rest
  | convert op x y hr => exact BigStep.plain_back (Plain.convert s f op x y hr) rest
  | convertTrap op x err hr =>
      cases rest; exact BigStep.plainTrap_back (PlainTrap.convert s f op x err hr)

/-- A step in a context of values and code, taken backwards: the `context` case of
`BigStep.stepBack_aux`. -/
private theorem BigStep.context_back {s s' : Store H} {f f' : Frame} {vs : List Value}
    {es es' tail : List Admin}
    (ih : ∀ {us : List Value} {o : Outcome H}, BigStep host s' f' us es' o →
      BigStep host s f us es o)
    {us : List Value} {o : Outcome H} (rest : BigStep host s' f' us (values vs ++ (es' ++ tail)) o) :
    BigStep host s f us (values vs ++ es ++ tail) o := by
  rw [List.append_assoc]
  refine BigStep.values_append_iff.mpr ?_
  rcases BigStep.append_inv (BigStep.values_append_iff.mp rest) with
    ⟨s₂, f₂, ws, hA, hB⟩ | ⟨hA, habrupt⟩
  · exact BigStep.append (ih hA) hB
  · exact BigStep.append_abrupt (ih hA) habrupt

/-- A step inside a label, taken backwards: the `label` case of
`BigStep.stepBack_aux`. -/
private theorem BigStep.label_back {s s' : Store H} {f f' : Frame} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
    {body body' : List Admin}
    (ih : ∀ {us : List Value} {o : Outcome H}, BigStep host s' f' us body' o →
      BigStep host s f us body o)
    {us : List Value} {o : Outcome H} (rest : BigStep host s' f' us [.label n cont body'] o) :
    BigStep host s f us [.label n cont body] o := by
  cases rest with
  | labelNormal innerD rest' => exact BigStep.labelNormal (ih innerD) rest'
  | labelBrZero innerD target arity rest' => exact BigStep.labelBrZero (ih innerD) target arity rest'
  | labelBrSucc innerD outerH => exact BigStep.labelBrSucc (ih innerD) outerH
  | labelRet innerD => exact BigStep.labelRet (ih innerD)
  | labelTrap innerD => exact BigStep.labelTrap (ih innerD)

/-- A step inside a frame, taken backwards: the `frame` case of `BigStep.stepBack_aux`. -/
private theorem BigStep.frame_back {s s' : Store H} {inner inner' outer : Frame} {n : Nat}
    {body body' : List Admin}
    (ih : ∀ {us : List Value} {o : Outcome H}, BigStep host s' inner' us body' o →
      BigStep host s inner us body o)
    {us : List Value} {o : Outcome H} (rest : BigStep host s' outer us [.frame n inner' body'] o) :
    BigStep host s outer us [.frame n inner body] o := by
  cases rest with
  | frameNormal innerD arity rest' => exact BigStep.frameNormal (ih innerD) arity rest'
  | frameRet innerD arity rest' => exact BigStep.frameRet (ih innerD) arity rest'
  | frameTrap innerD => exact BigStep.frameTrap (ih innerD)

/-- `BigStep.stepBack`, stated so that the `Step` induction goes through. -/
private theorem BigStep.stepBack_aux {c c' : Config H} (h : Step host c c') :
    ∀ {us : List Value} {o : Outcome H},
      BigStep host c'.store c'.frame us c'.code o → BigStep host c.store c.frame us c.code o := by
  induction h with
  | pure s f hp => intro us o rest; exact BigStep.pureBack hp rest
  | context hs vs tail ih =>
      intro us o rest
      exact BigStep.context_back ih (by simpa only [List.append_assoc] using rest)
  | label hs n cont ih => exact fun rest => BigStep.label_back ih rest
  | frame hs n outerF ih => exact fun rest => BigStep.frame_back ih rest
  | localGet s f i v found =>
      intro us o rest; exact BigStep.plain_back (Plain.localGet s f i v found) rest
  | localSet s f i v old found =>
      intro us o rest; exact BigStep.plain_back (Plain.localSet s f i v old found) rest
  | globalGet s f i a g index found =>
      intro us o rest; exact BigStep.plain_back (Plain.globalGet s f i a g index found) rest
  | globalSet s f i a g v index found mutable =>
      intro us o rest
      exact BigStep.plain_back (Plain.globalSet s f i a g v index found mutable) rest
  | call s f i a found => intro us o rest; exact BigStep.call found rest
  | callIndirect s f i c table a fn ft tableFound typeFound element found typeMatch =>
      intro us o rest
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.callIndirect i)]) o
      exact BigStep.values_append_iff.mpr
        (BigStep.callIndirect tableFound typeFound element found typeMatch rest)
  | callIndirectBounds s f i c table tableFound outOfBounds =>
      intro us o rest
      cases rest
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.callIndirect i)]) _
      exact BigStep.values_append_iff.mpr (BigStep.callIndirectBounds tableFound outOfBounds)
  | callIndirectNull s f i c table tableFound null =>
      intro us o rest
      cases rest
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.callIndirect i)]) _
      exact BigStep.values_append_iff.mpr (BigStep.callIndirectNull tableFound null)
  | callIndirectType s f i c table a fn ft tableFound typeFound element found typeMismatch =>
      intro us o rest
      cases rest
      show BigStep host s f us (values [.int .i32 c] ++ [.source (.callIndirect i)]) _
      exact BigStep.values_append_iff.mpr
        (BigStep.callIndirectType tableFound typeFound element found typeMismatch)
  | invokeWasm s f a ft md fn args found arity resultArity =>
      intro us o rest
      exact BigStep.values_append_iff.mpr (BigStep.invokeWasm found arity resultArity rest)
  | invokeHost s s' f a ft fn args r found arity behavior =>
      intro us o rest
      have rest' : BigStep host s' f us (result r ++ []) o := by simpa using rest
      exact BigStep.values_append_iff.mpr (BigStep.invokeHost found arity behavior rest')
  | invokeHostDiverges s f a ft fn args found arity behavior => intro us o rest; exact rest
  | intLoad s f t packed arg c a m v memory loaded =>
      intro us o rest
      exact BigStep.plain_back (Plain.intLoad s f t packed arg c a m v memory loaded) rest
  | intLoadTrap s f t packed arg c a m memory loaded =>
      intro us o rest
      cases rest
      exact BigStep.plainTrap_back (PlainTrap.intLoad s f t packed arg c a m memory loaded)
  | floatLoad s f t arg c a m v memory loaded =>
      intro us o rest
      exact BigStep.plain_back (Plain.floatLoad s f t arg c a m v memory loaded) rest
  | floatLoadTrap s f t arg c a m memory loaded =>
      intro us o rest
      cases rest
      exact BigStep.plainTrap_back (PlainTrap.floatLoad s f t arg c a m memory loaded)
  | intStore s f t packed arg c x a m bytes memory stored =>
      intro us o rest
      exact BigStep.plain_back (Plain.intStore s f t packed arg c x a m bytes memory stored) rest
  | intStoreTrap s f t packed arg c x a m memory stored =>
      intro us o rest
      cases rest
      exact BigStep.plainTrap_back (PlainTrap.intStore s f t packed arg c x a m memory stored)
  | floatStore s f t arg c x a m bytes memory stored =>
      intro us o rest
      exact BigStep.plain_back (Plain.floatStore s f t arg c x a m bytes memory stored) rest
  | floatStoreTrap s f t arg c x a m memory stored =>
      intro us o rest
      cases rest
      exact BigStep.plainTrap_back (PlainTrap.floatStore s f t arg c x a m memory stored)
  | memorySize s f a m memory =>
      intro us o rest; exact BigStep.plain_back (Plain.memorySize s f a m memory) rest
  | memoryGrow s f a m c r bytes memory grown =>
      intro us o rest
      exact BigStep.plain_back (Plain.memoryGrow s f a m c r bytes memory grown) rest

/-- The big-step relation is closed under taking a small step backwards. -/
theorem BigStep.stepBack {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (h : Step host ⟨s, f, before⟩ ⟨s', f', after⟩) {us : List Value} {o : Outcome H}
    (rest : BigStep host s' f' us after o) : BigStep host s f us before o :=
  BigStep.stepBack_aux h rest

theorem BigStep.stepsBack {c c' : Config H} (h : Steps host c c') {us : List Value}
    {o : Outcome H} (rest : BigStep host c'.store c'.frame us c'.code o) :
    BigStep host c.store c.frame us c.code o := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact rest
  | head hstep _ ih => exact BigStep.stepBack_aux hstep ih

theorem BigStep.ofSteps_normal {s s' : Store H} {f f' : Frame} {vs ws : List Value}
    {es : List Admin} (h : Steps host ⟨s, f, values vs ++ es⟩ ⟨s', f', values ws⟩) :
    BigStep host s f vs es ⟨s', f', .normal ws⟩ := by
  have base : BigStep host s' f' [] (values ws) ⟨s', f', .normal ws⟩ :=
    BigStep.values_iff.mpr (BigStep.nil s' f' ([] ++ ws))
  have h2 : BigStep host s f [] (values vs ++ es) ⟨s', f', .normal ws⟩ :=
    BigStep.stepsBack h base
  exact BigStep.values_append_iff.mp h2

theorem BigStep.ofSteps_trap {s s' : Store H} {f f' : Frame} {vs : List Value}
    {es : List Admin} (h : Steps host ⟨s, f, values vs ++ es⟩ ⟨s', f', [.trap]⟩) :
    BigStep host s f vs es ⟨s', f', .trap⟩ := by
  have base : BigStep host s' f' [] [.trap] ⟨s', f', .trap⟩ := BigStep.trap s' f' [] []
  have h2 : BigStep host s f [] (values vs ++ es) ⟨s', f', .trap⟩ := BigStep.stepsBack h base
  exact BigStep.values_append_iff.mp h2

end Silmaril.Wasm.Logic.V1
