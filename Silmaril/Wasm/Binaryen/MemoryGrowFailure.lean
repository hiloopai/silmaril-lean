module

public import Silmaril.Wasm.Behaviour.Optimization
public import Silmaril.Wasm.Behaviour.Semantics.Core
public import Silmaril.Wasm.Binaryen.VacuumLiteSim
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux

/-! # Selecting the failure outcome of `memory.grow`

A real instruction rewrite exercising refinement rather than equivalence:
`memory.grow x` becomes `drop; i32/i64.const -1`. The evaluated operand is
consumed, so its computation is retained. The local theorem requires a resolved
memory and permission to fail (or an impossible growth); it applies to both
address widths, arbitrary numerical profiles, and arbitrary hosts.

With a continuation we prove inclusion of every target behaviour, including
divergence. Without a continuation we additionally exhibit the target's return,
so `Optimization.Refines` includes a genuine feasibility proof. These are local
execution theorems, not an unchecked whole-module pass: lifting a rewrite to
arbitrary bodies still requires maintaining memory resolution and typing.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.MemoryGrowFailure

open Execution.Core Execution.Core.Sim Numerics Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Runtime value for a memory address or page count. -/
def addrVal (a : AddrType) (n : BitVec a.intType.width) : Val :=
  .num ⟨.int a.intType, n⟩

/-- Replacement instruction sequence: consume the already evaluated delta and
return the address-width failure sentinel. -/
def replacement (a : AddrType) : List Instr :=
  [.drop, .intConst a.intType (BitVec.allOnes _)]

/-- The replacement has precisely the stack type of `memory.grow`: one address
value in and one address value out, for both memory32 and memory64. -/
theorem replacement_typed (C : Context) (a : AddrType) :
    InstrsOk C (replacement a) (.plain [a.valType] [a.valType]) := by
  exact .cons (.parametric (.drop (.num (.int a.intType)))) (by simp)
    (.instr (.numeric (.intConst a.intType (BitVec.allOnes _))))

/-- The selected failure result. -/
def failed (a : AddrType) : Val := addrVal a (BitVec.allOnes _)

private theorem drop_not_result {code : List Admin}
    (hdrop : Admin.plain .drop ∈ code) : ∀ r : Result, code ≠ r.toAdmin := by
  intro r heq
  rw [heq] at hdrop
  cases r with
  | values vs => exact SingleThreaded.Det.mem_vals hdrop rfl
  | trap => simp [Result.toAdmin] at hdrop
  | throw a => simp [Result.toAdmin] at hdrop

private theorem behaviours_eq_of_unique_step {c d : Config H}
    (hs : Step P host c d) (hn : ∀ r : Result, c.code ≠ r.toAdmin)
    (hu : ∀ e, Step P host c e → e = d) :
    behavioursOf P host c = behavioursOf P host d := by
  refine Set.Subset.antisymm ?_ (behavioursOf_mono_steps hs.steps)
  rintro b (⟨e, r, hce, hfin, rfl⟩ | ⟨rfl, hdiv⟩)
  · rcases hce.cases_head with rfl | ⟨c', hc', hc'e⟩
    · exact (hn r hfin).elim
    · rw [hu c' hc'] at hc'e
      exact .inl ⟨e, r, hc'e, hfin, rfl⟩
  · obtain ⟨c', hc', hdiv'⟩ := InfiniteTrace.unfold hdiv
    rw [hu c' hc'] at hdiv'
    exact .inr ⟨rfl, hdiv'⟩

private theorem behaviours_values (s : Store H) (f : Frame) (vs : List Val) :
    behavioursOf P host ⟨s, f, vals vs⟩ = {Behaviour.returns vs} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro b (⟨e, r, hs, he, rfl⟩ | ⟨rfl, hd⟩)
    · rcases hs.cases_head with rfl | ⟨c', hc', _⟩
      · change vals vs = r.toAdmin at he
        cases r with
        | values ws =>
          have hvals := SingleThreaded.Det.vals_inj.mp he
          subst ws
          rfl
        | trap =>
          have hm : Admin.trap ∈ vals vs := by rw [he]; simp [Result.toAdmin]
          exact (SingleThreaded.Det.mem_vals hm rfl).elim
        | throw a =>
          have hm : Admin.plain .throwRef ∈ vals vs := by rw [he]; simp [Result.toAdmin]
          exact (SingleThreaded.Det.mem_vals hm rfl).elim
      · exact (Execution.Core.Step.not_vals hc').elim
    · obtain ⟨c', hc', _⟩ := InfiniteTrace.unfold hd
      exact (Execution.Core.Step.not_vals hc').elim
  · rintro b rfl
    exact returns_mem_behavioursOf .refl rfl

/-- The replacement consumes only the delta, leaves the entire store and frame
unchanged, and retains any stack prefix and continuation. -/
theorem replacement_step (s : Store H) (f : Frame) (vs : List Val)
    (a : AddrType) (n : BitVec a.intType.width) (rest : List Admin) :
    Step P host ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a) ++ rest⟩
      ⟨s, f, vals vs ++ [aconst a (BitVec.allOnes _)] ++ rest⟩ := by
  simpa [replacement, expression, addrVal, Val.toAdmin, List.append_assoc] using
    Step.append_right (Step.vals_left
      (Step.parametric (s := s) (f := f) (P := P) (host := host)
        (.drop (addrVal a n))) vs)
      (aconst a (BitVec.allOnes _) :: rest)

private theorem replacement_step_unique {s : Store H} {f : Frame} {vs : List Val}
    {a : AddrType} {n : BitVec a.intType.width} {rest : List Admin} {c : Config H}
    (hs : Step P host
      ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a) ++ rest⟩ c) :
    c = ⟨s, f, vals vs ++ [aconst a (BitVec.allOnes _)] ++ rest⟩ := by
  have hs' : Step P host
      ⟨s, f, vals (vs ++ [addrVal a n]) ++ .plain .drop ::
        aconst a (BitVec.allOnes _) :: rest⟩ c := by
    simpa [replacement, expression, addrVal, Val.toAdmin, vals, List.append_assoc] using hs
  rcases Step.split_head rfl hs' with ⟨ws, us, is', hw, hh, hc⟩ |
      ⟨he, _⟩ | ⟨he, _⟩
  · obtain ⟨us₀, v, hu, hstore, hframe, hcode⟩ :=
      VacuumLite.step_drop_inv hh us rfl
    have hpre : vs = ws ++ us₀ := by
      rw [hu, ← List.append_assoc] at hw
      exact (SingleThreaded.Det.append_singleton_inj.mp hw).1
    cases c with | mk s' f' code =>
      simp only at hstore hframe hcode hc
      subst s' f'
      apply congrArg (Config.mk s f)
      rw [hc, hcode, hpre]
      simp [vals, List.append_assoc]
  · cases he
  · cases he

/-- All target behaviours after the rewrite occur after its unique drop step. -/
theorem replacement_behaviours (s : Store H) (f : Frame) (vs : List Val)
    (a : AddrType) (n : BitVec a.intType.width) (rest : List Admin) :
    behavioursOf P host
      ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a) ++ rest⟩ =
    behavioursOf P host ⟨s, f, vals vs ++ [aconst a (BitVec.allOnes _)] ++ rest⟩ :=
  behaviours_eq_of_unique_step (replacement_step s f vs a n rest)
    (drop_not_result (by simp [replacement, expression]))
    (fun _ hs => replacement_step_unique hs)

/-- With no continuation, the target has exactly one return. This proves its
feasibility independently of whether the source has any observations. -/
theorem replacement_behaviours_eq (s : Store H) (f : Frame) (vs : List Val)
    (a : AddrType) (n : BitVec a.intType.width) :
    behavioursOf P host
      ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a)⟩ =
      {Behaviour.returns (vs ++ [failed a])} := by
  have h := replacement_behaviours (P := P) (host := host) s f vs a n []
  calc
    _ = behavioursOf P host ⟨s, f, vals (vs ++ [failed a])⟩ := by
      simpa [failed, addrVal, vals, Val.toAdmin] using h
    _ = _ := behaviours_values s f (vs ++ [failed a])

/-- The source can select the unchanged-memory failure transition. -/
theorem source_fail {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi))
    (hp : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none)
    (vs : List Val) (rest : List Admin) :
    Step P host ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)] ++ rest⟩
      ⟨s, f, vals vs ++ [aconst a (BitVec.allOnes _)] ++ rest⟩ := by
  exact Step.append_right (Step.vals_left (Step.memory (.growFail hm hp)) vs) rest

/-- Even an arbitrary continuation cannot introduce a target value, trap,
exception, or divergence absent from the source. This is the inclusion half;
an untyped continuation may be stuck after failure, so feasibility is stated
separately in `refines` below. -/
theorem behaviours_subset {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi))
    (hp : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none)
    (vs : List Val) (rest : List Admin) :
    behavioursOf P host
      ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a) ++ rest⟩ ⊆
    behavioursOf P host
      ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)] ++ rest⟩ := by
  rw [replacement_behaviours]
  exact behavioursOf_mono_steps (source_fail hm hp vs rest).steps

/-- A concrete, feasible Core instruction refinement, for memory32 and memory64.
The address-width hypothesis makes explicit the typed memory being rewritten;
the primitive reduction itself needs only the resolved memory. -/
theorem refines {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (_ha : mi.type.address = a)
    (hp : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none)
    (vs : List Val) :
    Optimization.Refines
      (behavioursOf P host ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)]⟩)
      (behavioursOf P host
        ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a)⟩) := by
  refine ⟨?_, fun _ => ?_⟩
  · simpa using behaviours_subset (host := host) hm hp vs []
  · rw [replacement_behaviours_eq]
    exact Set.singleton_nonempty _

/-- The same concrete rewrite discharges the named refinement optimization mode. -/
theorem correct_refinement {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (ha : mi.type.address = a)
    (hp : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none)
    (vs : List Val) :
    Optimization.Correct (Optimization.behaviourOrder Val) .refinement
      (behavioursOf P host ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)]⟩)
      (behavioursOf P host
        ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a)⟩) :=
  refines hm ha hp vs

/-- The WebAssembly specification profile permits this failure at every resolved
memory, including a growth which could also succeed. -/
theorem spec_refines {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (ha : mi.type.address = a)
    (vs : List Val) (nd : Bool := true) (r : RelaxedChoice := {}) :
    Optimization.Refines
      (behavioursOf (Profile.spec nd r) host
        ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)]⟩)
      (behavioursOf (Profile.spec nd r) host
        ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a)⟩) :=
  refines (P := Profile.spec nd r) (n := n) hm ha (.inl trivial) vs


/-- A valid state supplies memory resolution and the correct address width from
its static context. This discharges those dynamic side conditions rather than
assuming that a malformed memory index can execute. -/
theorem typed_spec_refines {s : Store H} {f : Frame} {C : Context} {x : MemIdx}
    {mt : MemoryType} {n : BitVec mt.address.intType.width}
    (hst : StateOk s f C) (hx : C.mems[x.toNat]? = some mt)
    (vs : List Val) (nd : Bool := true) (r : RelaxedChoice := {}) :
    Optimization.Refines
      (behavioursOf (Profile.spec nd r) host
        ⟨s, f, vals vs ++ [aconst mt.address n, .plain (.memoryGrow x)]⟩)
      (behavioursOf (Profile.spec nd r) host
        ⟨s, f, vals vs ++ [aconst mt.address n] ++ expression (replacement mt.address)⟩) := by
  obtain ⟨ma, mi, hm, ha, _⟩ := hst.mem hx
  exact spec_refines (n := n) hm ha vs nd r

/-- Any finite operand evaluation is retained on both sides, with exactly its
post-evaluation store and frame. The operand may have effects or call a host;
this theorem reuses the supplied execution and does not erase or re-evaluate it. -/
theorem operand_execution_preserved {s₀ s : Store H} {f₀ f : Frame}
    {operand : List Admin} {vs : List Val} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (heval : Steps P host ⟨s₀, f₀, operand⟩ ⟨s, f, vals (vs ++ [addrVal a n])⟩)
    (hm : s.mem? f x = some (ma, mi))
    (hp : P.growMayFail .memory ma mi.pages n.toNat ∨ mi.grow? n.toNat = none) :
    Steps P host ⟨s₀, f₀, operand ++ [.plain (.memoryGrow x)]⟩
      ⟨s, f, vals (vs ++ [failed a])⟩ ∧
    Steps P host ⟨s₀, f₀, operand ++ expression (replacement a)⟩
      ⟨s, f, vals (vs ++ [failed a])⟩ := by
  constructor
  · apply (Steps.append_right heval [.plain (.memoryGrow x)]).trans
    simpa [vals, addrVal, failed, Val.toAdmin, List.append_assoc] using
      (source_fail (host := host) hm hp vs []).steps
  · apply (Steps.append_right heval (expression (replacement a))).trans
    simpa [vals, addrVal, failed, Val.toAdmin, List.append_assoc] using
      (replacement_step (P := P) (host := host) s f vs a n []).steps

/-- When the source can also successfully grow and return a distinct old size,
this rewrite is strictly weaker than equivalence. -/
theorem not_equivalent_of_success {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi mi' : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (hg : mi.grow? n.toNat = some mi')
    (hp : P.growMaySucceed .memory ma mi.pages n.toNat)
    (hne : addrVal a (BitVec.ofNat _ mi.pages) ≠ failed a) (vs : List Val) :
    behavioursOf P host ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)]⟩ ≠
      behavioursOf P host
        ⟨s, f, vals vs ++ [aconst a n] ++ expression (replacement a)⟩ := by
  have hs := Step.vals_left
    (Step.memory (host := host) (MemoryStep.growSucceed hm hg hp)) vs
  have hb : Behaviour.returns (vs ++ [addrVal a (BitVec.ofNat _ mi.pages)]) ∈
      behavioursOf P host
        ⟨s, f, vals vs ++ [aconst a n, .plain (.memoryGrow x)]⟩ :=
    returns_mem_behavioursOf hs.steps (by simp [vals, addrVal, Val.toAdmin])
  intro heq
  rw [heq, replacement_behaviours_eq] at hb
  exact hne (by simpa using hb)

/-- A concrete zero-page memory: zero growth can succeed while the spec also
permits failure. This witnesses strict refinement at either address width. -/
def emptyMemory (a : AddrType) : MemInst :=
  ⟨⟨a, ⟨0, none⟩⟩, ByteArray.empty⟩

def exampleStore (H : Type) (a : AddrType) : Store H := { mems := [emptyMemory a] }

def exampleFrame : Frame := { module := { mems := [0] } }

/-- The strictness witness uses a valid memory in a well-formed store. -/
theorem exampleStore_ok (H : Type) (a : AddrType) : StoreOk (exampleStore H a) := by
  have hm : MemInstOk (emptyMemory a) := by
    simp [MemInstOk, emptyMemory, MemTypeOk, MemoryType.Valid, Limits.Valid]
  constructor <;> simp_all [exampleStore]

/-- Both sides of the strictness example have the same valid stack type. -/
theorem example_typed (a : AddrType) :
    let C : Context := { mems := [(emptyMemory a).type] }
    InstrsOk C [.memoryGrow ⟨0⟩] (.plain [a.valType] [a.valType]) ∧
      InstrsOk C (replacement a) (.plain [a.valType] [a.valType]) :=
  ⟨.instr (.memory (.memoryGrow rfl)), replacement_typed _ a⟩

/-- The premises are satisfiable: at memory32 and memory64, with any host,
forcing failure of zero growth is feasible refinement but not equivalence. -/
theorem strict_spec_example (a : AddrType) (host : HostSemantics H) :
    let s := exampleStore H a
    let source : Config H := ⟨s, exampleFrame, [aconst a 0, .plain (.memoryGrow ⟨0⟩)]⟩
    let target : Config H := ⟨s, exampleFrame, [aconst a 0] ++ expression (replacement a)⟩
    Optimization.Refines (behavioursOf Profile.spec host source)
      (behavioursOf Profile.spec host target) ∧
      behavioursOf Profile.spec host source ≠ behavioursOf Profile.spec host target := by
  have hm : (exampleStore H a).mem? exampleFrame ⟨0⟩ = some (0, emptyMemory a) := rfl
  constructor
  · exact spec_refines (n := 0) hm rfl []
  · apply not_equivalent_of_success (n := 0) hm (mi' := emptyMemory a)
      (by simp [emptyMemory, MemInst.grow?]; rfl) (by trivial) _ []
    cases a <;> decide

end Silmaril.Wasm.Binaryen.MemoryGrowFailure
