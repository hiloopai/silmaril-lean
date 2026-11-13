module

public import Silmaril.Wasm.Behaviour.Semantics.V3

/-!
# Erasing `select` annotations: definitions

The first 3.0 feature the container compiler (`Silmaril.Wasm.LimeCompile.Container`) handles beyond
Lime1 is the **typed `select`** `select (t*)` (Wasm 2.0, reference types; opcode `0x1C`). Lime1 has
only the untyped `select`, whose Core image is `select none`. Core 3.0's two `select` rules
(`ParametricStep.selectTrue`/`selectFalse`) ignore the annotation, so erasing it should not change
behaviour; this topic proves that at the level of Core configurations.

* `selI`, `selL`: erase every `select` annotation of an instruction (list), through `block`,
  `loop`, `if` and `try_table` bodies;
* `selA`, `selAs`: the same on administrative code, through `label` continuations and bodies,
  `handler` and `frame` bodies;
* `selFn`, `selFI`, `selS`, `selC`: on functions, function instances (Wasm code only), stores (the
  functions only) and configurations;
* `HostResp host`: the host does not tell apart stores that agree after erasure (a returning call
  on related stores returns the same result on related stores, a diverging one diverges);
* `selM m`: erase the annotations of a module's function bodies (initialisers are constant
  expressions, which have no `select`, and are left alone);
* `SelBI`: the base relation of silmaril-lean's code-relation closure (`Sim.InstrsRel`) that
  relates `select ts` to `select ts'`, used to reuse its module-instantiation lemma.

The relation of the bisimulation is `selC c = selC d`: it is symmetric, so one simulation
lemma gives both inclusions of behaviours.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

mutual
/-- Erase the `select` annotations of an instruction (deeply). -/
def selI : Instr → Instr
  | .select _ => .select none
  | .block bt b => .block bt (selL b)
  | .loop bt b => .loop bt (selL b)
  | .if_ bt b₁ b₂ => .if_ bt (selL b₁) (selL b₂)
  | .tryTable bt cs b => .tryTable bt cs (selL b)
  | i => i

/-- Erase the `select` annotations of an instruction sequence. -/
def selL : List Instr → List Instr
  | [] => []
  | i :: is => selI i :: selL is
end

mutual
/-- Erase the `select` annotations of administrative code (deeply). -/
def selA : Admin → Admin
  | .plain i => .plain (selI i)
  | .label n cont body => .label n (selL cont) (selAs body)
  | .handler n cs body => .handler n cs (selAs body)
  | .frame n f body => .frame n f (selAs body)
  | a => a

/-- Erase the `select` annotations of an administrative sequence. -/
def selAs : List Admin → List Admin
  | [] => []
  | a :: as => selA a :: selAs as
end

/-- Erase the `select` annotations of a function body. -/
def selFn (f : Func) : Func := ⟨f.type, f.locals, selL f.body⟩

variable {H : Type}

/-- Erase the `select` annotations of a function instance's code. -/
def selFI (fi : FuncInst H) : FuncInst H :=
  ⟨fi.type, fi.module, match fi.code with
    | .wasm f => .wasm (selFn f)
    | .host h => .host h⟩

/-- Erase the `select` annotations of a store's functions. -/
def selS (s : Store H) : Store H := { s with funcs := s.funcs.map selFI }

/-- Erase the `select` annotations of a configuration (store and code). -/
def selC (c : Config H) : Config H := ⟨selS c.store, c.frame, selAs c.code⟩

/-- A host **respects erasure**: on stores equal after erasure, every outcome of a call is
matched by an outcome on the other store, with the same result and stores equal after
erasure. -/
def HostResp (host : HostSemantics H) : Prop :=
  ∀ (h : H) (s t : Store H) (vs : List Val) (o : HostOutcome H),
    selS s = selS t → host h s vs o →
      ∃ o', host h t vs o' ∧
        Silmaril.Wasm.Execution.Host.Outcome.Sim (fun s t => selS s = selS t) id o o'

/-- Erase the `select` annotations of a module's function bodies. -/
def selM (m : Module) : Module := { m with funcs := m.funcs.map selFn }

/-- `select ts` and `select ts'`, as related one-instruction sequences. -/
def SelBI (x y : List Instr) : Prop := ∃ ts ts', x = [.select ts] ∧ y = [.select ts']

end Silmaril.Wasm.LimeCompile.Select
