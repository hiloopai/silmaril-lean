module

public import Silmaril.Wasm.Execution.Core.Runtime
public import Silmaril.Wasm.V2.Execution.Basic
public import Silmaril.Wasm.Models.V2Core.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare

/-!
# Spec-form instantiation with globals, host-free: definitions

* `GlobalsNamed s`: the function instances of `s` name only existing globals (their module
  instances' global addresses and global exports are below `s.globals.length`). This is the
  one store condition under which the global-address embedding of
  `Silmaril.Wasm.Game.SpecGlobals` relates the specification's double allocation to single
  allocation.
* `noHostC`: the Core host relation with no host calls.
* `GlobalsBlind host`: the Core host keeps the store's globals and functions, and
  its calls are unchanged when the globals and functions of the store are replaced. Such a
  host commutes with every global-address embedding.
* `pureHost F G`: a host that leaves the store unchanged and answers from the host
  function and the arguments only.
* `GlobalsNamedV s`: `GlobalsNamed` for a 2.0 store.
* 2.0 hosts under global embeddings: `moduleViewV`, `functionV`, `ModDomV` and
  `EmbV ρ D s t` are the global-address embedding of 2.0 stores (the 2.0 analogue of
  `Silmaril.Proofs.Wasm.Game.SpecGlobals.Emb`); `HostEmbV src`: a 2.0 host commuting with these
  embeddings; `GlobalsBlindV src`: a 2.0 host keeping, and not reading, globals and functions;
  `pureHostV F G`: a store-preserving 2.0 host;
  `GImg g`: a Core global is the image of a 2.0 global; `SpecGlobalsImg X`: the spec
  preparation (`prepare?`) of every valid 2.0 module's image into `X` holds only `GImg`
  globals.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The function instances of `s` name only existing globals. -/
def GlobalsNamed {H : Type} (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, (∀ a ∈ fi.module.globals, a < s.globals.length) ∧
    ∀ e ∈ fi.module.exports, ∀ a, e.addr = .global a → a < s.globals.length

/-- No host calls. -/
def noHostC {H : Type} : HostSemantics H := fun _ _ _ _ => False

/-- A Core host blind to the store's globals and functions: it keeps them, and its returns
and divergences are unchanged when they are replaced. -/
structure GlobalsBlind {H : Type} (host : HostSemantics H) : Prop where
  keeps : ∀ h s vs s' r, host h s vs (.returned s' r) → s'.globals = s.globals ∧ s'.funcs = s.funcs
  ret : ∀ h s vs s' r gs fs, host h s vs (.returned s' r) →
    host h { s with globals := gs, funcs := fs } vs (.returned { s' with globals := gs, funcs := fs } r)
  div : ∀ h s vs gs fs, host h s vs .diverged →
    host h { s with globals := gs, funcs := fs } vs .diverged

/-- A host that leaves the store unchanged and answers from the host function and the
arguments only (`F h vs r`: the call may return `r`; `G h vs`: the call may diverge). -/
def pureHost {H : Type} (F : H → List Val → Result → Prop) (G : H → List Val → Prop) :
    HostSemantics H :=
  fun h s vs o => (∃ r, F h vs r ∧ o = .returned s r) ∨ (G h vs ∧ o = .diverged)

/-- The function instances of a 2.0 store name only existing globals. -/
def GlobalsNamedV {H : Type} (s : Silmaril.Wasm.V2.Execution.Store H) : Prop :=
  ∀ fi ∈ s.funcs, (∀ a ∈ fi.module.globals, a < s.globals.length) ∧
    ∀ e ∈ fi.module.exports, ∀ a, e.addr = .global a → a < s.globals.length

/-! ## 2.0 hosts under global-address embeddings -/

/-- Rename a 2.0 global external address. -/
def externalV (ρ : Nat → Nat) :
    Silmaril.Wasm.V2.Execution.ExternAddr → Silmaril.Wasm.V2.Execution.ExternAddr
  | .global a => .global (ρ a)
  | other => other

/-- Rename the global addresses of a 2.0 module instance (its globals and global exports). -/
def moduleViewV (ρ : Nat → Nat) (m : Silmaril.Wasm.V2.Execution.ModuleInst) :
    Silmaril.Wasm.V2.Execution.ModuleInst :=
  { m with
    globals := m.globals.map ρ
    exports := m.exports.map fun e => { e with addr := externalV ρ e.addr } }

/-- Rename the global addresses of a 2.0 function's module instance. -/
def functionV {H : Type} (ρ : Nat → Nat) (fi : Silmaril.Wasm.V2.Execution.FuncInst H) :
    Silmaril.Wasm.V2.Execution.FuncInst H :=
  { fi with module := moduleViewV ρ fi.module }

/-- The global addresses named by a 2.0 module instance lie in `D`. -/
def ModDomV (D : Nat → Prop) (m : Silmaril.Wasm.V2.Execution.ModuleInst) : Prop :=
  (∀ a ∈ m.globals, D a) ∧ ∀ e ∈ m.exports, ∀ a, e.addr = .global a → D a

/-- **Global embedding of 2.0 stores**: `t` is `s` with global `a` at `ρ a` for `a ∈ D` (`ρ`
injective on `D`), every function renamed, the other components equal. -/
structure EmbV {H : Type} (ρ : Nat → Nat) (D : Nat → Prop)
    (s t : Silmaril.Wasm.V2.Execution.Store H) : Prop where
  globals : ∀ a, D a → t.globals[ρ a]? = s.globals[a]?
  inj : ∀ a b, D a → D b → ρ a = ρ b → a = b
  funcs : t.funcs = s.funcs.map (functionV ρ)
  fdom : ∀ fi ∈ s.funcs, ModDomV D fi.module
  tables : s.tables = t.tables
  mems : s.mems = t.mems
  elems : s.elems = t.elems
  datas : s.datas = t.datas

/-- A 2.0 host commutes with the global-address embeddings of 2.0 stores. -/
structure HostEmbV {H : Type} (src : Silmaril.Wasm.V2.Execution.HostSemantics H) : Prop where
  ret : ∀ {ρ : Nat → Nat} {D : Nat → Prop} {s t s' : Silmaril.Wasm.V2.Execution.Store H} {h : H}
    {vs : List Silmaril.Wasm.V2.Execution.Val} {r : Silmaril.Wasm.V2.Execution.Result},
    EmbV ρ D s t → src h s vs (.returned s' r) →
      ∃ t', src h t vs (.returned t' r) ∧ EmbV ρ D s' t'
  div : ∀ {ρ : Nat → Nat} {D : Nat → Prop} {s t : Silmaril.Wasm.V2.Execution.Store H} {h : H}
    {vs : List Silmaril.Wasm.V2.Execution.Val},
    EmbV ρ D s t → src h s vs .diverged → src h t vs .diverged

/-- A 2.0 host blind to the store's globals and functions: it keeps them, and its returns and
divergences are unchanged when they are replaced. -/
structure GlobalsBlindV {H : Type} (src : Silmaril.Wasm.V2.Execution.HostSemantics H) :
    Prop where
  keeps : ∀ h s vs s' r, src h s vs (.returned s' r) → s'.globals = s.globals ∧ s'.funcs = s.funcs
  ret : ∀ h s vs s' r gs fs, src h s vs (.returned s' r) →
    src h { s with globals := gs, funcs := fs } vs (.returned { s' with globals := gs, funcs := fs } r)
  div : ∀ h s vs gs fs, src h s vs .diverged →
    src h { s with globals := gs, funcs := fs } vs .diverged

/-- A 2.0 host that leaves the store unchanged and answers from the host function and the
arguments only. -/
def pureHostV {H : Type} (F : H → List Silmaril.Wasm.V2.Execution.Val → Silmaril.Wasm.V2.Execution.Result → Prop)
    (G : H → List Silmaril.Wasm.V2.Execution.Val → Prop) : Silmaril.Wasm.Models.V2Core.VHost H :=
  fun h s vs o => (∃ r, F h vs r ∧ o = .returned s r) ∨ (G h vs ∧ o = .diverged)

/-- A Core global is the image of a 2.0 global. -/
def GImg (g : GlobalInst) : Prop :=
  ∃ gv : Silmaril.Wasm.V2.Execution.GlobalInst, Silmaril.Wasm.V2.Execution.GlobalInst.toCore gv = g

/-- The spec preparation of every valid 2.0 module's Core image into `X` holds only images of
2.0 globals. -/
def SpecGlobalsImg {H : Type} (X : Store H) : Prop :=
  ∀ (m : Silmaril.Wasm.V2.Module) (cm : Module) (cxas : List ExternAddr) (c : Config H)
    (st : Option FuncIdx), Silmaril.Wasm.V2.Validation.ModuleValid m →
    Silmaril.Wasm.V2.Module.toCore m = some cm → prepare? evalConst? X cm cxas = some (c, st) →
    ∀ g ∈ c.store.globals, GImg g

end Silmaril.Wasm.Models.V2CoreSpec
