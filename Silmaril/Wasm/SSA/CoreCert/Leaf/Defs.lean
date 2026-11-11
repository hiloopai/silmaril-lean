module

public import Silmaril.Wasm.SSA.CoreCert.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V2.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Store
public import Silmaril.Wasm.Binaryen.Behaviour

/-!
# Leaf functions in Core 3.0 stores: statement vocabulary

The predicates and relations that the theorems of `Silmaril.Wasm.SSA.CoreCert.Thms` are stated
with. Nothing here is executed by the optimiser.

**Store-free leaf code** (`leafFunc` functions):
* `ValP a`, `FrameP a`, `PAdmin a`, `PAdmins a`: leaf values, frames and administrative
  instructions, whose only function reference is to address `a`;
* `LeafAt s a`: the function at address `a` of `s` is a store-free leaf;
* `LeafConf a c`: the leaf invariant of a configuration; `swapStore t c`: the same code and
  frame in store `t`; `Swap`: what a step of leaf code gives in another store.

**Strict leaf code** (`strictFunc` functions):
* `ValS`: values without references; `withMod`, `swapA`: replace the module instance of a
  frame;
* `canon X`: the canonical configuration of a frame administrative instruction `X` (empty
  store, empty enclosing frame, empty module instance); `LBeh P X`: its Core 3.0 behaviours
  under the closed host;
* `entry n mi vs fn`: the callee frame of `call_ref-func` for code `fn` on arguments `vs`.

**Related stores and modules:**
* `NoRefParams d`: arguments typed at the parameters of `d` hold no references;
* `LeafPair P fi gi`: equivalent strict leaf functions (same type and module instance, no
  reference parameters, equal `LBeh` of their callee frames on typed arguments); `FRel P`:
  equal, or a `LeafPair`; `SRel P`: silmaril's `Sim.StoreRel (FRel P)`;
* `LeafFun P dt fn fn'`: equivalent strict leaf code at the defined type `dt`; `FunRel P m`:
  equal or `LeafFun`-equivalent functions of the same type index; `ModRel P m m'`: Core modules
  equal except for `FunRel`-related function lists.

With the short facts used by dot notation (`SRel.symm`, `ModRel.refl`, …) and the `simp`
lemmas of `PAdmins`.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA

variable {H : Type} {P : Numerics.Profile}

/-! ## Store-free leaf code -/

/-- Values of leaf code: numbers, vectors, `ref.null` and the function `a`. -/
def ValP (a : Nat) : Val → Prop
  | .ref r => r = .null ∨ r = .func a
  | _ => True

/-- The locals of a frame are leaf values. -/
def FrameP (a : Nat) (fr : Frame) : Prop := ∀ v, some v ∈ fr.locals → ValP a v

/-- Plain instructions of leaf code: store-free instructions and constants. -/
def PInstr (i : Instr) : Prop := pureInstr i = true

mutual
/-- Administrative instructions of leaf code. -/
def PAdmin (a : Nat) : Admin → Prop
  | .plain i => PInstr i
  | .ref r => r = .null ∨ r = .func a
  | .callRefType _ => True
  | .returnCallRefType _ => False
  | .label _ cont body => pureInstrs cont = true ∧ PAdmins a body
  | .handler _ _ body => PAdmins a body
  | .frame _ fr body => FrameP a fr ∧ PAdmins a body
  | .trap => True
/-- `PAdmin` on a sequence. -/
def PAdmins (a : Nat) : List Admin → Prop
  | [] => True
  | c :: cs => PAdmin a c ∧ PAdmins a cs
end

@[simp] theorem pAdmins_nil {a : Nat} : PAdmins a [] := trivial

@[simp] theorem pAdmins_cons {a : Nat} {c : Admin} {cs : List Admin} :
    PAdmins a (c :: cs) ↔ PAdmin a c ∧ PAdmins a cs := Iff.rfl

@[simp] theorem pAdmins_append {a : Nat} {as bs : List Admin} :
    PAdmins a (as ++ bs) ↔ PAdmins a as ∧ PAdmins a bs := by
  induction as with
  | nil => simp
  | cons c as ih => simp [ih, and_assoc]

/-- The function at `a` is a store-free leaf. -/
def LeafAt (s : Store H) (a : Nat) : Prop :=
  ∃ fi fn, s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧ leafFunc fn = true

/-- What a step of leaf code gives in another store. -/
def Swap (P : Numerics.Profile) (host : HostSemantics H) (a : Nat) (t : Store H)
    (c c' : Config H) : Prop :=
  c'.store = c.store ∧ Step P host ⟨t, c.frame, c.code⟩ ⟨t, c'.frame, c'.code⟩ ∧
    PAdmins a c'.code ∧ FrameP a c'.frame

/-- The leaf invariant of a configuration in store `s`. -/
def LeafConf (a : Nat) (c : Config H) : Prop :=
  PAdmins a c.code ∧ FrameP a c.frame ∧ LeafAt c.store a

/-- The same code and frame, in store `t`. -/
def swapStore (t : Store H) (c : Config H) : Config H := ⟨t, c.frame, c.code⟩

/-! ## Strict leaf code -/

/-- Values of strict leaf code: no references. -/
def ValS : Val → Prop
  | .ref _ => False
  | _ => True

/-- Replace the module instance of a frame. -/
def withMod (fr : Frame) (mi : ModuleInst) : Frame := { fr with module := mi }

/-- Replace the module instance of a frame administrative instruction. -/
def swapA (mi : ModuleInst) : Admin → Admin
  | .frame n fr b => .frame n (withMod fr mi) b
  | a => a

/-- The canonical configuration of a strict frame: empty store, empty enclosing frame, the
frame's module instance replaced by the empty one. -/
def canon (X : Admin) : Config Empty := ⟨{}, {}, [swapA {} X]⟩

/-- **The canonical Core behaviours of a strict frame** (closed host). -/
def LBeh (P : Numerics.Profile) (X : Admin) : Set (Behaviour Val) :=
  behavioursOf P Binaryen.closedHost (canon X)

/-- The callee frame of `call_ref-func` for function code `fn` on arguments `vs`. -/
def entry (n : Nat) (mi : ModuleInst) (vs : List Val) (fn : Func) : Admin :=
  .frame n (Frame.forCall mi vs fn.locals) [.label n [] (expression fn.body)]

/-! ## Related stores -/

/-- Arguments typed at the parameters of `d` are no references. -/
def NoRefParams (d : Validation.DefType) : Prop :=
  ∀ ps rs, Validation.Expand d (.func ps rs) → ∀ {H : Type} (s : Store H) (vs : List Val),
    List.Forall₂ (ValOk s) vs ps.toList → ∀ v ∈ vs, ValS v

/-- **Equivalent strict leaf functions**: same type and module instance, strict leaf code,
no reference parameters, and the same canonical behaviours of their callee frames on typed
arguments. -/
def LeafPair (P : Numerics.Profile) (fi gi : FuncInst H) : Prop :=
  fi.type = gi.type ∧ fi.module = gi.module ∧ NoRefParams fi.type ∧
    ∃ fn fn', fi.code = .wasm fn ∧ gi.code = .wasm fn' ∧ strictFunc fn = true ∧
      strictFunc fn' = true ∧ ∀ ps rs vs, Validation.Expand fi.type (.func ps rs) →
        (∃ (H' : Type) (u : Store H'), List.Forall₂ (ValOk u) vs ps.toList) →
          LBeh P (entry rs.length {} vs fn) = LBeh P (entry rs.length {} vs fn')

/-- Equal function instances, or a `LeafPair`. -/
def FRel (P : Numerics.Profile) (fi gi : FuncInst H) : Prop := fi = gi ∨ LeafPair P fi gi

/-- Stores with `FRel`-related functions, equal otherwise. -/
abbrev SRel (P : Numerics.Profile) (s t : Store H) : Prop := Sim.StoreRel (FRel P) s t

theorem LeafPair.symm {fi gi : FuncInst H} (h : LeafPair P fi gi) : LeafPair P gi fi := by
  obtain ⟨hty, hmod, hnr, fn, fn', h₁, h₂, hs₁, hs₂, heq⟩ := h
  refine ⟨hty.symm, hmod.symm, hty ▸ hnr, fn', fn, h₂, h₁, hs₂, hs₁, ?_⟩
  intro ps rs vs he hv
  exact (heq ps rs vs (hty ▸ he) hv).symm

theorem FRel.symm {fi gi : FuncInst H} (h : FRel P fi gi) : FRel P gi fi :=
  h.elim (fun e => .inl e.symm) (fun h => .inr h.symm)

theorem FRel.type_eq {fi gi : FuncInst H} (h : FRel P fi gi) : fi.type = gi.type :=
  h.elim (fun e => e ▸ rfl) (fun h => h.1)

theorem SRel.symm {s t : Store H} (h : SRel P s t) : SRel P t s :=
  ⟨h.types.symm, h.other.symm, List.Forall₂.flip (h.funcs.imp fun _ _ h => h.symm)⟩

theorem SRel.refl (s : Store H) : SRel P s s := Sim.StoreRel.refl (fun _ => .inl rfl) s

/-! ## Related modules -/

/-- **Equivalent strict leaf functions at the defined type `dt`.** -/
def LeafFun (P : Numerics.Profile) (dt : Validation.DefType) (fn fn' : Func) : Prop :=
  NoRefParams dt ∧ strictFunc fn = true ∧ strictFunc fn' = true ∧
    ∀ ps rs vs, Validation.Expand dt (.func ps rs) →
      (∃ (H' : Type) (u : Store H'), List.Forall₂ (ValOk u) vs ps.toList) →
        LBeh P (entry rs.length {} vs fn) = LBeh P (entry rs.length {} vs fn')

theorem LeafFun.symm {dt : Validation.DefType} {fn fn' : Func} (h : LeafFun P dt fn fn') :
    LeafFun P dt fn' fn :=
  ⟨h.1, h.2.2.1, h.2.1, fun ps rs vs he hv => (h.2.2.2 ps rs vs he hv).symm⟩

theorem LeafFun.leafPair {dt : Validation.DefType} {fn fn' : Func} (h : LeafFun P dt fn fn')
    (mi : ModuleInst) :
    LeafPair (H := H) P ⟨dt, mi, .wasm fn⟩ ⟨dt, mi, .wasm fn'⟩ :=
  ⟨rfl, rfl, h.1, fn, fn', rfl, rfl, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The relation between the functions of `m` and of `m'`. -/
def FunRel (P : Numerics.Profile) (m : Module) (f g : Func) : Prop :=
  f.type = g.type ∧ (f = g ∨ ∀ dt, (allocTypes m.types)[f.type.toNat]? = some dt → LeafFun P dt f g)

/-- **Modules with equal or equivalent strict leaf functions.** -/
structure ModRel (P : Numerics.Profile) (m m' : Module) : Prop where
  other : ({ m with funcs := [] } : Module) = ({ m' with funcs := [] } : Module)
  funcs : List.Forall₂ (FunRel P m) m.funcs m'.funcs

theorem ModRel.types_eq {m m' : Module} (h : ModRel P m m') : m.types = m'.types := by
  have := congrArg (fun x : Module => x.types) h.other
  simpa using this

theorem ModRel.symm {m m' : Module} (h : ModRel P m m') : ModRel P m' m := by
  refine ⟨h.other.symm, List.Forall₂.flip (h.funcs.imp fun f g ⟨hty, hfg⟩ => ⟨hty.symm, ?_⟩)⟩
  rcases hfg with rfl | hl
  · exact .inl rfl
  · refine .inr fun dt hdt => (hl dt ?_).symm
    rw [h.types_eq, hty]
    exact hdt

theorem ModRel.refl (m : Module) : ModRel P m m :=
  ⟨rfl, List.forall₂_same.mpr fun _ _ => ⟨rfl, .inl rfl⟩⟩

end Silmaril.Wasm.SSA.CoreCert
