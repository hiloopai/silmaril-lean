module

public import Silmaril.Wasm.Execution.Core.Sim.Store

@[expose] public section

/-! # Code relations closed under the Core 3.0 evaluation-context structure

A transformation of instruction sequences is described by two *base* relations:

* `BI : List Instr → List Instr → Prop` on **source** sequences (what the pass
  rewrites, e.g. `unreachable :: es` ↦ `[unreachable]`), and
* `B : List Admin → List Admin → Prop` on **runtime** sequences (what those
  rewrites look like once execution has started inside them, e.g.
  `trap :: es` ↦ `[trap]`).

`InstrsRel BI` and `AdminsRel BI B` are their least closures under the syntax of
the language: sequencing (`append`), structured instructions (`block`, `loop`,
`if`, `try_table` bodies), and the administrative contexts `LABEL_n{cont}`,
`HANDLER_n{catch*}` and `FRAME_n{f}` (all of the spec's evaluation contexts).
`AdminsRel.src` embeds related source sequences into runtime code
(`expression`), which is how a block entry, a loop continuation or a function
call carries a source-level relation into the configuration.

`FuncRel BI` lifts `InstrsRel BI` to function instances (equal types, modules and
locals; related bodies; identical host code), and `CfgRel F R` relates two
configurations with `F`-related stores, equal frames and `R`-related code.

`codeSize` is the stuttering measure used by `Sim/Closure.lean`.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Validation

variable {H : Type}

mutual
/-- The closure of a source base relation on single instructions: identity, or
the same structured instruction with related bodies. -/
inductive InstrRel (BI : List Instr → List Instr → Prop) : Instr → Instr → Prop where
  | refl (i : Instr) : InstrRel BI i i
  | block (bt : BlockType) {b b' : List Instr} : InstrsRel BI b b' →
      InstrRel BI (.block bt b) (.block bt b')
  | loop (bt : BlockType) {b b' : List Instr} : InstrsRel BI b b' →
      InstrRel BI (.loop bt b) (.loop bt b')
  | if_ (bt : BlockType) {b₁ b₁' b₂ b₂' : List Instr} : InstrsRel BI b₁ b₁' →
      InstrsRel BI b₂ b₂' → InstrRel BI (.if_ bt b₁ b₂) (.if_ bt b₁' b₂')
  | tryTable (bt : BlockType) (cs : List Catch) {b b' : List Instr} : InstrsRel BI b b' →
      InstrRel BI (.tryTable bt cs b) (.tryTable bt cs b')
/-- The closure of a source base relation on sequences: pointwise, base pairs,
and concatenation. -/
inductive InstrsRel (BI : List Instr → List Instr → Prop) : List Instr → List Instr → Prop where
  | nil : InstrsRel BI [] []
  | cons {i i' : Instr} {is is' : List Instr} : InstrRel BI i i' → InstrsRel BI is is' →
      InstrsRel BI (i :: is) (i' :: is')
  | base {x y : List Instr} : BI x y → InstrsRel BI x y
  | append {x x' y y' : List Instr} : InstrsRel BI x y → InstrsRel BI x' y' →
      InstrsRel BI (x ++ x') (y ++ y')
end

mutual
/-- The closure on single administrative instructions: related source
instructions, identity, and the three administrative contexts with related
bodies (and related label continuations). -/
inductive AdminRel (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) :
    Admin → Admin → Prop where
  | refl (a : Admin) : AdminRel BI B a a
  | plain {i i' : Instr} : InstrRel BI i i' → AdminRel BI B (.plain i) (.plain i')
  | label (n : Nat) {cont cont' : List Instr} {b b' : List Admin} : InstrsRel BI cont cont' →
      AdminsRel BI B b b' → AdminRel BI B (.label n cont b) (.label n cont' b')
  | handler (n : Nat) (cs : List Catch) {b b' : List Admin} : AdminsRel BI B b b' →
      AdminRel BI B (.handler n cs b) (.handler n cs b')
  | frame (n : Nat) (f : Frame) {b b' : List Admin} : AdminsRel BI B b b' →
      AdminRel BI B (.frame n f b) (.frame n f b')
/-- The closure on runtime sequences: pointwise, base pairs, related source
sequences, and concatenation. -/
inductive AdminsRel (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) :
    List Admin → List Admin → Prop where
  | nil : AdminsRel BI B [] []
  | cons {a a' : Admin} {as as' : List Admin} : AdminRel BI B a a' → AdminsRel BI B as as' →
      AdminsRel BI B (a :: as) (a' :: as')
  | base {x y : List Admin} : B x y → AdminsRel BI B x y
  | src {x y : List Instr} : InstrsRel BI x y → AdminsRel BI B (expression x) (expression y)
  | append {x x' y y' : List Admin} : AdminsRel BI B x y → AdminsRel BI B x' y' →
      AdminsRel BI B (x ++ x') (y ++ y')
end

variable {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

theorem InstrsRel.refl : ∀ is : List Instr, InstrsRel BI is is
  | [] => .nil
  | i :: is => .cons (.refl i) (InstrsRel.refl is)

theorem AdminsRel.refl : ∀ as : List Admin, AdminsRel BI B as as
  | [] => .nil
  | a :: as => .cons (.refl a) (AdminsRel.refl as)

/-- Values are related to themselves. -/
theorem AdminsRel.vals (vs : List Val) : AdminsRel BI B (vals vs) (vals vs) :=
  AdminsRel.refl _

mutual
/-- Converse of the source closure (single instructions). -/
theorem InstrRel.flip {i j : Instr} : InstrRel BI i j → InstrRel (fun a b => BI b a) j i
  | .refl i => .refl i
  | .block bt h => .block bt h.flip
  | .loop bt h => .loop bt h.flip
  | .if_ bt h₁ h₂ => .if_ bt h₁.flip h₂.flip
  | .tryTable bt cs h => .tryTable bt cs h.flip
/-- Converse of the source closure: the closure of the converse base relation. -/
theorem InstrsRel.flip {x y : List Instr} : InstrsRel BI x y → InstrsRel (fun a b => BI b a) y x
  | .nil => .nil
  | .cons h t => .cons h.flip t.flip
  | .base h => .base h
  | .append h t => .append h.flip t.flip
end

mutual
/-- Converse of the runtime closure (single administrative instructions). -/
theorem AdminRel.flip {a b : Admin} :
    AdminRel BI B a b → AdminRel (fun a b => BI b a) (fun a b => B b a) b a
  | .refl a => .refl a
  | .plain h => .plain h.flip
  | .label n hc hb => .label n hc.flip hb.flip
  | .handler n cs hb => .handler n cs hb.flip
  | .frame n f hb => .frame n f hb.flip
/-- Converse of the closure: the closure of the converse base relations.
Used to obtain the backward simulation from the forward one. -/
theorem AdminsRel.flip {x y : List Admin} :
    AdminsRel BI B x y → AdminsRel (fun a b => BI b a) (fun a b => B b a) y x
  | .nil => .nil
  | .cons h t => .cons h.flip t.flip
  | .base h => .base h
  | .src h => .src h.flip
  | .append h t => .append h.flip t.flip
end

mutual
/-- The runtime closure is monotone in the runtime base relation (single
administrative instructions). -/
theorem AdminRel.mono {B' : List Admin → List Admin → Prop} (hB : ∀ x y, B x y → B' x y)
    {a b : Admin} : AdminRel BI B a b → AdminRel BI B' a b
  | .refl a => .refl a
  | .plain h => .plain h
  | .label n hc hb => .label n hc (AdminsRel.mono hB hb)
  | .handler n cs hb => .handler n cs (AdminsRel.mono hB hb)
  | .frame n f hb => .frame n f (AdminsRel.mono hB hb)
/-- The runtime closure is monotone in the runtime base relation. -/
theorem AdminsRel.mono {B' : List Admin → List Admin → Prop} (hB : ∀ x y, B x y → B' x y)
    {x y : List Admin} : AdminsRel BI B x y → AdminsRel BI B' x y
  | .nil => .nil
  | .cons h t => .cons (AdminRel.mono hB h) (AdminsRel.mono hB t)
  | .base h => .base (hB _ _ h)
  | .src h => .src h
  | .append h t => .append (AdminsRel.mono hB h) (AdminsRel.mono hB t)
end

/-! ## Function instances and configurations -/

/-- Related function code: Wasm functions with the same type index and locals and
`InstrsRel`-related bodies, or the very same host function. -/
def FuncCodeRel (BI : List Instr → List Instr → Prop) : FuncCode H → FuncCode H → Prop
  | .wasm f, .wasm g => f.type = g.type ∧ f.locals = g.locals ∧ InstrsRel BI f.body g.body
  | .host h, .host h' => h = h'
  | _, _ => False

/-- Related function instances: same defined type and module, related code. -/
def FuncRel (BI : List Instr → List Instr → Prop) (fi gi : FuncInst H) : Prop :=
  fi.type = gi.type ∧ fi.module = gi.module ∧ FuncCodeRel BI fi.code gi.code

theorem FuncCodeRel.refl : ∀ c : FuncCode H, FuncCodeRel BI c c
  | .wasm _ => ⟨rfl, rfl, InstrsRel.refl _⟩
  | .host _ => rfl

theorem FuncRel.refl (fi : FuncInst H) : FuncRel BI fi fi :=
  ⟨rfl, rfl, FuncCodeRel.refl _⟩

/-- Configurations with `F`-related stores, equal frames and `R`-related code. -/
structure CfgRel (F : FuncInst H → FuncInst H → Prop) (R : List Admin → List Admin → Prop)
    (c d : Config H) : Prop where
  store : StoreRel F c.store d.store
  frame : c.frame = d.frame
  code : R c.code d.code

/-- `CfgRel` is monotone in the code relation. -/
theorem CfgRel.mono {F : FuncInst H → FuncInst H → Prop} {R R' : List Admin → List Admin → Prop}
    (hR : ∀ x y, R x y → R' x y) {c d : Config H} (h : CfgRel F R c d) : CfgRel F R' c d :=
  ⟨h.store, h.frame, hR _ _ h.code⟩

/-- The stuttering measure: the structural size of the code. It is additive over
`++`, so a decrease inside an evaluation context is a decrease of the whole. -/
noncomputable def codeSize (es : List Admin) : Nat := sizeOf es

theorem codeSize_append (x y : List Admin) : codeSize (x ++ y) + 1 = codeSize x + codeSize y := by
  unfold codeSize
  induction x with
  | nil => simp only [List.nil_append, List.nil.sizeOf_spec]; omega
  | cons a x ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

end Silmaril.Wasm.Execution.Core.Sim
