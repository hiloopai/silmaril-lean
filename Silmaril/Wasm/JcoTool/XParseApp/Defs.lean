module

public import Silmaril.Wasm.JcoTool.XParse.Defs

/-!
# Appending custom sections to an output component: definitions

`wasm-jco new` appends a `component-name` and a `producers` custom section to the bytes the
layout certificate and the reference validator checked (`Adapt.withMeta`). `XParseApp.Thms`
proves that `xparse` then reads the checked component followed by two custom sections, and that
the reference translation (`LayoutRefX.toRefX`) and so the reference validator's verdict are
unchanged. This module holds what the statement needs:

* `Sub G G'`: inclusion of grammar relations; `OSub`: the same for optional grammars, pointwise.
* `dtBody t`: the tag dispatch of `defTypeG (k + 1)` with `defTypeG k` as the parameter `t`
  (`defTypeG_succ` in `Thms`: `defTypeG (k + 1) = tagged "type" (dtBody (defTypeG k))`), so the
  nesting depth of the grammar can be raised (`xsectionG_mono`).
* `customSecs`: the custom sections of a list, as emitted sections.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.XParseApp

open Silmaril.Parse.ByteParse (Grammar Bytes)
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary

/-- Inclusion of grammar relations. -/
def Sub {α : Type} (G G' : Bytes → α → Prop) : Prop := ∀ ⦃l a⦄, G l a → G' l a

/-- Inclusion of optional grammars: where the first is defined, so is the second, larger. -/
def OSub {α : Type} (o o' : Option (Grammar α)) : Prop :=
  ∀ g, o = some g → ∃ g', o' = some g' ∧ Sub g.G g'.G

/-- The tag dispatch of `defTypeG (k + 1)`, over the grammar `t` of nested type definitions. -/
def dtBody (t : Grammar DefType) (b : UInt8) : Option (Grammar DefType) :=
  match b.toNat with
  | 0x40 => some ((funcTypeBodyG false).map .func)
  | 0x43 => some ((funcTypeBodyG true).map .func)
  | 0x41 => some ((vec (tagged "componentdecl" (componentDeclBody t))
      (tagged_nonEmpty _ _)).map .component)
  | 0x42 => some ((vec (tagged "instancedecl" (instanceDeclBody t))
      (tagged_nonEmpty _ _)).map .instance)
  | 0x3f => some (resourceBodyG.map fun p => .resource p.1 p.2)
  | _ => (defValTypeBody b).map (Grammar.map .val)

/-- Custom sections as emitted sections. -/
def customSecs (cs : List (String × ByteArray)) : List XSection :=
  cs.map fun (n, d) => .sec (.custom n d)

end Silmaril.Wasm.JcoTool.XParseApp
