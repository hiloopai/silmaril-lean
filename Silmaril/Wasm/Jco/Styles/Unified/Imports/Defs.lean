module

public import Silmaril.Wasm.Jco.Styles.Unified.Defs
public import Silmaril.Wasm.Jco.Styles.Imports.Defs

/-!
# The unified wrapper with world imports

`wrapUI md enc` is the unified wrapper `wrapU md.toMeta enc` (spilled parameters, wide results,
string encodings) together with the `canon lower`s of `wrapI` for the world's imports. The
component is the same as for `wrapI`: the exports' callees run over the instance with the
lowered imports, and every `realloc` runs without imports (`may_leave`). The lowers' `realloc`
is the adaptor's `cabi_realloc`.

`IMeta.AllocIndep M md` says that `M`'s allocator does not depend on the imports. A C allocator
calls no imports. Under it the `cabi_realloc` behaves the same with and without imports, and
the unified convention is stated over the instance with the C convention's imports
(`Silmaril.Wasm.Jco.Styles.Unified.Imports.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

/-- A unified wrapper with world imports: an `XComp` and lowered imports. -/
structure UIComp where
  comp : XComp
  lowers : List Lower
  deriving Inhabited

namespace UIComp

variable (M : ICoreInst) (H : Host M.St) (c : UIComp)

/-- The imports the component gives the core instance: `canon lower`s, every `realloc` without
imports. -/
def imps : Imports M.St := fun n =>
  match c.lowers.find? (·.sig.name == n) with
  | some lw =>
    canonLowerWith (M.inst noImports)
      (lowerBytes (M.inst noImports) (c.comp.callRef (M.inst noImports) lw.realloc)) (H n) lw.sig
  | none => noImports n

/-- The behaviour of export `name`, with the unified `canon lift`. -/
def callExport (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match c.comp.lifts.find? (·.sig.name == name) with
  | some l =>
    canonCallU (M.inst (c.imps M H)) l.enc (c.comp.callRef (M.inst noImports) l.realloc)
      (c.comp.callRef (M.inst (c.imps M H)) l.callee) l.sig vs
  | none => RM.fail

end UIComp

/-- **The unified wrapper with world imports.** -/
def wrapUI (md : IMeta) (enc : StrEnc) : UIComp :=
  { comp := wrapU md.toMeta enc, lowers := md.imports.map fun s => ⟨s, .adapt 0⟩ }

/-- `M`'s allocator does not depend on its imports. -/
def IMeta.AllocIndep (M : ICoreInst) (md : IMeta) : Prop :=
  ∀ imps xs, (M.inst imps).call md.alloc xs = (M.inst noImports).call md.alloc xs

end Silmaril.Wasm.Jco
