module

public import Silmaril.Elf.Staged.Leaf.Thms
public import Silmaril.Prelude.Trust.Policy.Defs
-- Native runs interpret these functions while elaborating, so their code is loaded as `meta`.
public meta import Silmaril.Elf.Staged.Leaf.Thms
public meta import Silmaril.Prelude.Trust.Elab.Defs
public meta import Lean.Elab.Tactic

/-! # ELF leaves under the trust policy (`elf_leaf`)

Each leaf (`Silmaril.Elf.Staged.Leaf`) has **two checkers** for **one proposition**:

* the **native** checker `Native.<leaf> b c` runs the leaf on the `ByteArray` of a file
  (`fastRead`). It is registered as the native procedure `elf.<leaf>` with **no kernel
  fallback**, because the kernel would have to decode the `ByteArray` one byte at a time;
* the **kernel** checker `Kernel.<leaf> x c` runs the same leaf on core's kernel bytes `x`
  (`Silmaril.KBytes.readLE`). It is **never** run natively: it is not registered, and nothing
  here passes it to the native evaluator.

`Native.<leaf>_sound` and `Kernel.<leaf>_sound` conclude the same `P (blobOf ⟨raw⟩) c`, where
the kernel bytes are tied to the raw bytes by `x.toByteArray = raw` (from `kbytes_def … of_include`).

## `elf_leaf`

```
theorem layout : LayoutIs F L := by
  elf_leaf elf.layout (native := Native.layout_sound) (kernel := Kernel.layout_sound x.wf x.toByteArray_eq)
```

1. It asks the trust policy (`Silmaril.Trust.allowed`) whether the procedure may run natively
   in this module under the current profile, **before** running anything.
2. **Allowed:** it applies the native soundness lemma and closes `Native.<leaf> b c = true` with
   `edge_decide`, which runs it natively and records the use. If the run fails or returns
   `false`, the error propagates; there is no fallback to the kernel.
3. **Not allowed:** it applies the kernel soundness lemma and has the kernel check
   `Kernel.<leaf> x c = true` by `Eq.refl` in an auxiliary lemma, then records a kernel use
   under the same procedure name.
4. Without `(native := …)` the leaf is kernel-only: the kernel path is taken in every profile.
5. A procedure name that is not registered (an unsupported leaf such as `elf.dwarf.line`) is an
   error.

**Temporary.** This tactic stands in for a paired-procedure hook of the trust framework (one
procedure, a native and a kernel checker, two soundness lemmas, policy selection before
either runs). It reads the framework's internals (`procExt`, `allowed`, `recordUse`) and is to
be replaced by that hook when it exists. A recorded use is provenance, not authorization: each
path's proof is checked as usual (the native axiom by `edge_decide`, the kernel lemma by the
kernel).
-/

@[expose] public section

namespace Silmaril.Elf.Staged

open Silmaril.Formats.ELF (SectionHeader Rela)

namespace Native

/-- `elf.layout` on a `ByteArray`. -/
def layout (b : Silmaril.Formats.Bytes) (L : Layout) : Bool := Leaf.layout.native b L
/-- `elf.body` on a `ByteArray`. -/
def body (b : Silmaril.Formats.Bytes) (c : Layout × SectionHeader × Body) : Bool :=
  Leaf.body.native b c
/-- `elf.loader` on a `ByteArray`. -/
def loader (b : Silmaril.Formats.Bytes) (c : Layout × Loader) : Bool := Leaf.loader.native b c
/-- `elf.rela` on a `ByteArray`. -/
def rela (b : Silmaril.Formats.Bytes) (c : Nat × Nat × List Rela) : Bool := Leaf.rela.native b c
/-- `elf.tiles` on a `ByteArray`. -/
def tiles (b : Silmaril.Formats.Bytes) (c : Nat × List Nat) : Bool := Leaf.tiles.native b c
/-- `elf.tiles.x86` on a `ByteArray`. -/
def tilesX86 (b : Silmaril.Formats.Bytes) (c : Nat × List Nat) : Bool := Leaf.tilesX86.native b c
/-- `elf.symbols.byName` on a `ByteArray`. -/
def byName (b : Silmaril.Formats.Bytes) (x : Symbols.ByName) : Bool := Leaf.byName.native b x
/-- `elf.symbols.byAddr` on a `ByteArray`. -/
def byAddr (b : Silmaril.Formats.Bytes) (x : Symbols.ByAddr) : Bool := Leaf.byAddr.native b x

variable {raw : ByteArray}

theorem layout_sound {L : Layout} (h : layout ⟨raw⟩ L = true) : LayoutIs (blobOf ⟨raw⟩) L :=
  Leaf.layout.of_native h
theorem body_sound {c : Layout × SectionHeader × Body} (h : body ⟨raw⟩ c = true) :
    BodyIs (blobOf ⟨raw⟩) c.1 c.2.1 c.2.2 :=
  Leaf.body.of_native h
theorem loader_sound {c : Layout × Loader} (h : loader ⟨raw⟩ c = true) :
    LoaderIs (blobOf ⟨raw⟩) c.1 c.2 :=
  Leaf.loader.of_native h
theorem rela_sound {c : Nat × Nat × List Rela} (h : rela ⟨raw⟩ c = true) :
    EntriesAt (blobOf ⟨raw⟩) Parse.rela c.1 24 c.2.1 c.2.2 :=
  Leaf.rela.of_native h
theorem tiles_sound {c : Nat × List Nat} (h : tiles ⟨raw⟩ c = true) :
    TilesAt (blobOf ⟨raw⟩) (fun _ _ => true) c.1 c.2 :=
  Leaf.tiles.of_native h
theorem tilesX86_sound {c : Nat × List Nat} (h : tilesX86 ⟨raw⟩ c = true) :
    TilesAt (blobOf ⟨raw⟩) x86Ok c.1 c.2 :=
  Leaf.tilesX86.of_native h
theorem byName_sound {x : Symbols.ByName} (h : byName ⟨raw⟩ x = true) :
    x.sorted = true ∧ x.Sound (blobOf ⟨raw⟩) :=
  Leaf.byName.of_native h
theorem byAddr_sound {x : Symbols.ByAddr} (h : byAddr ⟨raw⟩ x = true) :
    x.sorted = true ∧ x.Sound (blobOf ⟨raw⟩) :=
  Leaf.byAddr.of_native h

end Native

namespace Kernel

/-- `elf.layout` on kernel bytes. -/
def layout (x : Silmaril.KBytes) (L : Layout) : Bool := Leaf.layout.kbytes x L
/-- `elf.body` on kernel bytes. -/
def body (x : Silmaril.KBytes) (c : Layout × SectionHeader × Body) : Bool := Leaf.body.kbytes x c
/-- `elf.loader` on kernel bytes. -/
def loader (x : Silmaril.KBytes) (c : Layout × Loader) : Bool := Leaf.loader.kbytes x c
/-- `elf.rela` on kernel bytes. -/
def rela (x : Silmaril.KBytes) (c : Nat × Nat × List Rela) : Bool := Leaf.rela.kbytes x c
/-- `elf.tiles` on kernel bytes. -/
def tiles (x : Silmaril.KBytes) (c : Nat × List Nat) : Bool := Leaf.tiles.kbytes x c
/-- `elf.tiles.x86` on kernel bytes. -/
def tilesX86 (x : Silmaril.KBytes) (c : Nat × List Nat) : Bool := Leaf.tilesX86.kbytes x c
/-- `elf.symbols.byName` on kernel bytes. -/
def byName (x : Silmaril.KBytes) (s : Symbols.ByName) : Bool := Leaf.byName.kbytes x s
/-- `elf.symbols.byAddr` on kernel bytes. -/
def byAddr (x : Silmaril.KBytes) (s : Symbols.ByAddr) : Bool := Leaf.byAddr.kbytes x s

variable {x : Silmaril.KBytes} {raw : ByteArray}

theorem layout_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {L : Layout}
    (h : layout x L = true) : LayoutIs (blobOf ⟨raw⟩) L :=
  Leaf.layout.of_kbytes hx hr h
theorem body_sound (hx : x.wf = true) (hr : x.toByteArray = raw)
    {c : Layout × SectionHeader × Body} (h : body x c = true) :
    BodyIs (blobOf ⟨raw⟩) c.1 c.2.1 c.2.2 :=
  Leaf.body.of_kbytes hx hr h
theorem loader_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Layout × Loader}
    (h : loader x c = true) : LoaderIs (blobOf ⟨raw⟩) c.1 c.2 :=
  Leaf.loader.of_kbytes hx hr h
theorem rela_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Nat × Nat × List Rela}
    (h : rela x c = true) : EntriesAt (blobOf ⟨raw⟩) Parse.rela c.1 24 c.2.1 c.2.2 :=
  Leaf.rela.of_kbytes hx hr h
theorem tiles_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Nat × List Nat}
    (h : tiles x c = true) : TilesAt (blobOf ⟨raw⟩) (fun _ _ => true) c.1 c.2 :=
  Leaf.tiles.of_kbytes hx hr h
theorem tilesX86_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {c : Nat × List Nat}
    (h : tilesX86 x c = true) : TilesAt (blobOf ⟨raw⟩) x86Ok c.1 c.2 :=
  Leaf.tilesX86.of_kbytes hx hr h
theorem byName_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {s : Symbols.ByName}
    (h : byName x s = true) : s.sorted = true ∧ s.Sound (blobOf ⟨raw⟩) :=
  Leaf.byName.of_kbytes hx hr h
theorem byAddr_sound (hx : x.wf = true) (hr : x.toByteArray = raw) {s : Symbols.ByAddr}
    (h : byAddr x s = true) : s.sorted = true ∧ s.Sound (blobOf ⟨raw⟩) :=
  Leaf.byAddr.of_kbytes hx hr h

end Kernel

end Silmaril.Elf.Staged

/-! ## Registrations -/

/-- The stage-1 layout of an ELF file, read natively from its `ByteArray` (`fastRead`). Trusts
the compiled reader and `Nat` arithmetic. No kernel fallback: the kernel checker reads
`Silmaril.KBytes` instead (`elf_leaf`). -/
native_decider elf.layout := Silmaril.Elf.Staged.Native.layout

/-- One section body, read natively. Trusts the compiled reader. No kernel fallback. -/
native_decider elf.body := Silmaril.Elf.Staged.Native.body

/-- The loader view, read natively. Trusts the compiled reader. No kernel fallback. -/
native_decider elf.loader := Silmaril.Elf.Staged.Native.loader

/-- A window of `RELA` entries, read natively. Trusts the compiled reader. No kernel fallback. -/
native_decider elf.rela := Silmaril.Elf.Staged.Native.rela

/-- Instruction tiles lie in the file, read natively. No kernel fallback. -/
native_decider elf.tiles := Silmaril.Elf.Staged.Native.tiles

/-- Instruction tiles each decode as one instruction of the local x86 model, natively. Trusts
the compiled decoder. No kernel fallback. -/
native_decider elf.tiles.x86 := Silmaril.Elf.Staged.Native.tilesX86

/-- A forward symbol index, checked natively. No kernel fallback. -/
native_decider elf.symbols.byName := Silmaril.Elf.Staged.Native.byName

/-- A reverse symbol map, checked natively. No kernel fallback. -/
native_decider elf.symbols.byAddr := Silmaril.Elf.Staged.Native.byAddr

/-! ## The tactic -/

public meta section

namespace Silmaril.Elf.Staged.Trust

open Lean Elab Tactic Meta

/-- `elf_leaf proc (native := hN) (kernel := hK)`: prove a leaf's proposition by the native
checker when the policy allows `proc` here, else by the kernel checker (module doc). -/
syntax (name := elfLeaf) "elf_leaf " ident " (" &"native" " := " term ")"
  " (" &"kernel" " := " term ")" : tactic

/-- `elf_leaf proc (kernel := hK)`: a kernel-only leaf, checked by the kernel in every profile. -/
syntax (name := elfLeafKernel) "elf_leaf " ident " (" &"kernel" " := " term ")" : tactic

/-- The leaf proof: `hN?` is the native soundness lemma, if the leaf has a native checker. -/
def runElfLeaf (procId : Syntax) (hN? : Option Syntax) (hK : Syntax) : TacticM Unit :=
    withMainContext do
  let proc := procId.getId
  let env ← getEnv
  let some p := (Silmaril.Trust.procExt.getState env).find? proc
    | throwError "elf_leaf: {proc} is not a registered ELF procedure (unsupported leaf)"
  let mod := env.mainModule
  let allow ← match Silmaril.Trust.allowed env mod (← Silmaril.Trust.profile)
      (← Silmaril.Trust.ceiling) with
    | .ok a => pure a
    | .error msg => throwError "elf_leaf: {msg}"
  match hN? with
  | some hN =>
    if allow.contains p.name then
      -- Native: `edge_decide` runs the registered `ByteArray` checker and records the use.
      evalTactic (← `(tactic| refine $(⟨hN⟩) ?_))
      evalTactic (← `(tactic| edge_decide $(⟨procId⟩):ident))
      return
  | none => pure ()
  -- Kernel: the `KBytes` checker, by `Eq.refl` in an auxiliary lemma; never native.
  evalTactic (← `(tactic| refine $(⟨hK⟩) ?_))
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, e, rhs) := (← whnfR ty).eq?
    | throwError "elf_leaf: the kernel goal must be `f a₁ … aₙ = true`{indentExpr ty}"
  unless (← whnfR rhs).isConstOf ``Bool.true do
    throwError "elf_leaf: the kernel goal must be `… = true`{indentExpr ty}"
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then
    throwError "elf_leaf: the kernel goal must be closed{indentExpr e}"
  let eq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
  let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let aux ← try
      withOptions (Elab.async.set · false) do mkAuxLemma [] eq pf
    catch ex =>
      throwError "elf_leaf: the kernel did not check {proc}: {ex.toMessageData}"
  let decl := (← Term.getDeclName?).getD .anonymous
  Silmaril.Trust.recordUse { decl, module := mod, proc := p.name, mode := .kernel,
                             profile := ← Silmaril.Trust.profileTag }
  goal.assign (← mkExpectedTypeHint (mkConst aux) ty)
  replaceMainGoal []

@[tactic elfLeaf] def evalElfLeaf : Tactic := fun stx =>
  runElfLeaf stx[1] (some stx[5]) stx[10]

@[tactic elfLeafKernel] def evalElfLeafKernel : Tactic := fun stx =>
  runElfLeaf stx[1] none stx[5]

end Silmaril.Elf.Staged.Trust
