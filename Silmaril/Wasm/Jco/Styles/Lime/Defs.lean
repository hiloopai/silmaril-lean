module

public import Silmaril.Wasm.Jco.Styles.EncWrap.Defs
public import Silmaril.Wasm.LimeCompile.Direct.Defs

/-!
# Feature sets: the Lime fragment of the wrappers

Lime1 is the Wasm 1.0-based feature set of silmaril (`Silmaril.Wasm.Lime1`): one 32-bit memory,
multi-value, bulk memory (`memory.copy`, `memory.fill`), sign extension, no reference types, no
SIMD, no exceptions, no GC. Core 3.0 has all of these.

**The Lime fragment of wrapper-style components.** Such a component (a wrapped module `m` and its
adaptor) is in the Lime fragment when each of its core modules is the Core image of a Lime1
module (`LimeFrag`). The canonical options of the lifts must also fit Lime: one 32-bit memory,
synchronous lifts, no resources. These hold for every lift of this directory, because the model
has no other options.

* `XInstr.toLime fi`: the adaptor instruction set encoded as Lime1 instructions. `fi` gives the
  function index of a called export of `m`, which is imported in that order. Every instruction
  has an image: `local.get/set`, `i32.const`, `call`, `i32.eqz`, `i32.lt_u`, untyped `select`,
  `memory.copy`, `if`, and the integer and float loads and stores. A load or store of an
  impossible width (other than 1, 2, 4 or 8 bytes) becomes `unreachable`.
* `adaptorLime md`: the adaptor of `wrapE md enc` as a **Lime1 module**. It has one type per
  function, the memory and the called exports of `m` as imports, the shims as functions, and
  their exports. Only the function bodies vary with the encoding, so the module serves every
  `enc`.
* `wrapCore m md`: the core modules of the wrapper, `[m, (adaptorLime md).toCore]`.

Proved in `Thms`: the wrapper of a Lime module is in the Lime fragment, and the 3.0 → Lime
compiler (`Silmaril.Wasm.LimeCompile.Direct.compile`, #861) maps the wrapper's core modules to
themselves, so the pipeline is Lime-preserving. **Not proved**: the agreement of `XInstr.step`
with Lime1 execution of `XInstr.toLime` (there is no bridge between `CoreInst` and silmaril's
semantics), and the validity of `adaptorLime md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm (NumType IntType FloatType Signedness)
open Silmaril.Wasm.V1 (PackSize)

/-- An index from a natural number (modulo `2^32`). -/
def mkIdx {k : Silmaril.Wasm.IndexKind} (n : Nat) : Silmaril.Wasm.Idx k :=
  ⟨⟨n % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- A memory argument with natural alignment exponent `a` and offset `off`. -/
def memArg (a off : Nat) : Silmaril.Wasm.V1.MemArg :=
  ⟨⟨a % 2 ^ 32, Nat.mod_lt _ (by decide)⟩, ⟨off % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- The alignment exponent of an access of `n` bytes. -/
def alignExp : Nat → Nat
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | _ => 3

/-- The packed size of a narrow access. -/
def packOf : Nat → Option Silmaril.Wasm.V1.PackSize
  | 1 => some .i8
  | 2 => some .i16
  | 4 => some .i32
  | _ => none

/-- `AInstr` in Lime1. -/
def AInstr.toLime (fi : String → Nat) : AInstr → Silmaril.Wasm.Lime1.Instr
  | .localGet i => .localGet (mkIdx i)
  | .localSet i => .localSet (mkIdx i)
  | .i32Const c => .intConst .i32 c
  | .call f _ => .call (mkIdx (fi f))

/-- An integer load of `n` bytes. -/
def intLoadL (it : IntType) (n : Nat) (sx : Bool) (off : Nat) : Silmaril.Wasm.Lime1.Instr :=
  if n * 8 = it.width then .intLoad it none (memArg (alignExp n) off)
  else match packOf n with
    | some p => .intLoad it (some (p, if sx then .signed else .unsigned)) (memArg (alignExp n) off)
    | none => .unreachable

/-- An integer store of `n` bytes. -/
def intStoreL (it : IntType) (n : Nat) (off : Nat) : Silmaril.Wasm.Lime1.Instr :=
  if n * 8 = it.width then .intStore it none (memArg (alignExp n) off)
  else match packOf n with
    | some p => .intStore it (some p) (memArg (alignExp n) off)
    | none => .unreachable

mutual
/-- **An adaptor instruction in Lime1.** -/
def XInstr.toLime (fi : String → Nat) : XInstr → Silmaril.Wasm.Lime1.Instr
  | .base i => i.toLime fi
  | .i32Eqz => .intTestOp .i32 .eqz
  | .i32LtU => .intRelOp .i32 (.lt .unsigned)
  | .select => .select
  | .memCopy => .memoryCopy
  | .ifElse res thn els =>
    .if_ (match res with | some t => .value t | none => .empty) (XInstr.toLimeL fi thn)
      (XInstr.toLimeL fi els)
  | .load (.int it) n sx off => intLoadL it n sx off
  | .load (.float ft) _ _ off => .floatLoad ft (memArg (alignExp (ft.width / 8)) off)
  | .store (.int it) n off => intStoreL it n off
  | .store (.float ft) _ off => .floatStore ft (memArg (alignExp (ft.width / 8)) off)

/-- An instruction sequence in Lime1. -/
def XInstr.toLimeL (fi : String → Nat) : List XInstr → List Silmaril.Wasm.Lime1.Instr
  | [] => []
  | i :: is => XInstr.toLime fi i :: XInstr.toLimeL fi is
end

/-! ## The adaptor as a Lime1 module -/

/-- The core type of an export shim (or of the C-convention export it calls). -/
def shimType (s : Sig) : Silmaril.Wasm.V1.FuncType :=
  if inMem s.result then ⟨flatParams s.params, [.int .i32]⟩
  else ⟨flatParams s.params, match s.result with | some t => t.flat | none => []⟩

/-- The core type of the C-convention export `s` of the wrapped module. -/
def calleeType (s : Sig) : Silmaril.Wasm.V1.FuncType :=
  if inMem s.result then ⟨flatParams s.params ++ [.int .i32], []⟩ else shimType s

/-- `(i32, i32) -> i32`, the allocator. -/
def allocType : Silmaril.Wasm.V1.FuncType := ⟨[.int .i32, .int .i32], [.int .i32]⟩

/-- `(i32, i32, i32, i32) -> i32`, `cabi_realloc`. -/
def reallocType : Silmaril.Wasm.V1.FuncType :=
  ⟨[.int .i32, .int .i32, .int .i32, .int .i32], [.int .i32]⟩

/-- The names of the imported functions, in index order: the allocator, then the world's
functions. -/
def importNames (md : Meta) : List String := md.alloc :: md.world.map (·.name)

/-- The function index of an imported name. -/
def funcIdxOf (md : Meta) (f : String) : Nat := (importNames md).idxOf f

/-- An adaptor function as a Lime1 function of type index `ty`. -/
def XFn.toLime (fi : String → Nat) (ty : Nat) (fn : XFn) : Silmaril.Wasm.Lime1.Func :=
  ⟨mkIdx ty, List.replicate fn.locals (.int .i32), XInstr.toLimeL fi fn.body⟩

/-- **The adaptor of `wrapE md enc` (and of `wrap md`) as a Lime1 module.** Types: the allocator,
the world's callees, `cabi_realloc`, the shims. -/
def adaptorLime (md : Meta) : Silmaril.Wasm.Lime1.Module :=
  let n := md.world.length
  let fi := funcIdxOf md
  { types := allocType :: md.world.map calleeType ++ reallocType :: md.world.map shimType
    imports := ⟨"m", "memory", .memory ⟨⟨0, none⟩⟩⟩ ::
      ⟨"m", md.alloc, .func (mkIdx 0)⟩ ::
        (md.world.zipIdx.map fun (s, i) => ⟨"m", s.name, .func (mkIdx (i + 1))⟩)
    funcs := (reallocShimX md.alloc).toLime fi (n + 1) ::
      (md.world.zipIdx.map fun (s, i) => (exportShim md s).toX.toLime fi (n + 2 + i))
    exports := ⟨"cabi_realloc", .func (mkIdx (n + 1))⟩ ::
      (md.world.zipIdx.map fun (s, i) => ⟨s.name, .func (mkIdx (n + 2 + i))⟩) }

/-- Core modules that are Core images of Lime1 modules. -/
def LimeFrag (ms : List Silmaril.Wasm.Module) : Prop :=
  ∀ m ∈ ms, ∃ l : Silmaril.Wasm.Lime1.Module, l.toCore = m

/-- The core modules of the wrapper of `m`. -/
def wrapCore (m : Silmaril.Wasm.Module) (md : Meta) : List Silmaril.Wasm.Module :=
  [m, (adaptorLime md).toCore]

/-- **The Lime-preserving pipeline**: compile each core module of the wrapper to Lime1 with the
3.0 → Lime compiler. -/
def limePipeline (m : Silmaril.Wasm.Module) (md : Meta) :
    Option (List Silmaril.Wasm.Lime1.Module) :=
  (wrapCore m md).mapM Silmaril.Wasm.LimeCompile.Direct.compile

end Silmaril.Wasm.Jco
