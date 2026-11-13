module

public import Silmaril.Wasm.Atlas.Variant.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

/-!
# A nonconformant model: wasmi 2.0.0 and its select fusion

wasmi 2.0.0 ([release](https://github.com/wasmi-labs/wasmi/releases/tag/v2.0.0)) translates
Wasm into its own register IR and then executes the IR. Issue
[#2046](https://github.com/wasmi-labs/wasmi/issues/2046) (open at 2.0.0, fixed later in
`fa7c6f7`): `try_fuse_select` drops a zero comparison `x != 0` feeding a `select` but keeps
the comparison's result slot as the condition, so the fused `select` reads a stale register.
The reproducer from the issue,

```wat
(module (func (export "f") (param $a i32) (param $b i32) (result i32)
  (select (i32.const 7) (local.get $a) (i32.ne (i32.const 0) (local.get $b)))))
```

must return `7` on `f 5 1`; wasmi 2.0.0 returns `5` (in all three compilation modes), as does
a local run against the `wasmi = "=2.0.0"` crate (`docs/projects/spectec/README.md` §4).

The model follows wasmi's structure, a translator followed by an executor
(`docs/projects/spectec/README.md` §4.2):

* `fuse`: the translation. It rewrites the reported pattern
  `i32.const 0; local.get x; i32.ne; select` (`zeroTestSel x t`) to
  `local.get x; drop; i32.const 0; select` (`fusedSel x t`), recursively inside blocks,
  loops, `if` arms and `try_table` bodies. The rewrite has the observed effect (the condition
  read is always `0`, so the second operand is selected) and keeps the stack shape;
* `fuseStore`: the translation of every Wasm function body of a store;
* `obs P x c`: **the wasmi observations**, the Core 3.0 observations of the translated store;
* `patFree`: code without the pattern, on which `fuse` is the identity.

**The loose model** (`Loose`): Core `Step P host` plus one quirk, `selectEither`: at a redex
`i32.const 0; local.get x; i32.ne; select`, the loose machine may read the local `x`, drop
it, and select by a chosen constant `0` or `1` instead of by the comparison, so either
operand may be produced. It is closed under the evaluation contexts
(`Silmaril.Wasm.Atlas.Variant.loose`).

**Feature set.** `Supported` is the instruction set wasmi 2.0.0 implements, restricted to
Core 3.0 syntax: it has no typed function references, GC or exception handling (README at
`v2.0.0`: "planned"). The extensions wasmi has beyond 3.0 (wide arithmetic, custom page
sizes) are not Core 3.0 syntax. This is a local stand-in for the `wasmi200` feature set of
`docs/projects/spectec/README.md` §1.1, to be reconciled with that track.

**The reproducer** (`reproMod`, `reproPrep`, `reproStore`): the module above, validated and
allocated by silmaril-lean's executable `prepare?` into the empty store, as in
`Silmaril.Wasm.Interp.Example`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas

variable {H : Type}

/-! ## The translation -/

/-- The reported source pattern `i32.const 0; local.get x; i32.ne; select t`. -/
def zeroTestSel (x : LocalIdx) (t : Option (List ValType)) : List Instr :=
  [.intConst .i32 0, .localGet x, .intRelOp .i32 .ne, .select t]

/-- wasmi's translation of the pattern: the comparison is dropped and the condition read is
`0`, modelled as `local.get x; drop; i32.const 0; select t`. -/
def fusedSel (x : LocalIdx) (t : Option (List ValType)) : List Instr :=
  [.localGet x, .drop, .intConst .i32 0, .select t]

mutual
/-- The translation of one instruction: recursion into structured bodies. -/
def fuseI : Instr → Instr
  | .block bt b => .block bt (fuse b)
  | .loop bt b => .loop bt (fuse b)
  | .if_ bt b₁ b₂ => .if_ bt (fuse b₁) (fuse b₂)
  | .tryTable bt cs b => .tryTable bt cs (fuse b)
  | i => i

/-- **wasmi's select fusion** on an instruction sequence. -/
def fuse : List Instr → List Instr
  | [] => []
  | .intConst .i32 c :: .localGet x :: .intRelOp .i32 .ne :: .select t :: rest =>
    if c = 0 then fusedSel x t ++ fuse rest
    else .intConst .i32 c :: fuse (.localGet x :: .intRelOp .i32 .ne :: .select t :: rest)
  | i :: rest => fuseI i :: fuse rest
end

/-- The translation of a function instance (Wasm code only). -/
def fuseFunc (fi : FuncInst H) : FuncInst H :=
  match fi.code with
  | .wasm g => { fi with code := .wasm { g with body := fuse g.body } }
  | .host _ => fi

/-- The translation of a store: every Wasm function body. -/
def fuseStore (s : Store H) : Store H := { s with funcs := s.funcs.map fuseFunc }

mutual
/-- The pattern does not occur in an instruction. -/
def patFreeI : Instr → Bool
  | .block _ b => patFree b
  | .loop _ b => patFree b
  | .if_ _ b₁ b₂ => patFree b₁ && patFree b₂
  | .tryTable _ _ b => patFree b
  | _ => true

/-- The pattern does not occur in a sequence (nor inside its structured bodies). -/
def patFree : List Instr → Bool
  | [] => true
  | .intConst .i32 c :: .localGet x :: .intRelOp .i32 .ne :: .select t :: rest =>
    c != 0 && patFree (.localGet x :: .intRelOp .i32 .ne :: .select t :: rest)
  | i :: rest => patFreeI i && patFree rest
end

/-- No function body of the store contains the pattern (`NoFusedSelect`). -/
def StorePatFree (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ g, fi.code = .wasm g → patFree g.body = true

/-! ## The wasmi observations -/

/-- **wasmi 2.0.0's observations**: the Core 3.0 observations of the translated store. -/
def obs (P : Numerics.Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Core.obs P (fuseStore x.1, x.2) c

/-! ## The feature set (local stand-in for `wasmi200`) -/

mutual
/-- wasmi 2.0.0 implements the instruction: no typed function references, GC or exception
handling (`call_ref`, `return_call_ref`, `br_on_null`, `br_on_non_null`, `br_on_cast*`,
`ref.as_non_null`, `ref.eq`, `ref.test`, `ref.cast`, `ref.i31`, `i31.get`, `struct.*`,
`array.*`, `extern.convert_any`, `any.convert_extern`, `throw`, `throw_ref`, `try_table`). -/
def SupportedI : Instr → Bool
  | .block _ b => Supported b
  | .loop _ b => Supported b
  | .if_ _ b₁ b₂ => Supported b₁ && Supported b₂
  | .callRef _ | .returnCallRef _ | .brOnNull _ | .brOnNonNull _ | .brOnCast .. | .brOnCastFail ..
  | .refAsNonNull | .refEq | .refTest _ | .refCast _ | .refI31 | .i31Get _
  | .structNew _ | .structNewDefault _ | .structGet .. | .structSet ..
  | .arrayNew _ | .arrayNewDefault _ | .arrayNewFixed .. | .arrayNewData .. | .arrayNewElem ..
  | .arrayGet .. | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData ..
  | .arrayInitElem .. | .externConvertAny | .anyConvertExtern
  | .throw _ | .throwRef | .tryTable .. => false
  | _ => true

/-- wasmi 2.0.0 implements every instruction of the sequence. -/
def Supported : List Instr → Bool
  | [] => true
  | i :: rest => SupportedI i && Supported rest
end

/-- Every Wasm function body of the store is in wasmi 2.0.0's feature set (a Boolean check). -/
def StoreSupported (s : Store H) : Prop :=
  (s.funcs.all fun fi => match fi.code with
    | .wasm g => Supported g.body
    | .host _ => true) = true

/-! ## The loose model -/

namespace Loose

/-- **The quirk `selectEither`**: at the redex `i32.const 0; local.get x; i32.ne; select t`,
read the local `x`, then drop it and select by the constant `if b then 1 else 0` instead of by
the comparison (so either operand may be produced). -/
inductive Quirk : Config H → Config H → Prop where
  | selectEither {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} {t : Option (List ValType)}
      (b : Bool) (h : f.local? x = some (some v)) :
      Quirk ⟨s, f, expression (zeroTestSel x t)⟩
        ⟨s, f, [v.toAdmin, .plain .drop, .plain (.intConst .i32 (if b then 1 else 0)),
          .plain (.select t)]⟩

/-- **The loose step relation**: Core 3.0 plus `selectEither` in every evaluation context. -/
abbrev Step (P : Numerics.Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  Variant.loose (Execution.Core.Step P host) Quirk

/-- The loose observations of a call. -/
def obs (P : Numerics.Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Variant.obsR (Step P) x c

end Loose

/-! ## The reproducer -/

/-- `i32`. -/
abbrev i32 : ValType := .num (.int .i32)

/-- The body of `f`: `(select (i32.const 7) (local.get 0) (i32.ne (i32.const 0) (local.get 1)))`
in linear form. -/
def reproBody : List Instr :=
  [.intConst .i32 7, .localGet ⟨0⟩] ++ zeroTestSel ⟨1⟩ none

/-- The reproducer module of issue #2046. -/
def reproMod : Module where
  types := [⟨[⟨true, [], .func ⟨[i32, i32], [i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], reproBody⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The reproducer module after wasmi's translation. -/
def reproModW : Module := { reproMod with funcs := [⟨⟨0⟩, [], fuse reproBody⟩] }

/-- The spec's allocation of `reproMod` into the empty store. -/
def reproPrep : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) reproMod []).getD (⟨{}, {}, []⟩, none)

/-- The allocation of the translated module. -/
def reproPrepW : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) reproModW []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of the reproducer. -/
def reproStore : Store Empty := reproPrep.1.store

/-- The store of the instance of the translated reproducer. -/
def reproStoreW : Store Empty := reproPrepW.1.store

/-- The reproducer point: its store, with no host functions. -/
def reproPt : Core.Pt Empty := (reproStore, fun _ _ _ _ => False)

/-- The reproducer call `f 5 1`. -/
def reproCall : Core.Call := (0, [Val.i32 5, Val.i32 1])

end Silmaril.Wasm.Wasmi
