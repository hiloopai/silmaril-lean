module

public import Silmaril.Wasm.LimeCompile.PassiveData.Defs
public import Silmaril.Wasm.LimeCompile.SimLift.Defs

/-!
# The passive-data container at module level: the store relation

The container of `Silmaril.Wasm.LimeCompile.PassiveData` changes three things that silmaril-lean's
code-simulation closure keeps fixed:

* the **data instances**: a passive segment holds its bytes in the source and is an empty
  (dropped active) segment in the target;
* the **function instances**: the target has one helper instance per data segment after all
  instances of the source, and the functions of the source module live in an instance with the
  helper addresses and the helper type appended;
* the **code**: `memory.init 0 y` in the source module's functions is a call of helper `y`, which
  runs in a call frame.

This file defines the relation of source and target stores after instantiation.

* `Ctx`: what instantiation fixes: the source module `m`, its instance `mi`, the helper type
  `hd`, the address `N₀` of the source module's first function, and the number `N` of function
  instances before the helpers.
* `Ctx.mi'`: the target instance, `mi` with the helper addresses `N, …, N + |data| - 1` and the
  helper type appended.
* `Ctx.extFI`: the target function instance of a function of the source module: the target
  instance and the rewritten body. Functions at addresses below `N₀` are unchanged. (Choosing by
  address rather than by instance matters: an earlier instance can equal `mi` when the module
  allocates no function and no data.)
* `Ctx.helperInsts`: the helper instances.
* **`SRel K s t`**: the store relation. Every component but functions and data is equal; the
  target functions are those below `N₀`, the `extFI` images of the source module's functions,
  and the helpers; the data instance of segment
  `y` holds `effBytes` (the passive bytes, or nothing for an active segment) in the source and
  nothing in the target; every other data instance is equal; exported functions take numeric
  parameters.
* `SInv K s`: invariants of the source store (valid, the source instance's functions run the
  source module's bodies, no other instance names its data, memory 0 is a valid 32-bit memory),
  and `SRelI K s t := SRel K s t ∧ SInv K s`, the relation of sessions.
* `Ctx.Ok`: facts about the context that instantiation of a valid module gives.
* `InstRel P host K c d`: related instantiation configurations (runs transport both ways).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.PassiveEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.PassiveData

variable {H : Type}

/-- What instantiation fixes. -/
structure Ctx where
  /-- The source module. -/
  m : Module
  /-- The instance of the source module. -/
  mi : ModuleInst
  /-- The helper type, `[i32 i32 i32] → []`, as allocated in the target. -/
  hd : DefType
  /-- The address of the first function of the source module. -/
  N₀ : Nat
  /-- The number of function instances before the helpers. -/
  N : Nat

namespace Ctx

/-- The addresses of the helpers. -/
def helperAddrs (K : Ctx) : List Nat := (List.range K.m.data.length).map (K.N + ·)

/-- The target instance: the helper addresses and the helper type appended. -/
def mi' (K : Ctx) : ModuleInst :=
  { K.mi with types := K.mi.types ++ [K.hd], funcs := K.mi.funcs ++ K.helperAddrs }

/-- The target code of a source function: the source module's bodies are rewritten. -/
def extCode (K : Ctx) : FuncCode H → FuncCode H
  | .wasm f => .wasm (rwFunc (helperBase K.m) f)
  | .host h => .host h

/-- The target function instance of a function of the source module: the target instance and
the rewritten body. -/
def extFI (K : Ctx) (fi : FuncInst H) : FuncInst H := ⟨fi.type, K.mi', K.extCode fi.code⟩

/-- The helper instance of data segment `y`. -/
def helperInst (K : Ctx) (y : Nat) (d : Data) : FuncInst H :=
  ⟨K.hd, K.mi', .wasm (helperFunc K.m y d)⟩

/-- The helper instances, in segment order. -/
def helperInsts (K : Ctx) : List (FuncInst H) :=
  ((List.range K.m.data.length).zip K.m.data).map fun p => K.helperInst p.1 p.2

/-- Facts about the context that instantiation of a valid module gives: the source module is
valid and compiles, the helper type is `[i32 i32 i32] → []`, the source instance has
`helperBase m` function addresses and one data address per segment, every helper index fits in
32 bits, and every segment fits in 32 bits. -/
structure Ok (K : Ctx) : Prop where
  valid : ∃ mt, ModuleOk K.m mt
  nfuncs : K.N = K.N₀ + K.m.funcs.length
  compiles : ∃ L, compile K.m = some L
  hd : ∃ ps rs : Ty (.list .val), Expand K.hd (.func ps rs) ∧ ps.length = 3 ∧ rs.length = 0
  funcs : K.mi.funcs.length = helperBase K.m
  datas : K.mi.datas.length = K.m.data.length
  bound : helperBase K.m + K.m.data.length ≤ 2 ^ 32
  segs : ∀ d ∈ K.m.data, (effBytes d).length ≤ 2 ^ 32

end Ctx

/-- The function at address `a`, if any, takes numeric parameters (as every Lime1 function
does). -/
def NumParamsAt (fs : List (FuncInst H)) (a : Nat) : Prop :=
  ∀ fi, fs[a]? = some fi → ∀ ps rs, Expand fi.type (.func ps rs) →
    ∀ p ∈ ps.toList, ∃ t, p = .num t

/-- **The store relation** after instantiation. -/
structure SRel (K : Ctx) (s t : Store H) : Prop where
  /-- Every component but the functions and the data is equal. -/
  other : ({ s with funcs := [], datas := [] } : Store H) = { t with funcs := [], datas := [] }
  /-- The source functions come first. -/
  nfuncs : s.funcs.length = K.N
  /-- The target functions: the functions before the source module's unchanged, the source
  module's functions with the target instance and rewritten bodies, then the helpers. -/
  funcs : t.funcs = s.funcs.take K.N₀ ++ (s.funcs.drop K.N₀).map K.extFI ++ K.helperInsts
  /-- The same number of data instances. -/
  ndatas : t.datas.length = s.datas.length
  /-- Segment `y`: the effective bytes in the source, nothing in the target. -/
  seg : ∀ (y : Nat) (d : Data), K.m.data[y]? = some d → ∃ a, K.mi.datas[y]? = some a ∧
    (s.datas[a]?).map (·.bytes.data.toList) = some (effBytes d) ∧
    (t.datas[a]?).map (·.bytes.data.toList) = some []
  /-- Every other data instance is equal. -/
  datas : ∀ a, a ∉ K.mi.datas → t.datas[a]? = s.datas[a]?
  /-- The exported functions are source functions with numeric parameters. -/
  exportsNum : ∀ x a, Silmaril.Wasm.Binaryen.exportFunc? K.mi x = some a →
    a < K.N ∧ NumParamsAt s.funcs a

/-- The invariants of a source store that the simulation needs: the store is valid, the
functions of the source instance run bodies of the source module, no other instance names the
data of the source instance, and memory 0 of the source instance is a valid 32-bit memory. -/
structure SInv (K : Ctx) (s : Store H) : Prop where
  /-- The source store is valid. -/
  ok : StoreOk s
  /-- The functions of the source module are in the source instance and run its bodies. -/
  ours : ∀ a fi, K.N₀ ≤ a → s.funcs[a]? = some fi → fi.module = K.mi ∧ ∃ f ∈ K.m.funcs,
    fi.code = .wasm f
  /-- No function before them names the data of the source instance. -/
  foreign : ∀ a fi, a < K.N₀ → s.funcs[a]? = some fi → ∀ d ∈ fi.module.datas, d ∉ K.mi.datas
  /-- Memory 0 of the source instance has whole pages and at most `2 ^ 32` bytes. -/
  mem0 : ∀ ma (mem : MemInst), K.mi.mems[0]? = some ma → s.mems[ma]? = some mem →
    mem.type.address = .i32 ∧ mem.bytes.size % 65536 = 0 ∧ mem.bytes.size ≤ 2 ^ 32

/-- The store relation of sessions: related stores whose source satisfies the invariants. -/
def SRelI (K : Ctx) (s t : Store H) : Prop := SRel K s t ∧ SInv K s

/-- Related frames of the source module: the target frame has the target instance. -/
def FRel (K : Ctx) (f g : Frame) : Prop := f.module = K.mi ∧ g = ⟨f.locals, K.mi'⟩

/-- Related instantiation configurations: the context is valid, the frames hold the source and
target instances, and the instantiation runs transport in both directions, finished runs with
`SRelI`-related final stores. -/
def InstRel (P : Numerics.Profile) (host : HostSemantics H) (K : Ctx) (c d : Config H) : Prop :=
  K.Ok ∧ c.frame.module = K.mi ∧ d.frame.module = K.mi' ∧
    SimLift.RunTransport P host (SRelI K) c d ∧ (Diverges P host c → Diverges P host d) ∧
    SimLift.RunTransport P host (fun t s => SRelI K s t) d c ∧ (Diverges P host d → Diverges P host c)

end Silmaril.Wasm.LimeCompile.PassiveEquiv
