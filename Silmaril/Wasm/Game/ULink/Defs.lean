module

public import Silmaril.Wasm.Game.Untyped.Defs
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Game.Linking.Defs

/-!
# Static linking in the untyped shared-store game

The untyped game of `Silmaril.Wasm.Game.Untyped` carries the whole store in its moves. Linking
two modules there is linking **in one store**: the linked module is the consumer
instantiated against the provider's exports in the provider's store (the Wasm
specification's linking at instantiation time), so everything the consumer imports from the
provider — functions, but also memories, tables and globals — is the provider's object at
the same address. Sharing state needs nothing of the game: both sides read and write the one
store that the moves carry.

## The data of a link (`ULink`)

* the linked exports `X`, at function addresses `addr` (the consumer's exports in the linked
  store);
* a **stub table** `stub a = some (k, c)`: the provider function at address `a`, with Wasm code
  `c`, which the consumer reaches by calling `a`. `target k = some a` reads it back from the
  host code `k`.

This is a semantic linker: it acts on instances over one store rather than on module syntax.
Function imports the consumer does not take from the provider stay host functions of the store
(**partial linking**: the linked module keeps imports, `target h = none`), and imported
memories, tables and globals are shared by construction. silmaril-lean's `link?` cannot
express either (its fragment `Recipe.Assembly` has a closed provider, function imports only,
and no memories, tables or globals). A syntactic linker for that fragment would
have to merge module sections; its correctness would be a statement relating its output to
the store built here, which is what the existing `Linking.Setup` does for `link?` (step A of
`Silmaril.Wasm.Game.Linking`).

## The three systems

* The **linked** module `L.U = ⟨X, addr⟩` (an untyped instance) runs in the *real* store, where
  the provider functions have their Wasm code.
* The **consumer** is the same untyped instance run in the *stubbed* store `L.stubS s`: the
  code of each provider function `a` replaced by the host code `k` of its stub (type and module
  instance unchanged, `stubFI`). A call of `a` is then a callout `⟨k, σ, args⟩`.
* The **provider** `L.rlts P` (the *resolver*) answers a stub call `⟨k, σ, args⟩` by running
  the provider function `target k` in the real store `L.unstubS σ` (the stubs given back their
  code), and replies in the stubbed store of its final store. Its own callouts (host functions
  of the real store) go down unchanged. A call of a host code that is not a stub is
  **forwarded**: asked down in the real store, and the reply returned in the stubbed store.
  This is the provider as the consumer's environment in the same store, with the store
  relation applied to the moves.

The composite is `(L.rlts P).comp (L.U.lts P)`, whose strategy is
`(L.rstrategy P).comp (L.U.strategy P)` (`Silmaril.Games` composition). Its upper moves carry
stubbed stores and its lower moves real stores; `L.stubUp` translates the upper moves of a play
of the linked module.

## Layout

`L.Layout s`: the provider functions of `s` have their code and no host function of `s` has a
stub code. Host-free steps preserve it (functions never change), and every host reply that
respects Core's `Extend` keeps the first half; the play-level statements are made for plays
whose stores satisfy it (`L.LayoutPlay`). For closed programs it is an invariant: from a store
with the layout containing the stubbed functions (`L.StubsIn`), against an environment that
allocates no stub codes (`L.EnvNoStub`) and satisfies the untyped host contract; the closed
composite is `L.compClosedD`.

## The link of a `link?` setup

`Linking.Setup.toULink`: the shared world of a `Silmaril.Wasm.Game.Linking.Setup` (provider and
consumer instantiated into one store) with the setup's stub set (host code `k` for the `k`-th
stub, as `Linking.stubOut`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- **A static link over one store**: linked exports and a stub table. -/
structure ULink where
  /-- The linked export names. -/
  X : Type
  /-- The function address of each linked export. -/
  addr : X → Nat
  /-- The stub of a provider function address: its host code and its Wasm code. -/
  stub : Nat → Option (Nat × Func)
  /-- The provider function address of a stub host code. -/
  target : Nat → Option Nat
  /-- `target` reads `stub` back. -/
  target_iff : ∀ k a, target k = some a ↔ ∃ c, stub a = some (k, c)

namespace ULink

variable (L : ULink)

/-- The linked module as an untyped instance. -/
def U : UInstance := ⟨L.X, L.addr⟩

/-- Stub out the function at address `a`. -/
def stubFI (a : Nat) (fi : FuncInst Nat) : FuncInst Nat :=
  match L.stub a with
  | some (k, _) => { fi with code := .host k }
  | none => fi

/-- Give the function at address `a` its provider code back. -/
def unstubFI (a : Nat) (fi : FuncInst Nat) : FuncInst Nat :=
  match L.stub a with
  | some (_, c) => { fi with code := .wasm c }
  | none => fi

/-- The stubbed store (the consumer's view). -/
def stubS (s : Store Nat) : Store Nat := { s with funcs := s.funcs.mapIdx L.stubFI }

/-- The real store of a stubbed store. -/
def unstubS (s : Store Nat) : Store Nat := { s with funcs := s.funcs.mapIdx L.unstubFI }

/-- The layout of a real store: provider functions have their code, and no host function has
a stub code. -/
structure Layout (s : Store Nat) : Prop where
  prov : ∀ (a : Nat) (fi : FuncInst Nat) (k : Nat) (c : Func), s.funcs[a]? = some fi →
    L.stub a = some (k, c) → fi.code = .wasm c
  noStub : ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi →
    fi.code = .host h → L.target h = none

/-- The question forwarded down for a call of a host code that is not a stub. -/
def fwdQ (e : UCall Nat) : UCall Nat := ⟨e.target, L.unstubS e.store, e.args⟩

/-- The configuration of a call of the Wasm function `fi` on `args`: its frame. -/
def callCode (fi : FuncInst Nat) (rs : Ty (.list .val)) (code : Func) (args : List Val) :
    List Admin :=
  [.frame rs.length (Frame.forCall fi.module args code.locals)
    [.label rs.length [] (expression code.body)]]

/-! ### The resolver (the provider as an environment) -/

/-- Hidden states of the resolver. -/
inductive RState where
  /-- No call is active. -/
  | idle
  /-- Serving the stub call `e`: the provider thread `t` runs in the real store `s`. -/
  | running (e : UCall Nat) (s : Store Nat) (t : Thread)
  /-- Serving `e`, the provider waits for the answer to its callout `e'`. -/
  | waiting (e : UCall Nat) (s : Store Nat) (t : Thread) (e' : UCall Nat)
  /-- A stub call that the provider cannot start (it never answers). -/
  | stuck (e : UCall Nat)
  /-- About to forward the call `e`. -/
  | fwd (e : UCall Nat)
  /-- Waiting for the reply to the forwarded call. -/
  | fwdWait (e : UCall Nat)
  /-- About to return the reply `a` to the forwarded call `e`. -/
  | fwdRet (e : UCall Nat) (a : UReply)

/-- The game position of a resolver state. -/
def RState.pos (L : ULink) : RState → Pos UImp UImp
  | .idle => .idle
  | .running e _ _ => .run e
  | .waiting e _ _ e' => .wait e e'
  | .stuck e => .run e
  | .fwd e => .run e
  | .fwdWait e => .wait e (L.fwdQ e)
  | .fwdRet e _ => .run e

/-- Transitions of the resolver, host-free steps silent. -/
inductive RTrans (P : Profile) : RState → Option (Move UImp UImp) → RState → Prop where
  /-- A stub call starts the provider function in the real store (Opponent). -/
  | call (e : UCall Nat) {a : Nat} {fi : FuncInst Nat} {ps rs : Ty (.list .val)} {code : Func}
      (ht : L.target e.target = some a) (hf : (L.unstubS e.store).funcs[a]? = some fi)
      (he : Expand fi.type (.func ps rs)) (hn : e.args.length = ps.length)
      (hc : fi.code = .wasm code) :
      RTrans P .idle (some (.inr (.ask e)))
        (.running e (L.unstubS e.store) (.active {} (callCode fi rs code e.args)))
  /-- A stub call may also never be answered (Opponent). -/
  | callStuck (e : UCall Nat) (ht : (L.target e.target).isSome) :
      RTrans P .idle (some (.inr (.ask e))) (.stuck e)
  /-- A call of a host code that is not a stub is to be forwarded (Opponent). -/
  | fwdCall (e : UCall Nat) (ht : L.target e.target = none) :
      RTrans P .idle (some (.inr (.ask e))) (.fwd e)
  /-- Forward it down in the real store (Proponent). -/
  | fwdAsk (e : UCall Nat) : RTrans P (.fwd e) (some (.inl (.ask (L.fwdQ e)))) (.fwdWait e)
  /-- The reply to the forwarded call (Opponent). -/
  | fwdAns (e : UCall Nat) (a : UReply) :
      RTrans P (.fwdWait e) (some (.inl (.ans (L.fwdQ e) a))) (.fwdRet e a)
  /-- Return it in the stubbed store (Proponent). -/
  | fwdRet (e : UCall Nat) (a : UReply) :
      RTrans P (.fwdRet e a) (some (.inr (.ans e ⟨L.stubS a.store, a.result⟩))) .idle
  /-- A host-free machine step of the provider (silent). -/
  | tau {e : UCall Nat} {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
      RTrans P (.running e s t) none (.running e s' t')
  /-- A callout of the provider is asked down in the real store (Proponent). -/
  | ucall {e : UCall Nat} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      (callout : CalloutAt s t h args) :
      RTrans P (.running e s t) (some (.inl (.ask ⟨h, s, args⟩))) (.waiting e s t ⟨h, s, args⟩)
  /-- Its answer resumes the provider (Opponent). -/
  | uret {e : UCall Nat} {s : Store Nat} {t : Thread} {e' : UCall Nat} (a : UReply) :
      RTrans P (.waiting e s t e') (some (.inl (.ans e' a)))
        (.running e a.store (resumeResult s t a.result))
  /-- The provider's result is replied in the stubbed store (Proponent). -/
  | oret {e : UCall Nat} {s : Store Nat} {t : Thread} {r : Result} (final : ResultAt s t r) :
      RTrans P (.running e s t) (some (.inr (.ans e ⟨L.stubS s, r⟩))) .idle

/-- The transition system of the resolver. -/
def rlts (P : Profile) : LTS UImp UImp := ⟨RState, .idle, L.RTrans P⟩

/-- **The provider's strategy**: the resolver, an environment of the consumer. -/
noncomputable def rstrategy (P : Profile) : Strategy UImp UImp := Strategy.ofLTS (L.rlts P)

/-- The provider's divergence-observing strategy. -/
noncomputable def rdstrategy (P : Profile) : DStrategy UImp UImp := DStrategy.ofLTS (L.rlts P)

/-- **The composite** of the provider and the consumer. -/
noncomputable def compStrategy (P : Profile) : Strategy UImp L.U.F :=
  (L.rstrategy P).comp (L.U.strategy P)

/-- **The divergence-observing composite** of the provider and the consumer. -/
noncomputable def compDStrategy (P : Profile) : DStrategy UImp L.U.F :=
  (L.rdstrategy P).comp (L.U.dstrategy P)

/-! ### Moves -/

/-- The stubbed export question. -/
def stubQ (f : L.U.F.Op) : L.U.F.Op := ⟨f.target, L.stubS f.store, f.args⟩

/-- The stubbed reply. -/
def stubR (a : UReply) : UReply := ⟨L.stubS a.store, a.result⟩

/-- **The store relation applied to moves**: upper moves carry stubbed stores, lower moves
real ones. -/
def stubUp : Move UImp L.U.F → Move UImp L.U.F
  | .inl m => .inl m
  | .inr (.ask f) => .inr (.ask (L.stubQ f))
  | .inr (.ans f a) => .inr (.ans (L.stubQ f) (L.stubR a))

/-- The stores of a move of the linked module satisfy the layout (its own callouts excepted,
whose store is the one it runs in). -/
def MoveLayout : Move UImp L.U.F → Prop
  | .inr (.ask f) => L.Layout f.store
  | .inr (.ans f a) => L.Layout f.store ∧ L.Layout a.store
  | .inl (.ask _) => True
  | .inl (.ans _ a) => L.Layout a.store

/-- The stores of a play satisfy the layout. -/
def LayoutPlay (p : List (Move UImp L.U.F)) : Prop := ∀ m ∈ p, L.MoveLayout m

/-! ### Closed programs: the layout from the initial store -/

/-- No host function of `s` has a stub code (the second half of `Layout`). -/
def NoStub (s : Store Nat) : Prop :=
  ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi → fi.code = .host h →
    L.target h = none

/-- The stubbed provider functions are functions of `s`. -/
def StubsIn (s : Store Nat) : Prop := ∀ (a k : Nat) (c : Func), L.stub a = some (k, c) → a < s.funcs.length

/-- **The environment allocates no stub codes**: an answer to a call made in a store without
stub-coded host functions has none either. -/
def EnvNoStub (Lenv : SEnv UImp) : Prop :=
  ∀ (q : Lenv.S) (e : UCall Nat) (a : UReply) (q' : Lenv.S), Lenv.Ans q e a q' → L.NoStub e.store →
    L.NoStub a.store

/-- **The closed composite**: the environment `Lenv` in state `q`, below the provider, below the
consumer. -/
noncomputable def compClosedD (P : Profile) (Lenv : SEnv UImp) (q : Lenv.S) :
    DStrategy Sig.empty L.U.F :=
  (Lenv.dstrategy q).comp (L.compDStrategy P)

end ULink

/-! ### The link of a `link?` setup -/

namespace Linking.Setup

/-- The Wasm code of the function at address `a` of `s` (a placeholder when it has none). -/
def wasmCodeAt (s : Store Nat) (a : Nat) : Func :=
  match s.funcs[a]?.map FuncInst.code with
  | some (.wasm c) => c
  | _ => ⟨⟨0⟩, [], []⟩

/-- The stub of the shared-store address `a`: the provider functions of the stub set, with the
host code `Setup.stubOut` gives them and their code in the shared store. -/
def ulinkStub (S : Setup) (a : Nat) : Option (Nat × Func) :=
  if S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs then
    some (S.stubs.idxOf (a - S.base.funcs.length), wasmCodeAt S.sc a)
  else none

/-- The shared-store address of the stub host code `k`. -/
def ulinkTarget (S : Setup) (k : Nat) : Option Nat :=
  if h : k < S.stubs.length then some (S.base.funcs.length + S.stubs[k]) else none

theorem ulinkTarget_eq_some {S : Setup} {k a : Nat} (h : S.ulinkTarget k = some a) :
    ∃ hk : k < S.stubs.length, S.base.funcs.length + S.stubs[k] = a := by
  unfold ulinkTarget at h
  split at h
  · exact ⟨_, Option.some.inj h⟩
  · cases h

theorem ulinkStub_eq_some {S : Setup} {a k : Nat} {c : Func} (h : S.ulinkStub a = some (k, c)) :
    (S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs) ∧
      S.stubs.idxOf (a - S.base.funcs.length) = k := by
  unfold ulinkStub at h
  split at h
  · exact ⟨by assumption, (Prod.mk.inj (Option.some.inj h)).1⟩
  · cases h

theorem ulinkStub_of_target {S : Setup} {k a : Nat} (h : S.ulinkTarget k = some a) :
    ∃ c, S.ulinkStub a = some (k, c) := by
  obtain ⟨hk, ha⟩ := ulinkTarget_eq_some h
  have hsub : a - S.base.funcs.length = S.stubs[k] := by omega
  have hcond : S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs :=
    ⟨by omega, hsub ▸ List.getElem_mem hk⟩
  have hidx : S.stubs.idxOf (a - S.base.funcs.length) = k := by
    rw [hsub]
    exact List.Nodup.idxOf_getElem S.stubs_nodup k hk
  refine ⟨wasmCodeAt S.sc a, ?_⟩
  unfold ulinkStub
  simp only [hcond, and_self, ↓reduceIte, hidx]

theorem ulinkTarget_of_stub {S : Setup} {k a : Nat} {c : Func} (h : S.ulinkStub a = some (k, c)) :
    S.ulinkTarget k = some a := by
  obtain ⟨hcond, hk⟩ := ulinkStub_eq_some h
  have hlt' : S.stubs.idxOf (a - S.base.funcs.length) < S.stubs.length :=
    List.idxOf_lt_length_of_mem hcond.2
  have hlt : k < S.stubs.length := hk ▸ hlt'
  have hget : S.stubs[k] = a - S.base.funcs.length := by
    subst hk
    exact List.getElem_idxOf hlt'
  have ha : S.base.funcs.length + S.stubs[k] = a := by omega
  unfold ulinkTarget
  simp only [hlt, ↓reduceDIte, ha]

theorem ulinkTarget_iff (S : Setup) (k a : Nat) :
    S.ulinkTarget k = some a ↔ ∃ c, S.ulinkStub a = some (k, c) :=
  ⟨ulinkStub_of_target, fun ⟨_, h⟩ => ulinkTarget_of_stub h⟩

/-- **The semantic link of a `link?` setup**: the shared world (`sharedI`: provider and consumer
instantiated into one store `sc`) with the stub set of the setup as stubs. -/
def toULink (S : Setup) : ULink where
  X := Fin S.exportTypes.length
  addr := S.sharedI.addr
  stub := S.ulinkStub
  target := S.ulinkTarget
  target_iff := S.ulinkTarget_iff

end Linking.Setup

/-! ### Worked example: a shared memory and a function -/

namespace ULinkExample

/-- One page of 32-bit memory. -/
def memTy1 : MemoryType := ⟨.i32, ⟨1, none⟩⟩

/-- `i32.const 0; i32.const 42; i32.store`. -/
def setBody : List Instr := [.intConst .i32 0, .intConst .i32 42, .intStore .i32 none ⟨0⟩ memarg0]

/-- The provider: exports its memory `mem` and `set : [] → []`, which stores `42` at address
`0`. -/
def exProv : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  memories := [memTy1]
  funcs := [⟨⟨0⟩, [], setBody⟩]
  exports := [⟨"mem", .memory ⟨0⟩⟩, ⟨"set", .func ⟨0⟩⟩]

/-- The consumer: imports the provider's memory and `set`, and exports
`run : [] → [i32]`, which calls `set` and loads address `0` of the imported memory. -/
def exCons : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩]
  imports := [⟨"p", "mem", .memory memTy1⟩, ⟨"p", "set", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], [.call ⟨0⟩, .intConst .i32 0, .intLoad .i32 none ⟨0⟩ memarg0]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

/-- The provider allocated by the spec's `prepare?` into the empty store. -/
def provPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) exProv []).getD (⟨{}, {}, []⟩, none)

/-- The consumer allocated against the provider's memory (address `0`) and `set` (address
`0`): **the linked store**, one store for both. -/
def consPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? provPrep.1.store exCons [.mem 0, .func 0]).getD (⟨{}, {}, []⟩, none)

/-- The linked store. -/
def exS : Store Nat := consPrep.1.store

/-- The code of the provider function `set`, as allocated. -/
def provCode : Func :=
  match exS.funcs[0]?.map FuncInst.code with
  | some (.wasm c) => c
  | _ => ⟨⟨0⟩, [], []⟩

/-- **The link**: export `run` at address `1`; the provider function at address `0` is the
consumer's import `set`, stubbed by host code `0`. -/
def exLink : ULink where
  X := Unit
  addr _ := 1
  stub a := if a = 0 then some (0, provCode) else none
  target k := if k = 0 then some 0 else none
  target_iff k a := by
    by_cases hk : k = 0 <;> by_cases ha : a = 0 <;> simp [hk, ha, eq_comm]

/-- Store `42` (as `i32`) at address `0`. -/
def store42 (mi : MemInst) : MemInst :=
  match Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr (0 : BitVec 32).toNat memarg0)
      (count := IntType.i32.width / 8) ((42 : BitVec IntType.i32.width).setWidth _) with
  | some b => { mi with bytes := b }
  | none => mi

/-- The linked store after `set`. -/
def exS' : Store Nat :=
  match exS.mems[0]? with
  | some mi => exS.setMem 0 (store42 mi)
  | none => exS

/-- The call of `run`. -/
def runQ : exLink.U.F.Op := ⟨(), exS, []⟩

/-- Its answer: `i32 42` in the written store. -/
def runA : UReply := ⟨exS', .values [.num ⟨.int .i32, 42⟩]⟩

end ULinkExample

/-! ### Worked example: partial linking and a callback -/

namespace ULinkCallback

/-- `i32`. -/
def i32T : ValType := .num (.int .i32)

/-- The types of both modules: `$cb = [] → [i32]` and `[(ref null $cb)] → [i32]`. -/
def cbTypes : List RecType :=
  [⟨[⟨true, [], .func ⟨[], [i32T]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[.ref ⟨true, .typeIdx ⟨0⟩⟩], [i32T]⟩⟩]⟩]

/-- The provider: exports `apply : [(ref null $cb)] → [i32]`, which calls its argument
(`local.get 0; call_ref $cb`): a callback into whoever passed the reference. -/
def exApply : Module where
  types := cbTypes
  funcs := [⟨⟨1⟩, [], [.localGet ⟨0⟩, .callRef ⟨0⟩]⟩]
  exports := [⟨"apply", .func ⟨0⟩⟩]

/-- The consumer: imports a host function `env.host : [] → [i32]`, which the provider does
**not** provide, and the provider's `apply`; defines `cb = call env.host` and
`run = ref.func cb; call apply`, and exports both. -/
def exUse : Module where
  types := cbTypes
  imports := [⟨"env", "host", .func ⟨0⟩⟩, ⟨"p", "apply", .func ⟨1⟩⟩]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩, ⟨⟨0⟩, [], [.refFunc ⟨2⟩, .call ⟨1⟩]⟩]
  exports := [⟨"cb", .func ⟨2⟩⟩, ⟨"run", .func ⟨3⟩⟩]

/-- The validated type of the consumer. -/
def useMT : CModuleType := (validate? exUse).getD ⟨[], []⟩

/-- The store providing the host import (host code `0`, address `0`). -/
def hostS : Store Nat := importStore ((CExternType.funcs useMT.imports).take 1)

/-- The provider allocated next to the host function (`apply` at address `1`). -/
def applyPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? hostS exApply []).getD (⟨{}, {}, []⟩, none)

/-- The consumer allocated against the host function and `apply` (`cb` at `2`, `run` at `3`). -/
def usePrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? applyPrep.1.store exUse [.func 0, .func 1]).getD (⟨{}, {}, []⟩, none)

/-- The linked store. -/
def cbS : Store Nat := usePrep.1.store

/-- The code of `apply`, as allocated. -/
def applyCode : Func :=
  match cbS.funcs[1]?.map FuncInst.code with
  | some (.wasm c) => c
  | _ => ⟨⟨0⟩, [], []⟩

/-- **The partial link**: export `run` (address `3`); the provider function `apply` (address
`1`) is stubbed by host code `1`; the host import (host code `0`) stays an import. -/
def cbLink : ULink where
  X := Unit
  addr _ := 3
  stub a := if a = 1 then some (1, applyCode) else none
  target k := if k = 1 then some 1 else none
  target_iff k a := by
    by_cases hk : k = 1 <;> by_cases ha : a = 1 <;> simp [hk, ha, eq_comm]

/-- The call of `run`. -/
def runQ : cbLink.U.F.Op := ⟨(), cbS, []⟩

/-- The host call made by the callback `cb`, in the linked store. -/
def hostQ : UCall Nat := ⟨0, cbS, []⟩

/-- The play: `run` is asked, the host is asked (from `cb`, called back by `apply`), the host
answers `a`, and `run` answers with the host's answer. -/
def runPlay (a : UReply) : List (Move UImp cbLink.U.F) :=
  [.inr (.ask runQ), .inl (.ask hostQ), .inl (.ans hostQ a), .inr (.ans runQ a)]

end ULinkCallback

end Silmaril.Wasm.Game
