module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Rules
public import Silmaril.Wasm.Verify.Check.Defs

@[expose] public section

/-!
# The instantiated LRAT checker

Kernel-checked facts (`decide +kernel`) about the instance of `lratModule` computed by
`Silmaril.Wasm.Verify.instance?` (validation and instantiation against no imports): its exports
are the functions `0 … 9` in order, each function's code is the module's, the module instance
resolves globals and memory as `MiOk` says, the eight globals hold their initial values and the
memory is `65536` zero bytes.

silmaril-lean's `Instr` has no decidable equality, so code is compared with `ibeqs`, a Boolean
equality on the instructions the checker uses, proved sound (`ibeqs_sound`).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.Verify Silmaril.Wasm.Game

/-! ## Comparing code -/

mutual
/-- Equality of instructions of the checker's fragment (`false` outside it). -/
def ibeq : Instr → Instr → Bool
  | .intConst .i32 a, .intConst .i32 b => a == b
  | .localGet x, .localGet y => x == y
  | .localSet x, .localSet y => x == y
  | .globalGet x, .globalGet y => x == y
  | .globalSet x, .globalSet y => x == y
  | .intBinOp .i32 o, .intBinOp .i32 p => o == p
  | .intRelOp .i32 o, .intRelOp .i32 p => o == p
  | .intTestOp .i32 o, .intTestOp .i32 p => o == p
  | .intLoad .i32 none x a, .intLoad .i32 none y b => x == y && a == b
  | .intStore .i32 none x a, .intStore .i32 none y b => x == y && a == b
  | .brIf l, .brIf m => l == m
  | .br l, .br m => l == m
  | .if_ .empty t e, .if_ .empty t' e' => ibeqs t t' && ibeqs e e'
  | .block .empty b, .block .empty b' => ibeqs b b'
  | .loop .empty b, .loop .empty b' => ibeqs b b'
  | _, _ => false
/-- Equality of instruction lists of the checker's fragment. -/
def ibeqs : List Instr → List Instr → Bool
  | [], [] => true
  | a :: as, b :: bs => ibeq a b && ibeqs as bs
  | _, _ => false
end

theorem ibeq_sound (a b : Instr) : ibeq a b = true → a = b := by
  apply ibeq.induct (motive_1 := fun a b => ibeq a b = true → a = b)
    (motive_2 := fun as bs => ibeqs as bs = true → as = bs)
  all_goals
    intros
    simp_all [ibeq, ibeqs]

theorem ibeqs_sound : ∀ (as bs : List Instr), ibeqs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ibeqs, Bool.and_eq_true] at h
    rw [ibeq_sound a b h.1, ibeqs_sound as bs h.2]
  | [], _ :: _, h => by simp [ibeqs] at h
  | _ :: _, [], h => by simp [ibeqs] at h

/-! ## The instance -/

/-- The instantiated checker. -/
def lratI : ScalarInstance := instOf lratModule

/-- The store of the instantiated checker. -/
def lratS : Store Nat := lratI.store

/-- The module instance of the checker's functions. -/
def lratMi : ModuleInst := ((lratS.funcs[0]?).map (·.module)).getD {}

/-- The type of the checker's globals. -/
def lratGt : CGlobalType := ((lratS.globals[0]?).map (·.type)).getD ⟨.const, .botv⟩

/-- The type of the checker's memory. -/
def lratMt : MemoryType := ⟨.i32, ⟨1, some 1⟩⟩

/-- The view's fixed part for the checker. -/
def lratX : Fix Nat := ⟨lratS.funcs, lratMi, lratGt, lratMt⟩

/-- The initial global values. -/
def G₀ : List (BitVec 32) := [0, 24576, 24576, 0, 0, 0, 0, 1]

/-- The initial memory. -/
def B₀ : ByteArray := ((lratS.mems[0]?).map (·.bytes)).getD .empty

/-- The code of a function instance and the module function it should be. -/
def codeMatches (fi : FuncInst Nat) (f : Func) : Bool :=
  match fi.code with
  | .wasm g => ibeqs g.body f.body && g.locals == f.locals && g.type == f.type
  | .host _ => false

/-- The function types of the exports, in order. -/
def lratTys : List CCompType :=
  [.func (Ty.ofList [.num (.int .i32)]) (Ty.ofList []), .func (Ty.ofList []) (Ty.ofList []),
    .func (Ty.ofList [.num (.int .i32)]) (Ty.ofList []), .func (Ty.ofList [.num (.int .i32)]) (Ty.ofList []),
    .func (Ty.ofList [.num (.int .i32)]) (Ty.ofList []), .func (Ty.ofList []) (Ty.ofList []),
    .func (Ty.ofList [.num (.int .i32)]) (Ty.ofList []), .func (Ty.ofList []) (Ty.ofList [.num (.int .i32)]),
    .func (Ty.ofList [.num (.int .i32)]) (Ty.ofList []), .func (Ty.ofList []) (Ty.ofList [])]

theorem lrat_instance : (instance? lratModule).isSome = true := by decide +kernel

theorem lrat_addrs : lratI.addrs = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide +kernel

theorem lrat_exports : lratI.exports.length = 10 ∧ lratI.imports = [] := by decide +kernel

theorem lrat_funcs : (lratS.funcs.zip lratModule.funcs).map (fun p => codeMatches p.1 p.2) =
    List.replicate 10 true ∧ lratS.funcs.map (·.module == lratMi) = List.replicate 10 true ∧
    lratS.funcs.map (·.type.expand?) = lratTys.map some := by
  decide +kernel

theorem lrat_mi : lratMi.globals = List.range 8 ∧ lratMi.mems = [0] := by decide +kernel

theorem lrat_globals : lratS.globals = G₀.map fun v => ⟨lratGt, Val.i32 v⟩ := by decide +kernel

theorem lrat_mems : lratS.mems.map (·.type) = [lratMt] ∧ lratS.mems.length = 1 := by decide +kernel

theorem lrat_zero : B₀.data.toList.all (· == 0) = true ∧ B₀.size = 65536 := by decide +kernel

theorem lrat_exports_eq : lratI.exports =
    [⟨[.num (.int .i32)], []⟩, ⟨[], []⟩, ⟨[.num (.int .i32)], []⟩, ⟨[.num (.int .i32)], []⟩,
      ⟨[.num (.int .i32)], []⟩, ⟨[], []⟩, ⟨[.num (.int .i32)], []⟩, ⟨[], [.num (.int .i32)]⟩,
      ⟨[.num (.int .i32)], []⟩, ⟨[], []⟩] := by
  decide +kernel

/-- The function, module function and type of export `j` agree. -/
def fnOk (j : Nat) : Bool :=
  match lratS.funcs[j]?, lratModule.funcs[j]?, lratTys[j]? with
  | some fi, some f, some ty => codeMatches fi f && fi.module == lratMi && fi.type.expand? == some ty
  | _, _, _ => false

theorem lrat_fnOk : (List.range 10).all fnOk = true := by decide +kernel

/-! The elaborator never needs to compute the instance: every fact about it is one of the kernel
checks above. -/
theorem lratI_store : lratI.store = lratS := rfl

attribute [irreducible] lratI lratS

end Silmaril.Wasm.Examples.LRAT
