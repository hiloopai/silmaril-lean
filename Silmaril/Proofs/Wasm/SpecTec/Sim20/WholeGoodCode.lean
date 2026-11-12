module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholePlainTail
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Defs

/-!
# Code in the forward fragment, and why it stays there

`ctrlOk i` says that `i`, and every instruction nested in it, is one the forward fragment of the
2.0 route covers (`Whole.FwdStep20C`): the control instructions (`nop`, `unreachable`, `drop`,
`select`, `block`, `loop`, `if`, `br`, `br_if`, `br_table`, `return`, `call`), the scalar
numeric instructions (an integer unary operator only where it is valid, a conversion only where
V2's `toShared` defines it), `ref.null`, `ref.func`, `ref.is_null`, the local and global
instructions, and the unpacked loads. Excluded: `call_indirect`, the packed loads, stores,
`memory.size`/`grow`/`fill`/`copy`/`init`, every table and vector instruction, and
`elem.drop`/`data.drop`.

`adminOk` extends it to administrative code (label continuations and bodies, frame bodies;
values, `TRAP` and `CALL_ADDR` are fine), and `StoreOk s` says that every function of the store
is a Wasm function whose body is `ctrlOk`.

* **`adminOk_step`**: every V2 step from `adminOk` code over an `StoreOk` store produces
  `adminOk` code and changes neither the functions nor the memories of the store
  (`StoreFM`). Steps by an excluded instruction cannot happen (their left-hand side is not
  `adminOk`), and host calls cannot (the store has none);
* `adminOk_steps`: the same along runs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## The instructions -/

mutual
/-- **The instructions the forward fragment covers**, recursively in block bodies. -/
def ctrlOk : V2.Instr → Bool
  | .block _ body | .loop _ body => ctrlOkL body
  | .if_ _ l r => ctrlOkL l && ctrlOkL r
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .call _
  | .return_ | .intConst _ _ | .floatConst _ _ | .vecConst _ | .floatUnOp _ _ | .intBinOp _ _
  | .floatBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .floatRelOp _ _ | .refNull _
  | .refFunc _ | .refIsNull | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .globalSet _ | .intLoad _ none _ | .floatLoad _ _ => true
  | .intUnOp t op => op.valid t
  | .cvtOp target source op => (op.toShared target source).isSome
  | _ => false

/-- `ctrlOk` on a sequence. -/
def ctrlOkL : List V2.Instr → Bool
  | [] => true
  | i :: is => ctrlOk i && ctrlOkL is
end

@[simp] theorem ctrlOkL_eq (l : List V2.Instr) : ctrlOkL l = l.all ctrlOk := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ctrlOkL, ih]

mutual
/-- **The administrative code the forward fragment covers.** -/
def adminOk : Admin → Bool
  | .plain i => ctrlOk i
  | .label _ cont body => ctrlOkL cont && adminOkL body
  | .frame _ _ body => adminOkL body
  | .trap | .callAddr _ | .refFuncAddr _ | .refHostAddr _ => true

/-- `adminOk` on a sequence. -/
def adminOkL : List Admin → Bool
  | [] => true
  | a :: rest => adminOk a && adminOkL rest
end

@[simp] theorem adminOkL_eq (l : List Admin) : adminOkL l = l.all adminOk := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [adminOkL, ih]

@[simp] theorem ctrlOk_block (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOk (.block bt b) = b.all ctrlOk := by simp [ctrlOk]

@[simp] theorem ctrlOk_loop (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOk (.loop bt b) = b.all ctrlOk := by simp [ctrlOk]

@[simp] theorem ctrlOk_if (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    ctrlOk (.if_ bt b₁ b₂) = (b₁.all ctrlOk && b₂.all ctrlOk) := by simp [ctrlOk]

@[simp] theorem adminOk_plain (i : V2.Instr) : adminOk (.plain i) = ctrlOk i := rfl

@[simp] theorem adminOk_label (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    adminOk (.label n cont body) = (cont.all ctrlOk && body.all adminOk) := by simp [adminOk]

@[simp] theorem adminOk_frame (n : Nat) (fi : Frame) (body : List Admin) :
    adminOk (.frame n fi body) = body.all adminOk := by simp [adminOk]

@[simp] theorem adminOk_trap : adminOk .trap = true := rfl
@[simp] theorem adminOk_callAddr (a : FuncAddr) : adminOk (.callAddr a) = true := rfl
@[simp] theorem adminOk_refFuncAddr (a : FuncAddr) : adminOk (.refFuncAddr a) = true := rfl
@[simp] theorem adminOk_refHostAddr (a : HostAddr) : adminOk (.refHostAddr a) = true := rfl

@[simp] theorem adminOk_toAdmin (v : Val) : adminOk v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> simp [Val.toAdmin, ctrlOk]

@[simp] theorem all_adminOk_vals (vs : List Val) : (vals vs).all adminOk = true := by
  simp [vals]

@[simp] theorem all_adminOk_expression (is : List V2.Instr) :
    (expression is).all adminOk = is.all ctrlOk := by
  simp [expression, Function.comp_def]

@[simp] theorem adminOk_constI32 (c : BitVec 32) : adminOk (constI32 c) = true := rfl

/-- A vector operator is not covered. -/
theorem ctrlOk_of_vecOp {i : V2.Instr} (h : vecOp20 i = true) : ctrlOk i = false := by
  cases i <;> simp_all [vecOp20, ctrlOk]

/-! ## The store -/

/-- **Every function of the store is a Wasm function with a covered body.** -/
def StoreOk (s : Store H) : Prop :=
  ∀ a fi, s.funcInst? a = some fi → ∃ fn, fi.code = .wasm fn ∧ fn.body.all ctrlOk = true

/-- The parts of the store that `StoreOk` and `WholePages` read. -/
def StoreFM (s s' : Store H) : Prop := s'.funcs = s.funcs ∧ s'.mems = s.mems

theorem StoreOk.of_fm {s s' : Store H} (h : StoreOk s) (e : StoreFM s s') : StoreOk s' := by
  intro a fi hf
  exact h a fi (by simpa [Store.funcInst?, e.1] using hf)

/-! ## Preservation -/

/-- What a step from covered code over a covered store keeps. -/
def KeepsOk (c c' : Config H) : Prop := c'.code.all adminOk = true ∧ StoreFM c.store c'.store

theorem keepsOk_same {s : Store H} {f f' : Frame} {is is' : List Admin}
    (h : is'.all adminOk = true) : KeepsOk ⟨s, f, is⟩ ⟨s, f', is'⟩ := ⟨h, rfl, rfl⟩

/-- **Every pure step keeps covered code covered.** -/
theorem adminOk_pureStep {P : Profile} {is is' : List Admin} (h : PureStep P is is')
    (hok : is.all adminOk = true) : is'.all adminOk = true := by
  cases h <;> simp_all [ctrlOk, List.all_append]

/-- **Every read step keeps covered code covered**, over a covered store. -/
theorem adminOk_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all adminOk = true) (hs : StoreOk s) :
    is'.all adminOk = true := by
  cases h with
  | @callAddr a vs fi fn hf hcode hk =>
    obtain ⟨fn', hc', hb⟩ := hs a fi hf
    rw [hcode] at hc'
    cases hc'
    simpa using hb
  | _ => simp_all [ctrlOk, List.all_append]


/-- A host function is not in a covered store. -/
theorem StoreOk.not_host {s : Store H} (hs : StoreOk s) {a : FuncAddr} {fi : FuncInst H} {h : H}
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h) : False := by
  obtain ⟨fn, hc, -⟩ := hs a fi hf
  rw [hcode] at hc
  cases hc

theorem storeFM_refl (s : Store H) : StoreFM s s := ⟨rfl, rfl⟩

theorem storeFM_global (s : Store H) (a : GlobalAddr) (gi : GlobalInst) :
    StoreFM s (s.setGlobalInst a gi) := ⟨rfl, rfl⟩

/-- `ctxt-instrs` keeps covered code covered. -/
theorem keepsOk_ctx {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hok : (vals vs ++ is ++ rest).all adminOk = true)
    (ih : is.all adminOk = true → KeepsOk ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    KeepsOk ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  simp only [List.all_append, Bool.and_eq_true] at hok
  obtain ⟨hi, hm⟩ := ih hok.1.2
  exact ⟨by simp [List.all_append, hi, hok.2], hm⟩

/-- **Every V2 step from covered code over a covered store keeps the code covered and the store's
functions and memories unchanged.** -/
theorem adminOk_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all adminOk = true) (hs : StoreOk c.store) :
    KeepsOk c c' := by
  induction h with
  | pure hp => exact keepsOk_same (adminOk_pureStep hp hok)
  | read hr => exact keepsOk_same (adminOk_readStep hr hok hs)
  | ctxtInstrs _ _ ih => exact keepsOk_ctx hok fun hi => ih hi hs
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    have hb : cont.all ctrlOk = true ∧ is.all adminOk = true := by simpa using hok
    obtain ⟨hi, hm⟩ := ih hb.2 hs
    exact ⟨by simp [hb.1, hi], hm⟩
  | ctxtFrame _ ih =>
    obtain ⟨hi, hm⟩ := ih (by simpa using hok) hs
    exact ⟨by simp [hi], hm⟩
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet => exact keepsOk_same rfl
  | globalSet => exact ⟨rfl, storeFM_global _ _ _⟩
  | _ => simp_all [ctrlOk]

/-- **Along a V2 run from covered code over a covered store, the code stays covered and the
store keeps its functions and memories.** -/
theorem adminOk_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hok : c.code.all adminOk = true) (hs : StoreOk c.store) :
    c'.code.all adminOk = true ∧ StoreFM c.store c'.store := by
  induction h with
  | refl => exact ⟨hok, storeFM_refl _⟩
  | tail _ h₂ ih =>
    obtain ⟨hok', hm⟩ := ih
    obtain ⟨hok'', hm'⟩ := adminOk_step h₂ hok' (hs.of_fm hm)
    exact ⟨hok'', hm'.1.trans hm.1, hm'.2.trans hm.2⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
