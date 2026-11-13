module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodTable

/-!
# Covered code with `call_indirect`, `table.size` and `memory.size`, read in a module

Round 3's covered code (`Whole.ctrlOk`) excludes `call_indirect`, although both of its rules are
proved forward (`Whole.CallIndFwd20`, `Whole.CallIndTrapFwd20`). The trap rule is proved where the
type index is defined: SpecTec's `call_indirect-trap` is an `otherwise`, and refuting
`call_indirect-call`'s body reads `$type(z, y)`. Wasm validation guarantees that every type index
of a function body exists in its module. So the covered code here is read **in a module**:

* `ctrlOkI m i`: `ctrlOk`, plus `call_indirect x y` where `m` defines type `y`, plus
  `table.size`, `memory.size` (forward in `CallIndGoodSize`) and `table.get`
  (`CallIndGoodTable`), recursively in block bodies;
* `adminOkI m`: the same for administrative code, a frame body read in its own frame's module;
* `StoreOkI s`: every function of the store is a Wasm function whose body is covered in the
  function's own module (the module of the frame `call_addr` builds).

* **`cover20CI`**: every V2 step from plain-tail code that is `adminOkI` in the frame's module,
  over a `StoreOkI` store, is a step of `Nest20 (FwdStep20G P)`: round 3's fragment with both
  `call_indirect` rules (`Whole.FwdStep20F`), `table.size`/`memory.size` (`SizeFwd20`) and
  `table.get` (`TableGetFwd20`).
* **`adminOkI_step`**: such a step keeps the code covered in the (unchanged) module of the
  frame, and keeps the functions and memories of the store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.CallIndGood

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk ctrlOkL adminOk Nest20 FwdStep20D FwdStep20E
  FwdStep20F StoreOk StoreFM Tail20)

variable {H : Type}

/-! ## The predicates -/

mutual
/-- **Covered instructions with `call_indirect`**, in the module `m`. -/
def ctrlOkI (m : ModuleInst) : V2.Instr → Bool
  | .block _ body | .loop _ body => ctrlOkIL m body
  | .if_ _ l r => ctrlOkIL m l && ctrlOkIL m r
  | .callIndirect _ y => (m.type? y).isSome
  | .tableSize _ | .memorySize | .tableGet _ => true
  | i => ctrlOk i

/-- `ctrlOkI` on a sequence. -/
def ctrlOkIL (m : ModuleInst) : List V2.Instr → Bool
  | [] => true
  | i :: is => ctrlOkI m i && ctrlOkIL m is
end

@[simp] theorem ctrlOkIL_eq (m : ModuleInst) (l : List V2.Instr) : ctrlOkIL m l = l.all (ctrlOkI m) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ctrlOkIL, ih]

mutual
/-- **Covered administrative code with `call_indirect`**, in the module `m`; a frame body is read
in its frame's module. -/
def adminOkI (m : ModuleInst) : Admin → Bool
  | .plain i => ctrlOkI m i
  | .label _ cont body => ctrlOkIL m cont && adminOkIL m body
  | .frame _ fi body => adminOkIL fi.module body
  | .trap | .callAddr _ | .refFuncAddr _ | .refHostAddr _ => true

/-- `adminOkI` on a sequence. -/
def adminOkIL (m : ModuleInst) : List Admin → Bool
  | [] => true
  | a :: rest => adminOkI m a && adminOkIL m rest
end

@[simp] theorem adminOkIL_eq (m : ModuleInst) (l : List Admin) : adminOkIL m l = l.all (adminOkI m) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [adminOkIL, ih]

@[simp] theorem adminOkI_plain (m : ModuleInst) (i : V2.Instr) : adminOkI m (.plain i) = ctrlOkI m i :=
  rfl

@[simp] theorem adminOkI_label (m : ModuleInst) (n : Nat) (cont : List V2.Instr) (body : List Admin) :
    adminOkI m (.label n cont body) = (cont.all (ctrlOkI m) && body.all (adminOkI m)) := by
  simp [adminOkI]

@[simp] theorem adminOkI_frame (m : ModuleInst) (n : Nat) (fi : Frame) (body : List Admin) :
    adminOkI m (.frame n fi body) = body.all (adminOkI fi.module) := by simp [adminOkI]

@[simp] theorem adminOkI_trap (m : ModuleInst) : adminOkI m .trap = true := rfl
@[simp] theorem adminOkI_callAddr (m : ModuleInst) (a : FuncAddr) : adminOkI m (.callAddr a) = true :=
  rfl
@[simp] theorem adminOkI_refFuncAddr (m : ModuleInst) (a : FuncAddr) :
    adminOkI m (.refFuncAddr a) = true := rfl
@[simp] theorem adminOkI_refHostAddr (m : ModuleInst) (a : HostAddr) :
    adminOkI m (.refHostAddr a) = true := rfl

@[simp] theorem ctrlOkI_block (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkI m (.block bt b) = b.all (ctrlOkI m) := by simp [ctrlOkI]

@[simp] theorem ctrlOkI_loop (m : ModuleInst) (bt : V2.BlockType) (b : List V2.Instr) :
    ctrlOkI m (.loop bt b) = b.all (ctrlOkI m) := by simp [ctrlOkI]

@[simp] theorem ctrlOkI_if (m : ModuleInst) (bt : V2.BlockType) (b₁ b₂ : List V2.Instr) :
    ctrlOkI m (.if_ bt b₁ b₂) = (b₁.all (ctrlOkI m) && b₂.all (ctrlOkI m)) := by simp [ctrlOkI]

@[simp] theorem ctrlOkI_callIndirect (m : ModuleInst) (x : TableIdx) (y : TypeIdx) :
    ctrlOkI m (.callIndirect x y) = (m.type? y).isSome := by simp [ctrlOkI]

@[simp] theorem adminOkI_toAdmin (m : ModuleInst) (v : Val) : adminOkI m v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> simp [Val.toAdmin, ctrlOkI, ctrlOk]

@[simp] theorem all_adminOkI_vals (m : ModuleInst) (vs : List Val) : (vals vs).all (adminOkI m) = true := by
  simp [vals]

@[simp] theorem all_adminOkI_expression (m : ModuleInst) (is : List V2.Instr) :
    (expression is).all (adminOkI m) = is.all (ctrlOkI m) := by
  simp [expression, Function.comp_def]

/-- **Every function of the store is a Wasm function whose body is covered in its module.** -/
def StoreOkI (s : Store H) : Prop :=
  ∀ a fi, s.funcInst? a = some fi → ∃ fn, fi.code = .wasm fn ∧ fn.body.all (ctrlOkI fi.module) = true

theorem StoreOkI.of_fm {s s' : Store H} (h : StoreOkI s) (e : StoreFM s s') : StoreOkI s' := by
  intro a fi hf
  exact h a fi (by simpa [Store.funcInst?, e.1] using hf)

theorem StoreOkI.not_host {s : Store H} (hs : StoreOkI s) {a : FuncAddr} {fi : FuncInst H} {h : H}
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h) : False := by
  obtain ⟨fn, hc, -⟩ := hs a fi hf
  rw [hcode] at hc
  cases hc

/-! ## Round 3's covered code is covered -/

/-- An instruction without nested code. -/
def isNest : V2.Instr → Bool
  | .block .. | .loop .. | .if_ .. | .callIndirect .. => true
  | _ => false

/-- **On an instruction without nested code and other than `call_indirect`, `ctrlOkI` is
`ctrlOk`.** -/
theorem ctrlOkI_flat (m : ModuleInst) (i : V2.Instr) (hn : isNest i = false) (h : ctrlOk i = true) :
    ctrlOkI m i = true := by
  cases i <;> simp_all [ctrlOkI, isNest]

/-- `ctrlOk` gives `ctrlOkI` in every module, below a size bound. -/
theorem ctrlOkI_of_ctrlOk_lt (m : ModuleInst) (n : Nat) :
    ∀ i : V2.Instr, sizeOf i < n → ctrlOk i = true → ctrlOkI m i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi h
    have hb : ∀ b : List V2.Instr, sizeOf b < n → b.all ctrlOk = true → b.all (ctrlOkI m) = true :=
      fun b hs hb => List.all_eq_true.2 fun x hx =>
        ih x (by have := List.sizeOf_lt_of_mem hx; omega) (List.all_eq_true.1 hb x hx)
    cases i with
    | block bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | loop bt b => simpa using hb b (by simp at hi; omega) (by simpa using h)
    | if_ bt l r =>
      have hlr : l.all ctrlOk = true ∧ r.all ctrlOk = true := by simpa using h
      simp only [ctrlOkI_if, Bool.and_eq_true]
      exact ⟨hb l (by simp at hi; omega) hlr.1, hb r (by simp at hi; omega) hlr.2⟩
    | callIndirect x y => simp [ctrlOk] at h
    | _ => exact ctrlOkI_flat m _ rfl h

/-- **`ctrlOk` gives `ctrlOkI` in every module.** -/
theorem ctrlOkI_of_ctrlOk (m : ModuleInst) (i : V2.Instr) (h : ctrlOk i = true) : ctrlOkI m i = true :=
  ctrlOkI_of_ctrlOk_lt m _ i (Nat.lt_succ_self _) h

/-- `ctrlOkI_of_ctrlOk` on a sequence. -/
theorem ctrlOkIL_of_ctrlOkL (m : ModuleInst) (l : List V2.Instr) (h : l.all ctrlOk = true) :
    ctrlOkIL m l = true := by
  rw [ctrlOkIL_eq]
  exact List.all_eq_true.2 fun x hx => ctrlOkI_of_ctrlOk m x (List.all_eq_true.1 h x hx)

mutual
/-- `adminOk` gives `adminOkI` in every module. -/
theorem adminOkI_of_adminOk (m : ModuleInst) : ∀ a : Admin, adminOk a = true → adminOkI m a = true
  | .plain i, h => ctrlOkI_of_ctrlOk m i h
  | .label _ cont body, h => by
    have hb : cont.all ctrlOk = true ∧ body.all adminOk = true := by simpa using h
    rw [adminOkI_label, ← ctrlOkIL_eq, ← adminOkIL_eq, ctrlOkIL_of_ctrlOkL m cont hb.1,
      adminOkIL_of_adminOk m body hb.2]
    rfl
  | .frame _ fi body, h => by
    rw [adminOkI_frame, ← adminOkIL_eq]
    exact adminOkIL_of_adminOk fi.module body (by simpa using h)
  | .trap, _ => rfl
  | .callAddr _, _ => rfl
  | .refFuncAddr _, _ => rfl
  | .refHostAddr _, _ => rfl

/-- `adminOkI_of_adminOk` on a sequence. -/
theorem adminOkIL_of_adminOk (m : ModuleInst) : ∀ l : List Admin, l.all adminOk = true →
    adminOkIL m l = true
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (adminOkI m a && adminOkIL m l) = true
    rw [adminOkI_of_adminOk m a h.1, adminOkIL_of_adminOk m l h.2]
    rfl
end

theorem storeOkI_of_storeOk {s : Store H} (h : StoreOk s) : StoreOkI s := by
  intro a fi hf
  obtain ⟨fn, hc, hb⟩ := h a fi hf
  exact ⟨fn, hc, by rw [← ctrlOkIL_eq]; exact ctrlOkIL_of_ctrlOkL _ _ hb⟩

/-! ## The cover lemma -/

/-- `PureRest20N` has an uncovered instruction. -/
theorem not_pureRest20N_okI {m : ModuleInst} {is : List Admin} (h : Whole.PureRest20N is)
    (hok : is.all (adminOkI m) = true) : False := by
  cases h with
  | @vec is i hm hv =>
    have hi : adminOkI m (.plain i) = true := List.all_eq_true.1 hok _ hm
    have hc : ctrlOkI m i = false := by
      cases i <;> simp_all [vecOp20, ctrlOkI, ctrlOk]
    rw [adminOkI_plain, hc] at hi
    exact absurd hi (by decide)
  | unOpInvalid h => simp_all [ctrlOkI, ctrlOk]
  | cvtUndefined h => simp_all [ctrlOkI, ctrlOk]

/-- **Round 3's fragment with both `call_indirect` rules, `table.size`, `memory.size` and
`table.get`.** -/
inductive FwdStep20G (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20F P c c') : FwdStep20G P c c'
  | size {c c' : Config H} (h : SizeFwd20 c c') : FwdStep20G P c c'
  | tget {c c' : Config H} (h : TableGetFwd20 c c') : FwdStep20G P c c'

theorem FwdStep20G.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20G P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | size h => exact h.step
  | tget h => exact h.step

/-- Into the widened fragment. -/
theorem fwdF_of_D {P : Profile} {c c' : Config H} (h : FwdStep20D P c c') : FwdStep20G P c c' :=
  .fwd (.fwd (.fwd h))

/-- The pure steps from covered plain-tail code are in the fragment. -/
theorem cover20CI_pure {P : Profile} {m : ModuleInst} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all (adminOkI m) = true) :
    FwdStep20G P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases Whole.pureStep_cover_tail hp ht with h | h | h
  · exact fwdF_of_D (Whole.fwdC_pure h)
  · exact fwdF_of_D (Whole.fwdC_pureB h)
  · exact (not_pureRest20N_okI h hok).elim

/-- **The read steps from covered code are in the fragment**; `call_indirect` traps where the
frame's module defines the type index. -/
theorem cover20CI_read {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all (adminOkI f.module) = true) :
    FwdStep20G P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases hr with
  | block hbt hk => exact fwdF_of_D (.fwd (.fwd (.block (.block hbt hk))))
  | loop hbt hk => exact fwdF_of_D (.fwd (.fwd (.block (.loop hbt hk))))
  | call hx => exact fwdF_of_D (Whole.fwdC_call (.call (by simpa [ModuleInst.funcAddr?] using hx)))
  | callAddr hf hcode hk => exact fwdF_of_D (.fwd (.callAddr (.mk hf hcode hk)))
  | loadIntTrap hm h => exact fwdF_of_D (.load (.intTrap hm h))
  | loadIntVal hm hb => exact fwdF_of_D (.load (.intVal hm hb))
  | loadFloatTrap hm h => exact fwdF_of_D (.load (.floatTrap hm h))
  | loadFloatVal hm hb => exact fwdF_of_D (.load (.floatVal hm hb))
  | localGet h =>
    exact fwdF_of_D (Whole.fwdC_read (.localGet (by simpa [State.local?, Frame.local?] using h)))
  | globalGet h =>
    obtain ⟨a, ha, hg⟩ := Whole.global?_some h
    exact fwdF_of_D (Whole.fwdC_read (.globalGet ha hg))
  | refFunc hx => exact fwdF_of_D (Whole.fwdC_read (.refFunc (by simpa [ModuleInst.funcAddr?] using hx)))
  | callIndirectCall ht hr hf hy => exact .fwd (.fwd (.callInd (.mk ht hr hf hy)))
  | tableSize ht hn => exact .size (.table ht hn)
  | memorySize hm hn => exact .size (.memory hm hn)
  | tableGetTrap ht h => exact .tget (.trap ht h)
  | tableGetVal ht hr => exact .tget (.val ht hr)
  | @callIndirectTrap x y i ti ht h =>
    have hy : (f.module.type? y).isSome = true := by simp_all
    obtain ⟨ft, hft⟩ := Option.isSome_iff_exists.1 hy
    exact .fwd (.callIndTrap (.mk ht (ft := ft) hft h))
  | _ => simp [ctrlOkI, ctrlOk] at hok

/-- **Every V2 step from covered plain-tail code with `call_indirect`, `table.size` and
`memory.size`, over a covered store, is in the nested fragment `FwdStep20G`.** -/
theorem cover20CI {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all (adminOkI c.frame.module) = true)
    (hs : StoreOkI c.store) : Nest20 (FwdStep20G P) c c' := by
  induction h with
  | pure hp => exact .base (cover20CI_pure hp ht hok)
  | read hr => exact .base (cover20CI_read hr hok)
  | ctxtInstrs hstep hne ih =>
    refine .ctx (ih (Whole.tail20_ctx hstep.not_allVals ht) ?_ hs) hne
    simp only [List.all_append, Bool.and_eq_true] at hok
    exact hok.1.2
  | ctxtLabel _ ih =>
    refine .label (ih (Whole.tail20_label ht).tail ?_ hs)
    simp only [List.all_cons, List.all_nil, Bool.and_true, adminOkI_label, Bool.and_eq_true] at hok
    exact hok.2
  | ctxtFrame _ ih => exact .frame (ih (Whole.tail20_frame ht).tail (by simpa using hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx => exact .base (fwdF_of_D (Whole.fwdC_top (.var (.localSet hx))))
  | globalSet ha hg => exact .base (fwdF_of_D (Whole.fwdC_top (.var (.globalSet ha hg))))
  | _ => simp [ctrlOkI, ctrlOk] at hok

/-! ## Preservation -/

/-- What a step from covered code with `call_indirect` keeps. -/
def KeepsI (c c' : Config H) : Prop :=
  c'.code.all (adminOkI c'.frame.module) = true ∧ StoreFM c.store c'.store ∧
    c'.frame.module = c.frame.module

/-- **Every pure step keeps covered code covered** in the same module. -/
theorem adminOkI_pureStep {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureStep P is is') (hok : is.all (adminOkI m) = true) : is'.all (adminOkI m) = true := by
  cases h <;> simp_all [ctrlOkI, ctrlOk, List.all_append]

/-- **Every read step keeps covered code covered**, over a covered store. -/
theorem adminOkI_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (adminOkI f.module) = true) (hs : StoreOkI s) :
    is'.all (adminOkI f.module) = true := by
  cases h with
  | @callAddr a vs fi fn hf hcode hk =>
    obtain ⟨fn', hc', hb⟩ := hs a fi hf
    rw [hcode] at hc'
    cases hc'
    simpa using hb
  | _ => simp_all [ctrlOkI, ctrlOk, List.all_append]

theorem keepsI_same {s : Store H} {f f' : Frame} {is is' : List Admin}
    (h : is'.all (adminOkI f'.module) = true) (hm : f'.module = f.module) :
    KeepsI ⟨s, f, is⟩ ⟨s, f', is'⟩ := ⟨h, ⟨rfl, rfl⟩, hm⟩

/-- **Every V2 step from covered code with `call_indirect` over a covered store keeps the code
covered, the store's functions and memories, and the module of the frame.** -/
theorem adminOkI_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all (adminOkI c.frame.module) = true)
    (hs : StoreOkI c.store) : KeepsI c c' := by
  induction h with
  | pure hp => exact keepsI_same (adminOkI_pureStep hp hok) rfl
  | read hr => exact keepsI_same (adminOkI_readStep hr hok hs) rfl
  | ctxtInstrs _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hok
    obtain ⟨hi, hm, hmod⟩ := ih hok.1.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hmod⟩
    rw [hmod]
    simp [List.all_append, hi', hok.2]
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    have hb : cont.all (ctrlOkI f.module) = true ∧ is.all (adminOkI f.module) = true := by
      simpa using hok
    obtain ⟨hi, hm, hmod⟩ := ih hb.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hmod⟩
    rw [hmod]
    simp [hb.1, hi']
  | ctxtFrame _ ih =>
    obtain ⟨hi, hm, -⟩ := ih (by simpa using hok) hs
    exact ⟨by simpa using hi, hm, rfl⟩
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet => exact ⟨rfl, ⟨rfl, rfl⟩, rfl⟩
  | globalSet => exact ⟨rfl, Whole.storeFM_global _ _ _, rfl⟩
  | _ => simp_all [ctrlOkI, ctrlOk]

end Silmaril.Wasm.SpecTec.Sim20.CallIndGood
