module

public import Silmaril.Wasm.Binaryen.Interp
public import Silmaril.Wasm.Binaryen.Profile

@[expose] public section

/-! # Throws are vacuous in the profile

On the Core side: starting from an invocation of a store whose functions are all
profile code, every reachable configuration carries only profile instructions
and constants (`OkAdmins`), and the store's functions never change. A thrown
result `(REF.EXN_ADDR a) THROW_REF` contains `THROW_REF`, which is not a profile
instruction, so it is never reached (`not_throws_mem_behaviours`).
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics

variable {H : Type}

/-! ## Profile instructions -/

theorem instrInProfile_flat {i : Instr} (h : structuredInstr i = false) :
    instrInProfile i ↔ profileInstr i = true := by
  rw [instrInProfile.eq_def]
  split <;> simp_all [structuredInstr]

/-- The flat case of `instrInProfile`, with side conditions `simp` discharges on
constructors. -/
theorem instrInProfile_flat' {i : Instr} (h₁ : ∀ bt body, i ≠ .block bt body)
    (h₂ : ∀ bt body, i ≠ .loop bt body) (h₃ : ∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂) :
    instrInProfile i ↔ profileInstr i = true := by
  rw [instrInProfile.eq_def]
  split <;> simp_all

theorem instrInProfile_block {bt : BlockType} {body : List Instr} :
    instrInProfile (.block bt body) ↔
      profileBlockType bt = true ∧ ∀ i ∈ body, instrInProfile i := by
  rw [instrInProfile.eq_def]
  simp only
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 ⟨i, hi⟩ (List.mem_attach _ _)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i _ => h2 i.1 i.2⟩

theorem instrInProfile_loop {bt : BlockType} {body : List Instr} :
    instrInProfile (.loop bt body) ↔ profileBlockType bt = true ∧ ∀ i ∈ body, instrInProfile i := by
  rw [instrInProfile.eq_def]
  simp only
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 ⟨i, hi⟩ (List.mem_attach _ _)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i _ => h2 i.1 i.2⟩

theorem instrInProfile_if {bt : BlockType} {b₁ b₂ : List Instr} :
    instrInProfile (.if_ bt b₁ b₂) ↔ profileBlockType bt = true ∧
      (∀ i ∈ b₁, instrInProfile i) ∧ ∀ i ∈ b₂, instrInProfile i := by
  rw [instrInProfile.eq_def]
  simp only
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i hi => h2 ⟨i, hi⟩ (List.mem_attach _ _),
      fun i hi => h3 ⟨i, hi⟩ (List.mem_attach _ _)⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun i _ => h2 i.1 i.2, fun i _ => h3 i.1 i.2⟩

theorem not_instrInProfile_tryTable {bt : BlockType} {cs : List Catch} {body : List Instr} :
    ¬ instrInProfile (.tryTable bt cs body) := by
  rw [instrInProfile.eq_def]
  simp [profileInstr]

/-- Plain instructions allowed in reachable code: profile instructions and the
constants of arbitrary value types (arguments need not be integers). -/
def OkInstr (i : Instr) : Prop :=
  instrInProfile i ∨ (∃ t b, i = .floatConst t b) ∨ (∃ b, i = .vecConst b)

mutual
/-- Administrative instructions built from profile code. -/
def OkAdmin : Admin → Prop
  | .plain i => OkInstr i
  | .label _ cont body => (∀ i ∈ cont, instrInProfile i) ∧ OkAdmins body
  | .handler _ _ body => OkAdmins body
  | .frame _ _ body => OkAdmins body
  | .ref _ | .callRefType _ | .returnCallRefType _ | .trap => True
/-- `OkAdmin` on a sequence. -/
def OkAdmins : List Admin → Prop
  | [] => True
  | a :: as => OkAdmin a ∧ OkAdmins as
end

@[simp] theorem okAdmins_nil : OkAdmins [] := trivial

@[simp] theorem okAdmins_cons {a : Admin} {as : List Admin} :
    OkAdmins (a :: as) ↔ OkAdmin a ∧ OkAdmins as := Iff.rfl

@[simp] theorem okAdmins_append {as bs : List Admin} :
    OkAdmins (as ++ bs) ↔ OkAdmins as ∧ OkAdmins bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, and_assoc]

@[simp] theorem okAdmin_plain {i : Instr} : OkAdmin (.plain i) ↔ OkInstr i := Iff.rfl

@[simp] theorem okAdmin_label {n : Nat} {cont : List Instr} {body : List Admin} :
    OkAdmin (.label n cont body) ↔ (∀ i ∈ cont, instrInProfile i) ∧ OkAdmins body := Iff.rfl

@[simp] theorem okAdmin_handler {n : Nat} {cs : List Catch} {body : List Admin} :
    OkAdmin (.handler n cs body) ↔ OkAdmins body := Iff.rfl

@[simp] theorem okAdmin_frame {n : Nat} {f : Frame} {body : List Admin} :
    OkAdmin (.frame n f body) ↔ OkAdmins body := Iff.rfl

@[simp] theorem okAdmin_ref {r : Ref} : OkAdmin (.ref r) := trivial

@[simp] theorem okAdmin_callRefType {d} : OkAdmin (.callRefType d) := trivial

@[simp] theorem okAdmin_returnCallRefType {d} : OkAdmin (.returnCallRefType d) := trivial

@[simp] theorem okAdmin_trap : OkAdmin .trap := trivial

@[simp] theorem okAdmin_toAdmin (v : Val) : OkAdmin v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;>
    simp only [Val.toAdmin, okAdmin_plain, okAdmin_ref, OkInstr]
  all_goals first
    | exact Or.inl ((instrInProfile_flat' (by simp) (by simp) (by simp)).2 rfl)
    | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    | exact Or.inr (Or.inr ⟨_, rfl⟩)

@[simp] theorem okAdmins_vals (vs : List Val) : OkAdmins (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨okAdmin_toAdmin v, ih⟩

@[simp] theorem okAdmin_constI32 (b : BitVec 32) : OkAdmin (constI32 b) := okAdmin_toAdmin _

theorem okAdmins_expression {is : List Instr} (h : ∀ i ∈ is, instrInProfile i) :
    OkAdmins (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    exact ⟨Or.inl (h i (List.mem_cons_self ..)), ih fun j hj => h j (List.mem_cons_of_mem _ hj)⟩

/-- A flat non-profile instruction is not allowed. -/
theorem okInstr_flat {i : Instr} (h : structuredInstr i = false) (hc : ∀ t b, i ≠ .floatConst t b)
    (hv : ∀ b, i ≠ .vecConst b) : OkInstr i ↔ profileInstr i = true := by
  unfold OkInstr
  rw [instrInProfile_flat h]
  constructor
  · rintro (h | ⟨t, b, rfl⟩ | ⟨b, rfl⟩)
    · exact h
    · exact absurd rfl (hc t b)
    · exact absurd rfl (hv b)
  · exact Or.inl

/-! ## Preservation along Core reductions -/

/-- Every function of the store is profile Wasm code. -/
def FuncsOk (F : List (FuncInst H)) : Prop :=
  ∀ fi ∈ F, ∃ fn, fi.code = .wasm fn ∧ ∀ i ∈ fn.body, instrInProfile i

macro "ok_simp" : tactic => `(tactic| simp_all [OkInstr, instrInProfile_block,
  instrInProfile_loop, instrInProfile_if, not_instrInProfile_tryTable, instrInProfile_flat',
  structuredInstr, profileInstr, throwing, Store.setGlobal, Store.setMem])

theorem okAdmin_retToCallIn {m : ModuleInst} {c : Admin} (hc : c.IsReturnCallRef)
    (h : OkAdmin c) : OkAdmin (c.retToCallIn m) := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · simp [OkInstr, instrInProfile_flat', profileInstr] at h
  · simp [Admin.retToCallIn]
  · exact absurd hc id

/-- **Preservation**: a reduction of the closed profile keeps code profile-clean
and leaves the functions of the store unchanged. -/
theorem okAdmins_step {P : Profile} {c c' : Config H} (h : Step P closedHost c c')
    (hc : OkAdmins c.code) (hF : FuncsOk c.store.funcs) :
    OkAdmins c'.code ∧ c'.store.funcs = c.store.funcs := by
  induction h with
  | parametric h => cases h <;> ok_simp
  | numeric h => cases h <;> ok_simp
  | vector h => cases h <;> ok_simp
  | «variable» h => cases h <;> ok_simp
  | table h => cases h <;> ok_simp
  | memory h => cases h <;> simp_all [aconst, load8u, store8, Store.setData, Store.setMem] <;> ok_simp
  | reference h => cases h <;> ok_simp
  | aggregate h => cases h <;> ok_simp
  | ctxtInstrs _ _ ih =>
    simp only [okAdmins_append] at hc ⊢
    obtain ⟨h1, h2⟩ := ih hc.1.2 hF
    exact ⟨⟨⟨hc.1.1, h1⟩, hc.2⟩, h2⟩
  | ctxtLabel _ ih =>
    simp only [okAdmins_cons, okAdmin_label, okAdmins_nil, and_true] at hc ⊢
    obtain ⟨h1, h2⟩ := ih hc.2 hF
    exact ⟨⟨hc.1, h1⟩, h2⟩
  | ctxtHandler _ ih =>
    simp only [okAdmins_cons, okAdmin_handler, okAdmins_nil, and_true] at hc ⊢
    exact ih hc hF
  | ctxtFrame _ ih =>
    simp only [okAdmins_cons, okAdmin_frame, okAdmins_nil, and_true] at hc ⊢
    exact ih hc hF
  | @callRefFunc s f c vs a fi ps rs code hcr hf he hn hcode =>
    refine ⟨?_, rfl⟩
    obtain ⟨fn, hfn, hbody⟩ := hF fi (List.mem_of_getElem? hf)
    rw [hcode] at hfn
    cases hfn
    simp only [okAdmins_cons, okAdmin_frame, okAdmin_label, okAdmins_nil, and_true]
    exact ⟨List.forall_mem_nil _, okAdmins_expression hbody⟩
  | callRefHost _ _ _ _ _ hhost => exact absurd hhost id
  | callRefHostDiv _ _ _ _ _ hhost => exact absurd hhost id
  | @returnCallRefFrameAddr s f fi' k vs' vs a c rest fn ps rs hcr hf he hn =>
    refine ⟨?_, rfl⟩
    have hcc : OkAdmin c := by simp_all
    simpa using okAdmin_retToCallIn (m := fi'.module) hcr hcc
  | _ => ok_simp <;> first | exact okAdmins_expression hc.2 | exact okAdmins_expression hc.1

theorem okAdmins_steps {P : Profile} {c c' : Config H} (h : Steps P closedHost c c')
    (hc : OkAdmins c.code) (hF : FuncsOk c.store.funcs) :
    OkAdmins c'.code ∧ c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => exact ⟨hc, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := okAdmins_step hstep h1 (h2 ▸ hF)
    exact ⟨h3, h4.trans h2⟩

/-- **Core side**: an invocation of a profile store never throws. -/
theorem throws_not_mem_behaviours {P : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (hF : FuncsOk s.funcs) (x : Nat) :
    Behaviour.throws x ∉ behaviours P closedHost s a vs := by
  rintro (⟨c', r, hsteps, hcode, hb⟩ | ⟨hb, _⟩)
  · have h0 : OkAdmins (invoke s a vs).code := by simp [invoke]
    obtain ⟨hok, _⟩ := okAdmins_steps hsteps h0 hF
    rw [hcode] at hok
    cases r with
    | values _ => simp [Result.toBehaviour] at hb
    | trap => simp [Result.toBehaviour] at hb
    | throw _ =>
      simp [Result.toAdmin, OkInstr, instrInProfile_flat', profileInstr] at hok
  · cases hb

/-! ## The native side -/

theorem evalFlat_not_throw {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {x : Nat}
    (h : evalFlat s f stk i = some (s', f', .throw x)) : False := by
  cases i
  case intBinOp t op =>
    simp only [evalFlat] at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, -, b, -, h⟩ := h
      split at h <;> simp at h
    · simp at h
  all_goals simp only [evalFlat] at h
  all_goals (repeat' split at h)
  all_goals simp_all [Option.map_eq_some_iff, Option.bind_eq_some_iff]

/-- The interpreter never produces a throw (there is no throwing instruction in
the profile it covers). -/
theorem eval_not_throw {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) : ∀ x, r.2.2 ≠ .throw x := by
  induction h with
  | nil => intro x; simp
  | argsAbort _ _ ih => exact ih
  | callOk _ _ _ _ _ _ _ _ _ ih => exact ih
  | callTrap => intro x; simp
  | callThrow _ _ _ _ _ _ ih => intro x _; exact ih _ rfl
  | opOk _ _ _ _ _ ih => exact ih
  | opStop _ _ hflat _ _ =>
    intro x hx
    simp only at hx
    subst hx
    exact evalFlat_not_throw hflat
  | blockOk _ _ _ _ _ ih => exact ih
  | blockBrk => intro x; simp
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ _ ih => exact ih
  | loopBack _ _ _ _ ih => exact ih
  | loopBrk => intro x; simp
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ _ _ _ _ ih => exact ih
  | ifBrk => intro x; simp
  | ifEsc _ _ _ _ _ _ ih => exact ih
  | ifAbort _ _ ih => exact ih

theorem throws_not_mem_nbeh {s : Store H} {a : Nat} {vs : List Val} (x : Nat) :
    Behaviour.throws x ∉ nbeh s a vs := by
  rintro (⟨fuel, s', fl, hrun, hb⟩ | ⟨hb, _⟩)
  · cases fl <;> simp [flowBeh] at hb
    subst hb
    unfold invokeRun at hrun
    split at hrun <;> try simp at hrun
    split at hrun <;> try simp at hrun
    split at hrun <;> simp at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact eval_not_throw (eval_of_run ‹_›) _ rfl
  · cases hb

end Silmaril.Wasm.Binaryen
