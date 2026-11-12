module

public import Silmaril.Proofs.Wasm.Verify.Guard.Basic

/-!
# Guarded calls: every Core 3.0 step keeps the guard discipline

`Step.pair`: for every profile and every host returning results (values, a trap or an
exception), a step from a configuration satisfying the reachability invariant
`CfgIn G fs (GuardPl G B fs)` (with guarded function bodies, `BodiesGuarded`) keeps the guard
discipline: if the code follows `Chain` from a state in any suffix context, so does the new
code, and nested bodies keep following it (`DeepP`).

Most rules have the shape handled by `pair_flat`: the left-hand side has no exit and ends with
an element that is neither a guard nor an exit, and the right-hand side holds no bad call.
Exits (`trap`, `throw_ref`) make the rest of their sequence unconstrained (`pair_exit`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {G B : Nat → Prop} {fs : List Nat}

/-- Every Wasm function body in `G` is guarded. -/
def BodiesGuarded (G B : Nat → Prop) (fs : List Nat) (funcs : List (FuncInst H)) : Prop :=
  ∀ a fi code, G a → funcs[a]? = some fi → fi.code = .wasm code → Guarded B fs code.body

/-- What a step keeps of the guard discipline. -/
def PairPost (B : Nat → Prop) (fs : List Nat) (c c' : Config H) : Prop :=
  DeepP B fs c.code →
    (∀ st l, Chain B fs st (c.code ++ l) → Chain B fs st (c'.code ++ l)) ∧ DeepP B fs c'.code

/-! ## Shapes of rules -/

theorem finSt_other {st : PSt} (hst : st ≠ .ex) :
    ∀ {L : List Admin} {e : Admin}, (∀ x ∈ L, isExA x = false) → L.getLast? = some e →
      isGdA e = false → finSt st L = .other
  | [], _, _, he, _ => by cases he
  | [x], e, hex, he, hg => by
    have hxe : x = e := by simpa using he
    subst hxe
    simp [finSt, nextSt, hst, hex x (by simp), hg]
  | x :: y :: L, e, hex, he, hg => by
    have hx : nextSt x st ≠ .ex := by simp [nextSt, hst, hex x (by simp)]; split <;> simp
    have := finSt_other hx (L := y :: L) (fun z hz => hex z (by simp [hz])) (by simpa using he) hg
    simpa using this

/-- The common shape of rules. -/
theorem pair_flat {L R : List Admin} (hex : ∀ x ∈ L, isExA x = false) (hne : L ≠ [])
    (hgd : ∀ e, L.getLast? = some e → isGdA e = false) (hR : ∀ x ∈ R, ¬ isBadA B fs x) :
    ∀ st l, Chain B fs st (L ++ l) → Chain B fs st (R ++ l) := by
  intro st l h
  obtain ⟨e, he⟩ : ∃ e, L.getLast? = some e := Option.isSome_iff_exists.1
    (List.getLast?_isSome.2 hne)
  have hg : isGdA e = false := hgd e he
  rw [chain_append] at h ⊢
  refine ⟨chain_of_noBad hR st, ?_⟩
  by_cases hst : st = .ex
  · subst hst
    rw [finSt_ex]
    exact chain_ex l
  · have hL : finSt st L = .other := finSt_other hst hex he hg
    exact (hL ▸ h.2).mono (PSt.le_other _)

/-- A right-hand side starting with an exit. -/
theorem pair_exit {x : Admin} {R : List Admin} (hx : isExA x = true) (hxb : ¬ isBadA B fs x) :
    ∀ st l, Chain B fs st ((x :: R) ++ l) := by
  intro st l
  refine ⟨fun h => absurd h hxb, ?_⟩
  have hn : nextSt x st = .ex := by simp [nextSt, hx]
  rw [hn]
  exact chain_ex _

theorem pair_throwing (a : Nat) : ∀ st l, Chain B fs st (throwing a ++ l) := by
  intro st l
  refine ⟨fun h => h.elim, ?_⟩
  exact pair_exit (x := .plain .throwRef) rfl (by simp [isBadA, BadI]) _ l

theorem deepP_flat {R : List Admin} (hb : codeBodies R = []) (hc : codeConts R = []) :
    DeepP B fs R :=
  ⟨by simp [hb], by simp [hc]⟩

/-! ## Classification lemmas -/

@[simp] theorem isExA_ref (r : Ref) : isExA (.ref r) = false := rfl
@[simp] theorem isGdA_ref (r : Ref) : isGdA (.ref r) = false := rfl
@[simp] theorem isBadA_ref (r : Ref) : ¬ isBadA B fs (.ref r) := id
@[simp] theorem isBadA_trap : ¬ isBadA B fs .trap := id
@[simp] theorem isBadA_callRefType (d : DefType) : ¬ isBadA B fs (.callRefType d) := id
@[simp] theorem isBadA_returnCallRefType (d : DefType) : ¬ isBadA B fs (.returnCallRefType d) := id
@[simp] theorem isBadA_label (n : Nat) (k : List Instr) (b : List Admin) :
    ¬ isBadA B fs (.label n k b) := id
@[simp] theorem isBadA_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    ¬ isBadA B fs (.handler n cs b) := id
@[simp] theorem isBadA_frame (n : Nat) (f : Frame) (b : List Admin) :
    ¬ isBadA B fs (.frame n f b) := id
@[simp] theorem isExA_label (n : Nat) (k : List Instr) (b : List Admin) :
    isExA (.label n k b) = false := rfl
@[simp] theorem isExA_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    isExA (.handler n cs b) = false := rfl
@[simp] theorem isExA_frame (n : Nat) (f : Frame) (b : List Admin) : isExA (.frame n f b) = false :=
  rfl
@[simp] theorem isGdA_label (n : Nat) (k : List Instr) (b : List Admin) :
    isGdA (.label n k b) = false := rfl
@[simp] theorem isGdA_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    isGdA (.handler n cs b) = false := rfl
@[simp] theorem isGdA_frame (n : Nat) (f : Frame) (b : List Admin) : isGdA (.frame n f b) = false :=
  rfl

theorem isCallRef_class {c : Admin} (h : c.IsCallRef) :
    isExA c = false ∧ isGdA c = false ∧ ¬ isBadA B fs c := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCallRef]
  · rename_i i
    cases i <;> simp_all [isExA, isGdA, isBadA, BadI]
  · exact ⟨rfl, rfl⟩

theorem isReturnCallRef_class {c : Admin} (h : c.IsReturnCallRef) :
    isExA c = false ∧ isGdA c = false ∧ ¬ isBadA B fs c := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all [isExA, isGdA, isBadA, BadI]
  · exact ⟨rfl, rfl⟩

theorem retToCallIn_noBad {c : Admin} (m : ModuleInst) (h : c.IsReturnCallRef) :
    ¬ isBadA B fs (c.retToCallIn m) := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCallIn]
  rename_i i
  cases i <;> simp_all
  split <;> simp [isBadA, BadI]

theorem toAdmin_noBad (r : Result) : ∀ x ∈ r.toAdmin, ¬ isBadA B fs x := by
  cases r with
  | values vs =>
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact isBadA_toAdmin v
  | throw a => simp [Result.toAdmin, isBadA, BadI]
  | trap => simp [Result.toAdmin]

/-! ## The families -/

theorem isBadA_plain_iff {i : Instr} : isBadA B fs (.plain i) ↔ BadI B fs i := Iff.rfl

/-- Split an elementwise goal over an explicit code list. -/
macro "verify_mem_split" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.forall_mem_append, vals, List.forall_mem_map,
    List.forall_mem_singleton, List.not_mem_nil, List.forall_mem_replicate, false_imp_iff,
    implies_true, and_true, true_and]
  try and_intros))

/-- One element is not an exit. -/
macro "verify_ex_one" : tactic => `(tactic| first
  | rfl
  | exact isExA_toAdmin _)

/-- One element is not an exit (possibly under binders). -/
macro "verify_ex_elem" : tactic => `(tactic| first
  | verify_ex_one
  | (intro _ _; verify_ex_one)
  | (intro _; verify_ex_one)
  | trivial)

/-- One element is not a bad call. -/
macro "verify_bad_one" : tactic => `(tactic| first
  | exact isBadA_toAdmin _
  | exact isBadA_ref _
  | exact isBadA_trap
  | exact isBadA_callRefType _
  | exact isBadA_returnCallRefType _
  | (simp only [store8, load8u, isBadA_plain_iff, BadI]; simp))

/-- One element is not a bad call (possibly under binders). -/
macro "verify_bad_elem" : tactic => `(tactic| first
  | verify_bad_one
  | exact .inr (isBadA_toAdmin _)
  | (intro _ _; verify_bad_one)
  | (intro _; verify_bad_one)
  | trivial)

/-- Close a `PairPost` goal of the common shape on explicit code lists. -/
macro "verify_flat_tac" : tactic => `(tactic| (
  refine fun _ => ⟨pair_flat ?_ (by simp) ?_ ?_, deepP_flat ?_ ?_⟩
  · verify_mem_split
    all_goals verify_ex_elem
  · intro e he
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, List.getLast?_append,
      List.getLast?_cons, Option.some.injEq, Option.some_or] at he
    subst he
    rfl
  · verify_mem_split
    all_goals verify_bad_elem
  · simp [constI32, Val.i32, aconst, vconst, arrRef, store8, load8u]
  · simp [constI32, Val.i32, aconst, vconst, arrRef, store8, load8u]))

theorem ParametricStep.pair {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ParametricStep is is') : PairPost B fs (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> verify_flat_tac

section
variable {P : Profile}

theorem NumericStep.pair {s : Store H} {f : Frame} {is is' : List Admin}
    (h : NumericStep P is is') : PairPost B fs (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> verify_flat_tac

theorem VectorStep.pair {s : Store H} {f : Frame} {is is' : List Admin}
    (h : VectorStep P is is') : PairPost B fs (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> verify_flat_tac

theorem VariableStep.pair {c c' : Config H} (h : VariableStep c c') : PairPost B fs c c' := by
  cases h <;> verify_flat_tac

theorem TableStep.pair {c c' : Config H} (h : TableStep P c c') : PairPost B fs c c' := by
  cases h <;> verify_flat_tac

theorem MemoryStep.pair {c c' : Config H} (h : MemoryStep P c c') : PairPost B fs c c' := by
  cases h <;> verify_flat_tac

theorem RefStep.pair {c c' : Config H} (h : RefStep c c') : PairPost B fs c c' := by
  cases h <;> verify_flat_tac

theorem AggregateStep.pair {c c' : Config H} (h : AggregateStep c c') : PairPost B fs c c' := by
  cases h <;> verify_flat_tac

end

/-! ## Context rules -/

theorem deepP_append {l₁ l₂ : List Admin} :
    DeepP B fs (l₁ ++ l₂) ↔ DeepP B fs l₁ ∧ DeepP B fs l₂ := by
  simp only [DeepP, codeBodies_append, codeConts_append, List.mem_append]
  constructor
  · intro h
    exact ⟨⟨fun b hb => h.1 b (.inl hb), fun k hk => h.2 k (.inl hk)⟩,
      ⟨fun b hb => h.1 b (.inr hb), fun k hk => h.2 k (.inr hk)⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun b hb => hb.elim (h₁.1 b) (h₂.1 b), fun k hk => hk.elim (h₁.2 k) (h₂.2 k)⟩

theorem deepP_vals (vs : List Val) : DeepP B fs (vals vs) := deepP_flat (by simp) (by simp)

theorem chain_vals_append {st : PSt} {vs : List Val} {l : List Admin} :
    Chain B fs st (vals vs ++ l) ↔ Chain B fs (finSt st (vals vs)) l := by
  rw [chain_append]
  exact ⟨fun h => h.2, fun h => ⟨chain_of_noBad (fun x hx => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact isBadA_toAdmin v) st, h⟩⟩

theorem pair_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (ih : PairPost B fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    PairPost B fs (⟨s, f, vals vs ++ is ++ rest⟩ : Config H) ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro hd
  have hd₁ : DeepP B fs is ∧ DeepP B fs rest :=
    ⟨(deepP_append.1 (deepP_append.1 hd).1).2, (deepP_append.1 hd).2⟩
  obtain ⟨hch, hd'⟩ := ih hd₁.1
  refine ⟨fun st l h => ?_, deepP_append.2 ⟨deepP_append.2 ⟨deepP_vals vs, hd'⟩, hd₁.2⟩⟩
  have h₁ : Chain B fs (finSt st (vals vs)) (is ++ (rest ++ l)) := by
    simpa only [List.append_assoc, chain_vals_append] using h
  have h₂ : Chain B fs (finSt st (vals vs)) (is' ++ (rest ++ l)) := hch _ _ h₁
  simpa only [List.append_assoc, chain_vals_append] using h₂

/-- A single structured element: its successor state does not depend on its body. -/
theorem chain_single {x y : Admin} (hby : ¬ isBadA B fs y)
    (hex : isExA x = isExA y) (hgd : isGdA x = isGdA y) :
    ∀ st l, Chain B fs st ([x] ++ l) → Chain B fs st ([y] ++ l) := by
  intro st l h
  refine ⟨fun hb => absurd hb hby, ?_⟩
  have hn : nextSt y st = nextSt x st := by simp [nextSt, hex, hgd]
  rw [hn]
  exact h.2

theorem pair_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : PairPost B fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    PairPost B fs (⟨s, f, [.label n cont is]⟩ : Config H) ⟨s', f', [.label n cont is']⟩ := by
  intro hd
  have hb : Chain B fs .other is := hd.1 is (by simp)
  have hdi : DeepP B fs is :=
    ⟨fun b hb' => hd.1 b (by simp [hb']), fun k hk => hd.2 k (by simp [hk])⟩
  obtain ⟨hch, hd'⟩ := ih hdi
  have hb' : Chain B fs .other is' := by simpa using hch .other [] (by simpa using hb)
  refine ⟨chain_single (by simp) rfl rfl, ⟨fun b hb'' => ?_, fun k hk => ?_⟩⟩
  · simp only [codeBodies_label, codeBodies_nil, List.append_nil, List.mem_cons] at hb''
    rcases hb'' with rfl | hb''
    · exact hb'
    · exact hd'.1 b hb''
  · simp only [codeConts_label, codeConts_nil, List.append_nil, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hd.2 _ (by simp)
    · exact hd'.2 k hk

theorem pair_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : PairPost B fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    PairPost B fs (⟨s, f, [.handler n cs is]⟩ : Config H) ⟨s', f', [.handler n cs is']⟩ := by
  intro hd
  have hb : Chain B fs .other is := hd.1 is (by simp)
  have hdi : DeepP B fs is :=
    ⟨fun b hb' => hd.1 b (by simp [hb']), fun k hk => hd.2 k (by simp [hk])⟩
  obtain ⟨hch, hd'⟩ := ih hdi
  have hb' : Chain B fs .other is' := by simpa using hch .other [] (by simpa using hb)
  refine ⟨chain_single (by simp) rfl rfl, ⟨fun b hb'' => ?_, fun k hk => ?_⟩⟩
  · simp only [codeBodies_handler, codeBodies_nil, List.append_nil, List.mem_cons] at hb''
    rcases hb'' with rfl | hb''
    · exact hb'
    · exact hd'.1 b hb''
  · simp only [codeConts_handler, codeConts_nil, List.append_nil] at hk
    exact hd'.2 k hk

theorem pair_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : PairPost B fs (⟨s, fi, is⟩ : Config H) ⟨s', fi', is'⟩) :
    PairPost B fs (⟨s, f, [.frame n fi is]⟩ : Config H) ⟨s', f, [.frame n fi' is']⟩ := by
  intro hd
  have hb : Chain B fs .other is := hd.1 is (by simp)
  have hdi : DeepP B fs is :=
    ⟨fun b hb' => hd.1 b (by simp [hb']), fun k hk => hd.2 k (by simp [hk])⟩
  obtain ⟨hch, hd'⟩ := ih hdi
  have hb' : Chain B fs .other is' := by simpa using hch .other [] (by simpa using hb)
  refine ⟨chain_single (by simp) rfl rfl, ⟨fun b hb'' => ?_, fun k hk => ?_⟩⟩
  · simp only [codeBodies_frame, codeBodies_nil, List.append_nil, List.mem_cons] at hb''
    rcases hb'' with rfl | hb''
    · exact hb'
    · exact hd'.1 b hb''
  · simp only [codeConts_frame, codeConts_nil, List.append_nil] at hk
    exact hd'.2 k hk

/-! ## Rules creating bodies, exits and calls -/

theorem lastVals_ex {vs : List Val} {x : Admin} (hx : isExA x = false) :
    ∀ y ∈ vals vs ++ [x], isExA y = false := by
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
    exact isExA_toAdmin v
  · exact (List.mem_singleton.1 hy) ▸ hx

theorem lastVals_gd {vs : List Val} {x : Admin} (hx : isGdA x = false) :
    ∀ e, (vals vs ++ [x]).getLast? = some e → isGdA e = false := by
  intro e he
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at he
  exact he ▸ hx

theorem pair_newBody {s : Store H} {f : Frame} {vs : List Val} {x y : Admin} (hx : isExA x = false)
    (hxg : isGdA x = false)
    (hy : ¬ isBadA B fs y) (hd : DeepP B fs [y]) :
    PairPost B fs (⟨s, f, vals vs ++ [x]⟩ : Config H) ⟨s, f, [y]⟩ :=
  fun _ => ⟨pair_flat (lastVals_ex hx) (by simp) (lastVals_gd hxg)
    (fun z hz => (List.mem_singleton.1 hz) ▸ hy), hd⟩

theorem deepP_label_body {n : Nat} {k : List Instr} {vs : List Val} {b : List Instr}
    (hk : ∀ i ∈ k, ¬ BadI B fs i) (hb : Guarded B fs b) :
    DeepP B fs [.label n k (vals vs ++ expression b)] := by
  refine ⟨fun b' hb' => ?_, fun k' hk' => ?_⟩
  · simp only [codeBodies_label, codeBodies_append, codeBodies_vals, codeBodies_expression,
      List.append_nil, codeBodies_nil, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rw [hb', chain_vals_append]
    exact chain_expression hb _
  · simp only [codeConts_label, codeConts_append, codeConts_vals, codeConts_expression,
      List.append_nil, codeConts_nil, List.mem_cons, List.not_mem_nil, or_false] at hk'
    exact hk' ▸ hk

theorem pair_block {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {body : List Instr}
    {n : Nat} (hpl : PlOK (GuardPl G B fs) (.block bt body)) :
    PairPost B fs (⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ : Config H)
      ⟨s, f, [.label n [] (vals vs ++ expression body)]⟩ :=
  pair_newBody rfl rfl (by simp) (deepP_label_body (by simp) hpl.guarded_block)

theorem pair_loop {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {body : List Instr}
    {n : Nat} (hpl : PlOK (GuardPl G B fs) (.loop bt body)) :
    PairPost B fs (⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ : Config H)
      ⟨s, f, [.label n [.loop bt body] (vals vs ++ expression body)]⟩ :=
  pair_newBody rfl rfl (by simp) (deepP_label_body (by simp [BadI]) hpl.guarded_loop)

theorem pair_tryTable {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {n : Nat} (hpl : PlOK (GuardPl G B fs) (.tryTable bt cs body)) :
    PairPost B fs (⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩ : Config H)
      ⟨s, f, [.handler n cs [.label n [] (vals vs ++ expression body)]]⟩ := by
  refine pair_newBody rfl rfl (by simp) ⟨fun b hb => ?_, fun k hk => ?_⟩
  · have hd : DeepP B fs [.label n [] (vals vs ++ expression body)] :=
      deepP_label_body (by simp) hpl.guarded_tryTable
    simp only [codeBodies_handler, codeBodies_nil, List.append_nil, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact chain_of_noBad (by simp) _
    · exact hd.1 b hb
  · have hd : DeepP B fs [.label n [] (vals vs ++ expression body)] :=
      deepP_label_body (by simp) hpl.guarded_tryTable
    simp only [codeConts_handler, codeConts_nil, List.append_nil] at hk
    exact hd.2 k hk

theorem lastRef_ex {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    ∀ y ∈ vals vs ++ [.ref (.func a), c], isExA y = false := by
  intro y hy
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with hy | rfl | rfl
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
    exact isExA_toAdmin v
  · rfl
  · exact (isCallRef_class (B := fun _ => False) (fs := []) hc).1

theorem lastRef_gd {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    ∀ e, (vals vs ++ [.ref (.func a), c]).getLast? = some e → isGdA e = false := by
  intro e he
  simp only [List.getLast?_append, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at he
  exact he ▸ (isCallRef_class (B := fun _ => False) (fs := []) hc).2.1

theorem deepP_frameBody {k : Nat} {fr : Frame} {code : Func} (hg : Guarded B fs code.body) :
    DeepP B fs [.frame k fr [.label k [] (expression code.body)]] := by
  have hd : DeepP B fs [.label k [] (vals [] ++ expression code.body)] :=
    deepP_label_body (by simp) hg
  refine ⟨fun b hb => ?_, fun k' hk => ?_⟩
  · simp only [codeBodies_frame, codeBodies_nil, List.append_nil, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact chain_of_noBad (by simp) _
    · exact hd.1 b (by simpa [vals] using hb)
  · simp only [codeConts_frame, codeConts_nil, List.append_nil] at hk
    exact hd.2 k' (by simpa [vals] using hk)

theorem pair_callRefFunc {s : Store H} {f fr : Frame} {c : Admin} {vs : List Val} {a k : Nat}
    {code : Func} (hc : c.IsCallRef) (hg : Guarded B fs code.body) :
    PairPost B fs (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H)
      ⟨s, f, [.frame k fr [.label k [] (expression code.body)]]⟩ :=
  fun _ => ⟨pair_flat (lastRef_ex hc) (by simp) (lastRef_gd hc)
    (by simp), deepP_frameBody hg⟩

theorem pair_brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs' vs : List Val}
    {l : LabelIdx} {rest : List Admin} :
    PairPost B fs (⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩ :
      Config H) ⟨s, f, vals vs ++ expression cont⟩ := by
  intro hd
  have hk : ∀ i ∈ cont, ¬ BadI B fs i := hd.2 cont (by simp)
  refine ⟨pair_flat (by simp) (by simp) (by simp) ?_, deepP_flat (by simp) (by simp)⟩
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact isBadA_toAdmin v
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hk i hi

theorem pair_exitR {c c' : Config H} {x : Admin} {R : List Admin} (hc' : c'.code = x :: R)
    (hx : isExA x = true) (hxb : ¬ isBadA B fs x) (hd : DeepP B fs c'.code) : PairPost B fs c c' :=
  fun _ => ⟨fun st l _ => hc' ▸ pair_exit hx hxb st l, hd⟩

theorem pair_throwingR {c : Config H} {s : Store H} {f : Frame} (a : Nat) :
    PairPost B fs c ⟨s, f, throwing a⟩ :=
  fun _ => ⟨fun st l _ => pair_throwing a st l, deepP_flat (by simp) (by simp)⟩

theorem pair_host {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {r : Result}
    (hc : c.IsCallRef) :
    PairPost B fs (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H) ⟨s', f, r.toAdmin⟩ :=
  fun _ => ⟨pair_flat (lastRef_ex hc) (by simp)
    (lastRef_gd hc) (toAdmin_noBad r),
    by cases r <;> exact deepP_flat (by simp [Result.toAdmin]) (by simp [Result.toAdmin])⟩

/-- Leaving a label, handler or frame with values and a non-bad element. -/
theorem pair_leave {c c' : Config H} {y : Admin} {vs : List Val} (hL : c.code ≠ [])
    (hex : ∀ x ∈ c.code, isExA x = false) (hgd : ∀ e, c.code.getLast? = some e → isGdA e = false)
    (hc' : c'.code = vals vs ++ [y]) (hy : ¬ isBadA B fs y) (hyd : DeepP B fs [y]) :
    PairPost B fs c c' := by
  refine fun _ => ⟨hc' ▸ pair_flat hex hL hgd ?_, hc' ▸ deepP_append.2 ⟨deepP_vals vs, hyd⟩⟩
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact isBadA_toAdmin v
  · exact (List.mem_singleton.1 hx) ▸ hy

theorem isReturnCallRef_flat {x : Admin} (hx : x.IsReturnCallRef) :
    codeBodies [x] = [] ∧ codeConts [x] = [] := by
  cases x <;> simp_all [Admin.IsReturnCallRef]

theorem retToCallIn_flat {c : Admin} (m : ModuleInst) (hc : c.IsReturnCallRef) :
    codeBodies [c.retToCallIn m] = [] ∧ codeConts [c.retToCallIn m] = [] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all [Admin.retToCallIn]
    split <;> simp
  · simp [Admin.retToCallIn]

theorem pair_returnFrame {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    PairPost B fs (⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩ :
      Config H) ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  refine fun _ => ⟨pair_flat (by simp) (by simp) (by simp) ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      exact isBadA_toAdmin v
    · exact isBadA_ref _
    · exact retToCallIn_noBad _ hc
  · obtain ⟨h₁, h₂⟩ := retToCallIn_flat fi.module hc
    exact deepP_flat (by simp [h₁]) (by simp [h₂])

theorem pair_retLabel {c c' : Config H} {x : Admin} {vs : List Val} (hx : x.IsReturnCallRef)
    (hL : ∃ y, c.code = [y] ∧ isExA y = false ∧ isGdA y = false) (hc' : c'.code = vals vs ++ [x]) :
    PairPost B fs c c' := by
  obtain ⟨y, hy, hyx, hyg⟩ := hL
  obtain ⟨-, -, hxb⟩ := isReturnCallRef_class (B := B) (fs := fs) hx
  obtain ⟨h₁, h₂⟩ := isReturnCallRef_flat hx
  exact pair_leave (by simp [hy]) (by simp [hy, hyx]) (by simp [hy, hyg]) hc' hxb
    (deepP_flat h₁ h₂)

theorem pair_callRefFunc' {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a k : Nat}
    {fi : FuncInst H} {code : Func} (hcr : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code)
    (hc : CfgIn G fs (GuardPl G B fs) (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H))
    (hbg : BodiesGuarded G B fs s.funcs) {fr : Frame} :
    PairPost B fs (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H)
      ⟨s, f, [.frame k fr [.label k [] (expression code.body)]]⟩ := by
  have ha : G a := by simpa using hc.2.2.ref_of_mem (r := .func a) (by simp)
  exact pair_callRefFunc hcr (hbg a fi code ha hf hcode)

theorem pair_handlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch}
    {a : Nat} : PairPost B fs (⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ : Config H)
      ⟨s, f, [.handler n cs (throwing a)]⟩ := by
  refine fun _ => ⟨pair_flat (by simp) (by simp) (by simp) (by simp), fun b hb => ?_,
    fun k hk => by simp at hk⟩
  simp only [codeBodies_handler, codeBodies_nil, List.append_nil, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact chain_of_noBad (by simp [isBadA, BadI]) _
  · simp at hb

set_option linter.unusedTactic false in
/-- **Every Core 3.0 step keeps the guard discipline** (every profile, every host). -/
theorem Step.pair {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hc : CfgIn G fs (GuardPl G B fs) c)
    (hbg : BodiesGuarded G B fs c.store.funcs) : PairPost B fs c c' := by
  induction h with
  | parametric h => exact ParametricStep.pair h
  | numeric h => exact NumericStep.pair h
  | vector h => exact VectorStep.pair h
  | «variable» h => exact VariableStep.pair h
  | table h => exact TableStep.pair h
  | memory h => exact MemoryStep.pair h
  | reference h => exact RefStep.pair h
  | aggregate h => exact AggregateStep.pair h
  | ctxtInstrs _ _ ih =>
    exact pair_ctxtInstrs (ih ⟨hc.1, hc.2.1, (CodeIn.append.1 (CodeIn.append.1 hc.2.2).1).2⟩ hbg)
  | ctxtLabel _ ih => exact pair_ctxtLabel (ih ⟨hc.1, hc.2.1, (CodeIn.label_iff.1 hc.2.2).2⟩ hbg)
  | ctxtHandler _ ih => exact pair_ctxtHandler (ih ⟨hc.1, hc.2.1, CodeIn.handler_iff.1 hc.2.2⟩ hbg)
  | ctxtFrame _ ih =>
    exact pair_ctxtFrame
      (ih ⟨hc.1, (CodeIn.frame_iff.1 hc.2.2).1, (CodeIn.frame_iff.1 hc.2.2).2⟩ hbg)
  | block => exact pair_block hc.2.2.last_plain
  | loop => exact pair_loop hc.2.2.last_plain
  | tryTable => exact pair_tryTable hc.2.2.last_plain
  | brLabelZero => exact pair_brLabelZero
  | callRefFunc hcr hf _ _ hcode => exact pair_callRefFunc' hcr hf hcode hc hbg
  | callRefHost hcr => exact pair_host hcr
  | callRefHostDiv => exact fun hd => ⟨fun _ _ h => h, hd⟩
  | throw => exact pair_throwingR _
  | throwRefInstrs => exact pair_throwingR _
  | throwRefLabel => exact pair_throwingR _
  | throwRefFrame => exact pair_throwingR _
  | throwRefHandlerEmpty => exact pair_throwingR _
  | returnCallRefLabel hcr => exact pair_retLabel hcr ⟨_, rfl, rfl, rfl⟩ rfl
  | returnCallRefHandler hcr => exact pair_retLabel hcr ⟨_, rfl, rfl, rfl⟩ rfl
  | returnCallRefFrameAddr hcr => exact pair_returnFrame hcr
  | throwRefHandlerNext => exact pair_handlerNext
  | _ =>
    first
      | (exact pair_exitR rfl rfl (by simp) (deepP_flat (by simp) (by simp)); done)
      | (verify_flat_tac; done)

end Silmaril.Wasm.Verify
