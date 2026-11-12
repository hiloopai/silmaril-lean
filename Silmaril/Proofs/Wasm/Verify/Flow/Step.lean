module

public import Silmaril.Proofs.Wasm.Verify.Flow.Basic
public import Silmaril.Proofs.Wasm.Verify.Guard.Step

/-!
# The flow analysis: preservation by every Core step

`FlowPost bad fs c c'` says what a step `c ⟶ c'` keeps of the flow invariant, for every list `K`
of stable locals of the frame of `c`: facts sound for the old frame stay sound (stable locals
are only ever written with nonzero `i32`s), the check of every continuation of the code (in a
surrounding sequence, from a sound state) is kept with possibly more facts, and the nested bodies
of the new code are checked. `Step.flow` proves it for every Core 3.0 rule, every profile, every
host, by induction on `Step`:

* most rules replace a flat left-hand side ending with an instruction whose successor state is
  `other` by elements without requirement (`flow_flat`);
* `local.get` may add its local to the facts, `local.set` changes the frame (`flow_localGet`,
  `flow_localSet`), `local.tee` (`flow_localTee`);
* `if` (`flow_ifTrue`, `flow_ifFalse`), `block`, `loop` and `try_table` create bodies checked from
  the current facts; a call of a Wasm function creates a frame body checked from the empty state
  (`BodiesFlow`); branches to a label run its continuation (`flow_brLabelZero`);
* the context rules (`flow_ctxtInstrs`, `flow_ctxtLabel`, `flow_ctxtHandler`, `flow_ctxtFrame`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {bad : Nat → Bool} {fs : List Nat}

/-- What a step keeps of the flow invariant (see the module docstring). -/
def FlowPost (bad : Nat → Bool) (fs : List Nat) (c c' : Config H) : Prop :=
  ∀ (K S : List Nat) (t : Top) (l : List Admin), t ≠ .ex → Sound c.frame K S →
    okA K bad fs ⟨S, t⟩ (c.code ++ l) = true →
    (∀ b ∈ scopeSeqs c.code, SeqOK K bad fs c.frame b) → FramesOK bad fs c.code →
    (∀ S₀, Sound c.frame K S₀ → Sound c'.frame K S₀) ∧
    (∃ S', (∀ k ∈ S, k ∈ S') ∧ Sound c'.frame K S' ∧
      okA K bad fs ⟨S', t⟩ (c'.code ++ l) = true) ∧
    (∀ b ∈ scopeSeqs c'.code, SeqOK K bad fs c'.frame b) ∧ FramesOK bad fs c'.code

/-! ## Classes of elements -/

/-- An element whose successor state is `other`, keeping the facts. -/
def OtherX (x : Admin) : Prop := ∀ (K : List Nat) (st : FSt), nextX K st x = ⟨st.S, .other⟩

/-- An element that keeps the facts and never ends the sequence. -/
def FlatX (x : Admin) : Prop :=
  ∀ (K : List Nat) (st : FSt), (nextX K st x).S = st.S ∧ (nextX K st x).top ≠ .ex

/-- An element without requirement. -/
def TrivX (x : Admin) : Prop :=
  ∀ (K : List Nat) (bad : Nat → Bool) (fs : List Nat) (st : FSt), okX K bad fs st x = true

theorem flatX_of_other {x : Admin} (h : OtherX x) : FlatX x := fun K st => by
  rw [h K st]
  exact ⟨rfl, nofun⟩

theorem flatX_toAdmin (v : Val) : FlatX v.toAdmin := fun K st => by
  rw [nextX_toAdmin]
  exact ⟨rfl, topOfVal_ne_ex v⟩

theorem trivX_toAdmin (v : Val) : TrivX v.toAdmin := fun _ _ _ st => okX_toAdmin st v

theorem topOfConst_ne_ex (i : Instr) : topOfConst i ≠ .ex := by
  unfold topOfConst
  split
  · split <;> exact nofun
  · exact nofun

theorem flatX_intConst (t : IntType) (c : BitVec t.width) : FlatX (.plain (.intConst t c)) :=
  fun _ _ => ⟨rfl, topOfConst_ne_ex _⟩

theorem flatX_floatConst (t : FloatType) (c : BitVec t.width) :
    FlatX (.plain (.floatConst t c)) :=
  fun _ _ => ⟨rfl, nofun⟩

theorem flatX_vecConst (c : BitVec 128) : FlatX (.plain (.vecConst c)) :=
  fun _ _ => ⟨rfl, nofun⟩

theorem flatX_ref (r : Ref) : FlatX (.ref r) := fun _ _ => ⟨rfl, nofun⟩

theorem isCallRef_flow {c : Admin} (h : c.IsCallRef) : OtherX c ∧ TrivX c := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCallRef]
  · rename_i i
    cases i <;> simp_all
    exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem isReturnCallRef_flow {c : Admin} (h : c.IsReturnCallRef) : OtherX c ∧ TrivX c := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all
    exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem retToCallIn_flow {c : Admin} (m : ModuleInst) (h : c.IsReturnCallRef) :
    TrivX (c.retToCallIn m) := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all [Admin.retToCallIn]
    split
    · exact fun _ _ _ _ => rfl
    · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ => rfl

/-! ## Flat rules -/

theorem finA_flat {K : List Nat} {S : List Nat} :
    ∀ {L : List Admin} {t : Top}, (∀ x ∈ L, FlatX x) → L ≠ [] →
      (∀ e, L.getLast? = some e → OtherX e) → t ≠ .ex → finA K ⟨S, t⟩ L = ⟨S, .other⟩
  | [], _, _, hne, _, _ => absurd rfl hne
  | [x], t, _, _, hlast, ht => by
    simp only [finA, ht, ↓reduceIte]
    exact hlast x rfl K _
  | x :: y :: L, t, hL, _, hlast, ht => by
    have hx : (nextX K ⟨S, t⟩ x).S = S ∧ (nextX K ⟨S, t⟩ x).top ≠ .ex := hL x (by simp) K _
    generalize hn : nextX K ⟨S, t⟩ x = n at hx
    obtain ⟨S₁, t₁⟩ := n
    obtain ⟨hS₁, ht₁⟩ := hx
    have hS₁' : S₁ = S := hS₁
    subst hS₁'
    simp only [finA, ht, ↓reduceIte, hn]
    exact finA_flat (fun z hz => hL z (List.mem_cons_of_mem _ hz)) (by simp)
      (fun e he => hlast e (by simpa using he)) ht₁

theorem okA_triv {K : List Nat} : ∀ {R : List Admin} (st : FSt), (∀ x ∈ R, TrivX x) →
    okA K bad fs st R = true
  | [], _, _ => by simp [okA]
  | x :: R, st, hR => by
    have h₁ : okX K bad fs st x = true := hR x (by simp) K bad fs st
    have h₂ : okA K bad fs (nextX K st x) R = true :=
      okA_triv _ (fun y hy => hR y (List.mem_cons_of_mem _ hy))
    simp [okA, h₁, h₂]

/-- The chain of a flat rule. -/
theorem okA_flat {K S : List Nat} {t : Top} {L R l : List Admin} (hL : ∀ x ∈ L, FlatX x)
    (hne : L ≠ []) (hlast : ∀ e, L.getLast? = some e → OtherX e) (hR : ∀ x ∈ R, TrivX x)
    (ht : t ≠ .ex) (h : okA K bad fs ⟨S, t⟩ (L ++ l) = true) :
    okA K bad fs ⟨S, t⟩ (R ++ l) = true := by
  have h₁ : okA K bad fs (finA K ⟨S, t⟩ L) l = true := ((okA_append _ L l).1 h).2
  have h₂ : okA K bad fs ⟨S, .other⟩ l = true := by
    rwa [finA_flat hL hne hlast ht] at h₁
  exact (okA_append _ R l).2 ⟨okA_triv _ hR, okA_mono l (fle_finA ⟨S, t⟩ R) h₂⟩

/-- **The common shape of rules**: a flat left-hand side ending with an element whose successor
state is `other`, replaced (same frame) by elements without requirement and without bodies. -/
theorem flow_flat {s s' : Store H} {f : Frame} {L R : List Admin} (hL : ∀ x ∈ L, FlatX x)
    (hne : L ≠ []) (hlast : ∀ e, L.getLast? = some e → OtherX e) (hR : ∀ x ∈ R, TrivX x)
    (hb : codeBodies R = []) : FlowPost bad fs (⟨s, f, L⟩ : Config H) ⟨s', f, R⟩ := by
  intro K S t l ht hS h _ _
  obtain ⟨hs, hfr⟩ := scopes_of_codeBodies hb
  refine ⟨fun _ h => h, ⟨S, fun _ h => h, hS, okA_flat hL hne hlast hR ht h⟩, ?_, ?_⟩
  · intro b hb'
    simp only [hs, List.not_mem_nil] at hb'
  · intro p hp
    simp only [hfr, List.not_mem_nil] at hp

/-- A right-hand side whose first elements end the sequence. -/
theorem okA_exitR {K S : List Nat} {t : Top} {x : Admin} {R l : List Admin}
    (hx : ∀ st : FSt, (nextX K st x).top = .ex) (hxt : TrivX x) :
    okA K bad fs ⟨S, t⟩ ((x :: R) ++ l) = true := by
  have h₁ : okA K bad fs (nextX K ⟨S, t⟩ x) (R ++ l) = true := by
    have hS : nextX K ⟨S, t⟩ x = ⟨(nextX K ⟨S, t⟩ x).S, .ex⟩ := by rw [← hx ⟨S, t⟩]
    rw [hS]
    exact okA_ex _
  simp [okA, hxt K bad fs, h₁]

theorem flow_exitR {c : Config H} {s : Store H} {f : Frame} {x : Admin} {R : List Admin}
    (hf : c.frame = f) (hx : ∀ (K : List Nat) (st : FSt), (nextX K st x).top = .ex) (hxt : TrivX x)
    (hb : codeBodies (x :: R) = []) : FlowPost bad fs c ⟨s, f, x :: R⟩ := by
  intro K S t l _ hS _ _ _
  obtain ⟨hs, hfr⟩ := scopes_of_codeBodies hb
  refine ⟨fun _ h => hf ▸ h, ⟨S, fun _ h => h, hf ▸ hS, okA_exitR (hx K) hxt⟩, ?_, ?_⟩
  · intro b hb'
    simp only [hs, List.not_mem_nil] at hb'
  · intro p hp
    simp only [hfr, List.not_mem_nil] at hp

theorem flow_throwingR {c : Config H} {s : Store H} {f : Frame} (hf : c.frame = f) (a : Nat) :
    FlowPost bad fs c ⟨s, f, throwing a⟩ := by
  intro K S t l ht hS _ _ _
  have hch : okA K bad fs ⟨S, t⟩ (throwing a ++ l) = true := by
    have h₁ : okA K bad fs ⟨S, .nonI32⟩ ([.plain .throwRef] ++ l) = true :=
      okA_exitR (fun _ => rfl) (fun _ _ _ _ => rfl)
    simpa [throwing, okA, okX, nextX, ht] using h₁
  refine ⟨fun _ h => hf ▸ h, ⟨S, fun _ h => h, hf ▸ hS, hch⟩, ?_, ?_⟩
  · intro b hb
    simp [throwing] at hb
  · intro p hp
    simp [throwing] at hp

/-! ## Tactics for flat rules -/

/-- One element keeps the facts and does not end the sequence. -/
macro "flow_flat_one" : tactic => `(tactic| first
  | exact flatX_toAdmin _
  | exact flatX_intConst _ _
  | exact flatX_floatConst _ _
  | exact flatX_vecConst _
  | exact flatX_ref _
  | (intro _ _; exact flatX_ref _)
  | (intro _; exact flatX_ref _)
  | (intro _ _; exact flatX_intConst _ _)
  | (intro _; exact flatX_intConst _ _)
  | exact flatX_of_other (fun _ _ => rfl)
  | (intro _ _; exact flatX_toAdmin _)
  | (intro _; exact flatX_toAdmin _)
  | (intro _ _; exact flatX_of_other (fun _ _ => rfl))
  | (intro _; exact flatX_of_other (fun _ _ => rfl))
  | trivial)

/-- One element has no requirement. -/
macro "flow_triv_one" : tactic => `(tactic| first
  | exact trivX_toAdmin _
  | exact fun _ _ _ _ => rfl
  | (intro _ _; exact trivX_toAdmin _)
  | (intro _; exact trivX_toAdmin _)
  | (intro _ _; exact fun _ _ _ _ => rfl)
  | (intro _; exact fun _ _ _ _ => rfl)
  | exact .inr (trivX_toAdmin _)
  | trivial)

/-- Close a `FlowPost` goal of the common shape on explicit code lists. -/
macro "flow_flat_tac" : tactic => `(tactic| (
  refine flow_flat ?_ (by simp) ?_ ?_ ?_
  · verify_mem_split
    all_goals flow_flat_one
  · intro e he
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, List.getLast?_append,
      List.getLast?_cons, Option.some.injEq, Option.some_or] at he
    subst he
    exact fun _ _ => rfl
  · verify_mem_split
    all_goals flow_triv_one
  · simp [constI32, Val.i32, aconst, vconst, arrRef, store8, load8u]))

/-! ## The families -/

theorem ParametricStep.flow {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ParametricStep is is') : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> flow_flat_tac

section
variable {P : Profile}

theorem NumericStep.flow {s : Store H} {f : Frame} {is is' : List Admin}
    (h : NumericStep P is is') : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> flow_flat_tac

theorem VectorStep.flow {s : Store H} {f : Frame} {is is' : List Admin}
    (h : VectorStep P is is') : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> flow_flat_tac

theorem TableStep.flow {c c' : Config H} (h : TableStep P c c') : FlowPost bad fs c c' := by
  cases h <;> flow_flat_tac

theorem MemoryStep.flow {c c' : Config H} (h : MemoryStep P c c') : FlowPost bad fs c c' := by
  cases h <;> flow_flat_tac

theorem RefStep.flow {c c' : Config H} (h : RefStep c c') : FlowPost bad fs c c' := by
  cases h <;> flow_flat_tac

theorem AggregateStep.flow {c c' : Config H} (h : AggregateStep c c') : FlowPost bad fs c c' := by
  cases h <;> flow_flat_tac

end

/-! ## Locals -/

theorem okA_cons_val {K S : List Nat} {t : Top} (ht : t ≠ .ex) (v : Val) (l : List Admin) :
    okA K bad fs ⟨S, t⟩ (v.toAdmin :: l) = okA K bad fs ⟨S, topOfVal v⟩ l := by
  simp [okA, ht, nextX_toAdmin]

theorem topOfVal_gd {v : Val} (h : topOfVal v = .gd) : ∃ c : BitVec 32, v = Val.i32 c ∧ c ≠ 0 := by
  cases v with
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int t =>
      cases t
      · simp only [topOfVal] at h
        split at h
        · cases h
        · rename_i hne
          have hc : c ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
          exact ⟨c, rfl, hc⟩
      · cases h
    | float t => cases h
  | vec b => cases h
  | ref r => cases h

theorem topOfVal_i32_ne {c : BitVec 32} (hc : c ≠ 0) : topOfVal (Val.i32 c) = .gd := by
  show (if c == 0 then Top.zero else .gd) = _
  have hc' : (c == 0) = false := beq_eq_false_iff_ne.2 hc
  rw [hc']
  rfl

theorem topOfVal_i32 (c : BitVec 32) : topOfVal (Val.i32 c) = if c = 0 then .zero else .gd := by
  show (if c == 0 then Top.zero else .gd) = _
  by_cases h : c = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [beq_eq_false_iff_ne.2 h]
    rfl

/-- Writing a nonzero `i32` (or a local that is not stable) keeps facts sound. -/
theorem sound_setLocal {f : Frame} {K S : List Nat} {x : LocalIdx} {v : Val}
    (hv : x.toNat ∈ K → ∃ c : BitVec 32, v = Val.i32 c ∧ c ≠ 0) (hS : Sound f K S) :
    Sound (f.setLocal x v) K S := by
  intro k hk
  obtain ⟨hkK, c, hc, hc0⟩ := hS k hk
  refine ⟨hkK, ?_⟩
  by_cases hkx : k = x.toNat
  · subst hkx
    obtain ⟨c', rfl, hc'⟩ := hv hkK
    have hlt : x.toNat < f.locals.length := (List.getElem?_eq_some_iff.1 hc).1
    exact ⟨c', by simp [Frame.setLocal, List.getElem?_set_self hlt], hc'⟩
  · exact ⟨c, by simpa [Frame.setLocal, List.getElem?_set_ne (Ne.symm hkx)] using hc, hc0⟩

/-- The value of a local: a nonzero `i32`, or its top state is `zero` or `nonI32`. -/
theorem topOfVal_cases (v : Val) :
    (∃ c : BitVec 32, v = Val.i32 c ∧ c ≠ 0) ∨ topOfVal v = .zero ∨ topOfVal v = .nonI32 := by
  cases v with
  | num n =>
    obtain ⟨ty, c⟩ := n
    cases ty with
    | int it =>
      cases it
      · by_cases hc : c = 0
        · exact .inr (.inl (by subst hc; rfl))
        · exact .inl ⟨c, rfl, hc⟩
      · exact .inr (.inr rfl)
    | float _ => exact .inr (.inr rfl)
  | vec _ => exact .inr (.inr rfl)
  | ref _ => exact .inr (.inr rfl)

/-- Reading a local known to be nonzero. -/
theorem localGet_known {f : Frame} {K S : List Nat} {t : Top} {x : LocalIdx} {v : Val}
    (hloc : f.locals[x.toNat]? = some (some v)) (hS : Sound f K S) (hxS : x.toNat ∈ S) :
    FLe (nextI K ⟨S, t⟩ (.localGet x)) ⟨S, topOfVal v⟩ := by
  obtain ⟨-, c, hc, hc0⟩ := hS _ hxS
  have hvc : v = Val.i32 c := by
    have h := hloc.symm.trans hc
    simpa using h
  have htop : topOfVal v = .gd := by rw [hvc]; exact topOfVal_i32_ne hc0
  refine .inr ⟨fun _ h => h, .inl ?_⟩
  simp [nextI, hxS, htop]

/-- Reading a stable local not yet known to be nonzero. -/
theorem localGet_stable {f : Frame} {K S : List Nat} {t : Top} {x : LocalIdx} {v : Val}
    (hloc : f.locals[x.toNat]? = some (some v)) (hS : Sound f K S) (hxS : x.toNat ∉ S)
    (hxK : x.toNat ∈ K) :
    ∃ S', (∀ k ∈ S, k ∈ S') ∧ Sound f K S' ∧
      FLe (nextI K ⟨S, t⟩ (.localGet x)) ⟨S', topOfVal v⟩ := by
  have hnext : nextI K ⟨S, t⟩ (.localGet x) = ⟨S, .loc x.toNat⟩ := by
    simp [nextI, hxS, hxK]
  rw [hnext]
  rcases topOfVal_cases v with ⟨c, hvc, hc0⟩ | h | h
  · have hS' : Sound f K (x.toNat :: S) := by
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact ⟨hxK, c, by rw [hloc, hvc], hc0⟩
      · exact hS k hk
    have htop : topOfVal v = .gd := by rw [hvc]; exact topOfVal_i32_ne hc0
    exact ⟨_, fun _ h => List.mem_cons_of_mem _ h, hS', .inr ⟨fun _ h => List.mem_cons_of_mem _ h,
      .inr (.inr (.inl ⟨_, rfl, .inr (.inr ⟨htop, List.mem_cons_self⟩)⟩))⟩⟩
  · exact ⟨S, fun _ h => h, hS, .inr ⟨fun _ h => h, .inr (.inr (.inl ⟨_, rfl, .inl h⟩))⟩⟩
  · exact ⟨S, fun _ h => h, hS, .inr ⟨fun _ h => h, .inr (.inr (.inl ⟨_, rfl, .inr (.inl h)⟩))⟩⟩

/-- **The facts after reading a local.** -/
theorem localGet_facts {f : Frame} {K S : List Nat} {t : Top} {x : LocalIdx} {v : Val}
    (hloc : f.locals[x.toNat]? = some (some v)) (hS : Sound f K S) :
    ∃ S', (∀ k ∈ S, k ∈ S') ∧ Sound f K S' ∧
      FLe (nextI K ⟨S, t⟩ (.localGet x)) ⟨S', topOfVal v⟩ := by
  by_cases hxS : x.toNat ∈ S
  · exact ⟨S, fun _ h => h, hS, localGet_known hloc hS hxS⟩
  by_cases hxK : x.toNat ∈ K
  · exact localGet_stable hloc hS hxS hxK
  · have hnext : nextI K ⟨S, t⟩ (.localGet x) = ⟨S, .other⟩ := by
      simp [nextI, hxS, hxK]
    exact ⟨S, fun _ h => h, hS, hnext ▸ FLe.of_other (fun _ h => h) _⟩

/-- **`local.get`**: reading a stable local may add it to the facts. -/
theorem flow_localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.local? x = some (some v)) :
    FlowPost bad fs (⟨s, f, [.plain (.localGet x)]⟩ : Config H) ⟨s, f, [v.toAdmin]⟩ := by
  intro K S t l ht hS hch _ _
  have hl : okA K bad fs (nextI K ⟨S, t⟩ (.localGet x)) l = true := by
    simpa [okA, ht, okX, okI, reqI, isBadCall, isSetK, nextX] using hch
  obtain ⟨S', hsub, hS', hle⟩ := localGet_facts (t := t) hv hS
  have hok : okA K bad fs ⟨S', t⟩ ([v.toAdmin] ++ l) = true := by
    rw [List.singleton_append, okA_cons_val ht]
    exact okA_mono l hle hl
  obtain ⟨hs, hfr⟩ := scopes_of_codeBodies (l := [v.toAdmin]) (by simp)
  exact ⟨fun _ h => h, ⟨S', hsub, hS', hok⟩, by simp [hs], by simp [FramesOK, hfr]⟩

/-- **`local.set`**: a stable local is written with a nonzero `i32`, and becomes a fact. -/
theorem flow_localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) :
    FlowPost bad fs (⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ : Config H)
      ⟨s, f.setLocal x v, []⟩ := by
  intro K S t l ht hS hch _ _
  have h₁ : okA K bad fs ⟨S, topOfVal v⟩ (.plain (.localSet x) :: l) = true := by
    rw [← okA_cons_val ht]
    simpa using hch
  have h₂ : (!K.contains x.toNat || topOfVal v == .gd) = true ∧
      okA K bad fs ⟨addK K x.toNat S, .other⟩ l = true := by
    simpa [okA, topOfVal_ne_ex, okX, okI, reqI, isBadCall, isSetK, nextX, nextI] using h₁
  have hv : x.toNat ∈ K → ∃ c : BitVec 32, v = Val.i32 c ∧ c ≠ 0 := by
    intro hxK
    have hgd : topOfVal v = .gd := by simpa [hxK] using h₂.1
    exact topOfVal_gd hgd
  have hS' : Sound (f.setLocal x v) K (addK K x.toNat S) := by
    intro k hk
    unfold addK at hk
    split at hk
    · rename_i hxK
      rcases List.mem_cons.1 hk with rfl | hk
      · obtain ⟨c, rfl, hc0⟩ := hv (by simpa using hxK)
        exact ⟨by simpa using hxK, c, by simp [Frame.setLocal, List.getElem?_set_self hx], hc0⟩
      · exact sound_setLocal hv hS k hk
    · exact sound_setLocal hv hS k hk
  refine ⟨fun S₀ h => sound_setLocal hv h, ⟨_, subset_addK _, hS', ?_⟩, by simp, by simp [FramesOK]⟩
  exact okA_mono l (FLe.of_other (fun _ h => h) t) h₂.2

/-- **`local.tee`**: the same requirement and facts as the `local.set` it becomes. -/
theorem flow_localTee {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} :
    FlowPost bad fs (⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩ : Config H)
      ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ := by
  intro K S t l ht hS hch _ _
  have h₁ : okA K bad fs ⟨S, topOfVal v⟩ (.plain (.localTee x) :: l) = true := by
    rw [← okA_cons_val ht]
    simpa using hch
  have h₂ : okA K bad fs ⟨S, topOfVal v⟩ (.plain (.localSet x) :: l) = true := by
    simpa [okA, topOfVal_ne_ex, okX, okI, reqI, isBadCall, isSetK, nextX, nextI] using h₁
  have hok : okA K bad fs ⟨S, t⟩ ([v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ l) = true := by
    simp only [List.cons_append, List.nil_append, okA_cons_val ht, okA_cons_val (topOfVal_ne_ex v)]
    exact h₂
  have hb : codeBodies [v.toAdmin, v.toAdmin, .plain (.localSet x)] = [] := by simp
  obtain ⟨hs, hfr⟩ := scopes_of_codeBodies hb
  exact ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, by simp [hs], by simp [FramesOK, hfr]⟩

theorem VariableStep.flow {c c' : Config H} (h : VariableStep c c') : FlowPost bad fs c c' := by
  cases h with
  | localGet hv => exact flow_localGet hv
  | localSet hx => exact flow_localSet hx
  | localTee => exact flow_localTee
  | globalGet => flow_flat_tac
  | globalSet => flow_flat_tac

/-! ## Bodies -/

theorem scopes_body (vs : List Val) (body : List Instr) :
    scopeSeqs (vals vs ++ expression body) = [] ∧ frameScopes (vals vs ++ expression body) = [] :=
  scopes_of_codeBodies (by simp)

/-- A body run from the current facts. -/
theorem seqOK_body {f : Frame} {K S : List Nat} (hS : Sound f K S) {body : List Instr}
    (hb : okL K bad fs ⟨S, .other⟩ body = true) (vs : List Val) :
    SeqOK K bad fs f (vals vs ++ expression body) := by
  refine ⟨S, hS, ?_⟩
  rw [okA_vals_append (by exact nofun), okA_expression]
  exact okL_mono body (FLe.of_other (fun _ h => h) _) hb

/-- A new label around a checked body. -/
theorem flow_newLabel {s : Store H} {f : Frame} {vs : List Val} {i : Instr} {n : Nat}
    {cont body : List Instr} (hi : ∀ (K : List Nat) (st : FSt), nextI K st i = ⟨st.S, .other⟩)
    (hreq : ∀ (K : List Nat) (st : FSt), okI K bad fs st i = true →
      okL K bad fs ⟨st.S, .other⟩ cont = true ∧ okL K bad fs ⟨st.S, .other⟩ body = true) :
    FlowPost bad fs (⟨s, f, vals vs ++ [.plain i]⟩ : Config H)
      ⟨s, f, [.label n cont (vals vs ++ expression body)]⟩ := by
  intro K S t l ht hS hch _ _
  have h₁ : okA K bad fs ⟨S, (vs.getLast?.map topOfVal).getD t⟩ ([.plain i] ++ l) = true := by
    rw [← okA_vals_append ht]
    simpa only [List.append_assoc] using hch
  have h₂ : okI K bad fs ⟨S, (vs.getLast?.map topOfVal).getD t⟩ i = true ∧
      okA K bad fs ⟨S, .other⟩ l = true := by
    simpa [okA, topVals_ne_ex ht, okX, nextX, hi] using h₁
  obtain ⟨hcont, hbody⟩ := hreq K _ h₂.1
  have hok : okA K bad fs ⟨S, t⟩ ([.label n cont (vals vs ++ expression body)] ++ l) = true := by
    simp [okA, okX, nextX, hcont, h₂.2]
  obtain ⟨hs, hfr⟩ := scopes_body vs body
  refine ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, ?_, ?_⟩
  · intro b hb
    simp only [scopeSeqs_label, hs, scopeSeqs_nil, List.append_nil, List.mem_singleton] at hb
    exact hb ▸ seqOK_body hS hbody vs
  · intro p hp
    simp [hfr] at hp

theorem flow_block {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {body : List Instr} {n : Nat} :
    FlowPost bad fs (⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ : Config H)
      ⟨s, f, [.label n [] (vals vs ++ expression body)]⟩ :=
  flow_newLabel (fun _ _ => rfl) fun _ _ h => ⟨by simp [okL], h⟩

theorem flow_loop {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {body : List Instr} {n : Nat} :
    FlowPost bad fs (⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ : Config H)
      ⟨s, f, [.label n [.loop bt body] (vals vs ++ expression body)]⟩ :=
  flow_newLabel (fun _ _ => rfl) fun _ _ h => ⟨by simpa [okL, okI] using h, h⟩

/-- The bodies created by `try_table`. -/
theorem tryTable_scopes {f : Frame} {K S : List Nat} (hS : Sound f K S) {vs : List Val}
    {body : List Instr} {n : Nat} {cs : List Catch} (hb : okL K bad fs ⟨S, .other⟩ body = true) :
    (∀ b ∈ scopeSeqs [.handler n cs [.label n [] (vals vs ++ expression body)]],
      SeqOK K bad fs f b) ∧
      FramesOK bad fs [.handler n cs [.label n [] (vals vs ++ expression body)]] := by
  obtain ⟨hs, hfr⟩ := scopes_body vs body
  refine ⟨fun b hbm => ?_, fun p hp => by simp [hfr] at hp⟩
  simp only [scopeSeqs_handler, scopeSeqs_label, hs, scopeSeqs_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hbm
  rcases hbm with rfl | rfl
  · exact ⟨S, hS, by simp [okA, okX, okL]⟩
  · exact seqOK_body hS hb vs

theorem flow_tryTable {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {n : Nat} :
    FlowPost bad fs (⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩ : Config H)
      ⟨s, f, [.handler n cs [.label n [] (vals vs ++ expression body)]]⟩ := by
  intro K S t l ht hS hch _ _
  have h₁ : okA K bad fs ⟨S, (vs.getLast?.map topOfVal).getD t⟩
      ([.plain (.tryTable bt cs body)] ++ l) = true := by
    rw [← okA_vals_append ht]
    simpa only [List.append_assoc] using hch
  have h₂ : okL K bad fs ⟨S, .other⟩ body = true ∧ okA K bad fs ⟨S, .other⟩ l = true := by
    simpa [okA, topVals_ne_ex ht, okX, okI, nextX, nextI] using h₁
  have hok : okA K bad fs ⟨S, t⟩ ([.handler n cs [.label n [] (vals vs ++ expression body)]] ++ l) =
      true := by
    simp [okA, okX, nextX, h₂.2]
  exact ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, tryTable_scopes hS h₂.1⟩

theorem flow_ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} (hc : c ≠ 0) :
    FlowPost bad fs (⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩ : Config H)
      ⟨s, f, [.plain (.block bt b₁)]⟩ := by
  intro K S t l ht hS hch _ _
  have hcv : constI32 c = (Val.i32 c).toAdmin := rfl
  have htop : topOfVal (Val.i32 c) = .gd := topOfVal_i32_ne hc
  have h₀ : okA K bad fs ⟨S, .gd⟩ (.plain (.if_ bt b₁ b₂) :: l) = true := by
    rw [← htop, ← okA_cons_val ht, ← hcv]
    simpa using hch
  have h₁ : okL K bad fs ⟨S, .other⟩ b₁ = true ∧ okA K bad fs ⟨S, .other⟩ l = true := by
    simpa [okA, okX, okI, nextX, nextI, thenS] using h₀
  have hok : okA K bad fs ⟨S, t⟩ ([.plain (.block bt b₁)] ++ l) = true := by
    simp [okA, okX, okI, nextX, nextI, h₁.1, h₁.2]
  exact ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, by simp, by simp [FramesOK]⟩

theorem flow_ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr} :
    FlowPost bad fs (⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩ : Config H)
      ⟨s, f, [.plain (.block bt b₂)]⟩ := by
  intro K S t l ht hS hch _ _
  have hcv : constI32 0 = (Val.i32 0).toAdmin := rfl
  have htop : topOfVal (Val.i32 0) = .zero := by simp [topOfVal_i32]
  have h₀ : okA K bad fs ⟨S, .zero⟩ (.plain (.if_ bt b₁ b₂) :: l) = true := by
    rw [← htop, ← okA_cons_val ht, ← hcv]
    simpa using hch
  have h₁ : okL K bad fs ⟨S, .other⟩ b₂ = true ∧ okA K bad fs ⟨S, .other⟩ l = true := by
    simpa [okA, okX, okI, nextX, nextI] using h₀
  have hok : okA K bad fs ⟨S, t⟩ ([.plain (.block bt b₂)] ++ l) = true := by
    simp [okA, okX, okI, nextX, nextI, h₁.1, h₁.2]
  exact ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, by simp, by simp [FramesOK]⟩

/-- **A branch to a label runs its continuation.** -/
theorem flow_brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {lb : LabelIdx} {rest : List Admin} :
    FlowPost bad fs
      (⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br lb)] ++ rest)]⟩ : Config H)
      ⟨s, f, vals vs ++ expression cont⟩ := by
  intro K S t l ht hS hch _ _
  have h₁ : okL K bad fs ⟨S, .other⟩ cont = true ∧ okA K bad fs ⟨S, .other⟩ l = true := by
    simpa [okA, ht, okX, nextX] using hch
  have hok : okA K bad fs ⟨S, t⟩ (vals vs ++ expression cont ++ l) = true := by
    rw [List.append_assoc, okA_vals_append ht, okA_append]
    refine ⟨?_, okA_mono l (fle_finA _ _) h₁.2⟩
    rw [okA_expression]
    exact okL_mono cont (FLe.of_other (fun _ h => h) _) h₁.1
  obtain ⟨hs, hfr⟩ := scopes_body vs cont
  refine ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, ?_, ?_⟩
  · intro b hb
    simp only [hs, List.not_mem_nil] at hb
  · intro p hp
    simp only [hfr, List.not_mem_nil] at hp

/-! ## Calls and handlers -/

theorem sound_nil {f : Frame} {K : List Nat} : Sound f K [] := fun _ h => by cases h

/-- Values followed by flat elements are flat. -/
theorem flatX_vals_append (vs : List Val) {L : List Admin} (hL : ∀ x ∈ L, FlatX x) :
    ∀ x ∈ vals vs ++ L, FlatX x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact flatX_toAdmin v
  · exact hL x hx

/-- The arguments of a call. -/
theorem flatX_callArgs (vs : List Val) (a : Nat) {c : Admin} (hc : OtherX c) :
    ∀ x ∈ vals vs ++ [.ref (.func a), c], FlatX x := by
  refine flatX_vals_append vs fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact flatX_ref _
  · exact flatX_of_other hc

theorem last_callArgs {vs : List Val} {a : Nat} {c : Admin} (hc : OtherX c) :
    ∀ e, (vals vs ++ [.ref (.func a), c]).getLast? = some e → OtherX e := by
  intro e he
  simp only [List.getLast?_append, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at he
  exact he ▸ hc

/-- The elements of a result have no requirement. -/
theorem trivX_result (r : Result) : ∀ x ∈ r.toAdmin, TrivX x := by
  intro x hx
  cases r with
  | values vs' =>
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact trivX_toAdmin w
  | throw a' =>
    simp only [Result.toAdmin, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact fun _ _ _ _ => rfl
  | trap =>
    simp only [Result.toAdmin, List.mem_singleton] at hx
    exact hx ▸ fun _ _ _ _ => rfl

theorem codeBodies_result (r : Result) : codeBodies r.toAdmin = [] := by
  cases r <;> simp [Result.toAdmin]

/-- The frame body of a call, checked from the empty state. -/
theorem framesOK_call {fr : Frame} {k : Nat} {code : Func}
    (hb : ∃ K', okL K' bad fs ⟨[], .other⟩ code.body = true) :
    FramesOK bad fs [.frame k fr [.label k [] (expression code.body)]] := by
  obtain ⟨K', hK'⟩ := hb
  obtain ⟨hse, hfe⟩ := scopes_body [] code.body
  have hse' : scopeSeqs (expression code.body) = [] := by simpa [vals] using hse
  have hfe' : frameScopes (expression code.body) = [] := by simpa [vals] using hfe
  intro p hp
  simp only [frameScopes_frame, frameScopes_label, hfe', frameScopes_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  refine ⟨K', ⟨[], sound_nil, by simp [okA, okX, okL]⟩, fun b hb' => ?_⟩
  simp only [scopeSeqs_label, hse', scopeSeqs_nil, List.append_nil, List.mem_singleton] at hb'
  subst hb'
  exact ⟨[], sound_nil, by rw [okA_expression]; exact hK'⟩

/-- **A call of a Wasm function creates a frame body checked from the empty state.** -/
theorem flow_callRefFunc {s : Store H} {f fr : Frame} {c : Admin} {vs : List Val} {a k : Nat}
    {code : Func} (hcr : c.IsCallRef) (hb : ∃ K', okL K' bad fs ⟨[], .other⟩ code.body = true) :
    FlowPost bad fs (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H)
      ⟨s, f, [.frame k fr [.label k [] (expression code.body)]]⟩ := by
  intro K S t l ht hS hch _ _
  obtain ⟨hco, -⟩ := isCallRef_flow hcr
  have hR : ∀ x ∈ [Admin.frame k fr [.label k [] (expression code.body)]], TrivX x := by
    intro x hx
    simp only [List.mem_singleton] at hx
    exact hx ▸ fun _ _ _ _ => rfl
  have hok := okA_flat (flatX_callArgs vs a hco) (by simp) (last_callArgs hco) hR ht hch
  exact ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, by simp, framesOK_call hb⟩

theorem flow_host {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {r : Result}
    (hc : c.IsCallRef) :
    FlowPost bad fs (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H) ⟨s', f, r.toAdmin⟩ :=
  flow_flat (flatX_callArgs vs a (isCallRef_flow hc).1) (by simp)
    (last_callArgs (isCallRef_flow hc).1) (trivX_result r) (codeBodies_result r)

theorem flow_handlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch}
    {a : Nat} : FlowPost bad fs (⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ : Config H)
      ⟨s, f, [.handler n cs (throwing a)]⟩ := by
  intro K S t l ht hS hch _ _
  have hok : okA K bad fs ⟨S, t⟩ ([.handler n cs (throwing a)] ++ l) = true := by
    simpa [okA, ht, okX, nextX] using hch
  refine ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hok⟩, ?_, ?_⟩
  · intro b hb
    simp [throwing] at hb
    subst hb
    exact ⟨[], sound_nil, by simp [okA, okX, okI, reqI, isBadCall, isSetK,
      nextX]⟩
  · intro p hp
    simp [throwing] at hp

theorem flow_retLabel {c c' : Config H} {x y : Admin} {vs : List Val} (hx : x.IsReturnCallRef)
    (hy : c.code = [y]) (hyo : OtherX y) (hc' : c'.code = vals vs ++ [x]) (hf : c'.frame = c.frame)
    : FlowPost bad fs c c' := by
  obtain ⟨-, hxt⟩ := isReturnCallRef_flow hx
  obtain ⟨hb₁, -⟩ := isReturnCallRef_flat hx
  have h := flow_flat (bad := bad) (fs := fs) (s := c.store) (s' := c'.store) (f := c.frame)
    (L := [y]) (R := vals vs ++ [x]) (by simpa using flatX_of_other hyo) (by simp)
    (fun e he => by simp at he; exact he ▸ hyo) (by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hz
        exact trivX_toAdmin v
      · exact (List.mem_singleton.1 hz) ▸ hxt) (by simp [hb₁])
  intro K S t l ht hS hch hsc hfr
  have h' := h K S t l ht hS (hy ▸ hch) (hy ▸ hsc) (hy ▸ hfr)
  rw [hc', hf]
  exact h'

theorem flow_returnFrame {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    FlowPost bad fs
      (⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩ : Config H)
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  refine flow_flat (by simpa using flatX_of_other (fun _ _ => rfl)) (by simp)
    (fun e he => by simp at he; exact he ▸ fun _ _ => rfl) ?_ ?_
  · intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      exact trivX_toAdmin v
    · exact fun _ _ _ _ => rfl
    · exact retToCallIn_flow _ hc
  · obtain ⟨h₁, -⟩ := retToCallIn_flat fi.module hc
    simp [h₁]

/-! ## Context rules -/

theorem flow_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin}
    (ih : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    FlowPost bad fs (⟨s, f, vals vs ++ is ++ rest⟩ : Config H) ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro K S t l ht hS hch hsc hfr
  have htv : (vs.getLast?.map topOfVal).getD t ≠ .ex := topVals_ne_ex ht vs
  have hch' : okA K bad fs ⟨S, (vs.getLast?.map topOfVal).getD t⟩ (is ++ (rest ++ l)) = true := by
    rw [← okA_vals_append ht]
    simpa only [List.append_assoc] using hch
  have hsv : scopeSeqs (vals vs) = [] ∧ frameScopes (vals vs) = [] :=
    scopes_of_codeBodies (by simp)
  have hsc₁ : ∀ b ∈ scopeSeqs is, SeqOK K bad fs f b := fun b hb =>
    hsc b (by simp [scopeSeqs_append, hsv.1, hb])
  have hfr₁ : FramesOK bad fs is := fun p hp => hfr p (by simp [frameScopes_append, hsv.2, hp])
  obtain ⟨hmono, ⟨S', hsub, hS', hok⟩, hsc', hfr'⟩ := ih K S _ (rest ++ l) htv hS hch' hsc₁ hfr₁
  have hgoal : okA K bad fs ⟨S', t⟩ (vals vs ++ is' ++ rest ++ l) = true := by
    simp only [List.append_assoc]
    rw [okA_vals_append ht]
    exact hok
  refine ⟨hmono, ⟨S', hsub, hS', hgoal⟩, ?_, ?_⟩
  · intro b hb
    simp only [scopeSeqs_append, hsv.1, List.nil_append, List.mem_append] at hb
    rcases hb with hb | hb
    · exact hsc' b hb
    · obtain ⟨Sb, hSb, hb'⟩ := hsc b (by simp [scopeSeqs_append, hsv.1, hb])
      exact ⟨Sb, hmono Sb hSb, hb'⟩
  · intro p hp
    simp only [frameScopes_append, hsv.2, List.nil_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hfr' p hp
    · exact hfr p (by simp [frameScopes_append, hsv.2, hp])

theorem okA_label_body {K S : List Nat} {t : Top} {n : Nat} {cont : List Instr}
    {b b' l : List Admin} :
    okA K bad fs ⟨S, t⟩ ([.label n cont b] ++ l) = okA K bad fs ⟨S, t⟩ ([.label n cont b'] ++ l) := by
  simp [okA, okX, nextX]

theorem okA_handler_body {K S : List Nat} {t : Top} {n : Nat} {cs : List Catch}
    {b b' l : List Admin} :
    okA K bad fs ⟨S, t⟩ ([.handler n cs b] ++ l) = okA K bad fs ⟨S, t⟩ ([.handler n cs b'] ++ l) := by
  simp [okA, okX, nextX]

theorem okA_frame_body {K S : List Nat} {t : Top} {n : Nat} {fr fr' : Frame}
    {b b' l : List Admin} :
    okA K bad fs ⟨S, t⟩ ([.frame n fr b] ++ l) = okA K bad fs ⟨S, t⟩ ([.frame n fr' b'] ++ l) := by
  simp [okA, okX, nextX]

/-- A nested body steps in the same frame. -/
theorem flow_nested {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (ih : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) {K : List Nat}
    (hb : SeqOK K bad fs f is) (hsc : ∀ b ∈ scopeSeqs is, SeqOK K bad fs f b)
    (hfr : FramesOK bad fs is) :
    (∀ S₀, Sound f K S₀ → Sound f' K S₀) ∧ SeqOK K bad fs f' is' ∧
      (∀ b ∈ scopeSeqs is', SeqOK K bad fs f' b) ∧ FramesOK bad fs is' := by
  obtain ⟨Sb, hSb, hch⟩ := hb
  obtain ⟨hmono, ⟨Sb', -, hSb', hok⟩, hsc', hfr'⟩ :=
    ih K Sb .other [] nofun hSb (by simpa using hch) hsc hfr
  exact ⟨hmono, ⟨Sb', hSb', by simpa using hok⟩, hsc', hfr'⟩

theorem flow_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    FlowPost bad fs (⟨s, f, [.label n cont is]⟩ : Config H) ⟨s', f', [.label n cont is']⟩ := by
  intro K S t l ht hS hch hsc hfr
  obtain ⟨hmono, hb', hsc', hfr'⟩ := flow_nested ih (hsc is (by simp))
    (fun b hb => hsc b (by simp [hb])) (fun p hp => hfr p (by simp [hp]))
  refine ⟨hmono, ⟨S, fun _ h => h, hmono S hS, okA_label_body.symm ▸ hch⟩, ?_, ?_⟩
  · intro b hb
    simp only [scopeSeqs_label, scopeSeqs_nil, List.append_nil, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hb'
    · exact hsc' b hb
  · intro p hp
    simp only [frameScopes_label, frameScopes_nil, List.append_nil] at hp
    exact hfr' p hp

theorem flow_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : FlowPost bad fs (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    FlowPost bad fs (⟨s, f, [.handler n cs is]⟩ : Config H) ⟨s', f', [.handler n cs is']⟩ := by
  intro K S t l ht hS hch hsc hfr
  obtain ⟨hmono, hb', hsc', hfr'⟩ := flow_nested ih (hsc is (by simp))
    (fun b hb => hsc b (by simp [hb])) (fun p hp => hfr p (by simp [hp]))
  refine ⟨hmono, ⟨S, fun _ h => h, hmono S hS, okA_handler_body.symm ▸ hch⟩, ?_, ?_⟩
  · intro b hb
    simp only [scopeSeqs_handler, scopeSeqs_nil, List.append_nil, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hb'
    · exact hsc' b hb
  · intro p hp
    simp only [frameScopes_handler, frameScopes_nil, List.append_nil] at hp
    exact hfr' p hp

theorem flow_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : FlowPost bad fs (⟨s, fi, is⟩ : Config H) ⟨s', fi', is'⟩) :
    FlowPost bad fs (⟨s, f, [.frame n fi is]⟩ : Config H) ⟨s', f, [.frame n fi' is']⟩ := by
  intro K S t l ht hS hch hsc hfr
  obtain ⟨K', hb, hscK⟩ := hfr (fi, is) (by simp)
  obtain ⟨-, hb', hsc', hfr'⟩ := flow_nested ih hb hscK (fun p hp => hfr p (by simp [hp]))
  refine ⟨fun _ h => h, ⟨S, fun _ h => h, hS, okA_frame_body.symm ▸ hch⟩, by simp, ?_⟩
  intro p hp
  simp only [frameScopes_frame, frameScopes_nil, List.append_nil, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ⟨K', hb', hsc'⟩
  · exact hfr' p hp

theorem flow_refl {c : Config H} : FlowPost bad fs c c := by
  intro K S t l _ hS hch hsc hfr
  exact ⟨fun _ h => h, ⟨S, fun _ h => h, hS, hch⟩, hsc, hfr⟩

/-! ## Every step -/

set_option linter.unusedTactic false in
/-- **Every Core 3.0 step keeps the flow invariant** (every profile, every host). -/
theorem Step.flow {G : Nat → Prop} {Pl : Instr → Prop} {P : Profile} {host : HostSemantics H}
    {c c' : Config H} (h : Step P host c c') (hc : CfgIn G fs Pl c)
    (hbf : BodiesFlow G bad fs c.store.funcs) : FlowPost bad fs c c' := by
  induction h with
  | parametric h => exact ParametricStep.flow h
  | numeric h => exact NumericStep.flow h
  | vector h => exact VectorStep.flow h
  | «variable» h => exact VariableStep.flow h
  | table h => exact TableStep.flow h
  | memory h => exact MemoryStep.flow h
  | reference h => exact RefStep.flow h
  | aggregate h => exact AggregateStep.flow h
  | ctxtInstrs _ _ ih =>
    exact flow_ctxtInstrs (ih ⟨hc.1, hc.2.1, (CodeIn.append.1 (CodeIn.append.1 hc.2.2).1).2⟩ hbf)
  | ctxtLabel _ ih => exact flow_ctxtLabel (ih ⟨hc.1, hc.2.1, (CodeIn.label_iff.1 hc.2.2).2⟩ hbf)
  | ctxtHandler _ ih => exact flow_ctxtHandler (ih ⟨hc.1, hc.2.1, CodeIn.handler_iff.1 hc.2.2⟩ hbf)
  | ctxtFrame _ ih =>
    exact flow_ctxtFrame
      (ih ⟨hc.1, (CodeIn.frame_iff.1 hc.2.2).1, (CodeIn.frame_iff.1 hc.2.2).2⟩ hbf)
  | block => exact flow_block
  | loop => exact flow_loop
  | tryTable => exact flow_tryTable
  | ifTrue hc' => exact flow_ifTrue hc'
  | ifFalse => exact flow_ifFalse
  | brLabelZero => exact flow_brLabelZero
  | @callRefFunc _ _ _ _ a _ _ _ _ hcr hf _ _ hcode =>
    have ha : G a := by simpa using hc.2.2.ref_of_mem (r := .func a) (by simp)
    exact flow_callRefFunc hcr (hbf _ _ _ ha hf hcode)
  | callRefHost hcr => exact flow_host hcr
  | callRefHostDiv => exact flow_refl
  | throw => exact flow_throwingR rfl _
  | throwRefInstrs => exact flow_throwingR rfl _
  | throwRefLabel => exact flow_throwingR rfl _
  | throwRefFrame => exact flow_throwingR rfl _
  | throwRefHandlerEmpty => exact flow_throwingR rfl _
  | returnCallRefLabel hcr => exact flow_retLabel hcr rfl (fun _ _ => rfl) rfl rfl
  | returnCallRefHandler hcr => exact flow_retLabel hcr rfl (fun _ _ => rfl) rfl rfl
  | returnCallRefFrameAddr hcr => exact flow_returnFrame hcr
  | throwRefHandlerNext => exact flow_handlerNext
  | _ =>
    first
      | (exact flow_exitR rfl (fun _ _ => rfl) (fun _ _ _ _ => rfl) (by simp); done)
      | (flow_flat_tac; done)

end Silmaril.Wasm.Verify
