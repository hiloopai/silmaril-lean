module

public import Silmaril.Wasm.FnInst.Opt.Seg.Defs

@[expose] public section

/-! # The fragment: composition, typing soundness, and rewriting at typed positions

* `Out.bind` laws and `run_append`: running `c ++ d` runs `c`, then `d` on every final state;
* `run_height`: the checker's heights are the runtime stack heights, under a typed
  environment;
* `run_ft`, `chk_ft`: code typed over `ft` runs and checks the same over every extension of
  `ft` (added functions);
* `chk_frame`: the frame rule (extra values below do not matter to the checker);
* `run_rw`: a segment pair that runs the same from every state of its hole (stack height at
  least `n`) can be exchanged at every typed position of any code;
* `fsem_rewrite`, `den_rewrite`: the same for every body of a module, at every call depth:
  exchanging a segment pair that is equivalent under *every* typed environment preserves the
  semantics of every function of the module.
-/

namespace Silmaril.Proofs.Wasm.FnInst.Opt

open Silmaril.Wasm.FnInst.Opt

/-! ## Sequential composition -/

namespace Out

open Silmaril.Wasm.FnInst.Opt.Out

@[simp] theorem mem_bind {S : Set Out} {k : St → Set Out} {o : Out} :
    o ∈ bind S k ↔ (∃ st, Out.ok st ∈ S ∧ o ∈ k st) ∨ (o ∈ S ∧ o.isOk = false) := Iff.rfl

@[simp] theorem isOk_ok (st : St) : (Out.ok st).isOk = true := rfl

@[simp] theorem bind_ok (st : St) (k : St → Set Out) : bind {Out.ok st} k = k st := by
  ext o
  simp only [mem_bind, Set.mem_singleton_iff]
  constructor
  · rintro (⟨_, h, ho⟩ | ⟨rfl, hk⟩)
    · cases h; exact ho
    · simp only [isOk_ok, Bool.true_eq_false] at hk
  · exact fun ho => Or.inl ⟨st, rfl, ho⟩

theorem bind_assoc (S : Set Out) (k : St → Set Out) (l : St → Set Out) :
    bind (bind S k) l = bind S (fun st => bind (k st) l) := by
  ext o
  simp only [mem_bind]
  constructor
  · rintro (⟨st, ⟨st₀, h₀, h₁⟩ | ⟨-, hbad⟩, h₂⟩ | ⟨⟨st₀, h₀, h₁⟩ | ⟨h₀, -⟩, hk⟩)
    · exact Or.inl ⟨st₀, h₀, Or.inl ⟨st, h₁, h₂⟩⟩
    · simp only [isOk_ok, Bool.true_eq_false] at hbad
    · exact Or.inl ⟨st₀, h₀, Or.inr ⟨h₁, hk⟩⟩
    · exact Or.inr ⟨h₀, hk⟩
  · rintro (⟨st₀, h₀, ⟨st, h₁, h₂⟩ | ⟨h₁, hk⟩⟩ | ⟨h₀, hk⟩)
    · exact Or.inl ⟨st, Or.inl ⟨st₀, h₀, h₁⟩, h₂⟩
    · exact Or.inr ⟨Or.inl ⟨st₀, h₀, h₁⟩, hk⟩
    · exact Or.inr ⟨Or.inr ⟨h₀, hk⟩, hk⟩

theorem bind_congr {S : Set Out} {k k' : St → Set Out}
    (h : ∀ st, Out.ok st ∈ S → k st = k' st) : bind S k = bind S k' := by
  ext o
  simp only [mem_bind]
  constructor
  · rintro (⟨st, hs, ho⟩ | ho)
    · exact Or.inl ⟨st, hs, h st hs ▸ ho⟩
    · exact Or.inr ho
  · rintro (⟨st, hs, ho⟩ | ho)
    · exact Or.inl ⟨st, hs, (h st hs).symm ▸ ho⟩
    · exact Or.inr ho

theorem bind_mono {S : Set Out} {k k' : St → Set Out}
    (h : ∀ st, Out.ok st ∈ S → k st ⊆ k' st) : bind S k ⊆ bind S k' := by
  rintro o (⟨st, hs, ho⟩ | ho)
  · exact Or.inl ⟨st, hs, h st hs ho⟩
  · exact Or.inr ho

theorem bind_mono_left {S S' : Set Out} (hS : S ⊆ S') (k : St → Set Out) :
    bind S k ⊆ bind S' k := by
  rintro o (⟨st, hs, ho⟩ | ⟨ho, hk⟩)
  · exact Or.inl ⟨st, hS hs, ho⟩
  · exact Or.inr ⟨hS ho, hk⟩

end Out

@[simp] theorem run_nil (ft : FTypes) (E : Env) (st : St) : run ft E [] st = {.ok st} := rfl

@[simp] theorem run_cons (ft : FTypes) (E : Env) (i : Instr) (c : Code) (st : St) :
    run ft E (i :: c) st = Out.bind (step ft E i st) (run ft E c) := rfl

theorem run_append (ft : FTypes) (E : Env) (c d : Code) (st : St) :
    run ft E (c ++ d) st = Out.bind (run ft E c st) (run ft E d) := by
  induction c generalizing st with
  | nil => simp
  | cons i c ih =>
    simp only [List.cons_append, run_cons, Out.bind_assoc]
    exact Out.bind_congr fun st' _ => ih st'

/-! ## Typing -/

@[simp] theorem chk_nil (ft : FTypes) (h : ℕ) : chk ft [] h = some h := rfl

@[simp] theorem chk_cons (ft : FTypes) (i : Instr) (c : Code) (h : ℕ) :
    chk ft (i :: c) h = (hgt ft i h).bind (chk ft c) := rfl

theorem chk_append (ft : FTypes) (c d : Code) (h : ℕ) :
    chk ft (c ++ d) h = (chk ft c h).bind (chk ft d) := by
  induction c generalizing h with
  | nil => rfl
  | cons i c ih =>
    simp only [List.cons_append, chk_cons]
    cases hgt ft i h with
    | none => rfl
    | some h₂ => exact ih h₂

theorem hgt_spec {ft : FTypes} {i : Instr} {h h₂ : ℕ} :
    hgt ft i h = some h₂ ↔ ∃ p q, arity ft i = some (p, q) ∧ p ≤ h ∧ h₂ = h - p + q := by
  unfold hgt
  cases ha : arity ft i with
  | none => simp
  | some pq =>
    obtain ⟨p, q⟩ := pq
    by_cases hp : p ≤ h <;> simp [hp, eq_comm]

theorem hgt_frame {ft : FTypes} {i : Instr} {h h' : ℕ} (k : ℕ) (hh : hgt ft i h = some h') :
    hgt ft i (h + k) = some (h' + k) := by
  obtain ⟨p, q, ha, hp, rfl⟩ := hgt_spec.mp hh
  exact hgt_spec.mpr ⟨p, q, ha, by omega, by omega⟩

theorem chk_frame {ft : FTypes} {c : Code} {h h' : ℕ} (k : ℕ) (hc : chk ft c h = some h') :
    chk ft c (h + k) = some (h' + k) := by
  induction c generalizing h with
  | nil => cases hc; rfl
  | cons i c ih =>
    simp only [chk_cons] at hc ⊢
    cases hi : hgt ft i h with
    | none => rw [hi] at hc; cases hc
    | some h₂ =>
      rw [hi] at hc
      rw [hgt_frame k hi]
      exact ih hc

/-- Code typed from `n` to `m` takes height `h ≥ n` to `h - n + m`. -/
theorem chk_shift {ft : FTypes} {c : Code} {n m h : ℕ} (hc : chk ft c n = some m) (hn : n ≤ h) :
    chk ft c h = some (h - n + m) := by
  have e : h = n + (h - n) := by omega
  rw [e, chk_frame (h - n) hc]
  congr 1
  omega

/-! ## Added functions -/

theorem getElem?_of_prefix {α : Type} {l l' : List α} (hp : l <+: l') {i : ℕ} {a : α}
    (h : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hi]
  exact h

theorem arity_of_prefix {ft ft' : FTypes} (hp : ft <+: ft') {i : Instr} {a : ℕ × ℕ}
    (h : arity ft i = some a) : arity ft' i = some a := by
  cases i <;> first | exact h | exact getElem?_of_prefix hp h

theorem hgt_ft {ft ft' : FTypes} (hp : ft <+: ft') {i : Instr} {h h₂ : ℕ}
    (hh : hgt ft i h = some h₂) : hgt ft' i h = some h₂ := by
  obtain ⟨p, q, ha, hpq, rfl⟩ := hgt_spec.mp hh
  exact hgt_spec.mpr ⟨p, q, arity_of_prefix hp ha, hpq, rfl⟩

theorem chk_ft {ft ft' : FTypes} (hp : ft <+: ft') {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') : chk ft' c h = some h' := by
  induction c generalizing h with
  | nil => exact hc
  | cons i c ih =>
    simp only [chk_cons] at hc ⊢
    cases hi : hgt ft i h with
    | none => rw [hi] at hc; cases hc
    | some h₂ => rw [hi] at hc; rw [hgt_ft hp hi]; exact ih hc

theorem step_ft {ft ft' : FTypes} (hp : ft <+: ft') (E : Env) {i : Instr} {a : ℕ × ℕ}
    (ha : arity ft i = some a) (st : St) : step ft E i st = step ft' E i st := by
  cases i with
  | call f =>
    have h' : ft'[f]? = some a := getElem?_of_prefix hp ha
    have h : ft[f]? = some a := ha
    simp only [step, h, h']
  | _ => rfl

theorem run_ft {ft ft' : FTypes} (hp : ft <+: ft') (E : Env) {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') (st : St) : run ft E c st = run ft' E c st := by
  induction c generalizing h st with
  | nil => rfl
  | cons i c ih =>
    simp only [chk_cons] at hc
    simp only [run_cons]
    cases hi : hgt ft i h with
    | none => rw [hi] at hc; cases hc
    | some h₂ =>
      rw [hi] at hc
      obtain ⟨p, q, ha, -, -⟩ := hgt_spec.mp hi
      rw [step_ft hp E ha st]
      exact Out.bind_congr fun st' _ => ih hc st'

theorem Env.typed_of_prefix {ft ft' : FTypes} (hp : ft <+: ft') {E : Env} (hE : E.Typed ft') :
    E.Typed ft :=
  fun f n m hf => hE f n m (getElem?_of_prefix hp hf)

theorem Env.typed_mono {ft : FTypes} {E M : Env} (hle : E ≤ M) (hM : M.Typed ft) : E.Typed ft :=
  fun f n m hf args g r g' hr => hM f n m hf args g r g' (hle f args g hr)

theorem Env.top_total : Env.top.Total := fun _ _ _ => ⟨Ans.trap, Set.mem_univ _⟩

/-! ## Runtime heights -/

theorem binop_height {f : Val → Val → Val} {st st' : St} {h : ℕ} (hs : st.stack.length = h)
    (ho : binop f st = .ok st') : 2 ≤ h ∧ st'.stack.length = h - 2 + 1 := by
  unfold binop at ho
  split at ho
  · rename_i b a r e
    cases ho
    rw [e] at hs
    simp only [List.length_cons] at hs ⊢
    omega
  · cases ho

theorem unop_height {f : Val → Val} {st st' : St} {h : ℕ} (hs : st.stack.length = h)
    (ho : unop f st = .ok st') : 1 ≤ h ∧ st'.stack.length = h - 1 + 1 := by
  unfold unop at ho
  split at ho
  · rename_i a r e
    cases ho
    rw [e] at hs
    simp only [List.length_cons] at hs ⊢
    omega
  · cases ho

theorem pop1_height {st st' : St} {k : Val → St → St} {d : ℕ}
    (hk : ∀ v s, (k v s).stack.length = s.stack.length + d) (ho : pop1 st k = .ok st') :
    1 ≤ st.stack.length ∧ st'.stack.length = st.stack.length - 1 + d := by
  unfold pop1 at ho
  split at ho
  · rename_i v r e
    cases ho
    have hl : (k v { st with stack := r }).stack.length = r.length + d := hk v _
    rw [hl, e, List.length_cons]
    omega
  · cases ho

/-- A push of one value, with arity `(0, 1)`. -/
theorem push_arity {st st' : St} {v : Val} {p q : ℕ} (ha : some (0, 1) = some (p, q))
    (ho : Out.ok { st with stack := v :: st.stack } = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q := by
  obtain ⟨rfl, rfl⟩ : 0 = p ∧ 1 = q := Prod.mk.inj (Option.some.inj ha)
  cases ho
  exact ⟨Nat.zero_le _, by simp⟩

theorem binop_arity {f : Val → Val → Val} {st st' : St} {p q : ℕ}
    (ha : some (2, 1) = some (p, q)) (ho : binop f st = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q := by
  obtain ⟨rfl, rfl⟩ : 2 = p ∧ 1 = q := Prod.mk.inj (Option.some.inj ha)
  exact binop_height rfl ho

theorem unop_arity {f : Val → Val} {st st' : St} {p q : ℕ}
    (ha : some (1, 1) = some (p, q)) (ho : unop f st = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q := by
  obtain ⟨rfl, rfl⟩ : 1 = p ∧ 1 = q := Prod.mk.inj (Option.some.inj ha)
  exact unop_height rfl ho

theorem pop1_arity {st st' : St} {k : Val → St → St} {d p q : ℕ}
    (hk : ∀ v s, (k v s).stack.length = s.stack.length + d) (ha : some (1, d) = some (p, q))
    (ho : pop1 st k = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q := by
  obtain ⟨rfl, rfl⟩ : 1 = p ∧ d = q := Prod.mk.inj (Option.some.inj ha)
  exact pop1_height hk ho

/-- Every deterministic instruction moves the stack height as its arity says. -/
theorem exec1_arity {ft : FTypes} {i : Instr} {p q : ℕ} (ha : arity ft i = some (p, q))
    {st st' : St} (ho : exec1 i st = .ok st') :
    p ≤ st.stack.length ∧ st'.stack.length = st.stack.length - p + q := by
  cases i with
  | const k => exact push_arity ha ho
  | localGet x => exact push_arity ha ho
  | globalGet x => exact push_arity ha ho
  | add | sub | mul | and | or | xor => exact binop_arity ha ho
  | eqz => exact unop_arity ha ho
  | localSet x =>
    exact pop1_arity (k := fun v s => { s with locals := Function.update s.locals x v })
      (d := 0) (fun _ _ => rfl) ha ho
  | localTee x =>
    exact pop1_arity
      (k := fun v s => { s with locals := Function.update s.locals x v, stack := v :: s.stack })
      (d := 1) (fun _ _ => rfl) ha ho
  | globalSet x =>
    exact pop1_arity (k := fun v s => { s with globals := Function.update s.globals x v })
      (d := 0) (fun _ _ => rfl) ha ho
  | drop => exact pop1_arity (k := fun _ s => s) (d := 0) (fun _ _ => rfl) ha ho
  | call f => exact absurd ho (by simp [exec1])

theorem exec1_height {ft : FTypes} {i : Instr} {h h₂ : ℕ} (hh : hgt ft i h = some h₂)
    {st st' : St} (hs : st.stack.length = h) (ho : exec1 i st = .ok st') :
    st'.stack.length = h₂ := by
  obtain ⟨p, q, ha, -, rfl⟩ := hgt_spec.mp hh
  rw [(exec1_arity ha ho).2, hs]

theorem step_height {ft : FTypes} {E : Env} (hE : E.Typed ft) {i : Instr} {h h₂ : ℕ}
    (hh : hgt ft i h = some h₂) {st st' : St} (hs : st.stack.length = h)
    (ho : Out.ok st' ∈ step ft E i st) : st'.stack.length = h₂ := by
  cases i with
  | call f =>
    obtain ⟨n, m, hf, hn, rfl⟩ := hgt_spec.mp hh
    have hf' : ft[f]? = some (n, m) := hf
    have hn' : n ≤ st.stack.length := hs ▸ hn
    simp only [step, hf', hn', ↓reduceIte] at ho
    rcases ho with ⟨r, g', hr, ho⟩ | ⟨ho, -⟩ | ⟨ho, -⟩
    · cases ho
      have hrm : r.length = m := hE f n m hf' _ _ r g' hr
      simp only [List.length_append, List.length_drop]
      omega
    · cases ho
    · cases ho
  | _ => exact exec1_height hh hs (Set.mem_singleton_iff.mp ho).symm

theorem run_height {ft : FTypes} {E : Env} (hE : E.Typed ft) {c : Code} {h h' : ℕ}
    (hc : chk ft c h = some h') {st st' : St} (hs : st.stack.length = h)
    (ho : Out.ok st' ∈ run ft E c st) : st'.stack.length = h' := by
  induction c generalizing h st with
  | nil => cases hc; cases ho; exact hs
  | cons i c ih =>
    simp only [chk_cons] at hc
    simp only [run_cons, Out.mem_bind, Out.isOk_ok, Bool.true_eq_false, and_false,
      or_false] at ho
    obtain ⟨st₁, h₁, h₂⟩ := ho
    cases hi : hgt ft i h with
    | none => rw [hi] at hc; cases hc
    | some h₃ =>
      rw [hi] at hc
      exact ih hc (step_height hE hi hs h₁) h₂

/-! ## Rewriting at typed positions -/

/-- **Exchanging a segment pair at typed positions.** If `s` and `s'` run the same from every
state with at least `n` operands, and `s` has stack type `n → m`, then exchanging occurrences
of `s` by `s'` at positions of height at least `n` does not change the run of any code. -/
theorem run_rw {ft : FTypes} {E : Env} (hE : E.Typed ft) {s s' : Code} {n m : ℕ}
    (hs : RunEq ft n E s s')
    (hty : chk ft s n = some m) {h : ℕ} {c c' : Code} (hr : Rw ft s s' n m h c c') :
    ∀ st : St, st.stack.length = h → run ft E c st = run ft E c' st := by
  induction hr with
  | nil h => intro st _; rfl
  | keep i hi _ ih =>
    intro st hst
    simp only [run_cons]
    exact Out.bind_congr fun st' ho => ih st' (step_height hE hi hst ho)
  | @seg h c c' hn _ ih =>
    intro st hst
    have hsh : chk ft s h = some (h - n + m) := chk_shift hty hn
    have hcont : Out.bind (run ft E s st) (run ft E c) = Out.bind (run ft E s st) (run ft E c') :=
      Out.bind_congr fun st' ho => ih st' (run_height hE hsh hst ho)
    rw [run_append, run_append, hcont, hs st (hst ▸ hn)]

/-! ## Modules -/

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (i : ℕ) :
    (l[i]? = none ∧ l'[i]? = none) ∨ ∃ a b, l[i]? = some a ∧ l'[i]? = some b ∧ R a b := by
  induction h generalizing i with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons hab _ ih =>
    cases i with
    | zero => exact Or.inr ⟨_, _, rfl, rfl, hab⟩
    | succ i => exact ih i

theorem answers_typed {ft : FTypes} {E : Env} (hE : E.Typed ft) {b : Code} {m : ℕ}
    (hb : chk ft b 0 = some m) {args : List Val} {g : ℕ → Val} {r : List Val} {g' : ℕ → Val}
    (ha : Ans.ret r g' ∈ answers (run ft E b (initSt args g))) : r.length = m := by
  rcases ha with ⟨st, hst, he⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · obtain ⟨rfl, rfl⟩ := Ans.ret.inj he
    exact run_height hE hb rfl hst
  · cases he
  · cases he

theorem fsem_zero_typed (M : Mdl) {imp : Env} (himp : imp.Typed M.ft) :
    (fsem M imp 0).Typed M.ft := by
  intro f n m hf args g r g' hr
  by_cases hlt : f < M.nimp
  · have h' : Ans.ret r g' ∈ imp f args g := by simpa only [fsem, hlt, ↓reduceIte] using hr
    exact himp f n m hf args g r g' h'
  · have h' : Ans.ret r g' ∈ ({Ans.div} : Set Ans) := by
      simpa only [fsem, hlt, ↓reduceIte] using hr
    cases Set.mem_singleton_iff.mp h'

/-- The body case: a defined function answers with its body's final stack, of its result
count. -/
theorem body_typed {M : Mdl} (hM : M.Typed) {E : Env} (hE : E.Typed M.ft) {f n m : ℕ}
    (hf : M.ft[f]? = some (n, m)) (hlt : ¬ f < M.nimp) {b : Code}
    (hb : M.bodies[f - M.nimp]? = some b) {args : List Val} {g : ℕ → Val} {r : List Val}
    {g' : ℕ → Val} (hr : Ans.ret r g' ∈ answers (run M.ft E b (initSt args g))) :
    r.length = m := by
  obtain ⟨n', m', hft, hchk⟩ := hM _ b hb
  have hfe : M.nimp + (f - M.nimp) = f := by omega
  have hft' : M.ft[f]? = some (n', m') := hfe ▸ hft
  have hnm : (n, m) = (n', m') := Option.some.inj (hf.symm.trans hft')
  have hm : m = m' := (Prod.mk.inj hnm).2
  rw [hm]
  exact answers_typed hE hchk hr

theorem fsem_succ_typed {M : Mdl} (hM : M.Typed) {imp : Env} (himp : imp.Typed M.ft) {k : ℕ}
    (ih : (fsem M imp k).Typed M.ft) : (fsem M imp (k + 1)).Typed M.ft := by
  intro f n m hf args g r g' hr
  by_cases hlt : f < M.nimp
  · have h' : Ans.ret r g' ∈ imp f args g := by simpa only [fsem, hlt, ↓reduceIte] using hr
    exact himp f n m hf args g r g' h'
  · cases hb : M.bodies[f - M.nimp]? with
    | none =>
      have h' : Ans.ret r g' ∈ ({Ans.trap} : Set Ans) := by
        simpa only [fsem, hlt, hb, ↓reduceIte] using hr
      cases Set.mem_singleton_iff.mp h'
    | some b =>
      have h' : Ans.ret r g' ∈ answers (run M.ft (fsem M imp k) b (initSt args g)) := by
        simpa only [fsem, hlt, hb, ↓reduceIte] using hr
      exact body_typed hM ih hf hlt hb h'

/-- The semantics of a well-typed module at every call depth is a typed environment. -/
theorem fsem_typed {M : Mdl} (hM : M.Typed) {imp : Env} (himp : imp.Typed M.ft) :
    ∀ k, (fsem M imp k).Typed M.ft
  | 0 => fsem_zero_typed M himp
  | k + 1 => fsem_succ_typed hM himp (fsem_typed hM himp k)

theorem step_nonempty {ft : FTypes} {E : Env} (hE : E.Total) (i : Instr) (st : St) :
    (step ft E i st).Nonempty := by
  cases i with
  | call f =>
    cases hf : ft[f]? with
    | none => exact ⟨.trap, by simp only [step, hf]; rfl⟩
    | some nm =>
      obtain ⟨n, m⟩ := nm
      by_cases hn : n ≤ st.stack.length
      · have hs : step ft E (.call f) st = callOut E f n st := by
          simp only [step, hf, hn, ↓reduceIte]
        rw [hs]
        obtain ⟨a, ha⟩ := hE f (st.stack.take n) st.globals
        cases a with
        | ret r g' => exact ⟨_, Or.inl ⟨r, g', ha, rfl⟩⟩
        | trap => exact ⟨_, Or.inr (Or.inl ⟨rfl, ha⟩)⟩
        | div => exact ⟨_, Or.inr (Or.inr ⟨rfl, ha⟩)⟩
      · exact ⟨.trap, by simp only [step, hf, hn, ↓reduceIte]; rfl⟩
  | _ => exact ⟨_, rfl⟩

theorem run_nonempty {ft : FTypes} {E : Env} (hE : E.Total) (c : Code) (st : St) :
    (run ft E c st).Nonempty := by
  induction c generalizing st with
  | nil => exact ⟨_, rfl⟩
  | cons i c ih =>
    obtain ⟨o, ho⟩ := step_nonempty (ft := ft) hE i st
    cases o with
    | ok st' =>
      obtain ⟨o', ho'⟩ := ih st'
      exact ⟨o', Or.inl ⟨st', ho, ho'⟩⟩
    | trap => exact ⟨_, Or.inr ⟨ho, rfl⟩⟩
    | div => exact ⟨_, Or.inr ⟨ho, rfl⟩⟩

theorem answers_nonempty {S : Set Out} (hS : S.Nonempty) : (answers S).Nonempty := by
  obtain ⟨o, ho⟩ := hS
  cases o with
  | ok st => exact ⟨_, Or.inl ⟨st, ho, rfl⟩⟩
  | trap => exact ⟨_, Or.inr (Or.inl ⟨rfl, ho⟩)⟩
  | div => exact ⟨_, Or.inr (Or.inr ⟨rfl, ho⟩)⟩

/-- The semantics of a module at every call depth always answers, when its imports do. -/
theorem fsem_total (M : Mdl) {imp : Env} (himp : imp.Total) : ∀ k, (fsem M imp k).Total := by
  intro k
  induction k with
  | zero =>
    intro f args g
    simp only [fsem]
    split
    · exact himp f args g
    · exact ⟨_, rfl⟩
  | succ k ih =>
    intro f args g
    simp only [fsem]
    split
    · exact himp f args g
    · split
      · exact answers_nonempty (run_nonempty ih _ _)
      · exact ⟨_, rfl⟩

/-- One more call depth: if the two modules agree at depth `k`, they agree at `k + 1`. -/
theorem fsem_succ_rewrite {M M' : Mdl} {s s' : Code} {n m : ℕ}
    (hs : SegEquiv M.ft n Env.top s s') (hty : chk M.ft s n = some m) (hM : M.Typed)
    {imp : Env} (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites s s' n m M M') {k : ℕ} (ih : fsem M imp k = fsem M' imp k) :
    fsem M imp (k + 1) = fsem M' imp (k + 1) := by
  obtain ⟨hft, hnimp, hb⟩ := hR
  have hE : (fsem M imp k).Typed M.ft := fsem_typed hM himp k
  have hc : (fsem M imp k).Completion M.ft Env.top := ⟨Env.le_top _, hE, fsem_total M himp' k⟩
  funext f args g
  by_cases hlt : f < M.nimp
  · have e₁ : fsem M imp (k + 1) f args g = imp f args g := by
      simp only [fsem, hlt, ↓reduceIte]
    have e₂ : fsem M' imp (k + 1) f args g = imp f args g := by
      simp only [fsem, hnimp, hlt, ↓reduceIte]
    rw [e₁, e₂]
  · show fsem M imp (k + 1) f args g = fsem M' imp (k + 1) f args g
    rcases forall₂_getElem? hb (f - M.nimp) with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hr⟩
    · have e₁ : fsem M imp (k + 1) f args g = {Ans.trap} := by
        simp only [fsem, hlt, h₁, ↓reduceIte]
      have e₂ : fsem M' imp (k + 1) f args g = {Ans.trap} := by
        simp only [fsem, hnimp, hlt, h₂, ↓reduceIte]
      rw [e₁, e₂]
    · have e₁ : fsem M imp (k + 1) f args g =
          answers (run M.ft (fsem M imp k) b (initSt args g)) := by
        simp only [fsem, hlt, h₁, ↓reduceIte]
      have e₂ : fsem M' imp (k + 1) f args g =
          answers (run M.ft (fsem M imp k) b' (initSt args g)) := by
        simp only [fsem, hnimp, hlt, h₂, hft, ← ih, ↓reduceIte]
      rw [e₁, e₂, run_rw hE (hs _ hc) hty hr _ rfl]

/-- **Module rewriting.** A segment pair that runs the same from every state of its hole in
every completion of the least informative model can be exchanged at typed positions in any
bodies of any well-typed module: the module's semantics is unchanged at every call depth. -/
theorem fsem_rewrite {M M' : Mdl} {s s' : Code} {n m : ℕ}
    (hs : SegEquiv M.ft n Env.top s s') (hty : chk M.ft s n = some m) (hM : M.Typed)
    {imp : Env} (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites s s' n m M M') : ∀ k, fsem M imp k = fsem M' imp k
  | 0 => by
    funext f args g
    simp only [fsem, hR.2.1]
  | k + 1 => fsem_succ_rewrite hs hty hM himp himp' hR (fsem_rewrite hs hty hM himp himp' hR k)

/-- The denotations of all functions agree after a module rewrite. -/
theorem den_rewrite {M M' : Mdl} {s s' : Code} {n m : ℕ}
    (hs : SegEquiv M.ft n Env.top s s') (hty : chk M.ft s n = some m) (hM : M.Typed)
    {imp : Env} (himp : imp.Typed M.ft) (himp' : imp.Total)
    (hR : Mdl.Rewrites s s' n m M M') : den M imp = den M' imp := by
  funext f args g
  simp only [den, fsem_rewrite hs hty hM himp himp' hR]

end Silmaril.Proofs.Wasm.FnInst.Opt
