module

public import Silmaril.Raw.Machine.OfLambdaSSA.Ops

/-!
# Frames, agreement and block runs

The vocabulary of the correctness proof for `ofLambdaSSA`:

* `Same n fr fr'`: the registers below `n` are unchanged. Compiling a region
  allocates registers from `n` upwards, so running it changes nothing below.
* `Agrees Γ ρ env fr`: every variable of the shape context `Γ` is held, in the
  registers `ρ` gives it, as the words of its lambda-SSA value.
* `Run E ops t`: the rest of a block, its ops and then its terminator, with the
  run after a transfer described by `E` (unbounded or bounded big-step runs).
* `Cont E L ℓ ws`: what leaving a region through label `ℓ` with words `ws`
  does, given the targets `L` of the labels.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

/-! ## Frames -/

/-- The registers below `n` hold the same words in both frames. -/
def Same (n : ℕ) (fr fr' : Frame ℕ) : Prop := ∀ x < n, fr'.get x = fr.get x

theorem Same.refl (n : ℕ) (fr : Frame ℕ) : Same n fr fr := fun _ _ => rfl

theorem Same.trans {n : ℕ} {a b c : Frame ℕ} (h₁ : Same n a b) (h₂ : Same n b c) :
    Same n a c := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Same.mono {n n' : ℕ} {a b : Frame ℕ} (h : Same n' a b) (hn : n ≤ n') : Same n a b :=
  fun x hx => h x (by omega)

/-- Every register holding a variable of `Γ` lies below `n`. -/
def Below (Γ : List Shape) (ρ : List (List ℕ)) (n : ℕ) : Prop :=
  ∀ (i : ℕ) (s : Shape) (g : List ℕ), Γ[i]? = some s → ρ[i]? = some g → ∀ x ∈ g, x < n

theorem Below.mono {Γ : List Shape} {ρ : List (List ℕ)} {n n' : ℕ} (h : Below Γ ρ n)
    (hn : n ≤ n') : Below Γ ρ n' :=
  fun i s g hs hg x hx => by have := h i s g hs hg x hx; omega

theorem Below.cons {Γ : List Shape} {ρ : List (List ℕ)} {s : Shape} {g : List ℕ} {n : ℕ}
    (hρ : Below Γ ρ n) (hg : ∀ x ∈ g, x < n) : Below (s :: Γ) (g :: ρ) n := by
  intro i s' g' hs hg' x hx
  cases i with
  | zero =>
    have same : g = g' := by simpa using hg'
    exact hg x (same ▸ hx)
  | succ i => exact hρ i s' g' (by simpa using hs) (by simpa using hg') x hx

/-- A read of registers below `n` does not see a change above it. -/
theorem readAll_of_same {n : ℕ} {fr fr' : Frame ℕ} (h : Same n fr fr') {g : List ℕ}
    (hg : ∀ x ∈ g, x < n) : fr'.readAll g = fr.readAll g :=
  readAll_congr fun x hx => h x (hg x hx)

/-- Reading two register lists one after the other. -/
theorem readAll_append {fr : Frame ℕ} {g g' : List ℕ} {ws ws' : List Word}
    (h : fr.readAll g = some ws) (h' : fr.readAll g' = some ws') :
    fr.readAll (g ++ g') = some (ws ++ ws') := by
  induction g generalizing ws with
  | nil =>
    have : ws = [] := by simpa using h.symm
    simpa [this] using h'
  | cons r rs ih =>
    obtain ⟨w, ws₀, hw, hrs, rfl⟩ := readAll_cons_eq_some.mp h
    rw [List.cons_append, readAll_cons, hw, ih hrs]
    rfl

/-! ## Agreement -/

/-- The variables of `Γ` are held in the registers `ρ` gives them. -/
def Agrees (Γ : List Shape) (ρ : List (List ℕ)) (env : Semantics.Env Word) (fr : Frame ℕ) :
    Prop :=
  ∀ (i : ℕ) (s : Shape), Γ[i]? = some s → ∃ g ws, ρ[i]? = some g ∧ fr.readAll g = some ws ∧
    s.Holds (env i) ws

/-- Agreement survives changes above the registers it uses. -/
theorem Agrees.same {Γ : List Shape} {ρ : List (List ℕ)} {env : Semantics.Env Word}
    {fr fr' : Frame ℕ} {n : ℕ} (hag : Agrees Γ ρ env fr) (hb : Below Γ ρ n) (hs : Same n fr fr') :
    Agrees Γ ρ env fr' := by
  intro i s hi
  obtain ⟨g, ws, hg, hr, hh⟩ := hag i s hi
  have unchanged : fr'.readAll g = fr.readAll g := readAll_of_same hs (hb i s g hi hg)
  exact ⟨g, ws, hg, unchanged.trans hr, hh⟩

/-- Binding a value held in `g` extends agreement. -/
theorem Agrees.cons {Γ : List Shape} {ρ : List (List ℕ)} {env : Semantics.Env Word}
    {fr : Frame ℕ} (hag : Agrees Γ ρ env fr) {s : Shape} {g : List ℕ} {v : Value Word}
    {ws : List Word} (hr : fr.readAll g = some ws) (hh : s.Holds v ws) :
    Agrees (s :: Γ) (g :: ρ) (Semantics.extend env v) fr := by
  intro i s' hi
  cases i with
  | zero =>
    have same : s = s' := by simpa using hi
    exact ⟨g, ws, rfl, hr, same ▸ hh⟩
  | succ i => exact hag i s' (by simpa using hi)

/-- The empty tuple bound by a `case` is held in no registers. -/
theorem Agrees.unit {Γ : List Shape} {ρ : List (List ℕ)} {env : Semantics.Env Word}
    {fr : Frame ℕ} (hag : Agrees Γ ρ env fr) :
    Agrees (.tuple 0 :: Γ) ([] :: ρ) (Semantics.extend env .unit) fr :=
  hag.cons (g := []) (ws := []) rfl ⟨rfl, rfl⟩

/-! ## Straight-line code -/

variable {oracle : CallOracle}

/-- Running two op lists one after the other (the Raw `Ops.Exec.append`). -/
theorem ops_exec_append {o₁ o₂ : List (Op ℕ)} {fr fr₁ fr₂ : Frame ℕ} {m m₁ m₂ : Memory}
    (h₁ : Ops.Exec oracle o₁ fr m fr₁ m₁) (h₂ : Ops.Exec oracle o₂ fr₁ m₁ fr₂ m₂) :
    Ops.Exec oracle (o₁ ++ o₂) fr m fr₂ m₂ :=
  Ops.Exec.append h₁ h₂

/-- A run of two op lists is a run of each. -/
theorem ops_exec_append_inv :
    ∀ {o₁ o₂ : List (Op ℕ)} {fr fr₂ : Frame ℕ} {m m₂ : Memory},
      Ops.Exec oracle (o₁ ++ o₂) fr m fr₂ m₂ →
      ∃ fr₁ m₁, Ops.Exec oracle o₁ fr m fr₁ m₁ ∧ Ops.Exec oracle o₂ fr₁ m₁ fr₂ m₂
  | [], _, fr, _, m, _, h => ⟨fr, m, .nil, h⟩
  | _ :: _, _, _, _, _, _, .op he h =>
    have ⟨fr₁, m₁, h₁, h₂⟩ := ops_exec_append_inv h
    ⟨fr₁, m₁, .op he h₁, h₂⟩
  | _ :: _, _, _, _, _, _, .call hr ho hw h =>
    have ⟨fr₁, m₁, h₁, h₂⟩ := ops_exec_append_inv h
    ⟨fr₁, m₁, .call hr ho hw h₁, h₂⟩

/-- Running ops changes only the registers they define. -/
theorem ops_exec_get {ops : List (Op ℕ)} {fr fr' : Frame ℕ} {m m' : Memory}
    (h : Ops.Exec oracle ops fr m fr' m') {x : ℕ} (hx : x ∉ ops.flatMap Op.defs) :
    fr'.get x = fr.get x := by
  induction h with
  | nil => rfl
  | op he _ ih =>
    rw [List.flatMap_cons] at hx
    rw [ih fun hm => hx (List.mem_append_right _ hm)]
    exact op_exec_get he fun hm => hx (List.mem_append_left _ hm)
  | call _ _ hw _ ih =>
    rw [List.flatMap_cons] at hx
    rw [ih fun hm => hx (List.mem_append_right _ hm)]
    exact get_writeAll_of_not_mem hw fun hm => hx (List.mem_append_left _ (by simpa [Op.defs] using hm))

/-- Ops whose definitions lie at or above `n` leave the registers below `n` alone. -/
theorem ops_exec_same {ops : List (Op ℕ)} {fr fr' : Frame ℕ} {m m' : Memory}
    (h : Ops.Exec oracle ops fr m fr' m') {n : ℕ} (hd : ∀ r ∈ ops.flatMap Op.defs, n ≤ r) :
    Same n fr fr' :=
  fun x hx => ops_exec_get h fun hm => absurd (hd x hm) (by omega)

/-! ## Block runs and continuations -/

variable (oracle) (fn : SSA.Func ℕ)

/-- A terminator, from the frame and memory its block's ops left, followed by
the run `E` of the block it transfers to. -/
def TermRun (E : Label → Frame ℕ → Memory → Exit → Prop) :
    Term ℕ → Frame ℕ → Memory → Exit → Prop
  | .jump t as, fr, m, out => ∃ vals bt fr', fr.readAll as = some vals ∧ fn.block? t = some bt ∧
      fr.writeAll bt.params vals = some fr' ∧ E t fr' m out
  | .cond c t₁ a₁ t₂ a₂, fr, m, out => ∃ x vals bt fr', fr.get c = some x ∧
      fr.readAll (if x = 0 then a₂ else a₁) = some vals ∧
      fn.block? (if x = 0 then t₂ else t₁) = some bt ∧ fr.writeAll bt.params vals = some fr' ∧
      E (if x = 0 then t₂ else t₁) fr' m out
  | .ret rs, fr, m, out => ∃ vals, fr.readAll rs = some vals ∧ out = .returned vals m
  | .trap, _, m, out => out = .trapped m

/-- The rest of a block: its ops, then its terminator. -/
def Run (E : Label → Frame ℕ → Memory → Exit → Prop) (ops : List (Op ℕ)) (t : Term ℕ)
    (fr : Frame ℕ) (m : Memory) (out : Exit) : Prop :=
  ∃ fr₁ m₁, Ops.Exec oracle ops fr m fr₁ m₁ ∧ TermRun fn E t fr₁ m₁ out

/-- Leaving a region through label `ℓ` with the words `ws`, from frame `frX`. -/
def Cont (E : Label → Frame ℕ → Memory → Exit → Prop) (L : List (SSA.Target × ℕ)) (ℓ : ℕ)
    (ws : List Word) (frX : Frame ℕ) (m : Memory) (out : Exit) : Prop :=
  match L[ℓ]? with
  | some (.block t, _) =>
      ∃ bt fr', fn.block? t = some bt ∧ frX.writeAll bt.params ws = some fr' ∧ E t fr' m out
  | some (.ret, _) => out = .returned ws m
  | some (.trap, _) => out = .trapped m
  | none => False

variable {oracle fn}

/-- Labels past a prefix of targets are the labels of the rest. -/
theorem cont_append {E : Label → Frame ℕ → Memory → Exit → Prop} {pre L : List (SSA.Target × ℕ)}
    {ℓ : ℕ} (hℓ : pre.length ≤ ℓ) {ws : List Word} {frX : Frame ℕ} {m : Memory} {out : Exit} :
    Cont fn E (pre ++ L) ℓ ws frX m out ↔ Cont fn E L (ℓ - pre.length) ws frX m out := by
  unfold Cont
  rw [List.getElem?_append_right hℓ]

/-- A run from a block is its ops and terminator. -/
theorem run_of_exec {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {fr : Frame ℕ}
    {m : Memory} {out : Exit} (h : Func.Exec oracle fn l fr m out) :
    Run oracle fn (Func.Exec oracle fn) b.ops b.term fr m out := by
  cases h with
  | jump hb' hops hterm hargs hbt hw hrest =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, _, _, hargs, hbt, hw, hrest⟩⟩
  | cond hb' hops hterm hget hargs hbt hw hrest =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, _, _, _, hget, hargs, hbt, hw, hrest⟩⟩
  | ret hb' hops hterm hargs =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, hargs, rfl⟩⟩
  | trap hb' hops hterm =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; rfl⟩

/-- A block's ops and terminator, followed by a run, are a run from the block. -/
theorem exec_of_run {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {fr : Frame ℕ}
    {m : Memory} {out : Exit} (h : Run oracle fn (Func.Exec oracle fn) b.ops b.term fr m out) :
    Func.Exec oracle fn l fr m out := by
  obtain ⟨fr₁, m₁, hops, hterm⟩ := h
  cases ht : b.term with
  | jump t as =>
    obtain ⟨vals, bt, fr', hargs, hbt, hw, hrest⟩ := ht ▸ hterm
    exact .jump hb hops ht hargs hbt hw hrest
  | cond c t₁ a₁ t₂ a₂ =>
    obtain ⟨x, vals, bt, fr', hget, hargs, hbt, hw, hrest⟩ := ht ▸ hterm
    exact .cond hb hops ht hget hargs hbt hw hrest
  | ret rs =>
    obtain ⟨vals, hargs, rfl⟩ := ht ▸ hterm
    exact .ret hb hops ht hargs
  | trap =>
    have hout : TermRun fn _ .trap fr₁ m₁ out := ht ▸ hterm
    exact (show out = .trapped m₁ from hout) ▸ .trap hb hops ht

/-- A block's run is its ops and terminator. -/
theorem exec_iff_run {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {fr : Frame ℕ}
    {m : Memory} {out : Exit} :
    Func.Exec oracle fn l fr m out ↔ Run oracle fn (Func.Exec oracle fn) b.ops b.term fr m out :=
  ⟨run_of_exec hb, exec_of_run hb⟩

/-- A bounded run with one more transfer is a block run followed by bounded runs. -/
theorem run_of_execIn_succ {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {n : ℕ}
    {fr : Frame ℕ} {m : Memory} {out : Exit} (h : Func.ExecIn oracle fn (n + 1) l fr m out) :
    Run oracle fn (Func.ExecIn oracle fn n) b.ops b.term fr m out := by
  cases h with
  | jump hb' hops hterm hargs hbt hw hrest =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, _, _, hargs, hbt, hw, hrest⟩⟩
  | cond hb' hops hterm hget hargs hbt hw hrest =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, _, _, _, hget, hargs, hbt, hw, hrest⟩⟩
  | ret hb' hops hterm hargs =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, hargs, rfl⟩⟩
  | trap hb' hops hterm =>
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact ⟨_, _, hops, by rw [hterm]; rfl⟩

/-- A block run followed by bounded runs is a bounded run with one more transfer. -/
theorem execIn_succ_of_run {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {n : ℕ}
    {fr : Frame ℕ} {m : Memory} {out : Exit}
    (h : Run oracle fn (Func.ExecIn oracle fn n) b.ops b.term fr m out) :
    Func.ExecIn oracle fn (n + 1) l fr m out := by
  obtain ⟨fr₁, m₁, hops, hterm⟩ := h
  cases ht : b.term with
  | jump t as =>
    obtain ⟨vals, bt, fr', hargs, hbt, hw, hrest⟩ := ht ▸ hterm
    exact .jump hb hops ht hargs hbt hw hrest
  | cond c t₁ a₁ t₂ a₂ =>
    obtain ⟨x, vals, bt, fr', hget, hargs, hbt, hw, hrest⟩ := ht ▸ hterm
    exact .cond hb hops ht hget hargs hbt hw hrest
  | ret rs =>
    obtain ⟨vals, hargs, rfl⟩ := ht ▸ hterm
    exact .ret hb hops ht hargs
  | trap =>
    have hout : TermRun fn _ .trap fr₁ m₁ out := ht ▸ hterm
    exact (show out = .trapped m₁ from hout) ▸ .trap hb hops ht

/-- A bounded run that makes one more transfer is a block run followed by bounded runs. -/
theorem execIn_succ_iff_run {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {n : ℕ}
    {fr : Frame ℕ} {m : Memory} {out : Exit} :
    Func.ExecIn oracle fn (n + 1) l fr m out ↔
      Run oracle fn (Func.ExecIn oracle fn n) b.ops b.term fr m out :=
  ⟨run_of_execIn_succ hb, execIn_succ_of_run hb⟩

/-- Allowing one more transfer allows every run that already fitted. -/
theorem execIn_succ {n : ℕ} {l : Label} {fr : Frame ℕ} {m : Memory} {out : Exit}
    (h : Func.ExecIn oracle fn n l fr m out) : Func.ExecIn oracle fn (n + 1) l fr m out := by
  induction h with
  | jump hb hops hterm hargs hbt hw _ ih => exact .jump hb hops hterm hargs hbt hw ih
  | cond hb hops hterm hget hargs hbt hw _ ih => exact .cond hb hops hterm hget hargs hbt hw ih
  | ret hb hops hterm hargs => exact .ret hb hops hterm hargs
  | trap hb hops hterm => exact .trap hb hops hterm

/-- Allowing more transfers allows every run that already fitted. -/
theorem execIn_mono {n n' : ℕ} (hn : n ≤ n') {l : Label} {fr : Frame ℕ} {m : Memory}
    {out : Exit} (h : Func.ExecIn oracle fn n l fr m out) : Func.ExecIn oracle fn n' l fr m out := by
  induction hn with
  | refl => exact h
  | step _ ih => exact execIn_succ ih

/-- A bounded run of a block is its ops and terminator, the rest bounded by one less. -/
theorem run_of_execIn {l : Label} {b : SSA.Block ℕ} (hb : fn.block? l = some b) {n : ℕ}
    {fr : Frame ℕ} {m : Memory} {out : Exit} (h : Func.ExecIn oracle fn n l fr m out) :
    Run oracle fn (Func.ExecIn oracle fn (n - 1)) b.ops b.term fr m out := by
  cases n with
  | zero =>
    cases h with
    | ret hb' hops hterm hargs =>
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      exact ⟨_, _, hops, by rw [hterm]; exact ⟨_, hargs, rfl⟩⟩
    | trap hb' hops hterm =>
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      exact ⟨_, _, hops, by rw [hterm]; rfl⟩
  | succ n => exact (execIn_succ_iff_run hb).1 h

end Silmaril.Proofs.Machine.OfLambdaSSA
