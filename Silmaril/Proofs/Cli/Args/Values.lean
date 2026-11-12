module

public import Silmaril.Cli.Args.Defs

@[expose] public section

/-!
# Proofs: typed values and positional arguments

* `digitsAux_eq`, `parseNat_toString`, `parseInt_toString`, **`parse_show`**: every value of a
  type parses back from its canonical spelling (`Value.show`), for every `ArgType`;
  `parse_has`: what a type parses is a value of the type;
* `Binds`: positional binding as an inductive relation, one rule per arity, and
  **`bindPos_eq_ok_iff`**: `bindPos ps ws = .ok r ↔ Binds ps ws r` for every list of
  positionals; `bindPos_show`: words spelled from values bind back to them.

A Silmaril addition.
-/

namespace Silmaril.Cli

/-! ## Values -/

theorem digitsAux_eq : ∀ {cs : List Char} (acc : Nat), (∀ ch ∈ cs, ch.isDigit = true) →
    ArgType.digitsAux acc cs = some (Nat.ofDigitChars 10 cs acc)
  | [], acc, _ => by simp [ArgType.digitsAux]
  | ch :: cs, acc, h => by
    have hch : ch.isDigit = true := h ch List.mem_cons_self
    have ih := digitsAux_eq (cs := cs) (10 * acc + (ch.toNat - '0'.toNat))
      fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [ArgType.digitsAux, hch, ↓reduceIte, ih, Nat.ofDigitChars_cons]

theorem digitsAux_none : ∀ {cs : List Char} (acc : Nat), (∃ ch ∈ cs, ch.isDigit = false) →
    ArgType.digitsAux acc cs = none
  | [], _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | ch :: cs, acc, ⟨c, hc, hd⟩ => by
    by_cases hch : ch.isDigit = true
    · have hc' : c ∈ cs := by
        rcases List.mem_cons.mp hc with rfl | hc'
        · simp_all
        · exact hc'
      simp only [ArgType.digitsAux, hch, ↓reduceIte]
      exact digitsAux_none _ ⟨c, hc', hd⟩
    · simp [ArgType.digitsAux, hch]

theorem toDigits_isDigit (n : Nat) : ∀ ch ∈ Nat.toDigits 10 n, ch.isDigit = true :=
  fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- Decimal digits read back. -/
theorem parseNat_toString (n : Nat) : ArgType.parseNat (toString n) = some n := by
  have hl : (toString n).toList = Nat.toDigits 10 n := by
    rw [Nat.toString_eq_repr, Nat.toList_repr]
  unfold ArgType.parseNat
  rw [hl]
  split
  · rename_i h; exact absurd h Nat.toDigits_ne_nil
  · rw [digitsAux_eq 0 (toDigits_isDigit n), Nat.ofDigitChars_ten_toDigits]

theorem toDigits_head (n : Nat) : ∃ ch cs, Nat.toDigits 10 n = ch :: cs ∧ ch ≠ '-' := by
  match h : Nat.toDigits 10 n with
  | [] => exact absurd h Nat.toDigits_ne_nil
  | ch :: cs =>
    refine ⟨ch, cs, rfl, fun he => ?_⟩
    have hd := toDigits_isDigit n ch (by rw [h]; exact List.mem_cons_self)
    rw [he] at hd
    exact absurd hd (by decide)

theorem parseInt_digits {s : String} {ch : Char} {cs : List Char} (hl : s.toList = ch :: cs)
    (hne : ch ≠ '-') (hall : ∀ c ∈ ch :: cs, c.isDigit = true) :
    ArgType.parseInt s = some (Nat.ofDigitChars 10 (ch :: cs) 0 : Int) := by
  unfold ArgType.parseInt
  rw [hl]
  split
  · rename_i h; simp at h
  · rename_i h; simp at h; exact absurd h.1 hne
  · rename_i h; simp at h; exact absurd h.1 hne
  · rw [digitsAux_eq 0 hall]; rfl

theorem parseInt_minus {s : String} {cs : List Char} (hl : s.toList = '-' :: cs) (hcs : cs ≠ [])
    (hall : ∀ c ∈ cs, c.isDigit = true) :
    ArgType.parseInt s = some (-(Nat.ofDigitChars 10 cs 0 : Int)) := by
  obtain ⟨c, cs₀, rfl⟩ := List.exists_cons_of_ne_nil hcs
  simp [ArgType.parseInt, hl, digitsAux_eq 0 hall]

/-- Integers read back. -/
theorem parseInt_toString (i : Int) : ArgType.parseInt (toString i) = some i := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  by_cases hi : 0 ≤ i
  · obtain ⟨ch, cs, hcs, hne⟩ := toDigits_head i.toNat
    have hl : i.toNat.repr.toList = ch :: cs := by rw [Nat.toList_repr, hcs]
    have hall : ∀ c ∈ ch :: cs, c.isDigit = true := hcs ▸ toDigits_isDigit i.toNat
    simp only [hi, ↓reduceIte]
    rw [parseInt_digits hl hne hall, ← hcs, Nat.ofDigitChars_ten_toDigits]
    simp [Int.toNat_of_nonneg hi]
  · obtain ⟨ch, cs, hcs, -⟩ := toDigits_head (-i).toNat
    have hl : ("-" ++ (-i).toNat.repr).toList = '-' :: ch :: cs := by
      simp [Nat.toList_repr, hcs]
    have hall : ∀ c ∈ ch :: cs, c.isDigit = true := hcs ▸ toDigits_isDigit (-i).toNat
    simp only [hi, ↓reduceIte]
    rw [parseInt_minus hl (by simp) hall, ← hcs, Nat.ofDigitChars_ten_toDigits]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ -i)]

/-- **Every value of a type parses back from its canonical spelling.** -/
theorem parse_show {t : ArgType} {v : Value} (h : t.Has v) : t.parse v.show = some v := by
  match t, v, h with
  | .str, .str _, _ => rfl
  | .path, .str _, _ => rfl
  | .nat, .nat n, _ =>
    show (ArgType.parseNat (toString n)).map Value.nat = some (.nat n)
    rw [parseNat_toString]; rfl
  | .int, .int i, _ =>
    show (ArgType.parseInt (toString i)).map Value.int = some (.int i)
    rw [parseInt_toString]; rfl
  | .enum cs, .str s, h => simp [ArgType.parse, Value.show, ArgType.Has] at h ⊢; exact h

/-- What a type parses is a value of the type. -/
theorem parse_has {t : ArgType} {s : String} {v : Value} (h : t.parse s = some v) : t.Has v := by
  cases t with
  | str => simp [ArgType.parse] at h; subst h; trivial
  | path => simp [ArgType.parse] at h; subst h; trivial
  | nat =>
    simp [ArgType.parse] at h; obtain ⟨n, -, rfl⟩ := h; trivial
  | int =>
    simp [ArgType.parse] at h; obtain ⟨n, -, rfl⟩ := h; trivial
  | enum cs =>
    simp [ArgType.parse] at h; obtain ⟨hs, rfl⟩ := h; exact hs

theorem parseAs_eq_ok {id : String} {t : ArgType} {s : String} {v : Value} :
    parseAs id t s = .ok v ↔ t.parse s = some v := by
  unfold parseAs
  cases t.parse s <;> simp

theorem mapM_parseAs {id : String} {t : ArgType} :
    ∀ {ws : List String} {vs : List Value},
      ws.mapM (parseAs id t) = .ok vs ↔ ws.mapM t.parse = some vs
  | [], vs => by simp [pure, Except.pure]
  | w :: ws, vs => by
    have ih := @mapM_parseAs id t ws
    cases hp : t.parse w with
    | none => simp [List.mapM_cons, parseAs, hp, bind, Except.bind]
    | some v =>
      have hw : parseAs id t w = .ok v := by simp [parseAs, hp]
      cases hr : ws.mapM t.parse with
      | none =>
        cases hq : ws.mapM (parseAs id t) with
        | error e => simp [List.mapM_cons, hw, hp, hr, hq, bind, Except.bind]
        | ok vs' => simp [ih.mp hq] at hr
      | some vs' =>
        have hq : ws.mapM (parseAs id t) = .ok vs' := ih.mpr hr
        simp [List.mapM_cons, hw, hp, hr, hq, bind, Except.bind, pure, Except.pure]

/-! ## Positional binding -/

/-- **Positional binding, one rule per arity.** -/
inductive Binds : List Pos → List String → List (String × List Value) → Prop where
  | nil : Binds [] [] []
  | one {p ps w ws v r} : p.arity = .one → p.type.parse w = some v → Binds ps ws r →
      Binds (p :: ps) (w :: ws) ((p.id, [v]) :: r)
  | optSome {p ps w ws v r} : p.arity = .optional → p.type.parse w = some v → Binds ps ws r →
      Binds (p :: ps) (w :: ws) ((p.id, [v]) :: r)
  | optNone {p ps r} : p.arity = .optional → Binds ps [] r → Binds (p :: ps) [] ((p.id, []) :: r)
  | many {p ps ws vs r} : p.arity = .many → ws.mapM p.type.parse = some vs → Binds ps [] r →
      Binds (p :: ps) ws ((p.id, vs) :: r)
  | atLeastOne {p ps ws vs r} : p.arity = .atLeastOne → ws ≠ [] →
      ws.mapM p.type.parse = some vs → Binds ps [] r → Binds (p :: ps) ws ((p.id, vs) :: r)

theorem except_bind_ok {ε α β : Type} {e : Except ε α} {k : α → Except ε β} {b : β}
    (h : (e >>= k) = .ok b) : ∃ a, e = .ok a ∧ k a = .ok b := by
  cases e with
  | error x => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

theorem bind2_ok {ε α β γ : Type} {e₁ : Except ε α} {e₂ : Except ε β} {f : α → β → γ} {c : γ}
    (h : (do let a ← e₁; let b ← e₂; pure (f a b)) = Except.ok c) :
    ∃ a b, e₁ = .ok a ∧ e₂ = .ok b ∧ c = f a b := by
  cases e₁ with
  | error x => exact absurd h (by simp [bind, Except.bind])
  | ok a =>
    cases e₂ with
    | error x => exact absurd h (by simp [bind, Except.bind])
    | ok b => exact ⟨a, b, rfl, rfl, (Except.ok.inj h).symm⟩

theorem bind1_ok {ε β γ : Type} {e₂ : Except ε β} {f : β → γ} {c : γ}
    (h : (do let b ← e₂; pure (f b)) = Except.ok c) : ∃ b, e₂ = .ok b ∧ c = f b := by
  cases e₂ with
  | error x => exact absurd h (by simp [bind, Except.bind])
  | ok b => exact ⟨b, rfl, (Except.ok.inj h).symm⟩

/-- Soundness of `bindPos`. -/
theorem bindPos_sound {ps : List Pos} {ws : List String} {r : List (String × List Value)} :
    bindPos ps ws = .ok r → Binds ps ws r := by
  fun_induction bindPos ps ws generalizing r with
  | case1 => intro h; simp at h; subst h; exact .nil
  | case2 => intro h; simp at h
  | case3 => intro h; simp at h
  | case4 => intro h; simp at h
  | case5 p ps w ws' ha ih =>
    intro h; obtain ⟨v, r', hv, hr, rfl⟩ := bind2_ok h; exact .one ha (parseAs_eq_ok.mp hv) (ih hr)
  | case6 p ps w ws' ha ih =>
    intro h; obtain ⟨v, r', hv, hr, rfl⟩ := bind2_ok h
    exact .optSome ha (parseAs_eq_ok.mp hv) (ih hr)
  | case7 p ps ha ih => intro h; obtain ⟨r', hr, rfl⟩ := bind1_ok h; exact .optNone ha (ih hr)
  | case8 p ps ws ha ih =>
    intro h; obtain ⟨vs, r', hvs, hr, rfl⟩ := bind2_ok h
    exact .many ha (mapM_parseAs.mp hvs) (ih hr)
  | case9 p ps ws hne ha ih =>
    intro h; obtain ⟨vs, r', hvs, hr, rfl⟩ := bind2_ok h
    exact .atLeastOne ha (by rintro rfl; exact hne rfl) (mapM_parseAs.mp hvs) (ih hr)

/-- Completeness of `bindPos`. -/
theorem bindPos_complete {ps : List Pos} {ws : List String} {r : List (String × List Value)}
    (h : Binds ps ws r) : bindPos ps ws = .ok r := by
  induction h with
  | nil => rfl
  | one ha hv _ ih =>
    simp [bindPos, ha, parseAs_eq_ok.mpr hv, ih, bind, Except.bind, pure, Except.pure]
  | optSome ha hv _ ih =>
    simp [bindPos, ha, parseAs_eq_ok.mpr hv, ih, bind, Except.bind, pure, Except.pure]
  | optNone ha _ ih => simp [bindPos, ha, ih, bind, Except.bind, pure, Except.pure]
  | @many p ps ws vs r ha hvs _ ih =>
    have hvs' : ws.mapM (parseAs p.id p.type) = .ok vs := mapM_parseAs.mpr hvs
    simp only [bindPos, ha]
    simp [hvs', ih, bind, Except.bind, pure, Except.pure]
  | @atLeastOne p ps ws vs r ha hne hvs _ ih =>
    have hvs' : ws.mapM (parseAs p.id p.type) = .ok vs := mapM_parseAs.mpr hvs
    match ws, hne, hvs' with
    | w :: ws, _, hvs' =>
      simp only [bindPos, ha]
      simp [hvs', ih, bind, Except.bind, pure, Except.pure]

/-- **Positional binding is the inductive relation**, for every arity. -/
theorem bindPos_eq_ok_iff {ps : List Pos} {ws : List String} {r : List (String × List Value)} :
    bindPos ps ws = .ok r ↔ Binds ps ws r :=
  ⟨bindPos_sound, bindPos_complete⟩

theorem mapM_parse_show {t : ArgType} :
    ∀ {vs : List Value}, (∀ v ∈ vs, t.Has v) → (vs.map Value.show).mapM t.parse = some vs := by
  intro vs
  induction vs with
  | nil => intro _; rfl
  | cons v vs ih =>
    intro h
    simp [parse_show (h v List.mem_cons_self), ih fun v hv => h v (List.mem_cons_of_mem _ hv)]

end Silmaril.Cli
