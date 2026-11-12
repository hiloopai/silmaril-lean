module

public import Silmaril.Proofs.Wasm.Tools.Meta.FastCmd
public import Silmaril.Wasm.Tools.Meta.Frame.Thms

/-!
# Proofs: `payloadOfB` and `addMetadataB` compute their specifications

Restated in `Silmaril.Wasm.Tools.Meta.FastCmd.Thms`.

The list walk (`walkItems`) locates a nested unit by adding up the lengths of the items before
it; the array walk (`walkItemsB`) takes the positions the parser recorded. `Lay` states that the
items of a successful array walk lie one after the other from where the walk started to where the
input ends (`secs_lay`), which makes the two agree (`Lay_len`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Tools.Meta

open Silmaril.Wasm.Tools.Meta Silmaril.Wasm.Tools.Meta.Metadata

/-! ## Layout of the items of a walk -/

/-- The items `is` lie one after the other from `p` to `q`: each section starts with its id at
the current position, its size field follows, then its contents; a nested unit's contents are its
header (8 bytes) and then its own items. -/
def Lay : Nat → List ItemB → Nat → Prop
  | p, [], q => p = q
  | p, .sec s :: is, q =>
    s.sizeAt = p + 1 ∧ s.sizeAt ≤ s.bodyAt ∧ s.bodyAt ≤ s.bodyEnd ∧ Lay s.bodyEnd is q
  | p, .nest _ sa a b _ its :: is, q =>
    sa = p + 1 ∧ sa ≤ a ∧ a + 8 ≤ b ∧ Lay (a + 8) its b ∧ Lay b is q
termination_by _ is _ => sizeOf is
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem Lay_le : ∀ (p : Nat) (is : List ItemB) (q : Nat), Lay p is q → p ≤ q
  | p, [], q, h => by unfold Lay at h; omega
  | p, .sec s :: is, q, h => by
    unfold Lay at h
    have := Lay_le _ is q h.2.2.2
    omega
  | p, .nest _ sa a b _ its :: is, q, h => by
    unfold Lay at h
    have := Lay_le _ is q h.2.2.2.2
    omega

theorem header_length (enc : Enc) : enc.header.length = 8 := by
  cases enc <;> rfl

theorem listBytes_cons (i : Item) (is : List Item) :
    Item.listBytes (i :: is) = i.bytes ++ Item.listBytes is := by
  rw [Item.listBytes]

theorem bytes_nest (id : UInt8) (size : List UInt8) (enc : Enc) (items : List Item) :
    (Item.nest id size enc items).bytes = id :: (size ++ (enc.header ++ Item.listBytes items)) := by
  rw [Item.bytes]

theorem bytes_sec (s : Sec) : (Item.sec s).bytes = s.bytes := by
  rw [Item.bytes]

/-- The items occupy exactly their layout. -/
theorem Lay_len (ba : ByteArray) : ∀ (p : Nat) (is : List ItemB) (q : Nat), Lay p is q →
    q ≤ ba.size → (Item.listBytes (is.map (ItemB.toItem ba))).length = q - p
  | p, [], q, h, _ => by unfold Lay at h; subst h; simp [Item.listBytes]
  | p, .sec s :: is, q, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hl := Lay_le _ is q h4
    have ih := Lay_len ba _ is q h4 hq
    rw [List.map_cons, listBytes_cons, toItem_sec, bytes_sec, List.length_append, ih]
    simp only [Sec.bytes, SecB.toSec, List.length_cons, List.length_append]
    rw [sl_length ba _ _ (by omega), sl_length ba _ _ (by omega)]
    omega
  | p, .nest id sa a b enc its :: is, q, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl := Lay_le _ is q h5
    have ih := Lay_len ba _ is q h5 hq
    have ih' := Lay_len ba _ its b h4 (by omega)
    rw [List.map_cons, listBytes_cons, toItem_nest, bytes_nest, List.length_append, ih]
    simp only [List.length_cons, List.length_append, header_length, ih']
    rw [sl_length ba _ _ (by omega)]
    omega
termination_by _ is _ => sizeOf is
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Every section of a layout inside the input lies inside the input. -/
theorem Lay_inside (ba : ByteArray) : ∀ (p : Nat) (is : List ItemB) (q : Nat), Lay p is q →
    q ≤ ba.size → ∀ it ∈ is, ItemB.inside ba.size it
  | p, [], q, _, _ => by simp
  | p, .sec s :: is, q, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hl := Lay_le _ is q h4
    intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · exact ⟨h3, by omega⟩
    · exact Lay_inside ba _ is q h4 hq it hit
  | p, .nest id sa a b enc its :: is, q, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl := Lay_le _ is q h5
    intro it hit
    rcases List.mem_cons.mp hit with rfl | hit
    · exact ⟨by omega, by omega⟩
    · exact Lay_inside ba _ is q h5 hq it hit

mutual
/-- **The items of a successful walk of a nested unit are laid out from its start to its input
limit.** -/
theorem secs_lay (ba : ByteArray) (hk : Hook) :
    ∀ (f : Nat) (enc : Enc) (st : PState) (pos lim m : Nat) (v : List ItemB),
      lim ≤ ba.size → pos ≤ lim → parseSecsHB ba hk f enc st pos lim (some m) = .ok v → Lay pos v lim
  | 0, _, _, _, _, _, _, _, _, h => by simp [parseSecsHB] at h
  | f + 1, enc, st, pos, lim, m, v, hl, hp, h => by
    unfold parseSecsHB at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h; · cases h
      split at h; · cases h
      cases h; unfold Lay; omega
    · split at h; · cases h
      split at h; · cases h
      split at h; · cases h
      rename_i _ r hr
      rcases r with ⟨len, a⟩
      have hal := rdU32_le ba lim (pos + 1) len a hr hl
      have hpa := rdU32_lt ba lim (pos + 1) len a hr
      split at h; · cases h
      split at h
      · -- nested
        split at h; · cases h
        split at h; · cases h
        rename_i _ r hu
        rcases r with ⟨enc', items⟩
        split at h; · cases h
        rename_i _ is hs
        cases h
        have hb : a + len ≤ lim := by
          by_cases hc : a + len ≤ lim
          · exact hc
          · have hmin : Nat.min (a + len) lim = lim := by
              unfold Nat.min; omega
            dsimp only at hu
            rw [hmin] at hu
            have := unit_ok_le ba hk f _ a lim (a + len) _ hl hu
            omega
        have hmin : Nat.min (a + len) lim = a + len := by unfold Nat.min; omega
        dsimp only at hu
        rw [hmin] at hu
        have hun := unit_lay ba hk f _ a (a + len) _ _ (by omega) hu
        have hrest := secs_lay ba hk f enc st (a + len) lim m is hl hb hs
        unfold Lay
        exact ⟨rfl, by omega, hun.1, hun.2, hrest⟩
      · split at h
        · -- code
          split at h; · cases h
          rename_i o _
          split at h; · cases h
          split at h; · cases h
          rename_i _ r hq
          rcases r with ⟨n, p⟩
          have hpl := rdU32_le ba lim a n p hq hl
          have hap := rdU32_lt ba lim a n p hq
          split at h; · cases h
          rename_i hlen
          split at h; · cases h
          split at h; · cases h
          rename_i _ e he
          have hce := codeBodiesB_end ba lim hl n p _ e hpl he
          split at h; · cases h
          rename_i _ is hs
          cases h
          have hrest := secs_lay ba hk f enc _ e lim m is hl hce.2 hs
          have hee : e = a + len := by dsimp only at hlen; omega
          subst hee
          unfold Lay
          exact ⟨rfl, by dsimp only; omega, by dsimp only; omega, hrest⟩
        · -- other sections
          split at h; · cases h
          rename_i _ e he
          obtain ⟨rfl, hle⟩ := rdBytes_ok lim a len e he
          split at h <;>
          · split at h; · cases h
            split at h
            · split at h; · cases h
              split at h; · cases h
              rename_i _ is hs
              cases h
              have hrest := secs_lay ba hk f _ _ (a + len) lim m is hl hle hs
              unfold Lay
              exact ⟨rfl, by dsimp only; omega, by dsimp only; omega, hrest⟩
            · split at h; · cases h
              rename_i _ is hs
              cases h
              have hrest := secs_lay ba hk f _ _ (a + len) lim m is hl hle hs
              unfold Lay
              exact ⟨rfl, by dsimp only; omega, by dsimp only; omega, hrest⟩
/-- A successful nested unit has its header and then its items laid out to its input limit. -/
theorem unit_lay (ba : ByteArray) (hk : Hook) :
    ∀ (f : Nat) (ex : Option Enc) (pos lim m : Nat) (v : Enc × List ItemB),
      lim ≤ ba.size → parseUnitHB ba hk f ex pos lim (some m) = .ok v → pos + 8 ≤ lim ∧ Lay (pos + 8) v.2 lim
  | 0, _, _, _, _, _, _, h => by simp [parseUnitHB] at h
  | f + 1, ex, pos, lim, m, v, hl, h => by
    unfold parseUnitHB at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i _ r hh
    rcases r with ⟨enc, p⟩
    have hp := readHeaderB_pos ba ex lim pos enc p hh
    split at h; · cases h
    rename_i _ is hs
    cases h
    obtain ⟨rfl, hpl⟩ := hp
    exact ⟨hpl, secs_lay ba hk f enc {} _ lim m is hl hpl hs⟩
end

/-- **The items of a successful walk of the outer unit are laid out to the end of the input.** -/
theorem secs_lay_outer (ba : ByteArray) (hk : Hook) :
    ∀ (f : Nat) (enc : Enc) (st : PState) (pos lim : Nat) (v : List ItemB),
      lim ≤ ba.size → pos ≤ lim → parseSecsHB ba hk f enc st pos lim none = .ok v → Lay pos v lim
  | 0, _, _, _, _, _, _, _, h => by simp [parseSecsHB] at h
  | f + 1, enc, st, pos, lim, v, hl, hp, h => by
    unfold parseSecsHB at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h; · cases h
      cases h; unfold Lay; omega
    · split at h; · cases h
      split at h; · cases h
      split at h; · cases h
      rename_i _ r hr
      rcases r with ⟨len, a⟩
      have hal := rdU32_le ba lim (pos + 1) len a hr hl
      have hpa := rdU32_lt ba lim (pos + 1) len a hr
      split at h
      · -- nested
        split at h; · cases h
        split at h; · cases h
        rename_i _ r hu
        rcases r with ⟨enc', items⟩
        split at h; · cases h
        rename_i _ is hs
        cases h
        have hb : a + len ≤ lim := by
          by_cases hc : a + len ≤ lim
          · exact hc
          · have hmin : Nat.min (a + len) lim = lim := by
              unfold Nat.min; omega
            dsimp only at hu
            rw [hmin] at hu
            have := unit_ok_le ba hk f _ a lim (a + len) _ hl hu
            omega
        have hmin : Nat.min (a + len) lim = a + len := by unfold Nat.min; omega
        dsimp only at hu
        rw [hmin] at hu
        have hun := unit_lay ba hk f _ a (a + len) _ _ (by omega) hu
        have hrest := secs_lay_outer ba hk f enc st (a + len) lim is hl hb hs
        unfold Lay
        exact ⟨rfl, by omega, hun.1, hun.2, hrest⟩
      · split at h
        · -- code
          split at h; · cases h
          rename_i o _
          split at h; · cases h
          split at h; · cases h
          rename_i _ r hq
          rcases r with ⟨n, p⟩
          have hpl := rdU32_le ba lim a n p hq hl
          have hap := rdU32_lt ba lim a n p hq
          split at h; · cases h
          rename_i hlen
          split at h; · cases h
          split at h; · cases h
          rename_i _ e he
          have hce := codeBodiesB_end ba lim hl n p _ e hpl he
          split at h; · cases h
          rename_i _ is hs
          cases h
          have hrest := secs_lay_outer ba hk f enc _ e lim is hl hce.2 hs
          have hee : e = a + len := by dsimp only at hlen; omega
          subst hee
          unfold Lay
          exact ⟨rfl, by dsimp only; omega, by dsimp only; omega, hrest⟩
        · -- other sections
          split at h; · cases h
          rename_i _ e he
          obtain ⟨rfl, hle⟩ := rdBytes_ok lim a len e he
          split at h <;>
          · split at h; · cases h
            split at h
            · split at h; · cases h
              split at h; · cases h
              rename_i _ is hs
              cases h
              have hrest := secs_lay_outer ba hk f _ _ (a + len) lim is hl hle hs
              unfold Lay
              exact ⟨rfl, by dsimp only; omega, by dsimp only; omega, hrest⟩
            · split at h; · cases h
              rename_i _ is hs
              cases h
              have hrest := secs_lay_outer ba hk f _ _ (a + len) lim is hl hle hs
              unfold Lay
              exact ⟨rfl, by dsimp only; omega, by dsimp only; omega, hrest⟩

theorem parseBinaryB_lay (ba : ByteArray) (enc : Enc) (items : List ItemB)
    (h : parseBinaryB ba = .ok (enc, items)) : 8 ≤ ba.size ∧ Lay 8 items ba.size := by
  unfold parseBinaryB parseBinaryHB parseUnitHB at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i _ r hh
  rcases r with ⟨en, p⟩
  have hp := readHeaderB_pos ba none ba.size 0 en p hh
  split at h; · cases h
  rename_i _ is hs
  cases h
  obtain ⟨rfl, hpl⟩ := hp
  exact ⟨hpl, secs_lay_outer ba noHook _ _ {} _ ba.size _ (Nat.le_refl _) hpl hs⟩

/-! ## `metadata show` -/

theorem bind_opt {ε ε' α β : Type} {x : Except ε α} {y : Except ε' α} {g : α → Except ε β}
    {g' : α → Except ε' β} (hx : x.toOption = y.toOption) (hg : ∀ a, (g a).toOption = (g' a).toOption) :
    (x >>= g).toOption = (y >>= g').toOption := by
  cases x <;> cases y <;> simp_all [Except.toOption, bind, Except.bind]

theorem readCustom_other (m : Meta) (nm data : List UInt8) (h : strOf nm ∉ metaNames) :
    readCustom m nm data = .ok m := by
  simp only [metaNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  unfold readCustom
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, pure, Except.pure]

/-- The effect of one custom section agrees. -/
theorem customStep_opt (ba : ByteArray) (m : Meta) (s : SecB) (hb : s.bodyEnd ≤ ba.size) :
    (match customOfB ba s.bodyAt s.bodyEnd with
      | .ok (ns, ne) =>
        match readCustomB ba m ns ne s.bodyEnd with
        | .ok m => (pure m : Except String Meta)
        | .error e => throw (customMsg ba ns ne s.bodyEnd e)
      | .error e => throw e.render).toOption =
    (match customOf (sl ba s.bodyAt s.bodyEnd) with
      | .ok (nm, data) => readCustom m nm data
      | .error e => throw e).toOption := by
  have hc := customOf_ag ba s.bodyAt s.bodyEnd hb
  cases hcb : customOfB ba s.bodyAt s.bodyEnd with
  | error e =>
    obtain ⟨e', he'⟩ := hc.err e (by simpa [customOfB] using hcb)
    simp [he', throw, throwThe, MonadExceptOf.throw, Except.toOption]
  | ok r =>
    rcases r with ⟨ns, ne⟩
    have he' := hc.ok_iff (ns, ne) (by simpa [customOfB] using hcb)
    simp only [he']
    unfold readCustomB
    by_cases hn : strOf (sl ba ns ne) ∈ metaNames
    · simp only [hn, ↓reduceIte]
      cases readCustom m (sl ba ns ne) (sl ba ne s.bodyEnd) <;>
        simp [throw, throwThe, MonadExceptOf.throw, Except.toOption, pure, Except.pure]
    · simp only [hn, ↓reduceIte, readCustom_other m _ _ hn]
      simp [pure, Except.pure, Except.toOption]

theorem walkItems_sec (off : Nat) (m : Meta) (s : Sec) (is : List Item) :
    walkItems off m (.sec s :: is) =
      (if s.id == 0 then
          match customOf s.body with
          | .ok (nm, data) => readCustom m nm data
          | .error e => throw e
        else pure m) >>= fun m => walkItems (off + s.bytes.length) m is := by
  rw [walkItems]
  dsimp only
  by_cases hc : (s.id == 0) = true
  · simp only [hc, ↓reduceIte]
    rcases customOf s.body with _ | ⟨nm, data⟩ <;> rfl
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem walkItems_nest (off : Nat) (m : Meta) (id : UInt8) (size : List UInt8) (enc : Enc)
    (items : List Item) (is : List Item) :
    walkItems off m (.nest id size enc items :: is) =
      walkUnit (off + 1 + size.length) (off + 1 + size.length + (enc.header ++ Item.listBytes items).length) enc items >>= fun p =>
      walkItems (off + 1 + size.length + (enc.header ++ Item.listBytes items).length) m is >>= fun x =>
      match x with
      | (m, cs) => pure (m, p :: cs) := by
  rw [walkItems]

theorem walkUnit_eq (a b : Nat) (enc : Enc) (items : List Item) :
    walkUnit a b enc items = walkItems (a + 8) { range := (a, b) } items >>= fun x =>
      match x, enc with
      | (m, _), .module => pure (.module m)
      | (m, cs), .component => pure (.component m cs) := by
  rw [walkUnit]
  cases enc <;> rfl

theorem walkItemsB_sec (ba : ByteArray) (m : Meta) (s : SecB) (is : List ItemB) :
    walkItemsB ba m (.sec s :: is) =
      (if s.id == 0 then
          match customOfB ba s.bodyAt s.bodyEnd with
          | .ok (ns, ne) =>
            match readCustomB ba m ns ne s.bodyEnd with
            | .ok m => (pure m : Except String Meta)
            | .error e => throw (customMsg ba ns ne s.bodyEnd e)
          | .error e => throw e.render
        else pure m) >>= fun m => walkItemsB ba m is := by
  rw [walkItemsB]
  dsimp only
  by_cases hc : (s.id == 0) = true
  · simp only [hc, ↓reduceIte]
    rcases customOfB ba s.bodyAt s.bodyEnd with _ | ⟨ns, ne⟩
    · rfl
    · dsimp only
      rcases readCustomB ba m ns ne s.bodyEnd with _ | m' <;> rfl
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem walkItemsB_nest (ba : ByteArray) (m : Meta) (id : UInt8) (sa a b : Nat) (enc : Enc)
    (items : List ItemB) (is : List ItemB) :
    walkItemsB ba m (.nest id sa a b enc items :: is) =
      walkUnitB ba a b enc items >>= fun p => walkItemsB ba m is >>= fun x =>
      match x with
      | (m, cs) => pure (m, p :: cs) := by
  rw [walkItemsB]

theorem walkUnitB_eq (ba : ByteArray) (a b : Nat) (enc : Enc) (items : List ItemB) :
    walkUnitB ba a b enc items = walkItemsB ba { range := (a, b) } items >>= fun x =>
      match x, enc with
      | (m, _), .module => pure (.module m)
      | (m, cs), .component => pure (.component m cs) := by
  rw [walkUnitB]
  cases enc <;> rfl

/-- **The array walk of `metadata show` agrees with the list walk** on a layout inside the
input. -/
theorem walkItems_opt (ba : ByteArray) : ∀ (off : Nat) (m : Meta) (is : List ItemB) (q : Nat),
    Lay off is q → q ≤ ba.size →
    (walkItemsB ba m is).toOption = (walkItems off m (is.map (ItemB.toItem ba))).toOption
  | off, m, [], q, _, _ => by
    rw [walkItemsB, List.map_nil, walkItems]
  | off, m, .sec s :: is, q, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hl := Lay_le _ is q h4
    rw [walkItemsB_sec, List.map_cons, toItem_sec, walkItems_sec]
    have hlen : off + (s.toSec ba).bytes.length = s.bodyEnd := by
      simp only [Sec.bytes, SecB.toSec, List.length_cons, List.length_append]
      rw [sl_length ba _ _ (by omega), sl_length ba _ _ (by omega)]
      omega
    simp only [SecB.toSec] at hlen ⊢
    rw [hlen]
    apply bind_opt
    · by_cases hid : s.id = 0
      · simp only [hid, beq_self_eq_true, ↓reduceIte]
        exact customStep_opt ba m s (by omega)
      · have : (s.id == 0) = false := by simpa using hid
        simp [this]
    · intro m'
      exact walkItems_opt ba _ m' is q h4 hq
  | off, m, .nest id sa a b enc its :: is, q, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl := Lay_le _ is q h5
    rw [walkItemsB_nest, List.map_cons, toItem_nest, walkItems_nest]
    have hst : off + 1 + (sl ba sa a).length = a := by
      rw [sl_length ba _ _ (by omega)]; omega
    have hen : a + (enc.header ++ Item.listBytes (its.map (ItemB.toItem ba))).length = b := by
      rw [List.length_append, header_length, Lay_len ba _ its b h4 (by omega)]; omega
    rw [hst, hen]
    apply bind_opt
    · rw [walkUnitB_eq, walkUnit_eq]
      apply bind_opt (walkItems_opt ba _ _ its b h4 (by omega))
      intro r
      rfl
    · intro p
      apply bind_opt (walkItems_opt ba _ m is q h5 hq)
      intro r
      rfl
termination_by _ _ is _ => sizeOf is
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- The array parse and the list parse both fail, or both succeed, with the same encoding and
corresponding items. -/
theorem parse_cases (ba : ByteArray) :
    (∃ e e', parseBinaryB ba = .error e ∧ parseBinary ba.data.toList = .error e') ∨
    (∃ enc items, parseBinaryB ba = .ok (enc, items) ∧
      parseBinary ba.data.toList = .ok (enc, items.map (ItemB.toItem ba))) := by
  have hp := parseBinaryB_spec_raw ba
  cases hfp : parseBinaryB ba with
  | error e =>
    rw [hfp] at hp
    cases hsp : parseBinary ba.data.toList with
    | ok _ => rw [hsp] at hp; simp [Except.toOption] at hp
    | error e' => exact .inl ⟨e, e', rfl, rfl⟩
  | ok r =>
    rcases r with ⟨enc, items⟩
    rw [hfp] at hp
    cases hsp : parseBinary ba.data.toList with
    | error _ => rw [hsp] at hp; simp [Except.toOption] at hp
    | ok x =>
      rw [hsp] at hp
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at hp
      exact .inr ⟨enc, items, rfl, hp ▸ rfl⟩

/-- **`payloadOfB` computes `payloadOf`.** -/
theorem payloadOfB_spec_raw (ba : ByteArray) :
    (payloadOfB ba).toOption = (payloadOf ba.data.toList).toOption := by
  unfold payloadOfB payloadOf
  rcases parse_cases ba with ⟨e, e', hfp, hsp⟩ | ⟨enc, items, hfp, hsp⟩
  · simp [hfp, hsp, Except.toOption, bind, Except.bind]
  have hl := parseBinaryB_lay ba enc items hfp
  simp only [hfp, hsp, bind, Except.bind, length_data]
  rw [walkUnitB_eq, walkUnit_eq]
  apply bind_opt (walkItems_opt ba 8 _ items ba.size hl.2 (Nat.le_refl _))
  intro r
  rfl

/-! ## `metadata add` -/

theorem empty_toList : ByteArray.empty.data.toList = [] := rfl

theorem size_toList (b : ByteArray) : b.size = b.data.toList.length := by
  cases b; simp [ByteArray.size]

theorem rawItems_sec (s : Sec) (is : List Item) :
    rawItems (.sec s :: is) = rawSec s.id s.body ++ rawItems is := by
  rw [rawItems]

theorem rawItems_nest (id : UInt8) (size : List UInt8) (enc : Enc) (items is : List Item) :
    rawItems (.nest id size enc items :: is) =
      (id :: (encU32 (enc.header ++ rawItems items).length ++ (enc.header ++ rawItems items))) ++
        rawItems is := by
  rw [rawItems]

theorem rawItems_nil : rawItems [] = [] := by rw [rawItems]

/-- Copying the items of a nested unit appends `rawItems`. -/
theorem pushRawItems_data (ba : ByteArray) : ∀ (p : Nat) (is : List ItemB) (q : Nat) (out : ByteArray),
    Lay p is q → q ≤ ba.size →
    (pushRawItems ba out is).data.toList = out.data.toList ++ rawItems (is.map (ItemB.toItem ba))
  | p, [], q, out, _, _ => by rw [pushRawItems, List.map_nil, rawItems_nil]; simp
  | p, .sec s :: is, q, out, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hl := Lay_le _ is q h4
    rw [pushRawItems, List.map_cons, toItem_sec, rawItems_sec,
      pushRawItems_data ba _ is q _ h4 hq, pushRawSec_data _ _ _ _ _ h3 (by omega)]
    simp [SecB.toSec]
  | p, .nest id sa a b enc its :: is, q, out, h, hq => by
    unfold Lay at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl := Lay_le _ is q h5
    rw [pushRawItems, List.map_cons, toItem_nest, rawItems_nest]
    dsimp only
    rw [pushRawItems_data ba _ is q _ h5 hq, ByteArray.toList_data_append, appendList_data,
      ByteArray.data_push, size_toList, pushRawItems_data ba _ its b _ h4 (by omega), appendList_data,
      empty_toList]
    simp
termination_by _ is _ _ => sizeOf is
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Both computations fail, or both succeed with related results. -/
def ExR {α β : Type} (R : α → β → Prop) : Except String α → Except String β → Prop
  | .ok x, .ok y => R x y
  | .error _, .error _ => True
  | _, _ => False

theorem ExR.bind {α β γ δ : Type} {R : α → β → Prop} {R' : γ → δ → Prop} {x : Except String α}
    {y : Except String β} {g : α → Except String γ} {g' : β → Except String δ} (h : ExR R x y)
    (hg : ∀ a b, R a b → ExR R' (g a) (g' b)) : ExR R' (x >>= g) (y >>= g') := by
  cases x <;> cases y <;> simp only [ExR] at h <;>
    first | exact hg _ _ h | exact trivial | exact h.elim

/-- The state of the array walk of `metadata add` and of the list walk agree, after the header
`h`. -/
def AddR (h : List UInt8) (b : AddStB) (l : AddSt) : Prop :=
  b.out.data.toList = h ++ l.out.reverse.flatten ∧ b.producersFound = l.producersFound ∧
    b.namesFound = l.namesFound

/-- The state after a section read from the empty state, merged into `st`. -/
def mergeSt (st r : AddSt) : AddSt :=
  { out := r.out ++ st.out, producersFound := st.producersFound || r.producersFound,
    namesFound := st.namesFound || r.namesFound }

theorem addSec_split (a : Add) (comp : Bool) (st : AddSt) (s : Sec) :
    addSec a comp st s = (addSec a comp {} s).map (mergeSt st) := by
  unfold addSec
  simp only [bind, Except.bind, pure, Except.pure, Except.map, mergeSt]
  split
  · simp
  · rcases customOf s.body with e | ⟨nm, data⟩
    · rfl
    · dsimp only
      split
      · rcases readProducers data with e | p <;> simp
      · split
        · rcases rewriteNames false a.name data with e | x <;> simp
        · split
          · rcases rewriteNames true a.name data with e | x <;> simp
          · split
            · rcases utf8Str data with e | v
              · rfl
              · dsimp only
                rcases ociValue (strOf nm) v with e | w <;> simp
            all_goals simp

theorem ociFields_lookup (a : Add) (n : String) (h : n ∉ addNames) : (ociFields a).lookup n = none := by
  simp only [addNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have e4 : (n == "authors") = false := by simpa using h4
  have e5 : (n == "description") = false := by simpa using h5
  have e6 : (n == "licenses") = false := by simpa using h6
  have e7 : (n == "source") = false := by simpa using h7
  have e8 : (n == "homepage") = false := by simpa using h8
  have e9 : (n == "revision") = false := by simpa using h9
  have e10 : (n == "version") = false := by simpa using h10
  simp only [ociFields, List.lookup, e4, e5, e6, e7, e8, e9, e10]

theorem addSec_other (a : Add) (comp : Bool) (s : Sec) (nm data : List UInt8)
    (hc : customOf s.body = .ok (nm, data)) (hn : strOf nm ∉ addNames) :
    addSec a comp {} s = .ok { out := [rawSec s.id s.body] } := by
  have hl := ociFields_lookup a _ hn
  simp only [addNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h1, h2, h3, -⟩ := hn
  unfold addSec
  simp only [bind, Except.bind, pure, Except.pure, hc]
  split
  · rfl
  · simp [h1, h2, h3, hl]

/-- One outer custom section that does not read. -/
theorem addSecB_rel_customErr (a : Add) (comp : Bool) (ba : ByteArray) (h : List UInt8)
    (stB : AddStB) (stL : AddSt) (s : SecB) {e : FErr} (hs : ItemB.inside ba.size (.sec s))
    (hid : s.id = 0) (hcb : customOfB ba s.bodyAt s.bodyEnd = .error e) :
    ExR (AddR h) (addSecB a comp ba stB s) (addSec a comp stL (s.toSec ba)) := by
  have hc := customOf_ag ba s.bodyAt s.bodyEnd hs.2
  obtain ⟨e', he'⟩ := hc.err e (by simpa [customOfB] using hcb)
  have hl : addSec a comp {} (s.toSec ba) = .error e' := by
    unfold addSec
    simp [SecB.toSec, he', hid, bind, Except.bind, pure, Except.pure]
  have hid' : (s.id != 0) = false := by simp [hid]
  rw [addSec_split]
  unfold addSecB
  simp only [hid', Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure, hcb]
  simp [hl, Except.map, ExR, throw, throwThe, MonadExceptOf.throw]

/-- One outer custom section that reads: a field `metadata add` sets is rewritten, another
section copied. -/
theorem addSecB_rel_customOk (a : Add) (comp : Bool) (ba : ByteArray) (h : List UInt8)
    (stB : AddStB) (stL : AddSt) (s : SecB) {ns ne : Nat} (hs : ItemB.inside ba.size (.sec s))
    (hr : AddR h stB stL) (hid : s.id = 0) (hcb : customOfB ba s.bodyAt s.bodyEnd = .ok (ns, ne)) :
    ExR (AddR h) (addSecB a comp ba stB s) (addSec a comp stL (s.toSec ba)) := by
  obtain ⟨r1, r2, r3⟩ := hr
  have hraw := pushRawSec_data stB.out s.id ba s.bodyAt s.bodyEnd hs.1 hs.2
  have he' := (customOf_ag ba s.bodyAt s.bodyEnd hs.2).ok_iff (ns, ne) (by simpa [customOfB] using hcb)
  have hid' : (s.id != 0) = false := by simp [hid]
  rw [addSec_split]
  unfold addSecB
  simp only [hid', Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure, hcb]
  by_cases hn : strOf (sl ba ns ne) ∈ addNames
  · simp only [hn, not_true_eq_false, ↓reduceIte]
    rcases addSec a comp {} (s.toSec ba) with e | x
    · simp [ExR, throw, throwThe, MonadExceptOf.throw, Except.map]
    · simp only [Except.map, ExR, AddR, mergeSt]
      exact ⟨by rw [appendList_data, r1]; simp, by rw [r2], by rw [r3]⟩
  · simp only [hn, not_false_eq_true, ↓reduceIte]
    rw [addSec_other a comp _ _ _ (by simpa [SecB.toSec] using he') hn]
    simp only [Except.map, ExR, AddR, mergeSt]
    exact ⟨by rw [hraw, r1]; simp [SecB.toSec, hid], by simp [r2], by simp [r3]⟩

/-- One outer section that is not custom: copied. -/
theorem addSecB_rel_plain (a : Add) (comp : Bool) (ba : ByteArray) (h : List UInt8)
    (stB : AddStB) (stL : AddSt) (s : SecB) (hs : ItemB.inside ba.size (.sec s))
    (hr : AddR h stB stL) (hid : ¬ s.id = 0) :
    ExR (AddR h) (addSecB a comp ba stB s) (addSec a comp stL (s.toSec ba)) := by
  obtain ⟨r1, r2, r3⟩ := hr
  have hraw := pushRawSec_data stB.out s.id ba s.bodyAt s.bodyEnd hs.1 hs.2
  have hid' : (s.id != 0) = true := by simpa [bne] using hid
  have hl : addSec a comp {} (s.toSec ba) = .ok { out := [rawSec s.id (sl ba s.bodyAt s.bodyEnd)] } := by
    unfold addSec
    simp [SecB.toSec, hid', pure, Except.pure]
  rw [addSec_split]
  unfold addSecB
  simp only [hid', ↓reduceIte, pure, Except.pure]
  rw [hl]
  simp only [Except.map, ExR, AddR, mergeSt]
  exact ⟨by rw [hraw, r1]; simp, by simp [r2], by simp [r3]⟩

/-- **One outer section agrees.** -/
theorem addSecB_rel (a : Add) (comp : Bool) (ba : ByteArray) (h : List UInt8) (stB : AddStB)
    (stL : AddSt) (s : SecB) (hs : ItemB.inside ba.size (.sec s)) (hr : AddR h stB stL) :
    ExR (AddR h) (addSecB a comp ba stB s) (addSec a comp stL (s.toSec ba)) := by
  by_cases hid : s.id = 0
  · cases hcb : customOfB ba s.bodyAt s.bodyEnd with
    | error e => exact addSecB_rel_customErr a comp ba h stB stL s hs hid hcb
    | ok r => exact addSecB_rel_customOk a comp ba h stB stL s hs hr hid hcb
  · exact addSecB_rel_plain a comp ba h stB stL s hs hr hid

/-- **The outer walk of `metadata add` agrees.** -/
theorem addFold_rel (a : Add) (comp : Bool) (ba : ByteArray) (h : List UInt8) :
    ∀ (p : Nat) (items : List ItemB) (q : Nat) (stB : AddStB) (stL : AddSt), Lay p items q →
      q ≤ ba.size → AddR h stB stL →
      ExR (AddR h)
        (items.foldlM (m := Except String) (fun st it =>
          match it with
          | .sec s => addSecB a comp ba st s
          | .nest id _ _ _ enc' items' =>
            let inner := pushRawItems ba (appendList ByteArray.empty enc'.header) items'
            pure { st with out := appendList (st.out.push id) (encU32 inner.size) ++ inner }) stB)
        ((items.map (ItemB.toItem ba)).foldlM (m := Except String) (fun st it =>
          match it with
          | .sec s => addSec a comp st s
          | .nest id _ enc' items' =>
            let inner := enc'.header ++ rawItems items'
            pure { st with out := (id :: (encU32 inner.length ++ inner)) :: st.out }) stL)
  | p, [], q, stB, stL, _, _, hr => by simpa [ExR, pure, Except.pure] using hr
  | p, .sec s :: is, q, stB, stL, hl, hq, hr => by
    have hin := Lay_inside ba p _ q hl hq _ List.mem_cons_self
    unfold Lay at hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    simp only [List.map_cons, List.foldlM_cons, toItem_sec]
    exact ExR.bind (addSecB_rel a comp ba h stB stL s hin hr)
      (fun x y hxy => addFold_rel a comp ba h _ is q x y h4 hq hxy)
  | p, .nest id sa a' b enc its :: is, q, stB, stL, hl, hq, hr => by
    unfold Lay at hl
    obtain ⟨h1, h2, h3, h4, h5⟩ := hl
    have hle := Lay_le _ is q h5
    simp only [List.map_cons, List.foldlM_cons, toItem_nest]
    refine ExR.bind (R := AddR h) ?_ (fun x y hxy => addFold_rel a comp ba h _ is q x y h5 hq hxy)
    obtain ⟨r1, r2, r3⟩ := hr
    simp only [pure, Except.pure, ExR, AddR]
    refine ⟨?_, r2, r3⟩
    rw [ByteArray.toList_data_append, appendList_data, ByteArray.data_push, size_toList,
      pushRawItems_data ba _ its b _ h4 (by omega), appendList_data, empty_toList, Array.toList_push, r1]
    simp

theorem forIn_rel {γ : Type} (L : List γ) (fB : γ → ByteArray → Except String (ForInStep ByteArray))
    (fL : γ → List UInt8 → Except String (ForInStep (List UInt8)))
    (hf : ∀ x oB oL, oB.data.toList = oL → ExR (fun sb sl => match sb, sl with
      | .yield b, .yield l => b.data.toList = l
      | .done b, .done l => b.data.toList = l
      | _, _ => False) (fB x oB) (fL x oL)) :
    ∀ oB oL, oB.data.toList = oL → ExR (fun b l => b.data.toList = l) (forIn L oB fB) (forIn L oL fL) := by
  induction L with
  | nil => intro oB oL h; simpa [ExR, pure, Except.pure] using h
  | cons x L ih =>
    intro oB oL h
    simp only [List.forIn_cons]
    refine ExR.bind (hf x oB oL h) ?_
    intro sb sl hs
    rcases sb with b | b <;> rcases sl with l | l <;> simp only at hs
    · simpa [ExR, pure, Except.pure] using hs
    · exact ih b l hs

theorem ExR.opt {x : Except String ByteArray} {y : Except String (List UInt8)}
    (h : ExR (fun b l => b.data.toList = l) x y) : x.toOption.map (·.data.toList) = y.toOption := by
  cases x <;> cases y <;> simp_all [ExR, Except.toOption]

/-- The OCI fields are appended alike. -/
theorem addOci_rel (a : Add) (oB : ByteArray) (oL : List UInt8) (h : oB.data.toList = oL) :
    ExR (fun b l => b.data.toList = l) (addOciB a oB) (addOci a oL) := by
  unfold addOciB addOci
  refine ExR.bind (forIn_rel _ _ _ ?_ _ _ h) (fun b l h => h)
  intro x oB oL h
  rcases x with ⟨k, f⟩
  cases f with
  | keep => exact h
  | clear => exact h
  | set v =>
    dsimp only
    cases ociValue k v with
    | error e => exact trivial
    | ok d =>
      show (appendList oB (strSec k d)).data.toList = oL ++ strSec k d
      rw [appendList_data, h]

theorem addR_init (enc : Enc) (ba : ByteArray) :
    AddR enc.header { out := appendList (ByteArray.emptyWithCapacity (ba.size + 256)) enc.header } {} := by
  refine ⟨?_, rfl, rfl⟩
  rw [appendList_data]
  simp [ewc_data]

/-- **`addMetadataB` computes `addMetadata`.** -/
theorem addMetadataB_spec_raw (a : Add) (ba : ByteArray) :
    (addMetadataB a ba).toOption.map (·.data.toList) = (addMetadata a ba.data.toList).toOption := by
  unfold addMetadataB addMetadata
  rcases parse_cases ba with ⟨e, e', hfp, hsp⟩ | ⟨enc, items, hfp, hsp⟩
  · simp [hfp, hsp, Except.toOption, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  have hl := parseBinaryB_lay ba enc items hfp
  apply ExR.opt
  simp only [hfp, hsp, pure, Except.pure, ok_bind]
  refine ExR.bind (addFold_rel a (enc == .component) ba enc.header 8 items ba.size _ {} hl.2
    (Nat.le_refl _) (addR_init enc ba)) ?_
  intro stB stL hr
  obtain ⟨r1, r2, r3⟩ := hr
  try dsimp only
  simp only [r2, r3]
  cases hnf : stL.namesFound <;> cases hpf : (!stL.producersFound && !List.isEmpty a.producers) <;>
    rcases hnm : a.name with _ | _ | v <;>
    simp only [Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true] <;>
    exact addOci_rel a _ _ (by simp [appendList_data, r1])

end Silmaril.Proofs.Wasm.Tools.Meta

end
