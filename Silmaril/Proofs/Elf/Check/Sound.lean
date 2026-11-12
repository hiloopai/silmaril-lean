module

public import Silmaril.Elf.Check.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # Soundness of the fast parse checker

`file_sound`: `Sub r F → Check.file r A = true → Parses F A`. Proved with the standard axioms
(no `sorry`, no new axiom). The proof follows `Silmaril.Elf.read` step by step: the parts the
checker runs as the specification transfer by `Rd.run_mono`; names (`nameOk`) go through
`run_cstr` (a wide read determines the byte-by-byte read), symbols (`symOk`) through
`blobRead_sub` (a field read is a slice of a record read), and the table loops through
`run_mapM` (a `List.mapM` run is the list of the element runs).
-/

@[expose] public section

namespace Silmaril.Elf.Check

open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader Symbol NameBytes ObjectSymbol)
open Silmaril.Elf.Link.DynElf (Rd leVal blobRead)
open Silmaril.Elf.Link.DynElf.Elf (u8 u16 u32 u64 cstr)
open Silmaril.X86.Link (Blob)

/-! ## Reading programs -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} : (if c then a else b) = b := by
  simp [h]

theorem bind_eq {α β : Type} (p : Rd α) (f : α → Rd β) : (p >>= f) = p.bind f := rfl

theorem run_le (r : Src) (o w : Nat) : (Rd.le o w).run r = r o w := by
  unfold Rd.le Rd.run
  cases r o w <;> rfl

theorem run_bind_of {α β : Type} {r : Src} {p : Rd α} {a : α} (f : α → Rd β)
    (h : p.run r = some a) : (p >>= f).run r = (f a).run r := by
  rw [bind_eq, Rd.run_bind, h]
  rfl

theorem run_read_of {β : Type} {r : Src} {o w v : Nat} (f : Nat → Rd β) (h : r o w = some v) :
    (Rd.le o w >>= f).run r = (f v).run r :=
  run_bind_of f (by rw [run_le]; exact h)

theorem run_guard_of {β : Type} {r : Src} {c : Prop} [Decidable c] (f : Unit → Rd β) (h : c) :
    (Rd.guard c >>= f).run r = (f ()).run r := by
  unfold Rd.guard
  rw [ite_t h]
  rfl

theorem run_ofOption_of {α β : Type} {r : Src} {a : α} (f : α → Rd β) :
    (Rd.ofOption (some a) >>= f).run r = (f a).run r := rfl

theorem run_pure {α : Type} (r : Src) (a : α) : (pure a : Rd α).run r = some a := rfl

/-- **A `List.mapM` run is the list of the element runs.** -/
theorem run_mapM_loop {α β : Type} (r : Src) (f : α → Rd β) : ∀ (l : List α) (out acc : List β),
    List.Forall₂ (fun a b => (f a).run r = some b) l out →
    (List.mapM.loop f l acc).run r = some (acc.reverse ++ out)
  | [], [], acc, .nil => by
    show (Rd.pure acc.reverse).run r = _
    simp [Rd.run]
  | a :: l, b :: out, acc, .cons hab hl => by
    show (f a >>= fun x => List.mapM.loop f l (x :: acc)).run r = _
    rw [run_bind_of _ hab, run_mapM_loop r f l out (b :: acc) hl]
    simp

theorem run_mapM {α β : Type} {r : Src} {f : α → Rd β} {l : List α} {out : List β}
    (h : List.Forall₂ (fun a b => (f a).run r = some b) l out) : (l.mapM f).run r = some out := by
  show (List.mapM.loop f l []).run r = some out
  simpa using run_mapM_loop r f l out [] h

theorem forall₂_map {β γ : Type} {P : β → γ → Prop} (g : γ → β) :
    ∀ (l : List γ), (∀ x ∈ l, P (g x) x) → List.Forall₂ P (l.map g) l
  | [], _ => .nil
  | x :: l, h => .cons (h x (by simp)) (forall₂_map (P := P) g l fun y hy => h y (by simp [hy]))

/-! ## Byte sources -/

theorem Sub.run {r : Src} {F : Blob} (hs : Sub r F) {α : Type} {p : Rd α} {a : α}
    (h : p.run r = some a) : p.run (blobRead F) = some a :=
  Rd.run_mono hs p a h

theorem Sub.run_beq {r : Src} {F : Blob} (hs : Sub r F) {α : Type} [BEq α] [LawfulBEq α] {p : Rd α} {a : α}
    (h : (p.run r == some a) = true) : p.run (blobRead F) = some a :=
  hs.run (beq_iff_eq.mp h)

theorem sub_blobRead (F : Blob) : Sub (blobRead F) F := fun _ _ _ h => h

/-- **A field read is a slice of a record read.** -/
theorem blobRead_sub {F : Blob} {o w v : Nat} (h : blobRead F o w = some v) {k w' : Nat}
    (hk : k + w' ≤ w) : blobRead F (o + k) w' = some (fld v k w') := by
  unfold blobRead Blob.readLEN at *
  unfold fld
  by_cases hw' : w' = 0
  · subst hw'
    simp [Nat.mod_one]
  · split at h
    · rename_i hc
      cases h
      have hle : o + k + w' ≤ F.len := by rcases hc with hc | hc <;> omega
      rw [ite_t (Or.inr hle)]
      congr 1
      have e := Silmaril.Elf.Link.DynElf.shiftRight_mod_of_mod
        (x := (F.n >>> (8 * o)) % 2 ^ (8 * w)) (y := F.n) (k := 8 * o) (L := 8 * w) (s := 8 * k)
        (m := 8 * w') (by rw [Nat.mod_mod]) (by omega)
      rw [e, show 8 * o + 8 * k = 8 * (o + k) by omega]
    · cases h

/-! ## Names -/

theorem leVal_lt : ∀ (l : List Nat), (∀ x ∈ l, x < 256) → leVal l < 2 ^ (8 * l.length)
  | [], _ => by simp [leVal]
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := leVal_lt xs fun y hy => h y (by simp [hy])
    simp only [leVal, List.length_cons]
    rw [Nat.mod_eq_of_lt hx, show 8 * (xs.length + 1) = 8 * xs.length + 8 by omega, Nat.pow_add]
    generalize 2 ^ (8 * xs.length) = P at *
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]
    omega

theorem shift8 {c L : Nat} (hc : c < 256) : (c + 256 * L) >>> 8 = L := by
  rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 8 = 256 from rfl,
    Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hc, Nat.zero_add]

/-- **A wide read determines the byte-by-byte read of a NUL-terminated string.** -/
theorem run_cstr {F : Blob} : ∀ (n : List Nat) (o fuel : Nat), n.length < fuel →
    (∀ c ∈ n, c ≠ 0 ∧ c < 256) → blobRead F o (n.length + 1) = some (leVal (n ++ [0])) →
    (cstr o fuel).run (blobRead F) = some n
  | [], o, fuel, hf, _, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have h0 : blobRead F o 1 = some 0 := by simpa [leVal] using h
    show (u8 o >>= fun c => if c = 0 then pure [] else do
      let rest ← cstr (o + 1) f
      pure (c :: rest)).run (blobRead F) = _
    simp only [u8]
    rw [run_read_of _ h0]
    rfl
  | c :: n, o, fuel, hf, hc, h => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hc0 := hc c (by simp)
    have hb : ∀ x ∈ n ++ [0], x < 256 := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact (hc x (by simp [hx])).2
      · omega
    have hlt := leVal_lt (n ++ [0]) hb
    have hv : leVal ((c :: n) ++ [0]) = c + 256 * leVal (n ++ [0]) := by
      simp only [List.cons_append, leVal, Nat.mod_eq_of_lt hc0.2]
    rw [hv, List.length_cons] at h
    have h1 : blobRead F o 1 = some c := by
      have := blobRead_sub h (k := 0) (w' := 1) (by omega)
      rw [Nat.add_zero] at this
      rw [this]
      simp only [fld, Nat.mul_zero, Nat.shiftRight_zero, Nat.mul_one]
      congr 1
      rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0.2]
    have h2 : blobRead F (o + 1) (n.length + 1) = some (leVal (n ++ [0])) := by
      have := blobRead_sub h (k := 1) (w' := n.length + 1) (by omega)
      rw [this]
      simp only [fld, Nat.mul_one]
      congr 1
      rw [shift8 hc0.2]
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      exact Nat.mod_eq_of_lt hlt
    have ih := run_cstr n (o + 1) f (by simp at hf; omega)
      (fun x hx => hc x (by simp [hx])) h2
    show (u8 o >>= fun c => if c = 0 then pure [] else do
      let rest ← cstr (o + 1) f
      pure (c :: rest)).run (blobRead F) = _
    simp only [u8]
    rw [run_read_of _ h1, ite_f hc0.1, run_bind_of _ ih]
    rfl

theorem nameVal_eq (n : NameBytes) : nameVal n = leVal (n.map BitVec.toNat ++ [0]) := rfl

/-- **`nameOk` is `Parse.name`.** -/
theorem run_name {r : Src} {F : Blob} (hs : Sub r F) {o fuel : Nat} {n : NameBytes}
    (h : nameOk r o fuel n = true) : (Parse.name o fuel).run (blobRead F) = some n := by
  simp only [nameOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨hf, hz⟩, hr⟩ := h
  have hr' := hs _ _ _ hr
  have hc := run_cstr (F := F) (n.map BitVec.toNat) o fuel (by simpa using hf)
    (by
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨b, hb, rfl⟩ := hc
      exact ⟨hz b hb, b.isLt⟩)
    (by simpa [nameVal] using hr')
  show (cstr o fuel >>= fun n => pure (Parse.toName n)).run (blobRead F) = _
  rw [run_bind_of _ hc]
  show some ((n.map BitVec.toNat).map (BitVec.ofNat 8)) = some n
  congr 1
  rw [List.map_map]
  conv => rhs; rw [← List.map_id n]
  exact List.map_congr_left fun b _ => by simp

theorem run_strAt {r : Src} {F : Blob} (hs : Sub r F) {strs : SectionHeader} {i : Nat}
    {n : NameBytes} (h : strAtOk r strs i n = true) :
    (Parse.strAt strs i).run (blobRead F) = some n := by
  simp only [strAtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  show (Rd.guard (i < strs.size) >>= fun _ => Parse.name (strs.offset + i) (strs.size - i)).run _ = _
  rw [run_guard_of _ h.1]
  exact run_name hs h.2

/-! ## Symbols -/

theorem run_symbol {r : Src} {F : Blob} (hs : Sub r F) {strs : SectionHeader} {o : Nat}
    {s : ObjectSymbol} (h : symOk r strs o s = true) :
    (Parse.symbol strs o).run (blobRead F) = some s := by
  unfold symOk at h
  split at h
  · cases h
  · rename_i v hv
    have hb := hs _ _ _ hv
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hn, hi⟩, ho⟩, hx⟩, hval⟩, hsz⟩, hname⟩ := h
    have r0 : blobRead F o 4 = some s.raw.name := by
      rw [hn]; have := blobRead_sub hb (k := 0) (w' := 4) (by omega); simpa using this
    have r4 : blobRead F (o + 4) 1 = some s.raw.info := by
      rw [hi]; exact blobRead_sub hb (by omega)
    have r5 : blobRead F (o + 5) 1 = some s.raw.other := by
      rw [ho]; exact blobRead_sub hb (by omega)
    have r6 : blobRead F (o + 6) 2 = some s.raw.sectionIndex := by
      rw [hx]; exact blobRead_sub hb (by omega)
    have r8 : blobRead F (o + 8) 8 = some s.raw.value := by
      rw [hval]; exact blobRead_sub hb (by omega)
    have r16 : blobRead F (o + 16) 8 = some s.raw.size := by
      rw [hsz]; exact blobRead_sub hb (by omega)
    have rn := run_strAt hs hname
    unfold Parse.symbol
    simp only [u32, u8, u16, u64]
    rw [run_read_of _ r0, run_read_of _ r4, run_read_of _ r5, run_read_of _ r6, run_read_of _ r8,
      run_read_of _ r16, run_bind_of _ rn]
    rfl

theorem forall₂_syms {r : Src} {F : Blob} (hs : Sub r F) {strs : SectionHeader} {o : Nat} :
    ∀ (i : Nat) (es : List ObjectSymbol), symsOk r strs o i es = true →
    List.Forall₂ (fun j s => (Parse.symbol strs (o + 24 * j)).run (blobRead F) = some s)
      (List.range' i es.length) es
  | _, [], _ => .nil
  | i, s :: es, h => by
    simp only [symsOk, Bool.and_eq_true] at h
    exact .cons (run_symbol hs h.1) (forall₂_syms hs (i + 1) es h.2)

theorem run_symbols {r : Src} {F : Blob} (hs : Sub r F) {strs : SectionHeader} {o k : Nat}
    {es : List ObjectSymbol} (hk : es.length = k) (h : symsOk r strs o 0 es = true) :
    (Parse.records o 24 k (Parse.symbol strs)).run (blobRead F) = some es := by
  subst hk
  unfold Parse.records
  rw [List.range_eq_range']
  exact run_mapM (forall₂_syms hs 0 es h)

/-! ## Word arrays and hash tables -/

theorem forall₂_words {r : Src} {F : Blob} (hs : Sub r F) {o w : Nat} :
    ∀ (i : Nat) (xs : List Nat), wordsOk r o w i xs = true →
    List.Forall₂ (fun j x => (Rd.le (o + w * j) w).run (blobRead F) = some x)
      (List.range' i xs.length) xs
  | _, [], _ => .nil
  | i, x :: xs, h => by
    simp only [wordsOk, Bool.and_eq_true, beq_iff_eq] at h
    exact .cons (by rw [run_le]; exact hs _ _ _ h.1) (forall₂_words hs (i + 1) xs h.2)

theorem run_words {r : Src} {F : Blob} (hs : Sub r F) {o w k : Nat} {f : Nat → Rd Nat}
    (hf : ∀ p, f p = Rd.le p w) {xs : List Nat} (hk : xs.length = k) (h : wordsOk r o w 0 xs = true) :
    (Parse.records o w k f).run (blobRead F) = some xs := by
  subst hk
  unfold Parse.records
  rw [List.range_eq_range']
  apply run_mapM
  have := forall₂_words hs 0 xs h
  simpa only [hf] using this

theorem run_gnuHash {r : Src} {F : Blob} (hs : Sub r F) {sh : SectionHeader} {g : GnuHash}
    (h : gnuOk r sh g = true) : (Parse.gnuHash sh).run (blobRead F) = some g := by
  simp only [gnuOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h4⟩, h8⟩, h12⟩, hhead⟩, hnb⟩, hch⟩, hbl⟩, hbu⟩, hcw⟩ := h
  unfold Parse.gnuHash
  simp only [u32]
  rw [run_read_of _ (hs _ _ _ h0), run_read_of _ (hs _ _ _ h4), run_read_of _ (hs _ _ _ h8),
    run_read_of _ (hs _ _ _ h12), run_guard_of _ hhead,
    run_bind_of _ (run_words (f := u64) hs (fun _ => rfl) rfl hbl),
    run_bind_of _ (run_words (f := u32) hs (fun _ => rfl) hnb hbu),
    run_bind_of _ (run_words (f := u32) hs (fun _ => rfl) hch hcw)]
  rfl

theorem run_sysvHash {r : Src} {F : Blob} (hs : Sub r F) {sh : SectionHeader} {t : SysvHash}
    (h : hashOk r sh t = true) : (Parse.sysvHash sh).run (blobRead F) = some t := by
  simp only [hashOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h4⟩, hb⟩, hc⟩ := h
  unfold Parse.sysvHash
  simp only [u32]
  rw [run_read_of _ (hs _ _ _ h0), run_read_of _ (hs _ _ _ h4),
    run_bind_of _ (run_words (f := u32) hs (fun _ => rfl) rfl hb),
    run_bind_of _ (run_words (f := u32) hs (fun _ => rfl) rfl hc)]
  rfl

/-! ## Bodies and sections -/

theorem run_body {r : Src} {F : Blob} (hs : Sub r F) {shs : List SectionHeader}
    {sh : SectionHeader} {b : Body} (h : bodyOk r shs sh b = true) :
    (Parse.body shs sh).run (blobRead F) = some b := by
  unfold bodyOk at h
  split at h
  · rename_i hk
    split at h
    · rename_i t es strs hl
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨he, ht⟩, hlen⟩, hsyms⟩ := h
      have h0 : ¬ sh.kind = SHT_NULL := by
        unfold SHT_NULL SHT_SYMTAB SHT_DYNSYM at *; omega
      have h8 : ¬ sh.kind = SHT_NOBITS := by
        unfold SHT_NOBITS SHT_SYMTAB SHT_DYNSYM at *; omega
      have h1 : ¬ sh.kind = SHT_PROGBITS := by
        unfold SHT_PROGBITS SHT_SYMTAB SHT_DYNSYM at *; omega
      have h3 : ¬ sh.kind = SHT_STRTAB := by
        unfold SHT_STRTAB SHT_SYMTAB SHT_DYNSYM at *; omega
      simp only [Parse.body]
      rw [ite_f h0, ite_f h8, ite_f h1, ite_f h3, ite_t hk, run_guard_of _ he, hl,
        run_ofOption_of, run_bind_of _ (run_symbols hs hlen hsyms)]
      show some (Body.symbols _ es) = some (Body.symbols t es)
      rw [ht]
      rfl
    · cases h
  · rename_i hk
    split at h
    · rename_i hg
      have nk : ∀ c, c ≠ SHT_GNU_HASH → ¬ sh.kind = c := fun c hc e => hc (e ▸ hg)
      split at h
      · rename_i g
        simp only [Parse.body]
        rw [ite_f (nk _ (by decide)), ite_f (nk _ (by decide)), ite_f (nk _ (by decide)),
          ite_f (nk _ (by decide)), ite_f hk, ite_f (nk _ (by decide)), ite_f (nk _ (by decide)),
          ite_f (nk _ (by decide)), ite_f (nk _ (by decide)), ite_t hg,
          run_bind_of _ (run_gnuHash hs h)]
        rfl
      · cases h
    · rename_i hg
      split at h
      · rename_i hh
        have nk : ∀ c, c ≠ SHT_HASH → ¬ sh.kind = c := fun c hc e => hc (e ▸ hh)
        split at h
        · rename_i t
          simp only [Parse.body]
          rw [ite_f (nk _ (by decide)), ite_f (nk _ (by decide)), ite_f (nk _ (by decide)),
            ite_f (nk _ (by decide)), ite_f hk, ite_f (nk _ (by decide)), ite_f (nk _ (by decide)),
            ite_f (nk _ (by decide)), ite_f (nk _ (by decide)), ite_f hg, ite_t hh,
            run_bind_of _ (run_sysvHash hs h)]
          rfl
        · cases h
      · rename_i hh
        split at h
        · rename_i hv
          have nk : ∀ c, c ≠ SHT_GNU_versym → ¬ sh.kind = c := fun c hc e => hc (e ▸ hv)
          split at h
          · rename_i vs
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            simp only [Parse.body]
            rw [ite_f (nk _ (by decide)), ite_f (nk _ (by decide)), ite_f (nk _ (by decide)),
              ite_f (nk _ (by decide)), ite_f hk, ite_f (nk _ (by decide)),
              ite_f (nk _ (by decide)), ite_f (nk _ (by decide)), ite_f (nk _ (by decide)),
              ite_f hg, ite_f hh, ite_t hv,
              run_bind_of _ (run_words (f := u16) hs (fun _ => rfl) h.1 h.2)]
            rfl
          · cases h
        · exact hs.run_beq h

theorem run_sections {r : Src} {F : Blob} (hs : Sub r F) {h : Header} {secs : List Section}
    (hc : sectionsOk r h secs = true) :
    (Parse.sections h (secs.map (·.header))).run (blobRead F) = some secs := by
  simp only [sectionsOk] at hc
  unfold Parse.sections
  by_cases he : secs.isEmpty
  · have : secs = [] := List.isEmpty_iff.mp he
    subst this
    rfl
  · have he' : (secs.map (·.header)).isEmpty = false := by simpa using he
    rw [ite_f (by simp [he'])]
    rw [ite_f he] at hc
    cases hn : (secs.map (·.header))[h.sectionNameIndex]? with
    | none => rw [hn] at hc; cases hc
    | some names =>
      rw [hn] at hc
      rw [run_ofOption_of]
      apply run_mapM
      apply forall₂_map
      intro s hs'
      simp only [List.all_eq_true, Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc s hs'
      rw [run_bind_of _ (run_strAt hs h1), run_bind_of _ (run_body hs h2)]
      rfl

/-! ## The file -/

/-- **Soundness of the checker.** -/
theorem file_sound {r : Src} {F : Blob} (hs : Sub r F) {A : File} (h : file r A = true) :
    Parses F A := by
  simp only [file, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, hp⟩, hsh⟩, hsec⟩, hd⟩, hi⟩, hn⟩, hso⟩, hrp⟩ := h
  unfold Parses parse read
  rw [run_bind_of _ (hs.run_beq hh), run_bind_of _ (hs.run_beq hp), run_bind_of _ (hs.run_beq hsh),
    run_bind_of _ (run_sections hs hsec), run_bind_of _ (hs.run_beq hd),
    run_bind_of _ (hs.run_beq hi), run_bind_of _ (hs.run_beq hn), run_bind_of _ (hs.run_beq hso),
    run_bind_of _ (hs.run_beq hrp)]
  rfl

end Silmaril.Elf.Check
