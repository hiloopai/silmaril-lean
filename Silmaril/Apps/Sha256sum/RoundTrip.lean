module

public import Silmaril.Apps.Sha256sum.Theorems

/-! # Compute, then check: the round trip

spec.md §11.2. Run `sha256sum [-b | --tag] -- f₁ … fₙ` on files that can all be read,
store its standard output in a check file `cf`, and run `sha256sum -c -- cf` on a file
system that still has the same contents at `f₁ … fₙ`. Then the check run prints
`fᵢ: OK` for every file, in order (with the name shown escaped when it is problematic),
prints nothing on standard error, and exits 0.

The hypotheses are what the statement needs, and each is necessary:

* the names are nonempty: an untagged record for the empty name is `HEX  ` with one
  trailing space, which `--check` reads as a BSD-reversed record naming ` `;
* the names are NUL-free: a NUL cannot be part of a file name, and `--check` cuts a name
  at NUL;
* no name is `-`: in the check run `-` would mean the check run's standard input;
* the list is nonempty: with no operand the compute run hashes standard input under the
  name `-`;
* `-z` is excluded: `-z` disables escaping and `--check` rejects `-z`.

## Main results

- `unescape_escapeName` (in `Escape`) and `nameOf_record`: the name field of a record
  decodes to the name.
- `parseLine_record`: every compute-mode record parses back to its digest and name, and
  leaves the format lock in `{unknown, standard}`.
- `compute_files`: the compute run on readable files prints one record per file.
- `check_after_compute`: the round trip.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

set_option maxRecDepth 100000 in
theorem hex_byte_fin : ∀ n : Fin 256, isHex (UInt8.ofNat n) = true →
    (UInt8.ofNat n) ≠ 92 ∧ (UInt8.ofNat n) ≠ 10 ∧ (UInt8.ofNat n) ≠ 13 ∧ (UInt8.ofNat n) ≠ 0 ∧
    isWS (UInt8.ofNat n) = false ∧ (UInt8.ofNat n) ≠ 41 ∧ (UInt8.ofNat n) ≠ 35 ∧
    (UInt8.ofNat n) ≠ 83 ∧ isDigestByte (UInt8.ofNat n) = true := by
  decide

theorem hex_byte (c : UInt8) (h : isHex c = true) :
    c ≠ 92 ∧ c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 0 ∧ isWS c = false ∧ c ≠ 41 ∧ c ≠ 35 ∧ c ≠ 83 ∧
      isDigestByte c = true := by
  have := hex_byte_fin ⟨c.toNat, c.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h

theorem takeWhile_digest (H r : Bytes) (h : ∀ c ∈ H, isDigestByte c = true) :
    (H ++ 32 :: r).takeWhile isDigestByte = H := by
  induction H with
  | nil => simp [isDigestByte, isWS]
  | cons x H ih =>
    simp only [List.cons_append, List.takeWhile_cons, h x (List.mem_cons_self ..), ↓reduceIte]
    rw [ih fun c hc => h c (List.mem_cons_of_mem _ hc)]

structure HexStr (H : Bytes) : Prop where
  length : H.length = 64
  digits : ∀ c ∈ H, isHex c = true ∧ lowerAscii c = c

theorem HexStr.valid {H : Bytes} (h : HexStr H) : validDigits H = true := by
  simp only [validDigits, h.length, decide_true, Bool.true_and, List.all_eq_true]
  exact fun c hc => (h.digits c hc).1

theorem lit_SHA256_ne (h0 : UInt8) (rest : Bytes) (h : h0 ≠ 83) :
    ¬ (h0 :: rest).take 6 = lit "SHA256" := by
  intro e
  have := congrArg List.head? e
  simp [lit] at this
  exact h (by simpa using this)

theorem parseLine_untagged' (mode : BsdMode) (e : Bool) (h0 : UInt8) (Ht nf : Bytes)
    (fl : UInt8) (hH : HexStr (h0 :: Ht)) (hfl : fl = 32 ∨ fl = 42) (hnf : nf ≠ [])
    (hmode : mode ≠ .reversed) :
    parseLine mode ((if e then [92] else []) ++ h0 :: (Ht ++ 32 :: fl :: nf)) =
      (.standard, (nameOf e nf).map fun name => (h0 :: Ht, name)) := by
  obtain ⟨n92, -, -, -, nws, -, -, n83, -⟩ := hex_byte h0 (hH.digits h0 (List.mem_cons_self ..)).1
  have hdig : ∀ c ∈ h0 :: Ht, isDigestByte c = true :=
    fun c hc => (hex_byte c (hH.digits c hc).1).2.2.2.2.2.2.2.2
  have hlen : Ht.length = 63 := by have := hH.length; simp at this; omega
  have hnfl : nf.length ≠ 0 := by simpa using hnf
  have htw : (h0 :: (Ht ++ 32 :: fl :: nf)).takeWhile isDigestByte = h0 :: Ht := by
    have := takeWhile_digest (h0 :: Ht) (fl :: nf) hdig; simpa using this
  have hdrop : (h0 :: (Ht ++ 32 :: fl :: nf)).drop ((h0 :: Ht).length + 1) = fl :: nf := by
    simp [List.drop_append]
  have hne : ¬ ((h0 :: Ht).length = (h0 :: (Ht ++ 32 :: fl :: nf)).length) := by simp
  have h6 := lit_SHA256_ne h0 (Ht ++ 32 :: fl :: nf) n83
  have hlock : lockStep mode (fl :: nf) = (.standard, some nf) := by
    unfold lockStep
    have : ((fl :: nf).length == 1 || (at0 (fl :: nf) 0 != 32 && at0 (fl :: nf) 0 != 42)) = false := by
      rcases hfl with rfl | rfl <;> simp [at0, hnfl]
    simp only [this, Bool.false_eq_true, ↓reduceIte, ne_eq, hmode, not_false_eq_true, List.drop_one, List.tail_cons]
  have h92 : (h0 == 92) = false := by simpa using n92
  cases e
  · have e1 : (h0 :: (Ht ++ 32 :: fl :: nf)).takeWhile isWS = [] := by simp [nws]
    have hl : ¬ ((h0 :: (Ht ++ 32 :: fl :: nf)).length - 0 < 66 + 0) := by simp; omega
    simp only [parseLine, Bool.false_eq_true, ↓reduceIte, List.nil_append, e1, List.length_nil,
      at0, List.getD_cons_zero, h92, List.drop_zero, h6, hl, htw, hne, hH.valid, Bool.not_true, hdrop, hlock,
      Option.bind_some]
  · have e1 : (92 :: h0 :: (Ht ++ 32 :: fl :: nf)).takeWhile isWS = [] := by simp [isWS]
    have hl : ¬ ((92 :: h0 :: (Ht ++ 32 :: fl :: nf)).length - 1 < 66 + 0) := by simp; omega
    simp only [parseLine, ↓reduceIte, List.cons_append, List.nil_append, e1, List.length_nil,
      at0, List.getD_cons_zero, beq_self_eq_true, Nat.zero_add, List.drop_one, List.tail_cons,
      List.getD_cons_succ, h92, Bool.false_eq_true, h6, hl, htw, hne, hH.valid, Bool.not_true,
      hdrop, hlock, Option.bind_some]

theorem lastIndexOf_eq_none (c : UInt8) : ∀ l : Bytes, c ∉ l → lastIndexOf c l = none
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have := lastIndexOf_eq_none c xs (fun m => h (List.mem_cons_of_mem _ m))
    simp [lastIndexOf, this, hx]

theorem lastIndexOf_append (c : UInt8) (rest : Bytes) (hr : c ∉ rest) :
    ∀ l : Bytes, lastIndexOf c (l ++ c :: rest) = some l.length
  | [] => by simp [lastIndexOf, lastIndexOf_eq_none c rest hr]
  | x :: xs => by
    simp [lastIndexOf, lastIndexOf_append c rest hr xs]

theorem lit_tag : lit "SHA256 (" = [83, 72, 65, 50, 53, 54, 32, 40] := by decide
theorem lit_eq : lit ") = " = [41, 32, 61, 32] := by decide

theorem bsdSplit_record (e : Bool) (nf H : Bytes) (hH : HexStr H) :
    bsdSplit (nf ++ 41 :: 32 :: 61 :: 32 :: H) e = (nameOf e nf).map fun name => (H, name) := by
  obtain ⟨h0, Ht, rfl⟩ : ∃ h0 Ht, H = h0 :: Ht := by
    match H, hH with
    | h0 :: Ht, _ => exact ⟨h0, Ht, rfl⟩
    | [], h => exact absurd h.length (by simp)
  obtain ⟨-, -, -, -, nws, n41, -, -, -⟩ := hex_byte h0 (hH.digits h0 (List.mem_cons_self ..)).1
  have hr : (41 : UInt8) ∉ 32 :: 61 :: 32 :: h0 :: Ht := by
    simp only [List.mem_cons, not_or]
    refine ⟨by decide, by decide, by decide, fun h => n41 h.symm, fun m => ?_⟩
    exact (hex_byte 41 (hH.digits 41 (List.mem_cons_of_mem _ m)).1).2.2.2.2.2.1 rfl
  unfold bsdSplit
  rw [lastIndexOf_append 41 _ hr]
  simp only [List.take_left']
  rcases nameOf e nf with _ | name
  · rfl
  · have hd : (nf ++ 41 :: 32 :: 61 :: 32 :: h0 :: Ht).drop (nf.length + 1) =
        32 :: 61 :: 32 :: h0 :: Ht := by simp [List.drop_append]
    simp only [hd, List.dropWhile_cons, show isWS 32 = true by decide,
      show isWS 61 = false by decide, nws, ↓reduceIte, Bool.false_eq_true, hH.valid,
      Option.map_some]

theorem parseLine_tagged' (mode : BsdMode) (e : Bool) (nf H : Bytes) (hH : HexStr H) :
    parseLine mode ((if e then [92] else []) ++ lit "SHA256 (" ++ nf ++ lit ") = " ++ H) =
      (mode, (nameOf e nf).map fun name => (H, name)) := by
  rw [lit_tag, lit_eq, ← bsdSplit_record e nf H hH]
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, List.append_assoc]
    simp [parseLine, at0, isWS, lit]
  · simp only [↓reduceIte, List.nil_append, List.cons_append, List.append_assoc]
    simp [parseLine, at0, isWS, lit]

theorem HexStr.lower {H : Bytes} (h : HexStr H) : H.map lowerAscii = H := by
  conv => rhs; rw [← List.map_id H]
  exact List.map_congr_left fun c hc => (h.digits c hc).2

theorem hexStr_hexDigest (d : Bytes) : HexStr (hexDigest d) :=
  ⟨hexDigest_length d, hexLower_all _⟩

def nameField (f : Bytes) : Bytes := if problematic f then escapeName f else f
def lead (f : Bytes) : Bytes := if problematic f then [92] else []

theorem beforeNul_of_not_mem : ∀ s : Bytes, (0 : UInt8) ∉ s → beforeNul s = s
  | [], _ => rfl
  | c :: s, h => by
    have hc : c ≠ 0 := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := beforeNul_of_not_mem s (fun m => h (List.mem_cons_of_mem _ m))
    unfold beforeNul at ih ⊢
    simp [hc, ih]

theorem nameOf_record (f : Bytes) (h0 : (0 : UInt8) ∉ f) :
    nameOf (problematic f) (nameField f) = some f := by
  unfold nameOf nameField
  cases problematic f
  · simp [beforeNul_of_not_mem f h0]
  · simp [unescape_escapeName f h0]

theorem escChar_ne_nil (c : UInt8) : escChar c ≠ [] := by
  unfold escChar; split <;> (try split) <;> (try split) <;> simp

theorem nameField_ne_nil (f : Bytes) (h : f ≠ []) : nameField f ≠ [] := by
  unfold nameField
  split
  · match f, h with
    | c :: cs, _ =>
      rw [escapeName_cons]
      exact fun e => escChar_ne_nil c (List.append_eq_nil_iff.mp e).1
  · exact h

theorem nameField_no (f : Bytes) (x : UInt8) (hx : x = 10 ∨ x = 13) : x ∉ nameField f := by
  unfold nameField
  cases hp : problematic f
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro hm
    have := not_problematic_mem f hp x hm
    rcases hx with rfl | rfl <;> simp_all
  · simp only [↓reduceIte]
    rcases hx with rfl | rfl
    · exact escapeName_not_lf f
    · exact escapeName_not_cr f

theorem recordBody_eq (o : Opts) (f d : Bytes) (hz : o.zero = false) :
    recordBody o f d =
      if o.tag then lead f ++ lit "SHA256 (" ++ nameField f ++ lit ") = " ++ hexDigest d
      else lead f ++ hexDigest d ++ [32, if o.binary = some true then 42 else 32] ++ nameField f := by
  simp [recordBody, hz, lead, nameField]

/-- The three compute-mode output formats the round trip covers. -/
inductive Format where
  | text | binary | tag
  deriving DecidableEq, Repr

def Format.args : Format → List Bytes
  | .text => []
  | .binary => [lit "-b"]
  | .tag => [lit "--tag"]

def Format.opts : Format → Opts
  | .text => {}
  | .binary => { binary := some true }
  | .tag => { tag := true, binary := some true }

theorem parseLine_record (mode : BsdMode) (fmt : Format) (f d : Bytes) (hf : f ≠ [])
    (h0 : (0 : UInt8) ∉ f) (hmode : mode ≠ .reversed) :
    ∃ m, m ≠ .reversed ∧ parseLine mode (recordBody fmt.opts f d) = (m, some (hexDigest d, f)) := by
  have hH := hexStr_hexDigest d
  obtain ⟨h0', Ht, hHe⟩ : ∃ h0 Ht, hexDigest d = h0 :: Ht := by
    match hexDigest d, hH with
    | h0 :: Ht, _ => exact ⟨h0, Ht, rfl⟩
    | [], h => exact absurd h.length (by simp)
  rw [recordBody_eq _ _ _ (by cases fmt <;> rfl)]
  have hH' : HexStr (h0' :: Ht) := hHe ▸ hH
  cases fmt
  · refine ⟨.standard, by decide, ?_⟩
    simp only [Format.opts, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, hHe, lead,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [parseLine_untagged' mode _ h0' Ht _ 32 hH' (.inl rfl) (nameField_ne_nil f hf) hmode,
      nameOf_record f h0]
    rfl
  · refine ⟨.standard, by decide, ?_⟩
    simp only [Format.opts, Bool.false_eq_true, ↓reduceIte, hHe, lead,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [parseLine_untagged' mode _ h0' Ht _ 42 hH' (.inr rfl) (nameField_ne_nil f hf) hmode,
      nameOf_record f h0]
    rfl
  · refine ⟨mode, hmode, ?_⟩
    simp only [Format.opts, ↓reduceIte, lead]
    rw [parseLine_tagged' mode _ _ _ hH, nameOf_record f h0]
    rfl

theorem recordBody_no (fmt : Format) (f d : Bytes) (x : UInt8) (hx : x = 10 ∨ x = 13) :
    x ∉ recordBody fmt.opts f d := by
  have hhex : x ∉ hexDigest d := fun m => by
    have := hex_byte x ((hexLower_all _ x m).1)
    rcases hx with rfl | rfl
    · exact this.2.1 rfl
    · exact this.2.2.1 rfl
  have hnf := nameField_no f x hx
  have hlead : x ∉ lead f := by
    unfold lead; split <;> rcases hx with rfl | rfl <;> decide
  rw [recordBody_eq _ _ _ (by cases fmt <;> rfl)]
  rcases hx with rfl | rfl <;> cases fmt <;>
    simp [Format.opts, lit_tag, lit_eq, hhex, hnf, hlead]

theorem recordBody_head (fmt : Format) (f d : Bytes) :
    (recordBody fmt.opts f d).head? ≠ some 35 := by
  rw [recordBody_eq _ _ _ (by cases fmt <;> rfl)]
  obtain ⟨h0', Ht, hHe⟩ : ∃ h0 Ht, hexDigest d = h0 :: Ht := by
    match hexDigest d, hexStr_hexDigest d with
    | h0 :: Ht, _ => exact ⟨h0, Ht, rfl⟩
    | [], h => exact absurd h.length (by simp)
  have hm : h0' ∈ hexDigest d := by rw [hHe]; exact List.mem_cons_self ..
  have n35 := (hex_byte h0' ((hexStr_hexDigest d).digits h0' hm).1).2.2.2.2.2.2.1
  unfold lead
  cases fmt <;> cases problematic f <;>
    simp [Format.opts, hHe, lit_tag, n35]

theorem dropCR_of_not_mem (L : Bytes) (h : (13 : UInt8) ∉ L) : dropCR L = L := by
  unfold dropCR
  split
  · rename_i e; exact absurd (List.mem_of_getLast? e) h
  · rfl

def checkOpts : Opts := { check := true }

theorem readPath_file (w : World) (st : St) (f : Bytes) (hd : f ≠ dash) :
    readPath w st f = (w.fs f, st) := by
  simp [readPath, hd]

theorem checkLine_record (w : World) (cname : Bytes) (st : St) (c : Counters) (n : Nat)
    (fmt : Format) (f d : Bytes) (hf : f ≠ []) (h0 : (0 : UInt8) ∉ f) (hd : f ≠ dash)
    (hfs : w.fs f = .ok d) (hmode : st.mode ≠ .reversed) :
    ∃ m, m ≠ .reversed ∧ checkLine w checkOpts false cname st c n (recordBody fmt.opts f d) =
      ({ st with out := st.out ++ (printedName f ++ lit ": OK\n"), mode := m },
       { c with properlyFormatted := true, matched := true }) := by
  obtain ⟨m, hm, hp⟩ := parseLine_record st.mode fmt f d hf h0 hmode
  refine ⟨m, hm, ?_⟩
  have hne : recordBody fmt.opts f d ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [recordBody_eq _ _ _ (by cases fmt <;> rfl)] at this
    cases fmt <;> simp [Format.opts, hexDigest_length] at this
  have hok : ((hexDigest d).map lowerAscii = hexDigest d) := (hexStr_hexDigest d).lower
  unfold checkLine
  rw [ite_eq_right_of_eq_false _ _ (eq_false (recordBody_head fmt f d)),
    dropCR_of_not_mem _ (recordBody_no fmt f d 13 (.inr rfl)), ite_eq_right_of_eq_false _ _ (eq_false hne), hp]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  unfold verifyLine
  rw [readPath_file _ _ _ hd, hfs]
  simp [hok, checkOpts, St.emit, shownName, printedName]

/-- What a round-trip file must satisfy. -/
def GoodFile (fs : Bytes → ReadResult) (p : Bytes × Bytes) : Prop :=
  p.1 ≠ [] ∧ (0 : UInt8) ∉ p.1 ∧ p.1 ≠ dash ∧ fs p.1 = .ok p.2

theorem checkLinesFrom_records (w : World) (cname : Bytes) (fmt : Format) :
    ∀ (files : List (Bytes × Bytes)) (p : Bytes × Bytes) (st : St) (c : Counters) (n : Nat),
      (∀ q ∈ p :: files, GoodFile w.fs q) → st.mode ≠ .reversed →
      ∃ m, checkLinesFrom w checkOpts false cname st c n
          ((p :: files).map fun q => recordBody fmt.opts q.1 q.2) =
        ({ st with
            mode := m
            out := st.out ++ (p :: files).flatMap (fun q => printedName q.1 ++ lit ": OK\n") },
         { c with properlyFormatted := true, matched := true })
  | [], p, st, c, n, hg, hm => by
    obtain ⟨hf, h0, hd, hfs⟩ := hg p (List.mem_cons_self ..)
    obtain ⟨m, -, e⟩ := checkLine_record w cname st c n fmt p.1 p.2 hf h0 hd hfs hm
    refine ⟨m, ?_⟩
    simp only [List.map_cons, List.map_nil, checkLinesFrom, e, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  | q :: files, p, st, c, n, hg, hm => by
    obtain ⟨hf, h0, hd, hfs⟩ := hg p (List.mem_cons_self ..)
    obtain ⟨m, hm', e⟩ := checkLine_record w cname st c n fmt p.1 p.2 hf h0 hd hfs hm
    obtain ⟨m', e'⟩ := checkLinesFrom_records w cname fmt files q
      { st with mode := m, out := st.out ++ (printedName p.1 ++ lit ": OK\n") }
      { c with properlyFormatted := true, matched := true } (n + 1)
      (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm'
    refine ⟨m', ?_⟩
    rw [List.map_cons, checkLinesFrom, e]
    simp only
    rw [e']
    simp [List.append_assoc]

theorem computeAll_files (w : World) (o : Opts) :
    ∀ (st : St) (files : List (Bytes × Bytes)), (∀ q ∈ files, GoodFile w.fs q) →
      computeAll w o st (files.map Prod.fst) =
        ({ st with out := st.out ++ files.flatMap fun q => computeLine o q.1 q.2 }, true)
  | st, [], _ => by simp [computeAll]
  | st, p :: files, hg => by
    obtain ⟨-, -, hd, hfs⟩ := hg p (List.mem_cons_self ..)
    simp only [List.map_cons, computeAll, computeOne, readPath_file _ _ _ hd, hfs]
    rw [computeAll_files w o _ files (fun r hr => hg r (List.mem_cons_of_mem _ hr))]
    simp [St.emit, List.append_assoc]

theorem scan_compute (P : Bytes) (posix : Bool) (fmt : Format) (names : List Bytes) :
    scan P posix (fmt.args ++ lit "--" :: names) = .done fmt.opts names := by
  cases fmt <;> rfl

theorem scan_check (P : Bytes) (posix : Bool) (cf : Bytes) :
    scan P posix [lit "-c", lit "--", cf] = .done checkOpts [cf] := by
  rfl

theorem splitOn_append (c : UInt8) (rest : Bytes) :
    ∀ l : Bytes, c ∉ l → splitOn c (l ++ c :: rest) = l :: splitOn c rest
  | [], _ => by simp [splitOn]
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := splitOn_append c rest xs (fun m => h (List.mem_cons_of_mem _ m))
    simp [splitOn, hx, ih]

theorem splitOn_flatMap (ls : List Bytes) (h : ∀ l ∈ ls, (10 : UInt8) ∉ l) :
    splitOn 10 (ls.flatMap (· ++ [10])) = ls ++ [[]] := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append]
    rw [splitOn_append 10 _ l (h l (List.mem_cons_self ..))]
    simp only [List.nil_append]
    rw [ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

theorem checkLines_flatMap (ls : List Bytes) (h : ∀ l ∈ ls, (10 : UInt8) ∉ l) :
    checkLines (ls.flatMap (· ++ [10])) = ls := by
  simp [checkLines, splitOn_flatMap ls h]

theorem validate_fmt (fmt : Format) : validate fmt.opts = none := by cases fmt <;> rfl

theorem computeLine_fmt (fmt : Format) (f d : Bytes) :
    computeLine fmt.opts f d = recordBody fmt.opts f d ++ [10] := by
  cases fmt <;> rfl

/-- The compute run on readable files: one record per file, in order; nothing on standard
error; status 0. -/
theorem compute_files (P : Bytes) (posix : Bool) (fmt : Format) (fs : Bytes → ReadResult)
    (stdin : Stdin) (files : List (Bytes × Bytes)) (hne : files ≠ [])
    (hg : ∀ q ∈ files, GoodFile fs q) :
    sha256sum { argv := P :: (fmt.args ++ lit "--" :: files.map Prod.fst), posix, fs, stdin } =
      { stdout := files.flatMap (fun q => recordBody fmt.opts q.1 q.2 ++ [10]), stderr := [],
        status := 0 } := by
  have hops : operandsOrStdin (files.map Prod.fst) = files.map Prod.fst := by
    simp [operandsOrStdin, hne]
  have hc : fmt.opts.check = false := by cases fmt <;> rfl
  simp only [sha256sum, World.prog, List.headD_cons, List.tail_cons, scan_compute, validate_fmt,
    runMode, hc, Bool.false_eq_true, ↓reduceIte, hops]
  rw [computeAll_files _ _ _ files hg]
  simp [finish, computeLine_fmt]

theorem summary_clean (w : World) (cname : Bytes) (st : St) :
    summary w checkOpts cname st { properlyFormatted := true, matched := true } = st := by
  rfl

/-- **Compute, then check** (spec.md §11.2). -/
theorem check_after_compute (P : Bytes) (posix posix' : Bool) (fmt : Format)
    (fs fs' : Bytes → ReadResult) (stdin stdin' : Stdin) (files : List (Bytes × Bytes))
    (cf : Bytes) (hne : files ≠ []) (hg : ∀ q ∈ files, GoodFile fs q)
    (hsame : ∀ q ∈ files, fs' q.1 = fs q.1) (hcf : cf ≠ dash)
    (hcs : fs' cf = .ok (sha256sum
      { argv := P :: (fmt.args ++ lit "--" :: files.map Prod.fst), posix, fs, stdin }).stdout) :
    sha256sum { argv := [P, lit "-c", lit "--", cf], posix := posix', fs := fs', stdin := stdin' } =
      { stdout := files.flatMap (fun q => printedName q.1 ++ lit ": OK\n"), stderr := [],
        status := 0 } := by
  rw [compute_files P posix fmt fs stdin files hne hg] at hcs
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, files = p :: rest := by
    cases files with
    | nil => exact absurd rfl hne
    | cons p rest => exact ⟨p, rest, rfl⟩
  have hg' : ∀ q ∈ p :: rest, GoodFile fs' q := by
    intro q hq
    obtain ⟨a, b, c, d⟩ := hg q hq
    exact ⟨a, b, c, (hsame q hq).trans d⟩
  have hlines : checkLines ((p :: rest).flatMap fun q => recordBody fmt.opts q.1 q.2 ++ [10]) =
      (p :: rest).map fun q => recordBody fmt.opts q.1 q.2 := by
    rw [← checkLines_flatMap ((p :: rest).map fun q => recordBody fmt.opts q.1 q.2)
      (fun l hl => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hl
        exact recordBody_no fmt q.1 q.2 10 (.inl rfl))]
    simp [List.flatMap_map]
  obtain ⟨m, e⟩ := checkLinesFrom_records
    { argv := [P, lit "-c", lit "--", cf], posix := posix', fs := fs', stdin := stdin' }
    cf fmt rest p { stdin := stdin' } {} 1 hg' (by simp)
  have hv : validate checkOpts = none := rfl
  have hck : checkOpts.check = true := rfl
  simp only [sha256sum, World.prog, List.headD_cons, List.tail_cons, scan_check, hv, runMode, hck,
    ↓reduceIte, operandsOrStdin, reduceCtorEq, checkAll, checkFile, hcf, decide_false,
    readPath_file _ _ _ hcf, hcs, hlines, e, summary_clean]
  simp [finish, Counters.ok]

end Silmaril.Apps.Sha256sum
