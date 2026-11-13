module

public import Silmaril.Net.Http.Uri.Defs
public import Silmaril.Net.Http.Abnf.Thms

@[expose] public section

/-!
# URI pieces for HTTP targets: theorems

PROVED (standard axioms), each grammar of `Uri/Defs.lean` equals its check:

* `atoms_iff`: `*( p / pct-encoded )` is decided by `scanPct p` (when `%` is not in `p`);
* `segment_iff`, **`absolutePath_iff`** (`1*( "/" segment )`), `query_iff`,
  **`pathWithQuery_iff`** (`absolute-path [ "?" query ]`);
* `regName_iff`, `port_iff`, **`httpAuthority_iff`** (`host [ ":" port ]`);
* `scheme_iff`; `Scheme.isValid_http`, `Scheme.isValid_https`;
* `split_iff`: `A [ c B ]` is decided by splitting at the first `c` when `A` never derives a
  string containing `c`.
-/

namespace Silmaril.Net.Http.Uri

open Silmaril.Formats.Grammar.Ebnf
open Silmaril.Net.Http.Abnf

variable {N : Type} {body : N → Expr UInt8 N}

/-! ## `pct-encoded` and atoms -/

theorem derives_pctEncoded_iff (xs : List UInt8) :
    Derives body pctEncoded xs ↔
      ∃ a b, isHexDig a = true ∧ isHexDig b = true ∧ xs = [0x25, a, b] := by
  simp only [pctEncoded, Derives.sequence_iff, derives_terminal_iff]
  constructor
  · rintro ⟨_, _, rfl, rfl, l, r, rfl, hl, hr⟩
    obtain ⟨a, ha, rfl⟩ := (single_hexdig l).mp hl
    obtain ⟨b, hb, rfl⟩ := (single_hexdig r).mp hr
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨[0x25], [a, b], rfl, rfl, [a], [b], rfl, (single_hexdig _).mpr ⟨a, ha, rfl⟩,
      (single_hexdig _).mpr ⟨b, hb, rfl⟩⟩

theorem derives_atom_iff (p : UInt8 → Bool) (xs : List UInt8) :
    Derives body (atom p) xs ↔
      (∃ x, p x = true ∧ xs = [x]) ∨
        ∃ a b, isHexDig a = true ∧ isHexDig b = true ∧ xs = [0x25, a, b] := by
  simp only [atom, Derives.alternative_iff, derives_cls_iff, derives_pctEncoded_iff]

theorem scanPct_cons_of_ne (p : UInt8 → Bool) {x : UInt8} (r : List UInt8) (hx : x ≠ 0x25) :
    scanPct p (x :: r) = (p x && scanPct p r) := by
  have hx' : (x != 0x25) = true := bne_iff_ne.mpr hx
  match r with
  | [] => simp [scanPct, hx']
  | [y] => simp [scanPct, hx', Bool.and_assoc]
  | [y, z] => simp [scanPct, hx]
  | y :: z :: w :: rest => simp [scanPct, hx]

theorem scanPct_pct (p : UInt8 → Bool) (a b : UInt8) (r : List UInt8) :
    scanPct p (0x25 :: a :: b :: r) = (isHexDig a && isHexDig b && scanPct p r) := by
  simp [scanPct]

theorem scanPct_pct_one (p : UInt8 → Bool) : scanPct p [0x25] = false := by
  simp [scanPct]

theorem scanPct_pct_two (p : UInt8 → Bool) (a : UInt8) : scanPct p [0x25, a] = false := by
  simp [scanPct]

theorem scanPct_atom_append {p : UInt8 → Bool} (hp : p 0x25 = false) {a : List UInt8}
    (h : Derives body (atom p) a) (r : List UInt8) : scanPct p (a ++ r) = scanPct p r := by
  rcases (derives_atom_iff p a).mp h with ⟨x, hx, rfl⟩ | ⟨a, b, ha, hb, rfl⟩
  · have hx' : x ≠ 0x25 := by rintro rfl; simp [hp] at hx
    simp [scanPct_cons_of_ne p r hx', hx]
  · simp [scanPct_pct, ha, hb]

theorem atoms_sound {p : UInt8 → Bool} (hp : p 0x25 = false) {xs : List UInt8}
    (h : Derives body (atoms p) xs) : scanPct p xs = true := by
  obtain ⟨parts, hparts, rfl⟩ := (derives_repetition_iff _ _).mp h
  clear h
  induction parts with
  | nil => rfl
  | cons q qs ih =>
    have hq : Derives body (atom p) q := hparts q (List.mem_cons_self ..)
    rw [List.flatten_cons, scanPct_atom_append hp hq]
    exact ih (fun r hr => hparts r (List.mem_cons_of_mem _ hr))

theorem atoms_complete (p : UInt8 → Bool) :
    (xs : List UInt8) → scanPct p xs = true → Derives body (atoms p) xs
  | [], _ => .nil
  | x :: rest, h => by
    by_cases hx : x = 0x25
    · match rest, h with
      | a :: b :: rest', h =>
        have hab : isHexDig a = true ∧ isHexDig b = true ∧ scanPct p rest' = true := by
          rw [hx, scanPct_pct] at h; simpa [Bool.and_assoc] using h
        have hd : Derives body (atom p) [0x25, a, b] :=
          (derives_atom_iff p _).mpr (Or.inr ⟨a, b, hab.1, hab.2.1, rfl⟩)
        rw [hx]
        exact Derives.cons (xs := [0x25, a, b]) hd (atoms_complete p rest' hab.2.2)
      | [], h => rw [hx, scanPct_pct_one] at h; exact absurd h (by decide)
      | [_], h => rw [hx, scanPct_pct_two] at h; exact absurd h (by decide)
    · have hr : p x = true ∧ scanPct p rest = true := by
        rw [scanPct_cons_of_ne p rest hx] at h; simpa using h
      have hd : Derives body (atom p) [x] := (derives_atom_iff p _).mpr (Or.inl ⟨x, hr.1, rfl⟩)
      exact Derives.cons (xs := [x]) hd (atoms_complete p rest hr.2)
termination_by xs => xs.length

/-- **`*( p / pct-encoded )` is decided by `scanPct p`.** -/
theorem atoms_iff {p : UInt8 → Bool} (hp : p 0x25 = false) (xs : List UInt8) :
    Derives body (atoms p) xs ↔ scanPct p xs = true :=
  ⟨atoms_sound hp, atoms_complete p xs⟩

theorem repetition_append {e : Expr UInt8 N} {a b : List UInt8} (ha : Derives body (.repetition e) a)
    (hb : Derives body (.repetition e) b) : Derives body (.repetition e) (a ++ b) := by
  obtain ⟨pa, hpa, rfl⟩ := (derives_repetition_iff _ _).mp ha
  obtain ⟨pb, hpb, rfl⟩ := (derives_repetition_iff _ _).mp hb
  refine (derives_repetition_iff _ _).mpr ⟨pa ++ pb, ?_, by simp⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hpa q hq
  · exact hpb q hq

theorem atom_ne_nil {p : UInt8 → Bool} {a : List UInt8} (h : Derives body (atom p) a) :
    a ≠ [] := by
  rcases (derives_atom_iff p a).mp h with ⟨x, -, rfl⟩ | ⟨a, b, -, -, rfl⟩ <;> simp

theorem not_mem_of_atoms {p : UInt8 → Bool} {c : UInt8} (hpc : p c = false)
    (hhex : isHexDig c = false) (hc : c ≠ 0x25) {xs : List UInt8}
    (h : Derives body (atoms p) xs) : c ∉ xs := by
  obtain ⟨parts, hparts, rfl⟩ := (derives_repetition_iff _ _).mp h
  simp only [List.mem_flatten, not_exists, not_and]
  intro q hq hcq
  rcases (derives_atom_iff p q).mp (hparts q hq) with ⟨x, hx, rfl⟩ | ⟨a, b, ha, hb, rfl⟩
  · simp only [List.mem_singleton] at hcq; subst hcq; simp [hpc] at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcq
    rcases hcq with rfl | rfl | rfl
    · exact hc rfl
    · simp [hhex] at ha
    · simp [hhex] at hb

/-! ## Splitting at a delimiter -/

theorem splitAt?_of_not_mem {c : UInt8} {a : List UInt8} (h : c ∉ a) :
    splitAt? c a = (a, none) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ c := fun hx => h (hx ▸ List.mem_cons_self ..)
    have hxs : c ∉ xs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [splitAt?, hx, ih hxs]

theorem splitAt?_append {c : UInt8} {a : List UInt8} (h : c ∉ a) (b : List UInt8) :
    splitAt? c (a ++ c :: b) = (a, some b) := by
  induction a with
  | nil => simp [splitAt?]
  | cons x xs ih =>
    have hx : x ≠ c := fun hx => h (hx ▸ List.mem_cons_self ..)
    have hxs : c ∉ xs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [splitAt?, hx, ih hxs]

theorem splitAt?_spec (c : UInt8) (xs : List UInt8) :
    c ∉ (splitAt? c xs).1 ∧
      xs = (splitAt? c xs).1 ++ ((splitAt? c xs).2.map (c :: ·)).getD [] := by
  induction xs with
  | nil => simp [splitAt?]
  | cons x xs ih =>
    by_cases hx : x = c
    · subst hx; simp [splitAt?]
    · simp only [splitAt?, hx, ite_false, List.mem_cons, List.cons_append]
      exact ⟨fun h => h.elim (fun h' => hx h'.symm) ih.1, by rw [← ih.2]⟩

/-- `A [ c B ]`, when `A` never derives a string with `c`, is decided by splitting at the
first `c`. -/
theorem split_iff {A B : Expr UInt8 N} {c : UInt8}
    (hA : ∀ xs, Derives body A xs → c ∉ xs) (xs : List UInt8) :
    Derives body (.sequence A (Expr.optional (.sequence (.terminal c) B))) xs ↔
      Derives body A (splitAt? c xs).1 ∧ ∀ b ∈ (splitAt? c xs).2, Derives body B b := by
  simp only [Derives.sequence_iff, Expr.optional, Derives.alternative_iff, Derives.epsilon_iff,
    derives_terminal_iff]
  constructor
  · rintro ⟨a, r, rfl, ha, rfl | ⟨_, b, rfl, rfl, hb⟩⟩
    · simp only [List.append_nil, splitAt?_of_not_mem (hA a ha)]
      exact ⟨ha, by simp⟩
    · simp only [List.singleton_append, splitAt?_append (hA a ha)]
      exact ⟨ha, by simpa using hb⟩
  · rintro ⟨ha, hb⟩
    have hspec := splitAt?_spec c xs
    cases hs : (splitAt? c xs).2 with
    | none =>
      refine ⟨(splitAt? c xs).1, [], ?_, ha, Or.inl rfl⟩
      simpa [hs] using hspec.2.symm
    | some b =>
      refine ⟨(splitAt? c xs).1, c :: b, ?_, ha, Or.inr ⟨[c], b, rfl, rfl, hb b (by simp [hs])⟩⟩
      simpa [hs] using hspec.2.symm

theorem option_forall_iff {P : List UInt8 → Prop} {f : List UInt8 → Bool}
    (h : ∀ b, P b ↔ f b = true) (o : Option (List UInt8)) :
    (∀ b ∈ o, P b) ↔ o.all f = true := by
  cases o <;> simp [h]

/-! ## Paths and queries -/

theorem segment_iff (xs : List UInt8) :
    Derives body segment xs ↔ scanPct isPcharOctet xs = true :=
  atoms_iff (by decide) xs

theorem query_iff (xs : List UInt8) : Derives body query xs ↔ isQuery xs = true :=
  atoms_iff (by decide) xs

/-- `"/" segment`. -/
abbrev slashSeg : Expr UInt8 N := .sequence (.terminal 0x2F) segment

theorem atoms_mono {p q : UInt8 → Bool} (hpq : ∀ x, p x = true → q x = true) {xs : List UInt8}
    (h : Derives body (atoms p) xs) : Derives body (atoms q) xs := by
  obtain ⟨parts, hparts, rfl⟩ := (derives_repetition_iff _ _).mp h
  refine (derives_repetition_iff _ _).mpr ⟨parts, fun r hr => ?_, rfl⟩
  rcases (derives_atom_iff p r).mp (hparts r hr) with ⟨x, hx, rfl⟩ | h
  · exact (derives_atom_iff q _).mpr (Or.inl ⟨x, hpq x hx, rfl⟩)
  · exact (derives_atom_iff q _).mpr (Or.inr h)

theorem slashSeg_atoms {xs : List UInt8} (h : Derives body slashSeg xs) :
    Derives body (atoms isPathOctet) xs ∧ xs.head? = some 0x2F := by
  obtain ⟨_, seg, rfl, hs, hseg⟩ := (Derives.sequence_iff _ _ _).mp h
  rw [(derives_terminal_iff _ _).mp hs]
  have hslash : Derives body (atom isPathOctet) [0x2F] :=
    (derives_atom_iff _ _).mpr (Or.inl ⟨0x2F, by decide, rfl⟩)
  have hseg' : Derives body (atoms isPathOctet) seg :=
    atoms_mono (fun x hx => by simp [isPathOctet, hx]) hseg
  exact ⟨Derives.cons hslash hseg', rfl⟩

theorem repSlashSeg_atoms {xs : List UInt8} (h : Derives body (.repetition slashSeg) xs) :
    Derives body (atoms isPathOctet) xs := by
  obtain ⟨parts, hparts, rfl⟩ := (derives_repetition_iff _ _).mp h
  clear h
  induction parts with
  | nil => exact .nil
  | cons q qs ih =>
    exact repetition_append (slashSeg_atoms (hparts q (List.mem_cons_self ..))).1
      (ih (fun r hr => hparts r (List.mem_cons_of_mem _ hr)))

theorem absolutePath_sound {xs : List UInt8} (h : Derives body absolutePath xs) :
    isAbsolutePath xs = true := by
  obtain ⟨a, r, rfl, ha, hr⟩ := (Derives.sequence_iff _ _ _).mp h
  obtain ⟨ha', hhead⟩ := slashSeg_atoms ha
  have hall : Derives body (atoms isPathOctet) (a ++ r) :=
    repetition_append ha' (repSlashSeg_atoms hr)
  have hhead' : (a ++ r).head? = some 0x2F := by simp [List.head?_append, hhead]
  simp only [isAbsolutePath, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hhead', atoms_sound (by decide) hall⟩

theorem atom_path_cases {a : List UInt8} (h : Derives body (atom isPathOctet) a) :
    a = [0x2F] ∨ Derives body pchar a := by
  rcases (derives_atom_iff _ a).mp h with ⟨x, hx, rfl⟩ | hp
  · by_cases hx' : x = 0x2F
    · exact Or.inl (by rw [hx'])
    · have hpc : isPcharOctet x = true := by simpa [isPathOctet, hx'] using hx
      exact Or.inr ((derives_atom_iff _ _).mpr (Or.inl ⟨x, hpc, rfl⟩))
  · exact Or.inr ((derives_atom_iff _ _).mpr (Or.inr hp))

theorem absolutePath_rep {xs : List UInt8} (h : Derives body absolutePath xs) :
    Derives body (.repetition slashSeg) xs := by
  obtain ⟨a, r, rfl, ha, hr⟩ := (Derives.sequence_iff _ _ _).mp h
  exact Derives.cons ha hr

/-- A slash, a segment and a run of path atoms form an `absolute-path`. -/
theorem absolutePath_of_atoms (as : List (List UInt8))
    (has : ∀ a ∈ as, Derives body (atom isPathOctet) a) :
    ∀ seg, Derives body segment seg → Derives body absolutePath ([0x2F] ++ seg ++ as.flatten) := by
  induction as with
  | nil =>
    intro seg hseg
    show Derives body absolutePath ([0x2F] ++ seg ++ ([] : List (List UInt8)).flatten)
    have h1 : Derives body slashSeg ([0x2F] ++ seg) := Derives.sequence (.terminal _) hseg
    have h2 : Derives body absolutePath (([0x2F] ++ seg) ++ []) := Derives.sequence h1 Derives.nil
    rw [List.append_nil] at h2
    simpa only [List.flatten_nil, List.append_nil] using h2
  | cons a as ih =>
    show ∀ seg, Derives body segment seg →
      Derives body absolutePath ([0x2F] ++ seg ++ (a :: as).flatten)
    intro seg hseg
    have hrest := ih (fun b hb => has b (List.mem_cons_of_mem _ hb))
    rcases atom_path_cases (has a (List.mem_cons_self ..)) with rfl | hp
    · show Derives body absolutePath ([0x2F] ++ seg ++ ([0x2F] :: as).flatten)
      have h1 : Derives body slashSeg ([0x2F] ++ seg) := Derives.sequence (.terminal _) hseg
      have h2 : Derives body absolutePath ([0x2F] ++ [] ++ as.flatten) := hrest [] .nil
      have h3 : Derives body absolutePath (([0x2F] ++ seg) ++ ([0x2F] ++ [] ++ as.flatten)) :=
        Derives.sequence h1 (absolutePath_rep h2)
      have e : [0x2F] ++ seg ++ List.flatten ([0x2F] :: as) =
          ([0x2F] ++ seg) ++ ([0x2F] ++ [] ++ as.flatten) := by simp
      rw [e]; exact h3
    · show Derives body absolutePath ([0x2F] ++ seg ++ (a :: as).flatten)
      have hsa' : Derives body segment (a ++ []) := Derives.cons hp Derives.nil
      have hsa : Derives body segment a := by rw [List.append_nil] at hsa'; exact hsa'
      have hseg' : Derives body segment (seg ++ a) := repetition_append hseg hsa
      simpa [List.append_assoc] using hrest (seg ++ a) hseg'

/-- **`absolute-path = 1*( "/" segment )` is decided by `isAbsolutePath`** (RFC 9110 §4.1). -/
theorem absolutePath_iff (xs : List UInt8) :
    Derives body absolutePath xs ↔ isAbsolutePath xs = true := by
  refine ⟨absolutePath_sound, fun h => ?_⟩
  simp only [isAbsolutePath, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨parts, hparts, rfl⟩ :=
    (derives_repetition_iff _ _).mp (atoms_complete (body := body) _ _ h.2)
  rcases parts with _ | ⟨q, qs⟩
  · simp at h
  · have hq : Derives body (atom isPathOctet) q := hparts q (List.mem_cons_self ..)
    have hqne := atom_ne_nil hq
    have hhead : q.head? = some 0x2F := by
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hqne
      simpa [List.flatten_cons] using h.1
    have hq' : q = [0x2F] := by
      rcases (derives_atom_iff _ q).mp hq with ⟨x, -, rfl⟩ | ⟨a, b, -, -, rfl⟩
      · simpa using hhead
      · simp at hhead
    subst hq'
    simpa using absolutePath_of_atoms qs (fun r hr => hparts r (List.mem_cons_of_mem _ hr)) []
      .nil

theorem not_mem_absolutePath {xs : List UInt8} (h : Derives body absolutePath xs) :
    (0x3F : UInt8) ∉ xs := by
  have h' := (absolutePath_iff xs).mp h
  simp only [isAbsolutePath, Bool.and_eq_true] at h'
  exact not_mem_of_atoms (p := isPathOctet) (by decide) (by decide) (by decide)
    (atoms_complete (body := body) _ _ h'.2)

/-- **`absolute-path [ "?" query ]` is decided by `isPathWithQuery`** (RFC 9110 §7.1). -/
theorem pathWithQuery_iff (xs : List UInt8) :
    Derives body pathWithQuery xs ↔ isPathWithQuery xs = true := by
  rw [pathWithQuery, split_iff (fun _ h => not_mem_absolutePath h), absolutePath_iff,
    option_forall_iff query_iff]
  simp only [isPathWithQuery, Bool.and_eq_true]

/-! ## Authorities -/

theorem regName_iff (xs : List UInt8) : Derives body regName xs ↔ isRegName xs = true :=
  atoms_iff (by decide) xs

theorem port_iff (xs : List UInt8) : Derives body port xs ↔ isPort xs = true :=
  single_digit.repetition_iff xs

/-- **`host [ ":" port ]` is decided by `isHttpAuthority`** (RFC 9110 §4.2.1). -/
theorem httpAuthority_iff (xs : List UInt8) :
    Derives body httpAuthority xs ↔ isHttpAuthority xs = true := by
  have hA : ∀ ys, Derives body regName ys → (0x3A : UInt8) ∉ ys :=
    fun _ h => not_mem_of_atoms (p := isRegNameOctet) (by decide) (by decide) (by decide) h
  rw [httpAuthority, split_iff hA, regName_iff, option_forall_iff port_iff]
  simp only [isHttpAuthority, Bool.and_eq_true]

/-! ## Schemes -/

/-- **`scheme` is decided by `isScheme`** (RFC 3986 §3.1). -/
theorem scheme_iff (xs : List UInt8) : Derives body scheme xs ↔ isScheme xs = true := by
  simp only [scheme, Derives.sequence_iff, single_alpha _, (single_cls isSchemeOctet).repetition_iff]
  constructor
  · rintro ⟨_, r, rfl, ⟨x, hx, rfl⟩, hr⟩
    simp [isScheme, hx, hr]
  · intro h
    rcases xs with _ | ⟨x, r⟩
    · simp [isScheme] at h
    · simp only [isScheme, Bool.and_eq_true] at h
      exact ⟨[x], r, rfl, ⟨x, h.1, rfl⟩, h.2⟩

/-! ## Vectors -/

/-- The octets of an ASCII string literal. -/
private abbrev lit (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)

example : isPathWithQuery (lit "/") = true := by decide
example : isPathWithQuery (lit "/a/b%20c?x=1&y=/z?") = true := by decide
example : isPathWithQuery (lit "//a") = true := by decide
example : isPathWithQuery (lit "a/b") = false := by decide
example : isPathWithQuery (lit "/a b") = false := by decide
example : isPathWithQuery (lit "/a%2") = false := by decide
example : isPathWithQuery (lit "/a#f") = false := by decide
example : isPathWithQuery [] = false := by decide
example : isHttpAuthority (lit "example.com") = true := by decide
example : isHttpAuthority (lit "127.0.0.1:8080") = true := by decide
example : isHttpAuthority (lit "example.com:") = true := by decide
example : isHttpAuthority (lit "a:b") = false := by decide
example : isHttpAuthority (lit "user@example.com") = false := by decide
example : isScheme (lit "coap+tcp") = true := by decide
example : isScheme (lit "1http") = false := by decide

end Silmaril.Net.Http.Uri

namespace Silmaril.Net.Http

theorem Scheme.isValid_http : Scheme.http.isValid = true := by decide

theorem Scheme.isValid_https : Scheme.https.isValid = true := by decide

end Silmaril.Net.Http
