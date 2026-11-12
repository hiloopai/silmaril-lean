module

public import Silmaril.Cli.Info.Defs
public import Silmaril.Cli.Institution.Thms
public import Silmaril.Cli.Io.Thms

@[expose] public section

/-!
# Proofs: the help and version sentences

* `utf8_append`, `utf8_line_ne`: UTF-8 bytes of an append, a line is not empty;
* `HelpVariant.fits_line`, `VersionVariant.fits_versionLine`: texts that fit a variant;
* the lattice: `ExitReq.Le`, `Dest.Le`, `Extra.Le`, `Reply.Le`, `HelpVariant.Le` and
  `VersionVariant.Le` are preorders whose order implies the sentences (`sen2_mono`, `sen_mono`);
* the levels: the `L3` sentence implies the `L2` one on the uniform reduct (`sen_le_liftAll`),
  and equals it without `quiet` (`sen_eq_liftAll`);
* models: `Prog.model_sat_iff`, `ofSpec_sat_iff`, `sat_via_iff`.

A Silmaril addition.
-/

namespace Silmaril.Cli.Info

open Silmaril.Cli Silmaril.Cli.Institution

/-! ## UTF-8 -/

theorem byteArray_toList_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hlt ih =>
    have hi : i < b.data.toList.length := by simpa using hlt
    rw [ih, List.drop_eq_getElem_cons hi]
    have hget : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, getElem!_pos, hlt]
    simp [hget]
  | case2 i r hlt =>
    have hle : b.data.toList.length ≤ i := by simpa using Nat.le_of_not_lt hlt
    simp [List.drop_eq_nil_of_le hle]

theorem byteArray_toList (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, byteArray_toList_loop]

theorem utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t := by
  simp only [utf8, String.toUTF8_eq_toByteArray, String.toByteArray_append, byteArray_toList,
    ByteArray.data_append, Array.toList_append]

theorem utf8_newline : utf8 "\n" = [10] := by decide +kernel

/-- A line (a text and a newline) is not empty. -/
theorem utf8_line_ne (s : String) : utf8 (s ++ "\n") ≠ [] := by
  rw [utf8_append, utf8_newline]; simp

/-! ## Texts that fit -/

theorem Dest.text_line (d : Dest) (b : Bytes) (c : ExitCode) :
    d.text { stdout := b, stderr := [], exit := c } = b := by
  cases d <;> simp [Dest.text]

theorem Dest.ok_line (d : Dest) (b : Bytes) (c : ExitCode) :
    d.Ok { stdout := b, stderr := [], exit := c } := by
  cases d <;> simp [Dest.Ok]

theorem ExitReq.ok_zero (e : ExitReq) : e.Ok 0 := by
  cases e <;> simp [ExitReq.Ok]

theorem Reply.shows_line {r : Reply} {b : Bytes} (h : r.TextOk b) :
    r.Shows { stdout := b, stderr := [], exit := 0 } :=
  ⟨r.exit.ok_zero, r.dest.ok_line b 0, by rw [Dest.text_line]; exact h⟩

/-- **A help text on stdout, exit 0, that fits shows help.** -/
theorem HelpVariant.shows_line {v : HelpVariant} {p : List String} {b : Bytes}
    (h : v.Fits p b) : v.Shows p { stdout := b, stderr := [], exit := 0 } :=
  ⟨Reply.shows_line h.1, fun q hq hp => by rw [Dest.text_line]; exact h.2 q hq hp⟩

/-- **A version text on stdout, exit 0, that fits shows the version.** -/
theorem VersionVariant.shows_line {v : VersionVariant} {b : Bytes} (h : v.Fits b) :
    v.Shows { stdout := b, stderr := [], exit := 0 } :=
  ⟨Reply.shows_line h.1, fun ver hv => by rw [Dest.text_line]; exact h.2 ver hv⟩

/-- A line fits a variant that pins no text and requires no substring. -/
theorem HelpVariant.fits_line {v : HelpVariant} (hm : v.reply.mentions = []) (ht : v.texts = [])
    (p : List String) (s : String) : v.Fits p (utf8 (s ++ "\n")) :=
  ⟨⟨fun _ => utf8_line_ne s, by simp [hm]⟩, by simp [ht]⟩

/-- The version line `NAME VERSION` fits a variant whose required substrings are the name or
the version, and whose version is that version. -/
theorem VersionVariant.fits_versionLine {v : VersionVariant} {name ver : String}
    (hm : ∀ m ∈ v.reply.mentions, m = name ∨ m = ver) (hv : ∀ x ∈ v.version?, x = ver) :
    v.Fits (utf8 (name ++ " " ++ ver ++ "\n")) := by
  have hname : utf8 name <:+: utf8 (name ++ " " ++ ver ++ "\n") :=
    ⟨[], utf8 " " ++ utf8 ver ++ utf8 "\n", by simp [utf8_append]⟩
  have hver : utf8 ver <:+: utf8 (name ++ " " ++ ver ++ "\n") :=
    ⟨utf8 name ++ utf8 " ", utf8 "\n", by simp [utf8_append]⟩
  refine ⟨⟨fun _ => utf8_line_ne _, fun m hm' => ?_⟩, fun x hx => ?_⟩
  · rcases hm m hm' with rfl | rfl
    · exact hname
    · exact hver
  · rw [hv x hx]; exact hver

/-- Exit code, streams and text are what a usage error of a derived front end shows. -/
theorem usageErr_line (b : Bytes) : UsageErr { stdout := [], stderr := b, exit := 2 } :=
  ⟨show (2 : ExitCode) ≠ 0 by decide, rfl⟩

/-! ## The lattice -/

theorem ExitReq.Le.refl (a : ExitReq) : a.Le a := .inr rfl

theorem ExitReq.Le.ok {a b : ExitReq} (h : a.Le b) {c : ExitCode} (hc : a.Ok c) : b.Ok c := by
  rcases h with rfl | rfl
  · trivial
  · exact hc

theorem Dest.Le.refl (a : Dest) : a.Le a := .inr rfl

theorem Dest.Le.text {a b : Dest} (h : a.Le b) {o : Spec.Out} (ho : a.Ok o) :
    b.Ok o ∧ b.text o = a.text o := by
  rcases h with rfl | rfl
  · refine ⟨trivial, ?_⟩
    cases a with
    | stdout =>
      have : o.stderr = [] := ho
      simp [Dest.text, this]
    | either => rfl
  · exact ⟨ho, rfl⟩

theorem Extra.Le.refl (a : Extra) : a.Le a := .inr (.inl rfl)

theorem Extra.Le.claim {a b : Extra} (h : a.Le b) {rest : List String} {H H' U : Prop}
    (hH : H → H') (hc : a.Claim rest H U) : b.Claim rest H' U := by
  rcases h with rfl | rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · trivial
  · cases a with
    | ignore => trivial
    | wins => exact hH hc
    | winsOperands => exact fun hr => hH (hc hr)
    | error => exact hc
    | either => exact hc.imp_left hH
  · exact fun _ => hH hc
  · exact .inl (hH hc)
  · exact .inr hc

theorem Extra.Le.covers {a b : Extra} (h : a.Le b) {rest : List String} (hc : b.Covers rest) :
    a.Covers rest := by
  rcases h with rfl | rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact hc.elim
  · exact hc
  all_goals trivial

theorem Reply.Le.refl (r : Reply) : r.Le r :=
  ⟨.refl _, .refl _, id, fun _ h => h⟩

theorem Reply.Le.shows {r s : Reply} (h : r.Le s) {o : Spec.Out} (ho : r.Shows o) :
    s.Shows o ∧ s.dest.text o = r.dest.text o := by
  obtain ⟨he, hd, hn, hm⟩ := h
  obtain ⟨hx, hok, hne, hmen⟩ := ho
  obtain ⟨hok', ht⟩ := hd.text hok
  refine ⟨⟨he.ok hx, hok', ?_, ?_⟩, ht⟩
  · rw [ht]; exact fun h => hne (hn h)
  · rw [ht]; exact fun m h => hmen m (hm h)

theorem HelpVariant.mem_tokens {v : HelpVariant} {t : String} :
    t ∈ v.tokens ↔ (v.long = true ∧ t = "--help") ∨ (v.short = true ∧ t = "-h") := by
  unfold HelpVariant.tokens
  cases v.long <;> cases v.short <;> simp

theorem VersionVariant.mem_tokens {v : VersionVariant} {t : String} :
    t ∈ v.tokens ↔ (v.long = true ∧ t = "--version") ∨ (v.short = true ∧ t = "-V") := by
  unfold VersionVariant.tokens
  cases v.long <;> cases v.short <;> simp

theorem HelpVariant.Le.refl (v : HelpVariant) : v.Le v :=
  ⟨id, id, id, fun _ h => h, .refl _, .refl _, fun _ h => h, id⟩

theorem HelpVariant.Le.tokens {v w : HelpVariant} (h : v.Le w) {t : String} (ht : t ∈ w.tokens) :
    t ∈ v.tokens := by
  rw [HelpVariant.mem_tokens] at ht ⊢
  exact ht.imp (fun ⟨a, b⟩ => ⟨h.1 a, b⟩) (fun ⟨a, b⟩ => ⟨h.2.1 a, b⟩)

theorem HelpVariant.Le.roots {v w : HelpVariant} (h : v.Le w) {p : List String}
    (hp : p ∈ w.roots) : p ∈ v.roots := by
  simp only [HelpVariant.roots, List.mem_cons] at hp ⊢
  exact hp.imp id fun hp => h.2.2.2.1 hp

theorem HelpVariant.Le.shows {v w : HelpVariant} (h : v.Le w) {p : List String} {o : Spec.Out}
    (ho : v.Shows p o) : w.Shows p o := by
  obtain ⟨hr, ht⟩ := h.2.2.2.2.2.1.shows ho.1
  exact ⟨hr, fun q hq hqp => by rw [ht]; exact ho.2 q (h.2.2.2.2.2.2.1 hq) hqp⟩

/-- **A stricter variant's `L2` sentence implies the looser one's.** -/
theorem HelpVariant.sen2_mono {v w : HelpVariant} (h : v.Le w) : v.sen2 ≤ w.sen2 := by
  intro a o H p hp
  obtain ⟨h1, h2, h3⟩ := H p (h.roots hp)
  refine ⟨fun t ht ha => h.shows (h1 t (h.tokens ht) ha), fun hw ha => h.shows (h2 (h.2.2.1 hw) ha),
    fun t ht rest hr ha => h.2.2.2.2.1.claim h.shows (h3 t (h.tokens ht) rest hr ha)⟩

theorem HelpVariant.Le.asked {v w : HelpVariant} (h : v.Le w) {args : List String}
    (ha : w.Asked args) : v.Asked args := by
  obtain ⟨p, hp, ⟨t, ht, hx⟩ | ⟨hw, hx⟩⟩ := ha
  · refine ⟨p, h.roots hp, .inl ⟨t, h.tokens ht, ?_⟩⟩
    exact hx.imp id fun ⟨rest, hr, he, hc⟩ => ⟨rest, hr, he, h.2.2.2.2.1.covers hc⟩
  · exact ⟨p, h.roots hp, .inr ⟨h.2.2.1 hw, hx⟩⟩

/-- **A stricter variant's sentence implies the looser one's.** -/
theorem HelpVariant.sen_mono {v w : HelpVariant} (h : v.Le w) : v.sen ≤ w.sen :=
  fun _ _ H => ⟨HelpVariant.sen2_mono h _ _ H.1,
    fun hq ha => H.2 (h.2.2.2.2.2.2.2 hq) (h.asked ha)⟩

theorem HelpVariant.Le.trans {u v w : HelpVariant} (h₁ : u.Le v) (h₂ : v.Le w) : u.Le w := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, k1⟩ := h₁
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, k2⟩ := h₂
  refine ⟨a1 ∘ a2, b1 ∘ b2, c1 ∘ c2, fun _ h => d1 (d2 h), ?_, ?_, fun _ h => g1 (g2 h), k1 ∘ k2⟩
  · rcases e1 with h1 | h1 | ⟨h1, h1' | h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases e2 with h2 | h2 | ⟨h2, h2' | h2'⟩ | ⟨h2, h2'⟩ <;>
    simp_all [Extra.Le]
  · obtain ⟨x1, y1, n1, m1⟩ := f1
    obtain ⟨x2, y2, n2, m2⟩ := f2
    refine ⟨?_, ?_, n1 ∘ n2, fun _ h => m1 (m2 h)⟩
    · rcases x1 with h1 | h1 <;> rcases x2 with h2 | h2 <;> simp_all [ExitReq.Le]
    · rcases y1 with h1 | h1 <;> rcases y2 with h2 | h2 <;> simp_all [Dest.Le]

theorem VersionVariant.Le.refl (v : VersionVariant) : v.Le v :=
  ⟨id, id, .refl _, fun _ h => by simpa using h, id⟩

theorem VersionVariant.Le.tokens {v w : VersionVariant} (h : v.Le w) {t : String}
    (ht : t ∈ w.tokens) : t ∈ v.tokens := by
  rw [VersionVariant.mem_tokens] at ht ⊢
  exact ht.imp (fun ⟨a, b⟩ => ⟨h.1 a, b⟩) (fun ⟨a, b⟩ => ⟨h.2.1 a, b⟩)

theorem VersionVariant.Le.shows {v w : VersionVariant} (h : v.Le w) {o : Spec.Out}
    (ho : v.Shows o) : w.Shows o := by
  obtain ⟨hr, ht⟩ := h.2.2.1.shows ho.1
  refine ⟨hr, fun ver hv => ?_⟩
  rw [ht]; exact ho.2 ver (by simp [h.2.2.2.1 ver hv])

/-- **A stricter version variant's `L2` sentence implies the looser one's.** -/
theorem VersionVariant.sen2_mono {v w : VersionVariant} (h : v.Le w) : v.sen2 ≤ w.sen2 :=
  fun _ _ H t ht ha => h.shows (H t (h.tokens ht) ha)

/-- **A stricter version variant's sentence implies the looser one's.** -/
theorem VersionVariant.sen_mono {v w : VersionVariant} (h : v.Le w) : v.sen ≤ w.sen :=
  fun _ _ H => ⟨VersionVariant.sen2_mono h _ _ H.1,
    fun hq t ht ha => H.2 (h.2.2.2.2 hq) t (h.tokens ht) ha⟩

/-! ## Levels -/

/-- **The `L3` sentence implies the `L2` sentence on every extension of the input.** -/
theorem HelpVariant.sen_le_liftAll (v : HelpVariant) : v.sen ≤ Level.liftAll v.sen2 :=
  fun i o h => (Level.liftAll_iff _ i o).mpr h.1

/-- Without `quiet`, the `L3` sentence is the uniform lift of the `L2` sentence. -/
theorem HelpVariant.sen_eq_liftAll {v : HelpVariant} (hq : v.quiet = false) :
    v.sen = Level.liftAll v.sen2 := by
  funext i o
  apply propext
  exact ⟨fun h => (Level.liftAll_iff _ i o).mpr h.1,
    fun h => ⟨(Level.liftAll_iff _ i o).mp h, fun h' => absurd (hq ▸ h') (by simp)⟩⟩

theorem VersionVariant.sen_le_liftAll (v : VersionVariant) : v.sen ≤ Level.liftAll v.sen2 :=
  fun i o h => (Level.liftAll_iff _ i o).mpr h.1

theorem VersionVariant.sen_eq_liftAll {v : VersionVariant} (hq : v.quiet = false) :
    v.sen = Level.liftAll v.sen2 := by
  funext i o
  apply propext
  exact ⟨fun h => (Level.liftAll_iff _ i o).mpr h.1,
    fun h => ⟨(Level.liftAll_iff _ i o).mp h, fun h' => absurd (hq ▸ h') (by simp)⟩⟩

/-- **A full model meeting the help sentence has an `L2` reduct meeting the `L2` one.** -/
theorem HelpVariant.sat_reduct {v : HelpVariant} {M : Model Level.full.sig} (h : M.Sat v.sen) :
    ((Level.homAll .command .full).mod M).Sat v.sen2 :=
  (Level.sat_liftAll_iff M v.sen2).mp (h.mono v.sen_le_liftAll)

theorem VersionVariant.sat_reduct {v : VersionVariant} {M : Model Level.full.sig}
    (h : M.Sat v.sen) : ((Level.homAll .command .full).mod M).Sat v.sen2 :=
  (Level.sat_liftAll_iff M v.sen2).mp (h.mono v.sen_le_liftAll)

/-! ## Models -/

/-- **A Lean program satisfies a sentence as a model iff it satisfies it as a program.** -/
theorem _root_.Silmaril.Cli.Io.Prog.model_sat_iff (p : Io.Prog ExitCode) (φ : Spec) :
    p.model.Sat φ ↔ p.Sat φ :=
  ⟨fun h i => h i _ rfl, fun h i _ ho => ho ▸ h i⟩

/-- A specification read as a model satisfies `φ` iff it refines `φ`. -/
theorem ofSpec_sat_iff (S φ : Spec) : (ofSpec S).Sat φ ↔ S ≤ φ :=
  ⟨fun h i o => h i o, fun h i o => h i o⟩

/-- **Any model with a morphism from the full interface**: it satisfies the translated
sentence iff its reduct to the full interface satisfies the sentence. -/
theorem sat_via_iff {A : Sig} (h : Level.full.sig ⟶ A) (M : Model A) (φ : Spec) :
    M.Sat (Hom.sen h φ) ↔ (Hom.mod h M).Sat φ :=
  Hom.sat_sen_iff h M φ

end Silmaril.Cli.Info
