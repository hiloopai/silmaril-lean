module

public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# Transporting x86-TSO consistency along an embedding of candidate executions

A candidate execution `x'`
whose units are, up to renumbered positions, those of `x` plus some `lfence`/`sfence` units
(which no x86-TSO relation orders except through `mfence`'s `fencerel`) is x86-TSO-consistent
when `x` is. The data of the embedding (`Emb`):

* `e`: the unit of `x` a **real** unit of `x'` (not an `lfence`/`sfence`) stands for, with the
  same thread, direction, footprint, `locked` tag and data, and the same program order among
  the units of one thread;
* `σ`: the inverse, onto the real units;
* `rf` and `co` of `x'` are those of `x` read through `σ`, and every `rmw` pair of `x'` is one
  of `x`.

`tso_of_emb`: `x.Tso → x'.Tso`. The extra fence units only take part in `mfence` edges, and two
`mfence` edges compose to one (`mf_trans`), so a `ghb` cycle of `x'` shortens to a cycle through
real units (`ghb_path`), which maps to a cycle of `x`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec BRel before Act)
open Relation (TransGen)

/-- A unit that is not an `lfence`/`sfence` (every unit the store-buffer programs produce). -/
def realE (u : Ev) : Bool := !(u.isFence .lfence || u.isFence .sfence)

/-- **An embedding of `x'` into `x`** (see the module doc). -/
structure Emb (x x' : Exec) (e σ : Nat → Nat) : Prop where
  lt : ∀ a < x'.n, realE (x'.evN a) = true → e a < x.n
  tid : ∀ a < x'.n, realE (x'.evN a) = true → (x'.evN a).tid = (x.evN (e a)).tid
  act : ∀ a < x'.n, realE (x'.evN a) = true → (x'.evN a).act = (x.evN (e a)).act
  addr : ∀ a < x'.n, realE (x'.evN a) = true → (x'.evN a).addr = (x.evN (e a)).addr
  size : ∀ a < x'.n, realE (x'.evN a) = true → (x'.evN a).size = (x.evN (e a)).size
  locked : ∀ a < x'.n, realE (x'.evN a) = true → (x'.evN a).locked = (x.evN (e a)).locked
  data : ∀ a < x'.n, realE (x'.evN a) = true → (x'.evN a).data = (x.evN (e a)).data
  pos : ∀ a < x'.n, ∀ b < x'.n, realE (x'.evN a) = true → realE (x'.evN b) = true →
    (x'.evN a).tid = (x'.evN b).tid →
      ((x'.evN a).pos < (x'.evN b).pos ↔ (x.evN (e a)).pos < (x.evN (e b)).pos)
  uniq : ∀ a < x'.n, ∀ b < x'.n, (x'.evN a).tid = (x'.evN b).tid →
    (x'.evN a).pos = (x'.evN b).pos → a = b
  σlt : ∀ w < x.n, σ w < x'.n
  σreal : ∀ w < x.n, realE (x'.evN (σ w)) = true
  eσ : ∀ w < x.n, e (σ w) = w
  rf : ∀ r y, x'.rf r y = (x.rf (e r) y).map σ
  rfLt : ∀ r y w, x.rf r y = some w → w < x.n
  co : ∀ y, x'.co y = (x.co y).map σ
  coLt : ∀ y w, w ∈ x.co y → w < x.n
  rmw : ∀ a b, (a, b) ∈ x'.rmw → a < x'.n → b < x'.n → realE (x'.evN a) = true →
    realE (x'.evN b) = true → (e a, e b) ∈ x.rmw

theorem evN_eq (x : Exec) (a : Fin x.n) : x.evN a.val = x.ev a := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD, a.2]

theorem real_of_isM {u : Ev} (h : u.isM = true) : realE u = true := by
  cases u with
  | mk tid pos act addr size accAddr accSize locked ann data =>
    cases act with
    | read => rfl
    | write => rfl
    | fence k => simp [Ev.isM, Ev.isR, Ev.isW] at h

theorem real_of_mfence {u : Ev} (h : u.isFence .mfence = true) : realE u = true := by
  cases u with
  | mk tid pos act addr size accAddr accSize locked ann data =>
    simp only [Ev.isFence, beq_iff_eq] at h
    subst h; rfl

theorem real_of_isR {u : Ev} (h : u.isR = true) : realE u = true :=
  real_of_isM (by simp [Ev.isM, h])

theorem real_of_isW {u : Ev} (h : u.isW = true) : realE u = true :=
  real_of_isM (by simp [Ev.isM, h])

/-- `before` along a map: every pair ordered in the mapped list comes from a pair ordered in
the list. -/
theorem before_map {σ : Nat → Nat} :
    ∀ {l : List Nat} {a b : Nat}, before (l.map σ) a b = true →
      ∃ a₀ ∈ l, ∃ b₀ ∈ l, σ a₀ = a ∧ σ b₀ = b ∧ before l a₀ b₀ = true
  | [], _, _, h => by simp [before] at h
  | c :: l, a, b, h => by
    simp only [List.map_cons, before, beq_iff_eq] at h
    by_cases hc : σ c = a
    · simp only [hc, ite_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at h
      obtain ⟨b₀, hb₀, rfl⟩ := h
      refine ⟨c, List.mem_cons_self .., b₀, List.mem_cons_of_mem _ hb₀, hc, rfl, ?_⟩
      simp [before, hb₀]
    · simp only [hc, ite_false] at h
      obtain ⟨a₀, ha₀, b₀, hb₀, h1, h2, h3⟩ := before_map h
      refine ⟨a₀, List.mem_cons_of_mem _ ha₀, b₀, List.mem_cons_of_mem _ hb₀, h1, h2, ?_⟩
      have : c ≠ a₀ := fun h => hc (h ▸ h1)
      simp [before, this, h3]

/-- The unit of `x` a real unit of `x'` stands for. -/
def Emb.F {x x' : Exec} {e σ : Nat → Nat} (E : Emb x x' e σ) (a : Fin x'.n)
    (h : realE (x'.ev a) = true) : Fin x.n :=
  ⟨e a.val, E.lt a.val a.2 (by rw [evN_eq]; exact h)⟩

/-- The `ghb` edges of `x'` between real units, as edges of `x`. -/
def Emb.G {x x' : Exec} {e σ : Nat → Nat} (E : Emb x x' e σ) (a b : Fin x'.n) : Prop :=
  ∃ ha hb, x.ghb (E.F a ha) (E.F b hb) = true

theorem mf_trans (x : Exec) {a b c : Fin x.n} (h1 : x.mfence a b = true)
    (h2 : x.mfence b c = true) : x.mfence a c = true := by
  simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true] at h1 h2 ⊢
  obtain ⟨f, ⟨hf, hf1⟩, hf2⟩ := h1
  obtain ⟨g, ⟨-, hg1⟩, hg2⟩ := h2
  exact ⟨f, ⟨hf, hf1⟩, x.po_trans hf2 (x.po_trans hg1 hg2)⟩

theorem mf_irrefl (x : Exec) (a : Fin x.n) : x.mfence a a = false := by
  cases h : x.mfence a a
  · rfl
  · have := x.fencerel_po h
    rw [x.po_irrefl] at this; cases this

/-- `a = c` or an `mfence` edge. -/
def MfR (x : Exec) (a c : Fin x.n) : Prop := a = c ∨ x.mfence a c = true

theorem MfR.trans {x : Exec} {a b c : Fin x.n} (h1 : MfR x a b) (h2 : MfR x b c) : MfR x a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact .inr h1
    · exact .inr (mf_trans x h1 h2)

section emb
variable {x x' : Exec} {e σ : Nat → Nat} (E : Emb x x' e σ)
include E

theorem Emb.F_val (a : Fin x'.n) (h : realE (x'.ev a) = true) : (E.F a h).val = e a.val := rfl

theorem Emb.ev_tid (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).tid = (x.ev (E.F a h)).tid := by
  rw [← evN_eq, ← evN_eq]; exact E.tid a a.2 (by rw [evN_eq]; exact h)

theorem Emb.ev_act (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).act = (x.ev (E.F a h)).act := by
  rw [← evN_eq, ← evN_eq]; exact E.act a a.2 (by rw [evN_eq]; exact h)

theorem Emb.ev_addr (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).addr = (x.ev (E.F a h)).addr := by
  rw [← evN_eq, ← evN_eq]; exact E.addr a a.2 (by rw [evN_eq]; exact h)

theorem Emb.ev_size (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).size = (x.ev (E.F a h)).size := by
  rw [← evN_eq, ← evN_eq]; exact E.size a a.2 (by rw [evN_eq]; exact h)

theorem Emb.ev_locked (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).locked = (x.ev (E.F a h)).locked := by
  rw [← evN_eq, ← evN_eq]; exact E.locked a a.2 (by rw [evN_eq]; exact h)

theorem Emb.ev_isR (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).isR = (x.ev (E.F a h)).isR := by simp [Ev.isR, E.ev_act a h]

theorem Emb.ev_isW (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).isW = (x.ev (E.F a h)).isW := by simp [Ev.isW, E.ev_act a h]

theorem Emb.ev_isM (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).isM = (x.ev (E.F a h)).isM := by simp [Ev.isM, E.ev_isR a h, E.ev_isW a h]

theorem Emb.ev_isA (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).isA = (x.ev (E.F a h)).isA := by simp [Ev.isA, E.ev_isM a h, E.ev_locked a h]

theorem Emb.ev_isFence (a : Fin x'.n) (h : realE (x'.ev a) = true) (k) :
    (x'.ev a).isFence k = (x.ev (E.F a h)).isFence k := by simp [Ev.isFence, E.ev_act a h]

theorem Emb.ev_bytes (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).bytes = (x.ev (E.F a h)).bytes := by simp [Ev.bytes, E.ev_addr a h, E.ev_size a h]

theorem Emb.ev_covers (a : Fin x'.n) (h : realE (x'.ev a) = true) :
    (x'.ev a).covers = (x.ev (E.F a h)).covers := by
  funext y; simp [Ev.covers, E.ev_addr a h, E.ev_size a h]

theorem Emb.po (a b : Fin x'.n) (ha : realE (x'.ev a) = true) (hb : realE (x'.ev b) = true)
    (h : x'.po a b = true) : x.po (E.F a ha) (E.F b hb) = true := by
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  refine ⟨by rw [← E.ev_tid a ha, ← E.ev_tid b hb]; exact h.1, ?_⟩
  have := E.pos a a.2 b b.2 (by rw [evN_eq]; exact ha) (by rw [evN_eq]; exact hb)
    (by rw [evN_eq, evN_eq]; exact h.1)
  rw [evN_eq, evN_eq] at this
  have h2 := this.1 h.2
  rwa [← evN_eq x (E.F a ha), ← evN_eq x (E.F b hb)]

theorem Emb.sm_eq (a b : Fin x'.n) (h : x'.sm a b = true) : a = b := by
  simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq] at h
  exact Fin.ext (E.uniq a a.2 b b.2 (by rw [evN_eq, evN_eq]; exact h.1)
    (by rw [evN_eq, evN_eq]; exact h.2))

theorem Emb.ext (a b : Fin x'.n) (ha : realE (x'.ev a) = true) (hb : realE (x'.ev b) = true)
    (h : x'.ext a b = true) : x.ext (E.F a ha) (E.F b hb) = true := by
  simpa only [Exec.ext, E.ev_tid a ha, E.ev_tid b hb] using h

theorem Emb.loc (a b : Fin x'.n) (ha : realE (x'.ev a) = true) (hb : realE (x'.ev b) = true)
    (h : x'.loc a b = true) : x.loc (E.F a ha) (E.F b hb) = true := by
  simpa only [Exec.loc, E.ev_isM a ha, E.ev_isM b hb, E.ev_bytes a ha, E.ev_covers b hb] using h

theorem Emb.rf_of (r : Fin x'.n) (y w : Nat) (h : x'.rf r.val y = some w) :
    ∃ w₀, x.rf (e r.val) y = some w₀ ∧ σ w₀ = w ∧ w₀ < x.n := by
  rw [E.rf] at h
  obtain ⟨w₀, h1, h2⟩ := Option.map_eq_some_iff.1 h
  exact ⟨w₀, h1, h2, E.rfLt _ _ _ h1⟩

/-- `σ` is a two-sided inverse of `e` onto the real units. -/
theorem Emb.F_σ (w : Fin x'.n) (hw : realE (x'.ev w) = true) {w₀ : Nat} (h₀ : w₀ < x.n)
    (h : σ w₀ = w.val) : (E.F w hw).val = w₀ := by
  rw [E.F_val, ← h, E.eσ w₀ h₀]

theorem Emb.rfR (a b : Fin x'.n) (h : x'.rfR a b = true) :
    ∃ ha hb, x.rfR (E.F a ha) (E.F b hb) = true := by
  simp only [Exec.rfR, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hW, hR⟩, y, hy, hrf, hc⟩ := h
  have ha := real_of_isW hW
  have hb := real_of_isR hR
  refine ⟨ha, hb, ?_⟩
  obtain ⟨w₀, h1, h2, h3⟩ := E.rf_of b y a.val hrf
  simp only [Exec.rfR, Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
  refine ⟨⟨by rw [← E.ev_isW a ha]; exact hW, by rw [← E.ev_isR b hb]; exact hR⟩, y,
    by rw [← E.ev_bytes b hb]; exact hy, ?_, by rw [← E.ev_covers a ha]; exact hc⟩
  rw [E.F_val b hb, h1, E.F_σ a ha h3 h2]

theorem Emb.coR (a b : Fin x'.n) (h : x'.coR a b = true) :
    ∃ ha hb, x.coR (E.F a ha) (E.F b hb) = true := by
  simp only [Exec.coR, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨hW, hW'⟩, y, hy, hc, hbf⟩ := h
  have ha := real_of_isW hW
  have hb := real_of_isW hW'
  refine ⟨ha, hb, ?_⟩
  rw [E.co] at hbf
  obtain ⟨a₀, ha₀, b₀, hb₀, h1, h2, h3⟩ := before_map hbf
  simp only [Exec.coR, Bool.and_eq_true, List.any_eq_true]
  refine ⟨⟨by rw [← E.ev_isW a ha]; exact hW, by rw [← E.ev_isW b hb]; exact hW'⟩, y,
    by rw [← E.ev_bytes a ha]; exact hy, by rw [← E.ev_covers b hb]; exact hc, ?_⟩
  rw [E.F_σ a ha (E.coLt _ _ ha₀) h1, E.F_σ b hb (E.coLt _ _ hb₀) h2]
  exact h3

theorem Emb.frR (a b : Fin x'.n) (h : x'.frR a b = true) :
    ∃ ha hb, x.frR (E.F a ha) (E.F b hb) = true := by
  simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨hR, hW⟩, y, hy, hc, hm⟩ := h
  have ha := real_of_isR hR
  have hb := real_of_isW hW
  refine ⟨ha, hb, ?_⟩
  simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true]
  refine ⟨⟨by rw [← E.ev_isR a ha]; exact hR, by rw [← E.ev_isW b hb]; exact hW⟩, y,
    by rw [← E.ev_bytes a ha]; exact hy, by rw [← E.ev_covers b hb]; exact hc, ?_⟩
  rw [E.F_val a ha]
  rw [E.rf] at hm
  cases hv : x.rf (e a.val) y with
  | none => rfl
  | some v₀ =>
    rw [hv] at hm
    simp only [Option.map_some] at hm
    rw [E.co] at hm
    obtain ⟨a₀, ha₀, b₀, hb₀, h1, h2, h3⟩ := before_map hm
    have hv₀ := E.rfLt _ _ _ hv
    have : a₀ = v₀ := by
      have := congrArg e h1; rwa [E.eσ a₀ (E.coLt _ _ ha₀), E.eσ v₀ hv₀] at this
    subst this
    simp only
    rw [E.F_σ b hb (E.coLt _ _ hb₀) h2]
    exact h3

theorem Emb.com (a b : Fin x'.n) (h : x'.com a b = true) :
    ∃ ha hb, x.com (E.F a ha) (E.F b hb) = true := by
  simp only [Exec.com, BRel.union_iff] at h
  rcases h with h | h | h
  · obtain ⟨ha, hb, h⟩ := E.rfR a b h
    exact ⟨ha, hb, by simp [Exec.com, BRel.union, h]⟩
  · obtain ⟨ha, hb, h⟩ := E.coR a b h
    exact ⟨ha, hb, by simp [Exec.com, BRel.union, h]⟩
  · obtain ⟨ha, hb, h⟩ := E.frR a b h
    exact ⟨ha, hb, by simp [Exec.com, BRel.union, h]⟩

theorem Emb.comSm (a b : Fin x'.n) (h : (x'.com.seq x'.sm) a b = true) :
    ∃ ha hb, (x.com.seq x.sm) (E.F a ha) (E.F b hb) = true := by
  obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
  have := E.sm_eq c b h2
  subst this
  obtain ⟨ha, hb, h⟩ := E.com a c h1
  exact ⟨ha, hb, BRel.seq_of_left (fun a => x.sm_refl a) h⟩

theorem Emb.uniproc (a b : Fin x'.n) (h : x'.uniproc a b = true) :
    ∃ ha hb, x.uniproc (E.F a ha) (E.F b hb) = true := by
  simp only [Exec.uniproc, BRel.union_iff] at h
  rcases h with h | h
  · rw [Exec.poLoc, BRel.inter_iff] at h
    have hl := h.2
    simp only [Exec.loc, Bool.and_eq_true] at hl
    have ha := real_of_isM hl.1.1
    have hb := real_of_isM hl.1.2
    exact ⟨ha, hb, by
      simp only [Exec.uniproc, BRel.union_iff, Exec.poLoc, BRel.inter_iff]
      exact .inl ⟨E.po a b ha hb h.1, E.loc a b ha hb h.2⟩⟩
  · obtain ⟨ha, hb, h⟩ := E.comSm a b h
    exact ⟨ha, hb, by simp only [Exec.uniproc, BRel.union_iff]; exact .inr h⟩

theorem Emb.mf_of (a b : Fin x'.n) (ha : realE (x'.ev a) = true) (hb : realE (x'.ev b) = true)
    (h : x'.mfence a b = true) : E.G a b := by
  simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true] at h
  obtain ⟨f, ⟨hf, h1⟩, h2⟩ := h
  have hfr := real_of_mfence hf
  refine ⟨ha, hb, ?_⟩
  simp only [Exec.ghb, BRel.union_iff]
  left
  simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true]
  exact ⟨E.F f hfr, ⟨by rw [← E.ev_isFence f hfr]; exact hf, E.po a f ha hfr h1⟩,
    E.po f b hfr hb h2⟩

/-- Every `ghb` edge of `x'` is an `mfence` edge or an edge between real units. -/
theorem Emb.ghb_cases (a b : Fin x'.n) (h : x'.ghb a b = true) : x'.mfence a b = true ∨ E.G a b := by
  simp only [Exec.ghb, BRel.union_iff] at h
  rcases h with h | h | h | h
  · exact .inl h
  · right
    simp only [Exec.implied, Bool.and_eq_true] at h
    have ha := real_of_isW h.1.1.2
    have hb := real_of_isR h.1.2
    refine ⟨ha, hb, ?_⟩
    simp only [Exec.ghb, BRel.union_iff]
    right; left
    simp only [Exec.implied, Bool.and_eq_true]
    exact ⟨⟨⟨E.po a b ha hb h.1.1.1, by rw [← E.ev_isW a ha]; exact h.1.1.2⟩,
      by rw [← E.ev_isR b hb]; exact h.1.2⟩, by rw [← E.ev_isA a ha, ← E.ev_isA b hb]; exact h.2⟩
  · right
    simp only [Exec.ppo, Bool.and_eq_true, Bool.or_eq_true] at h
    have hab : realE (x'.ev a) = true ∧ realE (x'.ev b) = true := by
      rcases h.2 with h2 | h2
      · exact ⟨real_of_isW h2.1, real_of_isW h2.2⟩
      · exact ⟨real_of_isR h2.1, real_of_isM h2.2⟩
    refine ⟨hab.1, hab.2, ?_⟩
    simp only [Exec.ghb, BRel.union_iff]
    right; right; left
    simp only [Exec.ppo, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨E.po a b hab.1 hab.2 h.1, ?_⟩
    rw [← E.ev_isW a hab.1, ← E.ev_isW b hab.2, ← E.ev_isR a hab.1, ← E.ev_isM b hab.2]
    exact h.2
  · right
    obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
    have := E.sm_eq c b h2
    subst this
    simp only [BRel.union_iff] at h1
    have key : ∃ ha hc, (x.rfe.union (x.frR.union x.coR)) (E.F a ha) (E.F c hc) = true := by
      rcases h1 with h1 | h1 | h1
      · rw [Exec.rfe, BRel.inter_iff] at h1
        obtain ⟨ha, hc, h⟩ := E.rfR a c h1.1
        exact ⟨ha, hc, by
          simp only [BRel.union_iff, Exec.rfe, BRel.inter_iff]
          exact .inl ⟨h, E.ext a c ha hc h1.2⟩⟩
      · obtain ⟨ha, hc, h⟩ := E.frR a c h1
        exact ⟨ha, hc, by simp only [BRel.union_iff]; exact .inr (.inl h)⟩
      · obtain ⟨ha, hc, h⟩ := E.coR a c h1
        exact ⟨ha, hc, by simp only [BRel.union_iff]; exact .inr (.inr h)⟩
    obtain ⟨ha, hc, h⟩ := key
    refine ⟨ha, hc, ?_⟩
    simp only [Exec.ghb, BRel.union_iff]
    right; right; right
    exact BRel.seq_of_left (fun a => x.sm_refl a) h

theorem Emb.G_real {a b : Fin x'.n} (h : TransGen E.G a b) :
    realE (x'.ev a) = true ∧ realE (x'.ev b) = true := by
  induction h with
  | single h => exact ⟨h.1, h.2.1⟩
  | tail _ h ih => exact ⟨ih.1, h.2.1⟩

theorem Emb.G_lift {a b : Fin x'.n} (h : TransGen E.G a b) (ha : realE (x'.ev a) = true)
    (hb : realE (x'.ev b) = true) : TransGen x.ghb.Holds (E.F a ha) (E.F b hb) := by
  induction h with
  | single h => exact .single h.2.2
  | tail h₁ h ih => exact (ih (E.G_real h₁).2).tail h.2.2

/-- **A `ghb` path of `x'`** is an `mfence` edge, or real edges between `mfence` edges. -/
theorem Emb.ghb_path {a b : Fin x'.n} (h : TransGen x'.ghb.Holds a b) :
    x'.mfence a b = true ∨ ∃ c d, MfR x' a c ∧ TransGen E.G c d ∧ MfR x' d b := by
  induction h with
  | single h =>
    rcases E.ghb_cases _ _ h with h | h
    · exact .inl h
    · exact .inr ⟨_, _, .inl rfl, .single h, .inl rfl⟩
  | tail _ h ih =>
    rename_i b c _
    rcases E.ghb_cases _ _ h with h | h
    · rcases ih with ih | ⟨c', d, h1, h2, h3⟩
      · exact .inl (mf_trans x' ih h)
      · exact .inr ⟨c', d, h1, h2, h3.trans (.inr h)⟩
    · rcases ih with ih | ⟨c', d, h1, h2, h3⟩
      · exact .inr ⟨b, c, .inr ih, .single h, .inl rfl⟩
      · rcases h3 with rfl | h3
        · exact .inr ⟨c', c, h1, h2.tail h, .inl rfl⟩
        · have hd := (E.G_real h2).2
          exact .inr ⟨c', c, h1, (h2.tail (E.mf_of _ _ hd h.1 h3)).tail h, .inl rfl⟩

theorem Emb.ghb_acyclic (h : BRel.Acyclic x.ghb) : BRel.Acyclic x'.ghb := by
  intro a ha
  rcases E.ghb_path ha with h1 | ⟨c, d, h1, h2, h3⟩
  · rw [mf_irrefl] at h1; cases h1
  · have hcd := E.G_real h2
    have hdc : TransGen E.G c c := by
      rcases h3.trans h1 with heq | hm
      · rw [heq] at h2; exact h2
      · exact h2.tail (E.mf_of _ _ hcd.2 hcd.1 hm)
    exact h _ (E.G_lift hdc hcd.1 hcd.1)

theorem Emb.uniproc_acyclic (h : BRel.Acyclic x.uniproc) : BRel.Acyclic x'.uniproc := by
  intro a ha
  have key : ∀ b c, TransGen x'.uniproc.Holds b c →
      ∃ hb hc, TransGen x.uniproc.Holds (E.F b hb) (E.F c hc) := by
    intro b c hbc
    induction hbc with
    | single h' =>
      obtain ⟨hb, hc, h'⟩ := E.uniproc _ _ h'
      exact ⟨hb, hc, .single h'⟩
    | tail _ h' ih =>
      obtain ⟨hb, _, ih2⟩ := ih
      obtain ⟨_, hc, h2⟩ := E.uniproc _ _ h'
      exact ⟨hb, hc, TransGen.tail ih2 h2⟩
  obtain ⟨h1, h2, h3⟩ := key a a ha
  exact h _ h3

theorem Emb.atomic (h : x.atomicB = true) : x'.atomicB = true := by
  rw [Exec.atomicB, BRel.emptyB_iff] at h ⊢
  intro a b
  cases hab : (x'.rmwR.inter (x'.fre.seq x'.coe)) a b
  · rfl
  · exfalso
    rw [BRel.inter_iff] at hab
    obtain ⟨c, h1, h2⟩ := BRel.seq_elim hab.2
    rw [Exec.fre, BRel.inter_iff] at h1
    rw [Exec.coe, BRel.inter_iff] at h2
    obtain ⟨ha, hc, hf⟩ := E.frR a c h1.1
    obtain ⟨hc', hb, hco⟩ := E.coR c b h2.1
    have hr : x.rmwR (E.F a ha) (E.F b hb) = true := by
      have := hab.1
      simp only [Exec.rmwR, List.contains_eq_mem, decide_eq_true_eq] at this ⊢
      exact E.rmw _ _ this a.2 b.2 (by rw [evN_eq]; exact ha) (by rw [evN_eq]; exact hb)
    have := h (E.F a ha) (E.F b hb)
    rw [BRel.inter_iff.2 ⟨hr, BRel.seq_mono (r := x.fre) (s := x.coe) (fun _ _ h => h)
      (fun _ _ h => h) ?_⟩] at this
    · cases this
    · simp only [BRel.seq, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
      exact ⟨E.F c hc, by rw [Exec.fre, BRel.inter_iff]; exact ⟨hf, E.ext a c ha hc h1.2⟩,
        by rw [Exec.coe, BRel.inter_iff]; exact ⟨hco, E.ext c b hc hb h2.2⟩⟩

/-- **x86-TSO consistency transports along an embedding.** -/
theorem tso_of_emb (h : x.Tso) : x'.Tso :=
  ⟨E.atomic h.1, E.uniproc_acyclic h.2.1, E.ghb_acyclic h.2.2⟩

end emb

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun
