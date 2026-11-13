module

public import Silmaril.X86.MemoryModel.Lattice.Defs
public import Silmaril.X86.MemoryModel.Xl.Thms

/-!
# A lattice of x86 memory models: proofs of the edges and of DRF-SC

* `reach_sound`, `reach_complete`: the Boolean reachability of `Lattice.Defs`;
* `path`: under x86-TSO, a `(po ∪ rf ∪ lockCom)⁺` path from a memory unit is a `po` edge, or a
  `ghb` path to a read or locked unit followed by at most one `po` edge. The `po` edges inside
  the path all start at a read or a locked unit, or end at a write or a locked unit, so they are
  `ppo` or `implied`; only a leading plain write → plain read `po` edge escapes `ghb`;
* `syncL_acyclic`: x86-TSO makes `hbL` acyclic;
* `ra_of_tso`: x86-TSO executions are release/acquire;
* `sc_of_hb`: the DRF-SC skeleton: if a transitive, irreflexive `H` contains `po` and every
  external communication edge, an unsplit execution with uniproc and atomicity is SC;
* `cf_of_tso` (DRF-SC for x86-TSO, locked accesses synchronising) and `cfPlain_of_ra`
  (DRF-SC for release/acquire).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic.Proofs.Lattice

open Silmaril.X86.MemoryModel.Axiomatic
open Relation

/-! ## Generic facts -/

section Generic
variable {n : Nat}

theorem reachK_sound (r : BRel n) (a : Fin n) :
    ∀ k b, BRel.reachK r a k b = true → TransGen r.Holds a b
  | 0, _, h => .single h
  | k + 1, b, h => by
    simp only [BRel.reachK, BRel.stepSet, Bool.or_eq_true, List.any_eq_true,
      Bool.and_eq_true] at h
    rcases h with h | ⟨c, -, hc, hcb⟩
    · exact reachK_sound r a k b h
    · exact .tail (reachK_sound r a k c hc) hcb

theorem reach_sound (r : BRel n) {a b : Fin n} (h : BRel.reach r a b = true) :
    TransGen r.Holds a b := reachK_sound r a n b h

theorem reachK_base (r : BRel n) (a : Fin n) :
    ∀ k d, r a d = true → BRel.reachK r a k d = true
  | 0, _, h => h
  | k + 1, d, h => by
    simp only [BRel.reachK, BRel.stepSet, Bool.or_eq_true]
    exact .inl (reachK_base r a k d h)

theorem closedB_iff (r : BRel n) (S : Fin n → Bool) :
    BRel.closedB r S = true ↔ ∀ c d, S c = true → r c d = true → S d = true := by
  simp only [BRel.closedB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff]
  constructor
  · intro h c d hc hr
    rcases h c d with (h | h) | h
    · simp [hc] at h
    · simp [hr] at h
    · exact h
  · intro h c d
    by_cases hc : S c = true
    · by_cases hr : r c d = true
      · exact .inr (h c d hc hr)
      · exact .inl (.inr (by simpa using hr))
    · exact .inl (.inl (by simpa using hc))

theorem tg_of_closed (r : BRel n) (S : Fin n → Bool)
    (hS : ∀ c d, S c = true → r c d = true → S d = true) {a b : Fin n}
    (ha : ∀ d, r a d = true → S d = true) (h : TransGen r.Holds a b) : S b = true := by
  induction h with
  | single h => exact ha _ h
  | tail _ h ih => exact hS _ _ ih h

theorem reach_complete (r : BRel n) (hc : BRel.reachClosedB r = true) {a b : Fin n}
    (h : TransGen r.Holds a b) : BRel.reach r a b = true := by
  simp only [BRel.reachClosedB, List.all_eq_true, List.mem_finRange, true_implies] at hc
  exact tg_of_closed r _ ((closedB_iff r _).mp (hc a)) (fun d hd => reachK_base r a n d hd) h

theorem reach_iff (r : BRel n) (hc : BRel.reachClosedB r = true) {a b : Fin n} :
    BRel.reach r a b = true ↔ TransGen r.Holds a b :=
  ⟨reach_sound r, reach_complete r hc⟩

/-- A path either stays inside `q` or passes through a node satisfying `P`. -/
theorem path_point {r q : Fin n → Fin n → Prop} {P : Fin n → Prop}
    (qt : ∀ a b c, q a b → q b c → q a c) (hr : ∀ a b, r a b → P b ∨ q a b) {s e : Fin n}
    (h : TransGen r s e) :
    q s e ∨ ∃ m, P m ∧ ReflTransGen r s m ∧ ReflTransGen r m e := by
  induction h with
  | single h =>
    rcases hr _ _ h with hp | hq
    · exact .inr ⟨_, hp, .single h, .refl⟩
    · exact .inl hq
  | tail hsc hce ih =>
    rcases hr _ _ hce with hp | hq
    · exact .inr ⟨_, hp, hsc.to_reflTransGen.tail hce, .refl⟩
    · rcases ih with ih | ⟨m, hm, h1, h2⟩
      · exact .inl (qt _ _ _ ih hq)
      · exact .inr ⟨m, hm, h1, h2.tail hce⟩

/-- A cycle that is not a `q` cycle passes through a node satisfying `P`. -/
theorem cycle_point {r q : Fin n → Fin n → Prop} {P : Fin n → Prop}
    (qt : ∀ a b c, q a b → q b c → q a c) (qi : ∀ a, ¬ q a a)
    (hr : ∀ a b, r a b → P b ∨ q a b) {a : Fin n} (h : TransGen r a a) :
    ∃ m, P m ∧ TransGen r m m := by
  rcases path_point qt hr h with hq | ⟨m, hm, h1, h2⟩
  · exact absurd hq (qi a)
  · exact ⟨m, hm, TransGen.trans_right h2 (TransGen.trans_left h h1)⟩

end Generic

/-! ## Facts about one execution -/

section Exec
variable (x : Exec)

theorem not_R_and_W (e : Ev) (hr : e.isR = true) (hw : e.isW = true) : False := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at hr hw
  rw [hr] at hw
  cases hw

theorem isA_isM {e : Ev} (h : e.isA = true) : e.isM = true := by
  simp only [Ev.isA, Bool.and_eq_true] at h
  exact h.2

theorem isR_isM {e : Ev} (h : e.isR = true) : e.isM = true := by
  simp [Ev.isM, h]

theorem isW_isM {e : Ev} (h : e.isW = true) : e.isM = true := by
  simp [Ev.isM, h]

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.covers y = true := by
  simp [Ev.bytes, Ev.covers, List.mem_range'_1]

/-- The endpoints of a communication edge share a byte. -/
theorem com_share {a b : Fin x.n} (h : x.com a b = true) :
    ∃ y, (x.ev a).covers y = true ∧ (x.ev b).covers y = true := by
  simp only [Exec.com, BRel.union_iff] at h
  rcases h with h | h | h
  · simp only [Exec.rfR, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨-, y, hy, -, hc⟩ := h
    exact ⟨y, hc, mem_bytes.mp hy⟩
  · simp only [Exec.coR, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨-, y, hy, hc, -⟩ := h
    exact ⟨y, mem_bytes.mp hy, hc⟩
  · simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨-, y, hy, hc, -⟩ := h
    exact ⟨y, mem_bytes.mp hy, hc⟩

theorem com_kinds {a b : Fin x.n} (h : x.com a b = true) :
    (x.ev a).isM = true ∧ (x.ev b).isM = true ∧ ((x.ev a).isW = true ∨ (x.ev b).isW = true) := by
  simp only [Exec.com, BRel.union_iff] at h
  rcases h with h | h | h
  · simp only [Exec.rfR, Bool.and_eq_true] at h
    exact ⟨isW_isM h.1.1, isR_isM h.1.2, .inl h.1.1⟩
  · simp only [Exec.coR, Bool.and_eq_true] at h
    exact ⟨isW_isM h.1.1, isW_isM h.1.2, .inl h.1.1⟩
  · simp only [Exec.frR, Bool.and_eq_true] at h
    exact ⟨isR_isM h.1.1, isW_isM h.1.2, .inr h.1.2⟩

theorem com_loc {a b : Fin x.n} (h : x.com a b = true) : x.loc a b = true ∧ x.loc b a = true := by
  obtain ⟨y, ha, hb⟩ := com_share x h
  obtain ⟨ma, mb, -⟩ := com_kinds x h
  simp only [Exec.loc, ma, mb, Bool.and_self, Bool.true_and, List.any_eq_true]
  exact ⟨⟨y, mem_bytes.mpr ha, hb⟩, ⟨y, mem_bytes.mpr hb, ha⟩⟩

theorem com_conflict {a b : Fin x.n} (h : x.com a b = true) (he : x.ext a b = true) :
    x.conflict a b = true := by
  obtain ⟨-, -, hw⟩ := com_kinds x h
  simp only [Exec.conflict, he, (com_loc x h).1, Bool.true_and, Bool.or_eq_true]
  exact hw

theorem ext_not_po {a b : Fin x.n} (he : x.ext a b = true) : x.po a b = false := by
  simp only [Exec.ext, bne_iff_ne, ne_eq] at he
  simp [Exec.po, he]

theorem ext_symm {a b : Fin x.n} (he : x.ext a b = true) : x.ext b a = true := by
  simp only [Exec.ext, bne_iff_ne, ne_eq] at he ⊢
  exact fun h => he h.symm

theorem not_ext_tid {a b : Fin x.n} (he : x.ext a b = false) : (x.ev a).tid = (x.ev b).tid := by
  simpa [Exec.ext] using he

theorem thinAir_syncL {a b : Fin x.n} (h : x.thinAir a b = true) : x.syncL a b = true :=
  BRel.union_iff.mpr (.inl h)

theorem po_thinAir {a b : Fin x.n} (h : x.po a b = true) : x.thinAir a b = true :=
  BRel.union_iff.mpr (.inl h)

theorem hb_hbL {a b : Fin x.n} (h : x.Hb a b) : x.HbL a b := by
  induction h with
  | single h => exact .single (thinAir_syncL x h)
  | tail _ h ih => exact .tail ih (thinAir_syncL x h)

/-! ### Uniproc -/

theorem uni_com {a b : Fin x.n} (h : x.com a b = true) :
    x.uniproc a b = true :=
  BRel.union_iff.mpr (.inr (BRel.seq_of_left x.sm_refl h))

/-- Uniproc forbids a communication edge against `po` on a shared location. -/
theorem uni_po_com (hu : BRel.Acyclic x.uniproc) {a b : Fin x.n} (hpo : x.po a b = true)
    (h : x.com b a = true) : False := by
  have hl : x.poLoc a b = true := BRel.inter_iff.mpr ⟨hpo, (com_loc x h).2⟩
  exact hu a (.tail (.single (BRel.union_iff.mpr (.inl hl))) (uni_com x h))

/-- Uniproc forbids a communication edge between units of the same access. -/
theorem uni_sm_com (hu : BRel.Acyclic x.uniproc) {a b : Fin x.n} (hs : x.sm b a = true)
    (h : x.com a b = true) : False := by
  apply hu a
  refine .single (BRel.union_iff.mpr (.inr ?_))
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
  exact ⟨b, List.mem_finRange b, h, hs⟩

/-- Units of one thread: `po` one way or the other, or the same access. -/
theorem same_tid_cases {a b : Fin x.n} (he : x.ext a b = false) :
    x.po a b = true ∨ x.sm a b = true ∨ x.po b a = true := by
  have ht := not_ext_tid x he
  rcases Nat.lt_trichotomy (x.ev a).pos (x.ev b).pos with h | h | h
  · exact .inl (by simp [Exec.po, ht, h])
  · exact .inr (.inl (by simp [Exec.sm, ht, h]))
  · exact .inr (.inr (by simp [Exec.po, ht, h]))

theorem sm_symm {a b : Fin x.n} (h : x.sm a b = true) : x.sm b a = true := by
  simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

/-- Under uniproc, a reads-from edge is external or goes forward in program order. -/
theorem rf_po_or_ext (hu : BRel.Acyclic x.uniproc) {a b : Fin x.n} (h : x.rfR a b = true) :
    x.po a b = true ∨ x.ext a b = true := by
  have hc : x.com a b = true := BRel.union_iff.mpr (.inl h)
  by_cases he : x.ext a b = true
  · exact .inr he
  · rcases same_tid_cases x (by simpa using he) with h1 | h1 | h1
    · exact .inl h1
    · exact (uni_sm_com x hu (sm_symm x h1) hc).elim
    · exact (uni_po_com x hu h1 hc).elim

/-! ### TSO's global order -/

theorem ppo_ghb {a b : Fin x.n} (h : x.ppo a b = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inr (.inr (.inl h))

/-- An external communication edge, and any `fr` or `co` edge, is a `ghb` edge. -/
theorem com_ghb {a b : Fin x.n} (h : x.com a b = true)
    (he : x.ext a b = true ∨ x.rfR a b = false) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  refine .inr (.inr (.inr (BRel.seq_of_left x.sm_refl ?_)))
  simp only [Exec.com, BRel.union_iff] at h
  simp only [BRel.union_iff]
  rcases h with h | h | h
  · rcases he with he | he
    · exact .inl (BRel.inter_iff.mpr ⟨h, he⟩)
    · simp [h] at he
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- A `po` edge between memory units is in `ghb` unless it goes from a plain write to a plain
read. -/
theorem po_ghb {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.ev a).isM = true)
    (hb : (x.ev b).isM = true)
    (hk : (x.ev a).isR = true ∨ (x.ev b).isW = true ∨ (x.ev a).isA = true ∨ (x.ev b).isA = true) :
    x.ghb a b = true := by
  by_cases hr : (x.ev a).isR = true
  · exact ppo_ghb x (by simp [Exec.ppo, hpo, hr, hb])
  · have haw : (x.ev a).isW = true := by
      simp only [Ev.isM, Bool.or_eq_true] at ha
      exact ha.resolve_left hr
    by_cases hw : (x.ev b).isW = true
    · exact ppo_ghb x (by simp [Exec.ppo, hpo, haw, hw])
    · have hbr : (x.ev b).isR = true := by
        simp only [Ev.isM, Bool.or_eq_true] at hb
        exact hb.resolve_right hw
      have hl : (x.ev a).isA = true ∨ (x.ev b).isA = true := by
        rcases hk with h | h | h
        · exact absurd h hr
        · exact absurd h hw
        · exact h
      simp only [Exec.ghb, BRel.union_iff]
      refine .inr (.inl ?_)
      simp only [Exec.implied, hpo, haw, hbr, Bool.and_self, Bool.true_and, Bool.or_eq_true]
      exact hl

/-- A cross edge of `hbL`: an external `rf` or a `lockCom` edge. -/
abbrev Cross (a b : Fin x.n) : Prop :=
  x.ghb a b = true ∧ (x.ev a).isM = true ∧ ((x.ev a).isW = true ∨ (x.ev a).isA = true) ∧
    ((x.ev b).isR = true ∨ (x.ev b).isA = true)

theorem syncL_cases (hu : BRel.Acyclic x.uniproc) {a b : Fin x.n} (h : x.syncL a b = true) :
    x.po a b = true ∨ Cross x a b := by
  simp only [Exec.syncL, Exec.thinAir, BRel.union_iff] at h
  rcases h with (h | h) | h
  · exact .inl h
  · rcases rf_po_or_ext x hu h with h1 | he
    · exact .inl h1
    · have hk : (x.ev a).isW = true ∧ (x.ev b).isR = true := by
        simp only [Exec.rfR, Bool.and_eq_true] at h
        exact h.1
      exact .inr ⟨com_ghb x (BRel.union_iff.mpr (.inl h)) (.inl he), isW_isM hk.1, .inl hk.1,
        .inl hk.2⟩
  · simp only [Exec.lockCom, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, he⟩, ha⟩, hb⟩ := h
    exact .inr ⟨com_ghb x hc (.inl he), isA_isM ha, .inr ha, .inr hb⟩

/-- **Paths of `hbL` under x86-TSO.** -/
theorem path (hu : BRel.Acyclic x.uniproc) {s e : Fin x.n} (hs : (x.ev s).isM = true)
    (h : TransGen x.syncL.Holds s e) :
    x.po s e = true ∨ ∃ r, TransGen x.ghb.Holds s r ∧
      ((x.ev r).isR = true ∨ (x.ev r).isA = true) ∧ (r = e ∨ x.po r e = true) := by
  induction h with
  | single h =>
    rcases syncL_cases x hu h with h | ⟨hg, -, -, hk⟩
    · exact .inl h
    · exact .inr ⟨_, .single hg, hk, .inl rfl⟩
  | @tail c d _ hcd ih =>
    rcases syncL_cases x hu hcd with hpo | ⟨hg, hcM, hcW, hk⟩
    · rcases ih with ih | ⟨r, h1, h2, h3⟩
      · exact .inl (x.po_trans ih hpo)
      · refine .inr ⟨r, h1, h2, .inr ?_⟩
        rcases h3 with rfl | h3
        · exact hpo
        · exact x.po_trans h3 hpo
    · rcases ih with ih | ⟨r, h1, h2, h3⟩
      · have : x.ghb s c = true := po_ghb x ih hs hcM (by
          rcases hcW with h | h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inr h)))
        exact .inr ⟨d, .tail (.single this) hg, hk, .inl rfl⟩
      · rcases h3 with rfl | h3
        · exact .inr ⟨d, .tail h1 hg, hk, .inl rfl⟩
        · have hrM : (x.ev r).isM = true := by
            rcases h2 with h | h
            · exact isR_isM h
            · exact isA_isM h
          have : x.ghb r c = true := po_ghb x h3 hrM hcM (by
            rcases h2 with h | h
            · exact .inl h
            · exact .inr (.inr (.inl h)))
          exact .inr ⟨d, .tail (.tail h1 this) hg, hk, .inl rfl⟩

/-- Between memory units, an `hbL` path is a `po` edge or a `ghb` path. -/
theorem path_ghb (hu : BRel.Acyclic x.uniproc) {s e : Fin x.n} (hs : (x.ev s).isM = true)
    (he : (x.ev e).isM = true) (h : TransGen x.syncL.Holds s e) :
    x.po s e = true ∨ TransGen x.ghb.Holds s e := by
  rcases path x hu hs h with h | ⟨r, h1, h2, h3⟩
  · exact .inl h
  · rcases h3 with rfl | h3
    · exact .inr h1
    · have hrM : (x.ev r).isM = true := by
        rcases h2 with h | h
        · exact isR_isM h
        · exact isA_isM h
      refine .inr (.tail h1 (po_ghb x h3 hrM he ?_))
      rcases h2 with h | h
      · exact .inl h
      · exact .inr (.inr (.inl h))

/-- **x86-TSO makes `hbL` acyclic.** -/
theorem syncL_acyclic (h : x.Tso) (a : Fin x.n) : ¬ x.HbL a a := by
  intro hc
  have hstep : ∀ c d, x.syncL.Holds c d → (x.ev d).isM = true ∨ x.po c d = true := by
    intro c d hcd
    rcases syncL_cases x h.2.1 hcd with hpo | ⟨-, -, -, hk⟩
    · exact .inr hpo
    · rcases hk with hk | hk
      · exact .inl (isR_isM hk)
      · exact .inl (isA_isM hk)
  obtain ⟨m, hm, hmm⟩ := cycle_point (q := fun c d => x.po c d = true)
    (fun _ _ _ h1 h2 => x.po_trans h1 h2) (fun a h => by simp [x.po_irrefl a] at h) hstep hc
  rcases path_ghb x h.2.1 hm hm hmm with hp | hg
  · simp [x.po_irrefl m] at hp
  · exact h.2.2 m hg

/-! ## TSO is release/acquire -/

theorem ra_of_tso (h : x.Tso) : x.Ra := by
  refine ⟨h.1, h.2.1, x.thinAir_of_tso h, ?_⟩
  intro a b hab
  by_contra hc
  have hc : x.com b a = true := by simpa using hc
  have hu := h.2.1
  obtain ⟨hbM, haM, -⟩ := com_kinds x hc
  have hL := hb_hbL x hab
  -- a ghb path from a to b, closed by the communication edge
  have close : TransGen x.ghb.Holds a b → x.ghb b a = true → False :=
    fun h1 h2 => h.2.2 a (.tail h1 h2)
  rcases path x hu haM hL with hpo | ⟨r, h1, h2, h3⟩
  · exact uni_po_com x hu hpo hc
  · have hrM : (x.ev r).isM = true := by
      rcases h2 with h | h
      · exact isR_isM h
      · exact isA_isM h
    have hrk : (x.ev r).isR = true ∨ (x.ev a).isW = true ∨ (x.ev r).isA = true ∨
        (x.ev a).isA = true := by
      rcases h2 with h | h
      · exact .inl h
      · exact .inr (.inr (.inl h))
    by_cases he : x.ext b a = true
    · rcases path_ghb x hu haM hbM hL with hp | hg
      · simp [ext_not_po x (ext_symm x he)] at hp
      · exact close hg (com_ghb x hc (.inl he))
    · rcases same_tid_cases x (a := b) (b := a) (by simpa using he) with hba | hs | hab'
      · -- po b a: a ghb edge from r (or something before b) to a
        rcases h3 with rfl | h3
        · exact h.2.2 a (.tail h1 (po_ghb x hba hrM haM hrk))
        · exact h.2.2 a (.tail h1 (po_ghb x (x.po_trans h3 hba) hrM haM hrk))
      · exact uni_sm_com x hu (sm_symm x hs) hc |>.elim
      · exact uni_po_com x hu hab' hc

/-! ## The DRF-SC skeleton -/

theorem sc_of_hb (H : Fin x.n → Fin x.n → Prop) (Ht : ∀ a b c, H a b → H b c → H a c)
    (Hi : ∀ a, ¬ H a a) (Hpo : ∀ a b, x.po a b = true → H a b) (hat : x.atomicB = true)
    (hu : BRel.Acyclic x.uniproc) (hus : x.Unsplit)
    (hcom : ∀ a b, x.com a b = true → x.ext a b = true → H a b) : x.Sc := by
  refine ⟨hat, ?_⟩
  have edge : ∀ a b, x.scRel a b = true → H a b := by
    intro a b hab
    simp only [Exec.scRel, BRel.union_iff] at hab
    rcases hab with hab | hab
    · exact Hpo a b hab
    · obtain ⟨c, hac, hcb⟩ := BRel.seq_elim hab
      obtain rfl := hus c b hcb
      by_cases he : x.ext a c = true
      · exact hcom a c hac he
      · rcases same_tid_cases x (by simpa using he) with h | h | h
        · exact Hpo a c h
        · exact (uni_sm_com x hu (sm_symm x h) hac).elim
        · exact (uni_po_com x hu h hac).elim
  intro a hc
  have : ∀ b, TransGen x.scRel.Holds a b → H a b := by
    intro b h
    induction h with
    | single h => exact edge _ _ h
    | tail _ h ih => exact Ht _ _ _ ih (edge _ _ h)
  exact Hi a (this a hc)

/-! ## DRF-SC -/

/-- **DRF-SC for x86-TSO, locked accesses synchronising.** -/
theorem cf_of_tso (h : x.Tso) : x.Cf := by
  intro hus hdrf
  have hu := h.2.1
  refine sc_of_hb x x.HbL (fun _ _ _ h1 h2 => TransGen.trans h1 h2) (syncL_acyclic x h)
    (fun a b hab => .single (thinAir_syncL x (po_thinAir x hab))) h.1 hu hus ?_
  intro a b hc he
  obtain ⟨haM, hbM, -⟩ := com_kinds x hc
  by_cases hA : ((x.ev a).isA && (x.ev b).isA) = true
  · simp only [Bool.and_eq_true] at hA
    refine .single (BRel.union_iff.mpr (.inr ?_))
    simp [Exec.lockCom, hc, he, hA.1, hA.2]
  · rcases hdrf a b (com_conflict x hc he) (by simpa using hA) with h1 | h1
    · exact h1
    · rcases path_ghb x hu hbM haM h1 with hp | hg
      · simp [ext_not_po x (ext_symm x he)] at hp
      · exact (h.2.2 b (.tail hg (com_ghb x hc (.inl he)))).elim

/-- **DRF-SC for release/acquire.** -/
theorem cfPlain_of_ra (h : x.Ra) : x.CfPlain := by
  intro hus hdrf
  obtain ⟨hat, hu, hta, hcoh⟩ := h
  refine sc_of_hb x x.Hb (fun _ _ _ h1 h2 => TransGen.trans h1 h2) hta
    (fun a b hab => .single (po_thinAir x hab)) hat hu hus ?_
  intro a b hc he
  rcases hdrf a b (com_conflict x hc he) with h1 | h1
  · exact h1
  · simp [hcoh b a h1] at hc

theorem drfL_of_drf (h : x.Drf) : x.DrfL := by
  intro a b hc _
  rcases h a b hc with h1 | h1
  · exact .inl (hb_hbL x h1)
  · exact .inr (hb_hbL x h1)

theorem cfPlain_of_cf (h : x.Cf) : x.CfPlain := fun hus hd => h hus (drfL_of_drf x hd)

/-! ## Boolean checks -/

theorem unsplitB_iff : x.unsplitB = true ↔ x.Unsplit := by
  simp [Exec.unsplitB, Exec.Unsplit, List.all_eq_true, Bool.or_eq_true]
  constructor
  · intro h a b hs
    rcases h a b with h | h
    · simp [hs] at h
    · exact h
  · intro h a b
    by_cases hs : x.sm a b = true
    · exact .inr (h a b hs)
    · exact .inl (by simpa using hs)

theorem hbB_iff (hc : x.hbClosedB = true) {a b : Fin x.n} : x.hbB a b = true ↔ x.Hb a b :=
  reach_iff _ hc

theorem hbLB_iff (hc : x.hbLClosedB = true) {a b : Fin x.n} : x.hbLB a b = true ↔ x.HbL a b :=
  reach_iff _ hc

theorem drfB_iff (hc : x.hbClosedB = true) : x.drfB = true ↔ x.Drf := by
  simp only [Exec.drfB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', hbB_iff x hc, Exec.Drf]
  constructor
  · intro h a b hc'
    rcases h a b with (h | h) | h
    · simp [hc'] at h
    · exact .inl h
    · exact .inr h
  · intro h a b
    by_cases hc' : x.conflict a b = true
    · rcases h a b hc' with h | h
      · exact .inl (.inr h)
      · exact .inr h
    · exact .inl (.inl (by simpa using hc'))

theorem drfLB_iff (hc : x.hbLClosedB = true) : x.drfLB = true ↔ x.DrfL := by
  simp only [Exec.drfLB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true', hbLB_iff x hc, Exec.DrfL]
  constructor
  · intro h a b hc' hA
    rcases h a b with ((h | h) | h) | h
    · simp [hc'] at h
    · simp [hA] at h
    · exact .inl h
    · exact .inr h
  · intro h a b
    by_cases hc' : x.conflict a b = true
    · by_cases hA : ((x.ev a).isA && (x.ev b).isA) = true
      · exact .inl (.inl (.inr hA))
      · rcases h a b hc' (by simpa using hA) with h | h
        · exact .inl (.inr h)
        · exact .inr h
    · exact .inl (.inl (.inl (by simpa using hc')))

theorem raCohB_iff (hc : x.hbClosedB = true) :
    x.raCohB = true ↔ ∀ a b, x.Hb a b → x.com b a = false := by
  simp only [Exec.raCohB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · intro h a b hab
    rcases h a b with h | h
    · rw [← hbB_iff x hc] at hab
      simp [hab] at h
    · exact h
  · intro h a b
    by_cases hab : x.hbB a b = true
    · exact .inr (h a b ((hbB_iff x hc).mp hab))
    · exact .inl (by simpa using hab)

end Exec

end Silmaril.X86.MemoryModel.Axiomatic.Proofs.Lattice
