module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Thread

/-!
# Process-level threads: the lowered process refines the CIR sync semantics

`rel_step`: every step of the lowered process is matched by zero or
one step of the CIR sync machine, preserving `Rel`; `refines`: every reachable process
configuration is related to a reachable sync configuration.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)
open Silmaril.X86.Concurrency.Cir.Proc

/-! ## Generic facts -/

theorem star_one {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b :=
  .step h .refl

theorem star_trans {α : Type} {r : α → α → Prop} {a b c : α} (h : Star r a b) (h' : Star r b c) :
    Star r a c := by
  induction h with
  | refl => exact h'
  | step h _ ih => exact .step h (ih h')

theorem upd_same {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by
  simp [upd]

theorem upd_other {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

theorem upd_eq_self {α : Type} (f : Nat → α) (t : Nat) : upd f t (f t) = f := by
  funext u; simp only [upd]; split <;> subst_vars <;> rfl

theorem tstep_not_skip {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs}
    (h : TStep .skip rs l s' rs') : False := by cases h

theorem isCtl_ctlAddr (u : Nat) : isCtl (ctlAddr u) = true := by
  have h1 : 0x7f0000 ≤ ctlAddr u := by simp [ctlAddr]
  have h2 : (ctlAddr u - 0x7f0000) % 64 = 0 := by simp [ctlAddr]
  simp [isCtl, h1, h2]

theorem isCtl_true {a : Nat} (h : isCtl a = true) : ∃ u, a = ctlAddr u := by
  simp only [isCtl, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨(a - 0x7f0000) / 64, by simp only [ctlAddr]; omega⟩

theorem ctlAddr_lt {P : SProg} (hw : P.Wf) {u : Nat} (hu : u < P.N) : ctlAddr u < 2 ^ 64 := by
  have := hw.small; simp only [ctlAddr] at *; omega

theorem toNat_ctl {P : SProg} (hw : P.Wf) {u : Nat} (hu : u < P.N) :
    (BitVec.ofNat 64 (ctlAddr u)).toNat = ctlAddr u := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (ctlAddr_lt hw hu)

theorem plain_isMem {l : Lab} (h : l.plain = true) : l.isMem = true := by
  cases l <;> simp_all [Lab.plain, Lab.isMem]

theorem updH_rd (H : Heap) (m : Mode) (fl : Flav) (a sz v : Nat) :
    (Lab.rd m fl a sz v).updH H = H := by
  funext x; simp [Lab.updH, Lab.wval]

theorem updH_fwait (H : Heap) (a e v r : Nat) : (Lab.fwait a e v r).updH H = H := by
  funext x; simp [Lab.updH, Lab.wval]

theorem updH_fwake (H : Heap) (a n q : Nat) : (Lab.fwake a n q).updH H = H := by
  funext x; simp [Lab.updH, Lab.wval]

/-! ## The relation with an explicit thread map -/

/-- `Rel` with the thread map `g` fixed. -/
structure RelG (P : SProg) (L : Layout) (C : PCfg PSt) (A : SCfg) (g : Nat → Nat) : Prop where
  heap : ∀ a, isCtl a = false → C.mem a = A.mem a
  actl : ∀ u, A.mem (ctlAddr u) = none
  cctl : ∀ u, 0 < u → u < P.N →
    ∃ v, C.mem (ctlAddr u) = some v ∧ (v = 0 → A.started u = true ∧ (A.ts u).1 = .skip)
  fresh : ∀ u, A.started u = false → A.ts u = (P.body u, Regs.zero)
  inj : ∀ t t' r r', C.th t = some r → C.th t' = some r' → g t = g t' → t = t'
  thr : ∀ t r, C.th t = some r → g t < P.N ∧ A.started (g t) = true ∧ TCorr L r (A.ts (g t)) ∧
    ((r.ctid = none ∧ g t = 0) ∨ (r.ctid = some (ctlAddr (g t)) ∧ 0 < g t))

theorem relG_of_rel {P : SProg} {L : Layout} {C : PCfg PSt} {A : SCfg} (R : Rel P L C A) :
    ∃ g, RelG P L C A g := by
  obtain ⟨g, hi, ht⟩ := R.map
  exact ⟨g, R.heap, R.actl, R.cctl, R.fresh, hi, ht⟩

theorem rel_of_relG {P : SProg} {L : Layout} {C : PCfg PSt} {A : SCfg} {g : Nat → Nat}
    (R : RelG P L C A g) : Rel P L C A :=
  ⟨R.heap, R.actl, R.cctl, R.fresh, ⟨g, R.inj, R.thr⟩⟩

section
variable {P : SProg} {L : Layout} {C : PCfg PSt} {A : SCfg} {g : Nat → Nat}

/-- A mapped sync cell is not a control cell. -/
theorem notCtl (R : RelG P L C A g) {a : Nat} (h : (A.mem a).isSome) : isCtl a = false := by
  cases hc : isCtl a
  · rfl
  · obtain ⟨u, rfl⟩ := isCtl_true hc
    rw [R.actl] at h; cases h

/-- **Replace one thread** (and its CIR thread's state), with new heaps. -/
theorem relG_thread (R : RelG P L C A g) {t : Nat} {r : TRec PSt} (ht : C.th t = some r)
    (r' : TRec PSt) (hct : r'.ctid = r.ctid) (x' : Stmt × Regs) (hx : TCorr L r' x')
    (Cm Am : Heap) (st : Option Nat) (hheap : ∀ a, isCtl a = false → Cm a = Am a)
    (hactl : ∀ u, Am (ctlAddr u) = none)
    (hcm : ∀ u, 0 < u → u < P.N → ∃ v, Cm (ctlAddr u) = some v ∧
      (v = 0 → A.started u = true ∧ (upd A.ts (g t) x' u).1 = .skip)) :
    RelG P L ⟨setTh C.th t r', Cm, st⟩ ⟨upd A.ts (g t) x', A.started, Am⟩ g := by
  obtain ⟨hlt, hst, -, -⟩ := R.thr t r ht
  refine ⟨hheap, hactl, hcm, fun u hu => ?_, fun t1 t2 r1 r2 h1 h2 he => ?_, fun t2 r2 h2 => ?_⟩
  · have : u ≠ g t := fun e => by rw [e, hst] at hu; cases hu
    simp only [upd_other _ _ this]; exact R.fresh u hu
  · simp only [setTh, upd] at h1 h2
    split at h1 <;> split at h2
    · subst_vars; rfl
    · subst_vars; exact R.inj _ _ _ _ ht h2 he
    · subst_vars; exact R.inj _ _ _ _ h1 ht he
    · exact R.inj _ _ _ _ h1 h2 he
  · simp only [setTh, upd] at h2
    split at h2
    · subst_vars; cases h2
      refine ⟨hlt, hst, by simpa [upd_same] using hx, ?_⟩
      rw [hct]; exact (R.thr _ _ ht).2.2.2
    · rename_i hne
      have hg : g t2 ≠ g t := fun e => hne (R.inj _ _ _ _ h2 ht e)
      obtain ⟨a1, a2, a3, a4⟩ := R.thr t2 r2 h2
      exact ⟨a1, a2, by simpa [upd_other _ _ hg] using a3, a4⟩

/-- The control words are unchanged and a finished CIR thread stays put. -/
theorem hcm_same (R : RelG P L C A g) {t : Nat} {x' : Stmt × Regs} (Cm : Heap)
    (hc : ∀ u, Cm (ctlAddr u) = C.mem (ctlAddr u)) (hdone : (A.ts (g t)).1 = .skip → x' = A.ts (g t))
    (u : Nat) (h0 : 0 < u) (hu : u < P.N) : ∃ v, Cm (ctlAddr u) = some v ∧
      (v = 0 → A.started u = true ∧ (upd A.ts (g t) x' u).1 = .skip) := by
  obtain ⟨v, hv, h⟩ := R.cctl u h0 hu
  refine ⟨v, by rw [hc]; exact hv, fun hv0 => ?_⟩
  obtain ⟨h1, h2⟩ := h hv0
  refine ⟨h1, ?_⟩
  by_cases e : u = g t
  · subst e; rw [upd_same, hdone h2]; exact h2
  · rw [upd_other _ _ e]; exact h2

/-- **Wake threads**: waiters become runnable in the state they resume in. -/
theorem relG_wake (R : RelG P L C A g) (ws : List Nat) (st : Option Nat) :
    RelG P L ⟨wakeAll C.th ws, C.mem, st⟩ A g := by
  have key : ∀ t r, wakeAll C.th ws t = some r → ∃ r0, C.th t = some r0 ∧
      (r = r0.wake ∨ r = r0) := by
    intro t r h
    simp only [wakeAll] at h
    split at h
    · cases h0 : C.th t with
      | none => rw [h0] at h; cases h
      | some r0 => rw [h0] at h; cases h; exact ⟨r0, rfl, Or.inl rfl⟩
    · exact ⟨r, h, Or.inr rfl⟩
  refine ⟨R.heap, R.actl, R.cctl, R.fresh, fun t1 t2 r1 r2 h1 h2 he => ?_, fun t r h => ?_⟩
  · obtain ⟨r1', h1', -⟩ := key t1 r1 h1
    obtain ⟨r2', h2', -⟩ := key t2 r2 h2
    exact R.inj _ _ _ _ h1' h2' he
  · obtain ⟨r0, h0, hr⟩ := key t r h
    obtain ⟨a1, a2, a3, a4⟩ := R.thr t r0 h0
    rcases hr with hr | hr
    · refine ⟨a1, a2, ?_, ?_⟩
      · subst hr; unfold TRec.wake; split
        · rename_i k hk; simp only [TCorr] at a3 ⊢; rw [hk] at a3; exact a3
        · exact a3
      · subst hr; unfold TRec.wake; split <;> exact a4
    · subst hr; exact ⟨a1, a2, a3, a4⟩

theorem wakeAll_run {th : Nat → Option (TRec PSt)} {ws : List Nat} {t : Nat} {r : TRec PSt}
    {s : PSt} (ht : th t = some r) (hr : r.st = .run s) : wakeAll th ws t = some r := by
  simp only [wakeAll]; split
  · rw [ht]; simp only [Option.map_some, TRec.wake]; split
    · rename_i h; rw [hr] at h; cases h
    · rfl
  · exact ht

theorem setTh2_cases {th : Nat → Option (TRec PSt)} {t t' : Nat} {r1 r2 : TRec PSt} {x : Nat}
    {y : TRec PSt} (h : setTh (setTh th t r1) t' r2 x = some y) :
    (x = t' ∧ y = r2) ∨ (x ≠ t' ∧ x = t ∧ y = r1) ∨ (x ≠ t' ∧ x ≠ t ∧ th x = some y) := by
  simp only [setTh, upd] at h
  by_cases e1 : x = t'
  · rw [ite_eq_left e1] at h; cases h; exact Or.inl ⟨e1, rfl⟩
  · rw [ite_eq_right e1] at h
    by_cases e2 : x = t
    · rw [ite_eq_left e2] at h; cases h; exact Or.inr (Or.inl ⟨e1, e2, rfl⟩)
    · rw [ite_eq_right e2] at h; exact Or.inr (Or.inr ⟨e1, e2, h⟩)

theorem setTh2_side {th : Nat → Option (TRec PSt)} {t t' : Nat} {r1 r2 : TRec PSt} {x : Nat}
    {y : TRec PSt} (ht : th t ≠ none) (h : setTh (setTh th t r1) t' r2 x = some y) :
    x = t' ∨ (x ≠ t' ∧ ∃ r0, th x = some r0) := by
  rcases setTh2_cases h with ⟨e, -⟩ | ⟨n, e, -⟩ | ⟨n, -, c⟩
  · exact Or.inl e
  · subst e; exact Or.inr ⟨n, Option.ne_none_iff_exists'.mp ht⟩
  · exact Or.inr ⟨n, _, c⟩

/-- The thread `t` (running `s` with record `r`) has outcome `OutT` against its CIR thread. -/
theorem thread_out (R : RelG P L C A g) {t : Nat} {r : TRec PSt} {s : PSt}
    (ht : C.th t = some r) (hr : r.st = .run s) {act : UAct PSt}
    (hs : PTStep (P.code L) r.tp s.1 s.2 act) :
    OutT (P.code L) L act (A.ts (g t)).1 (A.ts (g t)).2 := by
  have h3 := (R.thr t r ht).2.2.1
  simp only [TCorr, hr] at h3
  exact sim_top h3 hs

end

/-! ## The step simulation -/

section
variable {P : SProg} {L : Layout} {base : Base}

/-- **One process step is matched by at most one sync step.** -/
theorem rel_step (hw : P.Wf) (hss : P.SyncSafe) {C C' : PCfg (pIsa (P.code L)).St} {A : SCfg}
    (hA : SReach P P.init A) {g : Nat → Nat} (R : RelG P L C A g)
    (hstep : PStep (pIsa (P.code L)) base C C') :
    ∃ A' g', Star (SStep P.N) A A' ∧ RelG P L C' A' g' := by
  cases hstep
  case tau t r s s' hl ht hr hs =>
    obtain ⟨hlt, hst, -, -⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, -⟩, -⟩
    · rcases h with h | ⟨s2, rs2, h2, h3⟩
      · refine ⟨A, g, .refl, ?_⟩
        have := relG_thread R ht { r with st := .run s' } rfl (A.ts (g t)) h C.mem A.mem C.status
          R.heap R.actl (hcm_same R C.mem (fun _ => rfl) fun _ => rfl)
        rwa [upd_eq_self] at this
      · refine ⟨_, g, star_one (.tau hlt hst h2), ?_⟩
        exact relG_thread R ht { r with st := .run s' } rfl (s2, rs2) h3 C.mem A.mem C.status
          R.heap R.actl (hcm_same R C.mem (fun _ => rfl)
            fun hd => absurd h2 (by rw [hd]; exact fun h => tstep_not_skip h))
    · cases h
  case mem t r s l s' hl ht hr hs hp hc hok =>
    obtain ⟨hlt, hst, -, -⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, -⟩, -⟩
    · rcases h with ⟨s2, rs2, h2, h3⟩ | ⟨u, v, rfl, ⟨sj, rj, hj⟩, hne, heq⟩
      · -- a user memory label
        obtain ⟨hcA, -, -⟩ := hss A hA (g t) hlt hst l s2 rs2 h2
        have hok' : l.okH A.mem := fun p hp' => by
          have hm := hcA p.1 (Or.inl ⟨p.2, hp'⟩)
          rw [← R.heap p.1 (notCtl R hm)]; exact hok p hp'
        have hwv : ∀ u, l.wval (ctlAddr u) = none := fun u => by
          cases e : l.wval (ctlAddr u)
          · rfl
          · have := hcA _ (Or.inr (by rw [e]; rfl)); rw [R.actl] at this; cases this
        refine ⟨_, g, star_one (.lab hlt hst h2 (plain_isMem hp) hcA hok'), ?_⟩
        refine relG_thread R ht { r with st := .run s' } rfl (s2, rs2) h3 (l.updH C.mem)
          (l.updH A.mem) C.status (fun a ha => ?_) (fun u => ?_) (hcm_same R _ (fun u => ?_)
            fun hd => absurd h2 (by rw [hd]; exact fun h => tstep_not_skip h))
        · simp only [Lab.updH, R.heap a ha]
        · simp only [Lab.updH, hwv, R.actl]; rfl
        · simp only [Lab.updH, hwv]; rfl
      · -- the join loop reads a control word
        obtain ⟨-, -, hju⟩ := hss A hA (g t) hlt hst _ sj rj hj
        obtain ⟨hu0, huN⟩ := hju u rfl
        rw [Nat.mod_eq_of_lt (ctlAddr_lt hw huN)] at hok hp hc ⊢
        have hv : C.mem (ctlAddr u) = some v := hok (ctlAddr u, v) (by simp [Lab.reads])
        rw [updH_rd]
        by_cases hv0 : v = 0
        · obtain ⟨s2, rs2, h2, h3⟩ := heq hv0
          obtain ⟨w, hw', hdone⟩ := R.cctl u hu0 huN
          rw [hv] at hw'; cases hw'
          obtain ⟨hsu, hdu⟩ := hdone hv0
          refine ⟨_, g, star_one (.join hlt hst h2 hsu hdu), ?_⟩
          exact relG_thread R ht { r with st := .run s' } rfl (s2, rs2) h3 C.mem A.mem C.status
            R.heap R.actl (hcm_same R C.mem (fun _ => rfl)
              fun hd => absurd h2 (by rw [hd]; exact fun h => tstep_not_skip h))
        · refine ⟨A, g, .refl, ?_⟩
          have := relG_thread R ht { r with st := .run s' } rfl (A.ts (g t)) (hne hv0) C.mem A.mem
            C.status R.heap R.actl (hcm_same R C.mem (fun _ => rfl) fun _ => rfl)
          rwa [upd_eq_self] at this
    · cases h
  case gettid t r s args k ch hl ht hr hs =>
    exfalso
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [nrGettid, nrFutex, nrClone] at h
    · cases h; rcases he with h | h <;> simp [nrGettid, nrExit, nrExitGroup] at h
  case setTid t r s a args k ch hl ht hr hs =>
    exfalso
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [nrSetTid, nrFutex, nrClone] at h
    · cases h; rcases he with h | h <;> simp [nrSetTid, nrExit, nrExitGroup] at h
  case base t r s nr args k ch ret mem' hl ht hr hs hn hb =>
    exfalso
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> subst h <;> exact hn (by simp [threadNr])
    · cases h; rcases he with h | h <;> subst h <;> exact hn (by simp [threadNr])
  case futexBlock t r s a op v args k ch w hl ht hr hs hop hwv hlt heq =>
    obtain ⟨hgN, hst, -, -⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨-, a1, v1, he, h⟩ | ⟨-, u, v1, he, -, h⟩ | ⟨-, a1, n1, he, -⟩ |
          ⟨h, -⟩
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        obtain ⟨s2, rs2, h2, h3⟩ := h w hlt
        rw [ite_eq_left heq] at h3
        obtain ⟨hcA, -, -⟩ := hss A hA (g t) hgN hst _ s2 rs2 h2
        have hm : (A.mem a.toNat).isSome := hcA _ (Or.inl ⟨w, by simp [Lab.reads]⟩)
        have hok : (Lab.fwait a.toNat (v.toNat % 2 ^ 32) w 0).okH A.mem := fun p hp' => by
          simp only [Lab.reads, List.mem_singleton] at hp'; subst hp'
          rw [← R.heap _ (notCtl R hm)]; exact hwv
        refine ⟨_, g, star_one (.lab hgN hst h2 rfl hcA hok), ?_⟩
        rw [updH_fwait]
        exact relG_thread R ht { r with st := .wait a.toNat k } rfl (s2, rs2) h3 C.mem A.mem
          C.status R.heap R.actl (hcm_same R C.mem (fun _ => rfl)
            fun hd => absurd h2 (by rw [hd]; exact fun h => tstep_not_skip h))
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        refine ⟨A, g, .refl, ?_⟩
        have := relG_thread R ht { r with st := .wait (BitVec.ofNat 64 (ctlAddr u)).toNat k } rfl (A.ts (g t)) (h 0) C.mem A.mem
          C.status R.heap R.actl (hcm_same R C.mem (fun _ => rfl) fun _ => rfl)
        rwa [upd_eq_self] at this
      · simp only [List.cons.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        rcases hop with h | h <;> simp at h
      · simp [nrFutex, nrClone] at h
    · cases h; rcases he with h | h <;> simp [nrFutex, nrExit, nrExitGroup] at h
  case futexAgain t r s a op v args k ch w hl ht hr hs hop hwv hlt hne =>
    obtain ⟨hgN, hst, -, -⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨-, a1, v1, he, h⟩ | ⟨-, u, v1, he, -, h⟩ | ⟨-, a1, n1, he, -⟩ |
          ⟨h, -⟩
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        obtain ⟨s2, rs2, h2, h3⟩ := h w hlt
        rw [ite_eq_right hne] at h3
        obtain ⟨hcA, -, -⟩ := hss A hA (g t) hgN hst _ s2 rs2 h2
        have hm : (A.mem a.toNat).isSome := hcA _ (Or.inl ⟨w, by simp [Lab.reads]⟩)
        have hok : (Lab.fwait a.toNat (v.toNat % 2 ^ 32) w 0).okH A.mem := fun p hp' => by
          simp only [Lab.reads, List.mem_singleton] at hp'; subst hp'
          rw [← R.heap _ (notCtl R hm)]; exact hwv
        refine ⟨_, g, star_one (.lab hgN hst h2 rfl hcA hok), ?_⟩
        rw [updH_fwait]
        exact relG_thread R ht { r with st := .run (k errAgain) } rfl (s2, rs2) h3 C.mem A.mem
          C.status R.heap R.actl (hcm_same R C.mem (fun _ => rfl)
            fun hd => absurd h2 (by rw [hd]; exact fun h => tstep_not_skip h))
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        refine ⟨A, g, .refl, ?_⟩
        have := relG_thread R ht { r with st := .run (k errAgain) } rfl (A.ts (g t)) (h _) C.mem
          A.mem C.status R.heap R.actl (hcm_same R C.mem (fun _ => rfl) fun _ => rfl)
        rwa [upd_eq_self] at this
      · simp only [List.cons.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        rcases hop with h | h <;> simp at h
      · simp [nrFutex, nrClone] at h
    · cases h; rcases he with h | h <;> simp [nrFutex, nrExit, nrExitGroup] at h
  case futexWake t r s a op n args k ch ws hl ht hr hs hop hws =>
    obtain ⟨hgN, hst, -, -⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨-, a1, v1, he, -⟩ | ⟨-, u, v1, he, -⟩ | ⟨-, a1, n1, he, s2, rs2, h2, h3⟩ |
          ⟨h, -⟩
      · simp only [List.cons.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        rcases hop with h | h <;> simp at h
      · simp only [List.cons.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        rcases hop with h | h <;> simp at h
      · simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        have hcA : ∀ x, (Lab.fwake a.toNat n.toNat 0).Touches x → (A.mem x).isSome := by
          rintro x (⟨v, hv⟩ | hv) <;> simp [Lab.reads, Lab.wval] at hv
        have hok : (Lab.fwake a.toNat n.toNat 0).okH A.mem := fun p hp => by
          simp [Lab.reads] at hp
        refine ⟨_, g, star_one (.lab hgN hst h2 rfl hcA hok), ?_⟩
        rw [updH_fwake]
        have R1 := relG_wake R ws C.status
        have := relG_thread R1 (wakeAll_run ht hr) { r with st := .run (k (BitVec.ofNat 64 ws.length)) } rfl (s2, rs2) (h3 _)
          C.mem A.mem C.status R1.heap R1.actl (hcm_same R1 C.mem (fun _ => rfl)
            fun hd => absurd h2 (by rw [hd]; exact fun h => tstep_not_skip h))
        exact this
      · simp [nrFutex, nrClone] at h
    · cases h; rcases he with h | h <;> simp [nrFutex, nrExit, nrExitGroup] at h
  case spurious t r a k hl ht hr =>
    refine ⟨A, g, .refl, ?_⟩
    have h3 := (R.thr t r ht).2.2.1
    simp only [TCorr, hr] at h3
    have := relG_thread R ht { r with st := .run (k 0) } rfl (A.ts (g t)) h3 C.mem A.mem C.status
      R.heap R.actl (hcm_same R C.mem (fun _ => rfl) fun _ => rfl)
    rwa [upd_eq_self] at this
  case clone t r s fl sp ptid ctid tls args k ch t' hl ht hr hs hf hfresh h0 hmax hpt =>
    obtain ⟨hgN, hst, -, hct⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨⟨_, _, _, _, h, he⟩, -⟩
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, u, he, hch, s2, rs2, hT, h3⟩
      · simp [nrFutex, nrClone] at h
      · simp [nrFutex, nrClone] at h
      · simp [nrFutex, nrClone] at h
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨-, hsp, -⟩ := hss A hA (g t) hgN hst _ s2 rs2 hT
      obtain ⟨hu0, huN, hun⟩ := hsp u rfl
      rw [toNat_ctl hw huN] at hpt ⊢
      have hne : u ≠ g t := fun e => by rw [e, hst] at hun; cases hun
      have htt : t' ≠ t := fun e => by rw [e, ht] at hfresh; cases hfresh
      refine ⟨_, upd g t' u, star_one (.spawn hgN hst hT ⟨hu0, huN⟩ hun), ?_⟩
      have hg' : ∀ t2, t2 ≠ t' → upd g t' u t2 = g t2 := fun t2 h => upd_other _ _ h
      have hgs : ∀ t2 r2, C.th t2 = some r2 → g t2 ≠ u := fun t2 r2 h e => by
        have := (R.thr t2 r2 h).2.1; rw [e, hun] at this; cases this
      refine ⟨fun a ha => ?_, R.actl, fun u2 h02 hu2 => ?_, fun u2 hu2 => ?_,
        fun t1 t2 r1 r2 h1 h2 he => ?_, fun t2 r2 h2 => ?_⟩
      · have : a ≠ ctlAddr u := fun e => by rw [e, isCtl_ctlAddr] at ha; cases ha
        simp only [heapPut, ite_eq_right this]; exact R.heap a ha
      · by_cases e : u2 = u
        · subst e; refine ⟨t', by simp [heapPut], fun h => absurd h (by omega)⟩
        · obtain ⟨v, hv, hd⟩ := R.cctl u2 h02 hu2
          have : ctlAddr u2 ≠ ctlAddr u := fun h => e (by simp only [ctlAddr] at h; omega)
          refine ⟨v, by simp only [heapPut, ite_eq_right this]; exact hv, fun hv0 => ?_⟩
          obtain ⟨hs1, hs2⟩ := hd hv0
          refine ⟨by simp [upd, hs1], ?_⟩
          by_cases e2 : u2 = g t
          · subst e2; exact absurd hT (by rw [hs2]; exact fun h => tstep_not_skip h)
          · simp only [upd_other _ _ e2]; exact hs2
      · have h1 : u2 ≠ u := fun e => by subst e; simp [upd] at hu2
        have h2' : A.started u2 = false := by simpa [upd, h1] using hu2
        have h3 : u2 ≠ g t := fun e => by rw [e, hst] at h2'; cases h2'
        simp only [upd_other _ _ h3]; exact R.fresh u2 h2'
      · rcases setTh2_side (by rw [ht]; exact Option.some_ne_none _) h1 with e1 | ⟨n1, r1', c1⟩ <;>
          rcases setTh2_side (by rw [ht]; exact Option.some_ne_none _) h2 with e2 | ⟨n2, r2', c2⟩
        · rw [e1, e2]
        · exfalso; rw [e1, upd_same, hg' _ n2] at he; exact hgs _ _ c2 he.symm
        · exfalso; rw [e2, upd_same, hg' _ n1] at he; exact hgs _ _ c1 he
        · rw [hg' _ n1, hg' _ n2] at he; exact R.inj _ _ _ _ c1 c2 he
      · rcases setTh2_cases h2 with ⟨e, ey⟩ | ⟨n, e, ey⟩ | ⟨n, n', c⟩
        · -- the child
          subst ey; rw [e]
          refine ⟨by simp [upd]; exact huN, by simp [upd], ?_, Or.inr ⟨?_, by simp [upd]; exact hu0⟩⟩
          · simp only [TCorr, upd_same, upd_other _ _ hne]
            rw [R.fresh u hun, hch]
            exact top_child _ (hw.noR u) _
          · simp [upd]
        · -- the parent
          subst ey; rw [hg' _ n, e]
          refine ⟨hgN, by simp [upd, hst], ?_, hct⟩
          simp only [TCorr, upd_same]; exact h3 _
        · rw [hg' _ n]
          have hg2 : g t2 ≠ g t := fun e => n' (R.inj _ _ _ _ c ht e)
          have hgu : g t2 ≠ u := hgs _ _ c
          obtain ⟨a1, a2, a3, a4⟩ := R.thr t2 r2 c
          refine ⟨a1, by simp [upd, a2], ?_, a4⟩
          simpa [upd_other _ _ hg2] using a3
    · cases h; rcases he with h | h <;> simp [nrClone, nrExit, nrExitGroup] at h
  case exitClear t r s code args k ch a ws hl ht hr hs hcta hmap hlive hws =>
    obtain ⟨hgN, hst, -, hct⟩ := R.thr t r ht
    rcases thread_out R ht hr hs with h | ⟨-, hsk⟩
    · exfalso
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [nrExit, nrFutex, nrClone] at h
    rcases hct with ⟨hct, -⟩ | ⟨hct, hpos⟩
    · rw [hct] at hcta; cases hcta
    rw [hct] at hcta; cases hcta
    refine ⟨A, g, .refl, ?_⟩
    have R1 := relG_thread R ht { r with st := .exited } rfl (A.ts (g t)) hsk
      (heapPut C.mem (ctlAddr (g t)) 0) A.mem C.status (fun a ha => ?_) R.actl ?_
    · have R2 := relG_wake R1 ws C.status
      rwa [upd_eq_self] at R2
    · have : a ≠ ctlAddr (g t) := fun e => by rw [e, isCtl_ctlAddr] at ha; cases ha
      simp only [heapPut, ite_eq_right this]; exact R.heap a ha
    · intro u h0 hu
      by_cases e : u = g t
      · subst e; refine ⟨0, by simp [heapPut], fun _ => ⟨hst, by simp [upd_same, hsk]⟩⟩
      · have : ctlAddr u ≠ ctlAddr (g t) := fun h => e (by simp only [ctlAddr] at h; omega)
        obtain ⟨v, hv, hd⟩ := R.cctl u h0 hu
        refine ⟨v, by simp only [heapPut, ite_eq_right this]; exact hv, fun hv0 => ?_⟩
        obtain ⟨h1, h2⟩ := hd hv0
        exact ⟨h1, by simp only [upd_other _ _ e]; exact h2⟩
  case exitPlain t r s code args k ch hl ht hr hs hnc =>
    rcases thread_out R ht hr hs with h | ⟨-, hsk⟩
    · exfalso
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [nrExit, nrFutex, nrClone] at h
    refine ⟨A, g, .refl, ?_⟩
    have := relG_thread R ht { r with st := .exited } rfl (A.ts (g t)) hsk C.mem A.mem
      (lastExit (setTh C.th t { r with st := .exited }) (code.toNat % 256)) R.heap R.actl
      (hcm_same R C.mem (fun _ => rfl) fun _ => rfl)
    rwa [upd_eq_self] at this
  case exitGroup t r s code args k ch hl ht hr hs =>
    exact ⟨A, g, .refl, R.heap, R.actl, R.cctl, R.fresh, R.inj, R.thr⟩

end

/-! ## Initialisation and reachability -/

section
variable {P : SProg} {L : Layout}

theorem pheap_user {a : Nat} (ha : isCtl a = false) : P.pheap a = P.heap a := by
  simp only [SProg.pheap]
  split
  · rename_i h
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨u, -, -, rfl⟩ := h
    rw [isCtl_ctlAddr] at ha; cases ha
  · rfl

theorem pheap_ctl {u : Nat} (h0 : 0 < u) (hu : u < P.N) : P.pheap (ctlAddr u) = some 1 := by
  simp only [SProg.pheap]
  rw [ite_eq_left]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨u, hu, h0, rfl⟩

theorem relG_init (hw : P.Wf) (tid0 : Nat) (tp0 : Word) :
    RelG P L (P.pinit L tid0 tp0) P.init (fun _ => 0) := by
  refine ⟨fun a ha => pheap_user ha, hw.noCtl, fun u h0 hu => ⟨1, pheap_ctl h0 hu, fun h => ?_⟩,
    fun u _ => rfl, fun t1 t2 r1 r2 h1 h2 _ => ?_, fun t r h => ?_⟩
  · cases h
  · simp only [SProg.pinit, PCfg.init] at h1 h2
    split at h1 <;> split at h2 <;> simp_all
  · simp only [SProg.pinit, PCfg.init] at h
    split at h
    · cases h
      refine ⟨hw.pos, rfl, ?_, Or.inl ⟨rfl, rfl⟩⟩
      exact .tail (.low (hw.noR 0) (ag_refl _)) (Or.inr rfl)
    · cases h

/-- **Refinement**: every configuration the lowered process reaches is related to a
configuration the CIR sync machine reaches. -/
theorem refines {base : Base} (hw : P.Wf) (hss : P.SyncSafe) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (P.code L)).St} (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C) :
    ∃ A, SReach P P.init A ∧ Rel P L C A := by
  suffices key : ∀ C0 C, PReach (pIsa (P.code L)) base C0 C → ∀ A g, SReach P P.init A →
      RelG P L C0 A g → ∃ A', SReach P P.init A' ∧ Rel P L C A' from
    key _ _ h _ _ .refl (relG_init hw tid0 tp0)
  intro C0 C hr
  induction hr with
  | refl => intro A g hA R; exact ⟨A, hA, rel_of_relG R⟩
  | step hs _ ih =>
    intro A g hA R
    obtain ⟨A', g', hAA, R'⟩ := rel_step hw hss hA R hs
    exact ih A' g' (star_trans hA hAA) R'

end


/-! ## Consequences -/

section
variable {P : SProg} {L : Layout}

theorem userHeap_eq {C : PCfg PSt} {A : SCfg} (R : Rel P L C A) : userHeap C.mem = userHeap A.mem := by
  funext a; simp only [userHeap]; split
  · rfl
  · rename_i h; exact R.heap a (by simpa using h)

/-- **Safety transfer**: a property of the user heap (the heap without the control cells) that
holds in every reachable sync configuration holds in every reachable lowered process. -/
theorem safety_transfer {base : Base} (hw : P.Wf) (hss : P.SyncSafe) (tid0 : Nat) (tp0 : Word)
    (Q : Heap → Prop) (hQ : ∀ A, SReach P P.init A → Q (userHeap A.mem))
    {C : PCfg (pIsa (P.code L)).St} (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C) :
    Q (userHeap C.mem) := by
  obtain ⟨A, hA, R⟩ := refines hw hss tid0 tp0 h
  rw [userHeap_eq R]; exact hQ A hA

/-- **The join rule**: in a reachable lowered process, a control word that reads `0` means
the thread has been spawned and has finished in a related reachable sync configuration (and
so the join loop, which leaves only after reading `0`, implements `join`). -/
theorem join_rule {base : Base} (hw : P.Wf) (hss : P.SyncSafe) (tid0 : Nat) (tp0 : Word)
    {C : PCfg (pIsa (P.code L)).St} (h : PReach (pIsa (P.code L)) base (P.pinit L tid0 tp0) C)
    {u : Nat} (h0 : 0 < u) (hu : u < P.N) (hz : C.mem (ctlAddr u) = some 0) :
    ∃ A, SReach P P.init A ∧ Rel P L C A ∧ A.started u = true ∧ (A.ts u).1 = .skip := by
  obtain ⟨A, hA, R⟩ := refines hw hss tid0 tp0 h
  obtain ⟨v, hv, hd⟩ := R.cctl u h0 hu
  rw [hz] at hv; cases hv
  exact ⟨A, hA, R, hd rfl⟩

end

end Silmaril.Proofs.X86.Concurrency.Cir.Proc
