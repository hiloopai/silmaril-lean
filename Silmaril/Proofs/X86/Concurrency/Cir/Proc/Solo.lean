module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs

/-!
# Process-level threads: the single-threaded view and generic process rules

* `solo_fwd`, `solo_bwd`: a process with one thread that never requests `clone` or `futex`
  steps exactly like the single-threaded machine `SoloStep` (the LPS-shaped view);
* `tp_stable`, `clone_tp`: thread pointers are per-thread constants; a `clone` child's is the
  `tls` argument;
* `exited_stuck`: an exited process does not step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd Star)
open Silmaril.X86.Concurrency.Cir.Proc

section
variable {I : UIsa} {base : Base}

theorem setTh_same {σ : Type} (th : Nat → Option (TRec σ)) (t : Nat) (r : TRec σ) :
    setTh th t r t = some r := by simp [setTh, upd]

theorem setTh_other {σ : Type} (th : Nat → Option (TRec σ)) {t u : Nat} (r : TRec σ)
    (h : u ≠ t) : setTh th t r u = th u := by simp [setTh, upd, h]

theorem lastExit_none {σ : Type} {th : Nat → Option (TRec σ)} (h : ¬ ∃ t, Live th t) (c : Nat) :
    lastExit th c = some c := by
  simp [lastExit, h]

theorem TRec.wake_tp {σ : Type} (r : TRec σ) : r.wake.tp = r.tp := by
  unfold TRec.wake; split <;> rfl

/-- An exited process does not step. -/
theorem exited_stuck {C C' : PCfg I.St} {c : Nat} (hc : C.status = some c)
    (h : PStep I base C C') : False := by
  cases h <;> simp_all

/-- **Thread pointers are per-thread constants**: every thread present before a step is
present after it, with the same thread pointer. -/
theorem tp_stable {C C' : PCfg I.St} (h : PStep I base C C') {t : Nat} {r : TRec I.St}
    (ht : C.th t = some r) : ∃ r', C'.th t = some r' ∧ r'.tp = r.tp := by
  have hs : ∀ {u} (r1 : TRec I.St), C.th u = some r1 → ∀ r2 : TRec I.St, r2.tp = r1.tp →
      ∃ r', setTh C.th u r2 t = some r' ∧ r'.tp = r.tp := by
    intro u r1 hu r2 htp
    by_cases e : t = u
    · subst e; rw [hu] at ht; cases ht; exact ⟨r2, setTh_same _ _ _, htp⟩
    · exact ⟨r, by rw [setTh_other _ _ e]; exact ht, rfl⟩
  have hw : ∀ (th : Nat → Option (TRec I.St)) (ws : List Nat) (r0 : TRec I.St),
      th t = some r0 → ∃ r', wakeAll th ws t = some r' ∧ r'.tp = r0.tp := by
    intro th ws r0 h0
    simp only [wakeAll]; split
    · exact ⟨r0.wake, by rw [h0]; rfl, TRec.wake_tp r0⟩
    · exact ⟨r0, h0, rfl⟩
  cases h
  case tau t1 r1 _ _ _ ht1 _ _ => exact hs r1 ht1 _ rfl
  case mem t1 r1 _ _ _ _ ht1 _ _ _ _ _ => exact hs r1 ht1 _ rfl
  case gettid t1 r1 _ _ _ _ _ ht1 _ _ => exact hs r1 ht1 _ rfl
  case setTid t1 r1 _ _ _ _ _ _ ht1 _ _ => exact hs r1 ht1 _ rfl
  case futexBlock t1 r1 _ _ _ _ _ _ _ _ _ ht1 _ _ _ _ _ _ => exact hs r1 ht1 _ rfl
  case futexAgain t1 r1 _ _ _ _ _ _ _ _ _ ht1 _ _ _ _ _ _ => exact hs r1 ht1 _ rfl
  case futexWake t1 r1 s1 a op n args k ch ws _ ht1 _ _ _ _ =>
    by_cases e : t = t1
    · subst e; exact ⟨_, setTh_same _ _ _, by rw [ht] at ht1; cases ht1; rfl⟩
    · simp only [setTh_other _ _ e]; exact hw _ _ _ ht
  case spurious t1 r1 _ _ _ ht1 _ => exact hs r1 ht1 _ rfl
  case clone t1 r1 _ _ _ _ _ _ _ _ _ t' _ ht1 _ _ _ hfresh _ _ _ =>
    have : t ≠ t' := fun e => by rw [e, hfresh] at ht; cases ht
    simp only [setTh_other _ _ this]; exact hs r1 ht1 _ rfl
  case exitClear t1 r1 _ _ _ _ _ _ ws _ ht1 _ _ _ _ _ _ =>
    obtain ⟨r', h1, h2⟩ := hs r1 ht1 { r1 with st := .exited } rfl
    obtain ⟨r'', h3, h4⟩ := hw _ ws r' h1
    exact ⟨r'', h3, h4.trans h2⟩
  case exitPlain t1 r1 _ _ _ _ _ _ ht1 _ _ _ => exact hs r1 ht1 _ rfl
  case exitGroup => exact ⟨r, ht, rfl⟩
  case base t1 r1 _ _ _ _ _ _ _ _ ht1 _ _ _ _ => exact hs r1 ht1 _ rfl

theorem TRec.wake_ctid {σ : Type} (r : TRec σ) : r.wake.ctid = r.ctid := by
  unfold TRec.wake; split <;> rfl

/-- **`clear_child_tid` changes only at `set_tid_address`**: a thread present before a step
that does not request `set_tid_address` keeps its `clear_child_tid` address. -/
theorem ctid_stable {C C' : PCfg I.St} (h : PStep I base C C') {t : Nat} {r : TRec I.St}
    (ht : C.th t = some r)
    (hns : ∀ s a args k ch, r.st = .run s → ¬ I.step r.tp s (.sys nrSetTid (a :: args) k ch)) :
    ∃ r', C'.th t = some r' ∧ r'.ctid = r.ctid := by
  have hs : ∀ {u} (r1 : TRec I.St), C.th u = some r1 → ∀ r2 : TRec I.St, r2.ctid = r1.ctid →
      ∃ r', setTh C.th u r2 t = some r' ∧ r'.ctid = r.ctid := by
    intro u r1 hu r2 htp
    by_cases e : t = u
    · subst e; rw [hu] at ht; cases ht; exact ⟨r2, setTh_same _ _ _, htp⟩
    · exact ⟨r, by rw [setTh_other _ _ e]; exact ht, rfl⟩
  have hw : ∀ (th : Nat → Option (TRec I.St)) (ws : List Nat) (r0 : TRec I.St),
      th t = some r0 → ∃ r', wakeAll th ws t = some r' ∧ r'.ctid = r0.ctid := by
    intro th ws r0 h0
    simp only [wakeAll]; split
    · exact ⟨r0.wake, by rw [h0]; rfl, TRec.wake_ctid r0⟩
    · exact ⟨r0, h0, rfl⟩
  cases h
  case tau t1 r1 _ _ _ ht1 _ _ => exact hs r1 ht1 _ rfl
  case mem t1 r1 _ _ _ _ ht1 _ _ _ _ _ => exact hs r1 ht1 _ rfl
  case gettid t1 r1 _ _ _ _ _ ht1 _ _ => exact hs r1 ht1 _ rfl
  case setTid t1 r1 s1 a args k ch _ ht1 hr1 hs1 =>
    by_cases e : t = t1
    · subst e; rw [ht] at ht1; cases ht1; exact absurd hs1 (hns _ _ _ _ _ hr1)
    · exact ⟨r, by simp only [setTh_other _ _ e]; exact ht, rfl⟩
  case futexBlock t1 r1 _ _ _ _ _ _ _ _ _ ht1 _ _ _ _ _ _ => exact hs r1 ht1 _ rfl
  case futexAgain t1 r1 _ _ _ _ _ _ _ _ _ ht1 _ _ _ _ _ _ => exact hs r1 ht1 _ rfl
  case futexWake t1 r1 s1 a op n args k ch ws _ ht1 _ _ _ _ =>
    by_cases e : t = t1
    · subst e; exact ⟨_, setTh_same _ _ _, by rw [ht] at ht1; cases ht1; rfl⟩
    · simp only [setTh_other _ _ e]; exact hw _ _ _ ht
  case spurious t1 r1 _ _ _ ht1 _ => exact hs r1 ht1 _ rfl
  case clone t1 r1 _ _ _ _ _ _ _ _ _ t' _ ht1 _ _ _ hfresh _ _ _ =>
    have : t ≠ t' := fun e => by rw [e, hfresh] at ht; cases ht
    simp only [setTh_other _ _ this]; exact hs r1 ht1 _ rfl
  case exitClear t1 r1 _ _ _ _ _ _ ws _ ht1 _ _ _ _ _ _ =>
    obtain ⟨r', h1, h2⟩ := hs r1 ht1 { r1 with st := .exited } rfl
    obtain ⟨r'', h3, h4⟩ := hw _ ws r' h1
    exact ⟨r'', h3, h4.trans h2⟩
  case exitPlain t1 r1 _ _ _ _ _ _ ht1 _ _ _ => exact hs r1 ht1 _ rfl
  case exitGroup => exact ⟨r, ht, rfl⟩
  case base t1 r1 _ _ _ _ _ _ _ _ ht1 _ _ _ _ => exact hs r1 ht1 _ rfl

/-- **A `clone` child's thread pointer is the `tls` argument** (`CLONE_SETTLS`), and its
`clear_child_tid` is the `ctid` argument. -/
theorem clone_tp {C : PCfg I.St} {t : Nat} {r : TRec I.St} {s : I.St} {fl sp ptid ctid tls : Word}
    {args : List Word} {k : Word → I.St} {ch : I.St} {t' : Nat} (hl : C.status = none)
    (ht : C.th t = some r) (hr : r.st = .run s)
    (hs : I.step r.tp s (.sys nrClone (fl :: sp :: ptid :: ctid :: tls :: args) k ch))
    (hf : CloneOk fl) (hfresh : C.th t' = none) (h0 : 0 < t') (hmax : t' < pidMax)
    (hpt : (C.mem ptid.toNat).isSome) :
    ∃ C', PStep I base C C' ∧ C'.th t' = some ⟨.run ch, tls, some ctid.toNat⟩ ∧
      C'.mem ptid.toNat = some t' ∧ (∃ r', C'.th t = some r' ∧ r'.st = .run (k (BitVec.ofNat 64 t'))) := by
  have htt : t' ≠ t := fun e => by rw [e, ht] at hfresh; cases hfresh
  refine ⟨_, .clone hl ht hr hs hf hfresh h0 hmax hpt, setTh_same _ _ _, by simp [heapPut], ?_⟩
  exact ⟨{ r with st := .run (k (BitVec.ofNat 64 t')) },
    by simp only [setTh_other _ _ (Ne.symm htt), setTh_same], rfl⟩

/-! ## The single-threaded view -/

theorem solo_run {tid : Nat} {x : SoloCfg I.St} {C : PCfg I.St} (h : SoloRel tid x C)
    (hl : x.status = none) : ∃ r, C.th tid = some r ∧ r.tp = x.tp ∧ r.st = .run x.st := by
  obtain ⟨-, -, -, r, h1, h2, h3 | ⟨h3, -⟩⟩ := h
  · exact ⟨r, h1, h2, h3⟩
  · rw [hl] at h3; cases h3

theorem solo_upd {tid : Nat} {x : SoloCfg I.St} {C : PCfg I.St} {M : Heap} {st : Option Nat}
    (h : SoloRel tid x C) (r' : TRec I.St) (htp : r'.tp = x.tp)
    (y : SoloCfg I.St) (hm : y.mem = M) (hs : y.status = st) (hy : y.tp = x.tp)
    (hst : r'.st = .run y.st ∨ (y.status.isSome ∧ r'.st = .exited)) :
    SoloRel tid y ⟨setTh C.th tid r', M, st⟩ := by
  refine ⟨hm.symm, hs.symm, fun t ht => ?_, r', setTh_same _ _ _, by rw [htp, hy], hst⟩
  show setTh C.th tid r' t = none
  rw [setTh_other _ _ ht]; exact h.2.2.1 t ht

theorem no_live_solo {tid : Nat} {x : SoloCfg I.St} {C : PCfg I.St} (h : SoloRel tid x C)
    (r' : TRec I.St) (hr' : r'.st = .exited) : ¬ ∃ u, Live (setTh C.th tid r') u := by
  rintro ⟨u, r0, hu, hx⟩
  by_cases e : u = tid
  · subst e; rw [setTh_same] at hu; cases hu; rw [hr'] at hx; cases hx
  · rw [setTh_other _ _ e, h.2.2.1 u e] at hu; cases hu

/-- **Forward**: every single-threaded step is a process step. -/
theorem solo_fwd {tid : Nat} {x y : SoloCfg I.St} {C : PCfg I.St} (h : SoloRel tid x C)
    (hs : SoloStep I base tid x y) : ∃ C', PStep I base C C' ∧ SoloRel tid y C' := by
  have hst := h.2.1
  cases hs
  case tau s' hl hs =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs
    exact ⟨_, .tau (by rw [hst, hl]) hr hrun hs,
      solo_upd h { r with st := .run s' } htp { x with st := s' } h.1.symm hst.symm rfl
        (Or.inl rfl)⟩
  case mem l s' hl hs hp hc hok =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs; rw [← h.1] at hc hok
    refine ⟨_, .mem (by rw [hst, hl]) hr hrun hs hp hc hok, ?_⟩
    exact solo_upd h { r with st := .run s' } htp { x with st := s', mem := l.updH x.mem }
      (by simp [h.1]) hst.symm rfl (Or.inl rfl)
  case gettid args k ch hl hs =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs
    exact ⟨_, .gettid (by rw [hst, hl]) hr hrun hs,
      solo_upd h { r with st := .run (k (BitVec.ofNat 64 tid)) } htp
        { x with st := k (BitVec.ofNat 64 tid) } h.1.symm hst.symm rfl (Or.inl rfl)⟩
  case setTid args k ch hl hs hne =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs
    cases args with
    | nil => exact absurd rfl hne
    | cons a args =>
      exact ⟨_, .setTid (by rw [hst, hl]) hr hrun hs,
        solo_upd h { r with st := .run (k (BitVec.ofNat 64 tid)), ctid := some a.toNat } htp
          { x with st := k (BitVec.ofNat 64 tid) } h.1.symm hst.symm rfl (Or.inl rfl)⟩
  case exit code args k ch hl hs =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs
    have hnl := no_live_solo h { r with st := .exited } rfl
    refine ⟨_, .exitPlain (by rw [hst, hl]) hr hrun hs fun _ _ _ => hnl, ?_⟩
    rw [lastExit_none hnl]
    exact solo_upd h { r with st := .exited } htp { x with status := some (code.toNat % 256) }
      h.1.symm rfl rfl (Or.inr ⟨rfl, rfl⟩)
  case exitGroup code args k ch hl hs =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs
    exact ⟨_, .exitGroup (by rw [hst, hl]) hr hrun hs, h.1, rfl, h.2.2.1, r, hr, htp, Or.inl hrun⟩
  case base nr args k ch ret mem' hl hs hn hb =>
    obtain ⟨r, hr, htp, hrun⟩ := solo_run h hl
    rw [← htp] at hs; rw [← h.1] at hb
    exact ⟨_, .base (by rw [hst, hl]) hr hrun hs hn hb,
      solo_upd h { r with st := .run (k ret) } htp { x with st := k ret, mem := mem' } rfl
        hst.symm rfl (Or.inl rfl)⟩

/-- **Backward**: a process step of a single-threaded process whose thread requests no `clone`
or `futex` is a single-threaded step. -/
theorem solo_bwd {tid : Nat} {x : SoloCfg I.St} {C C' : PCfg I.St} (h : SoloRel tid x C)
    (hn : NoThreadSys I x.tp x.st) (hs : PStep I base C C') :
    ∃ y, SoloStep I base tid x y ∧ SoloRel tid y C' := by
  obtain ⟨hm, hst, hoth, -⟩ := id h
  -- the stepping thread is `tid`, running `x.st`
  have key : ∀ {t r}, C.status = none → C.th t = some r → tid = t ∧ x.status = none ∧
      r.tp = x.tp ∧ r.st = .run x.st := by
    intro t r hl ht
    by_cases e : t = tid
    · subst e
      have hx : x.status = none := by rw [← hst, hl]
      obtain ⟨r0, h0, htp, hrun⟩ := solo_run h hx
      rw [h0] at ht; cases ht
      exact ⟨rfl, hx, htp, hrun⟩
    · rw [hoth t e] at ht; cases ht
  cases hs
  case tau t r s s' hl ht hr hs =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact ⟨_, .tau hx hs, solo_upd h { r with st := .run s' } htp { x with st := s' } hm.symm
      hst.symm rfl (Or.inl rfl)⟩
  case mem t r s l s' hl ht hr hs hp hc hok =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs; rw [hm] at hc hok
    exact ⟨_, .mem hx hs hp hc hok, solo_upd h { r with st := .run s' } htp
      { x with st := s', mem := l.updH x.mem } (by simp [hm]) hst.symm rfl (Or.inl rfl)⟩
  case gettid t r s args k ch hl ht hr hs =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact ⟨_, .gettid hx hs, solo_upd h { r with st := .run (k (BitVec.ofNat 64 tid)) } htp
      { x with st := k (BitVec.ofNat 64 tid) } hm.symm hst.symm rfl (Or.inl rfl)⟩
  case setTid t r s a args k ch hl ht hr hs =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact ⟨_, .setTid hx hs (List.cons_ne_nil _ _),
      solo_upd h { r with st := .run (k (BitVec.ofNat 64 tid)), ctid := some a.toNat } htp
        { x with st := k (BitVec.ofNat 64 tid) } hm.symm hst.symm rfl (Or.inl rfl)⟩
  case futexBlock t r s a op v args k ch w hl ht hr hs _ _ _ _ =>
    obtain ⟨e, -, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact absurd rfl (hn _ _ _ _ hs).2.1
  case futexAgain t r s a op v args k ch w hl ht hr hs _ _ _ _ =>
    obtain ⟨e, -, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact absurd rfl (hn _ _ _ _ hs).2.1
  case futexWake t r s a op n args k ch ws hl ht hr hs _ _ =>
    obtain ⟨e, -, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact absurd rfl (hn _ _ _ _ hs).2.1
  case spurious t r a k hl ht hr =>
    obtain ⟨e, -, -, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun
  case clone t r s fl sp ptid ctid tls args k ch t' hl ht hr hs _ _ _ _ _ =>
    obtain ⟨e, -, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact absurd rfl (hn _ _ _ _ hs).1
  case exitClear t r s code args k ch a ws hl ht hr hs _ _ hlive _ =>
    obtain ⟨e, -, -, -⟩ := key hl ht; subst e
    exact absurd hlive (no_live_solo h _ rfl)
  case exitPlain t r s code args k ch hl ht hr hs hnc =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    refine ⟨_, .exit hx hs, ?_⟩
    rw [lastExit_none (no_live_solo h _ rfl)]
    exact solo_upd h { r with st := .exited } htp { x with status := some (code.toNat % 256) }
      hm.symm rfl rfl (Or.inr ⟨rfl, rfl⟩)
  case exitGroup t r s code args k ch hl ht hr hs =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs
    exact ⟨_, .exitGroup hx hs, hm, rfl, hoth, r, ht, htp, Or.inl hr⟩
  case base t r s nr args k ch ret mem' hl ht hr hs hnr hb =>
    obtain ⟨e, hx, htp, hrun⟩ := key hl ht; subst e
    rw [hr] at hrun; cases hrun; rw [htp] at hs; rw [hm] at hb
    exact ⟨_, .base hx hs hnr hb, solo_upd h { r with st := .run (k ret) } htp
      { x with st := k ret, mem := mem' } rfl hst.symm rfl (Or.inl rfl)⟩

theorem star_snoc {α : Type} {r : α → α → Prop} {a b c : α} (h : Star r a b) (h' : r b c) :
    Star r a c := by
  induction h with
  | refl => exact .step h' .refl
  | step h _ ih => exact .step h (ih h')

/-- The initial process of a single-threaded launch is its single-threaded view. -/
theorem solo_init (tid : Nat) (s : I.St) (tp : Word) (h : Heap) :
    SoloRel tid ⟨s, tp, h, none⟩ (PCfg.init tid s tp h) := by
  refine ⟨rfl, rfl, fun t ht => by simp [PCfg.init, ht], ⟨.run s, tp, none⟩, by simp [PCfg.init],
    rfl, Or.inl rfl⟩

/-- **Single-threaded processes are their single-threaded view**: if no reachable
single-threaded state requests `clone` or `futex`, the process reaches exactly the
configurations of the single-threaded machine (up to `SoloRel`). -/
theorem solo_reach {tid : Nat} {x0 : SoloCfg I.St} {C0 : PCfg I.St} (h0 : SoloRel tid x0 C0)
    (hn : ∀ x, Star (SoloStep I base tid) x0 x → NoThreadSys I x.tp x.st) {C : PCfg I.St}
    (hr : Star (PStep I base) C0 C) : ∃ x, Star (SoloStep I base tid) x0 x ∧ SoloRel tid x C := by
  suffices key : ∀ C1 C, Star (PStep I base) C1 C → ∀ x, Star (SoloStep I base tid) x0 x →
      SoloRel tid x C1 → ∃ y, Star (SoloStep I base tid) x0 y ∧ SoloRel tid y C from
    key _ _ hr _ .refl h0
  intro C1 C hr
  induction hr with
  | refl => intro x hx h; exact ⟨x, hx, h⟩
  | step hs _ ih =>
    intro x hx h
    obtain ⟨y, hy, h'⟩ := solo_bwd h (hn x hx) hs
    exact ih y (star_snoc hx hy) h'

end

end Silmaril.Proofs.X86.Concurrency.Cir.Proc
