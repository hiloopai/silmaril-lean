module

public import Silmaril.Process.Mt.Pthread.Glibc.Defs

/-!
# glibc's spin lock implements the spin-lock specification (proofs)

`sim`: every step of the spin-lock machine from a configuration that does not fault is
matched by no abstract step (an instruction before the linearization point, a failed
`lock decl`, a spin-loop load, a buffered store) or by one step of the specification (a
successful `lock decl`, an `xchg`, the flush of an unlock's store, an unlock's store under
`sc`), and keeps the lock-word invariant `SConf.Inv`. `reach` iterates it; `sound` is
`Csl.Model.Sound` for every client invariant.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Pthread.Spin

open Silmaril.Process.Mt.Csl
open Silmaril.Process.Mt.Pthread
open Silmaril.Process.Mt.Pthread.Glibc

/-- The most general client of the spin lock. -/
abbrev U : TIsa pstore := TIsa.mgc (S := pstore) spinSpec

theorem upd_eq_set {α : Type} (f : Nat → α) (a : Nat) (x : α) : Heap.upd f a x = Silmaril.Process.Mt.Pthread.set f a x :=
  rfl

/-- The fault predicate reads only the spin locks. -/
theorem fault_congr {t : Nat} {args : List Nat} {m m' : PSt} (h : m.spin = m'.spin) :
    spinSpec.fault t args m ↔ spinSpec.fault t args m' := by
  show (match spinOp args with | some sp => sp.fault t [arg args 1] m | none => True) ↔
    (match spinOp args with | some sp => sp.fault t [arg args 1] m' | none => True)
  have hcase : spinOp args = none ∨ spinOp args = some spinLock ∨ spinOp args = some spinTrylock ∨
      spinOp args = some spinUnlock := by
    unfold spinOp; split <;> simp
  rcases hcase with e | e | e | e <;> rw [e] <;> simp [spinLock, spinTrylock, spinUnlock, h]

theorem fault_lock {c : SConf} {t a : Nat} {rest : List (List Nat)} (h : absTh c t = some ([1, a] :: rest))
    (hf : ¬ c.Fault) : c.gh a ≠ .uninit ∧ c.gh a ≠ .held t := by
  have : ¬ (c.gh a = .uninit ∨ c.gh a = .held t) := fun e =>
    hf ⟨t, _, h, [1, a], rest, rfl, by simpa [spinSpec, spinOp, spinLock, arg] using e⟩
  exact ⟨fun e => this (Or.inl e), fun e => this (Or.inr e)⟩

theorem fault_try {c : SConf} {t a : Nat} {rest : List (List Nat)} (h : absTh c t = some ([2, a] :: rest))
    (hf : ¬ c.Fault) : c.gh a ≠ .uninit := fun e =>
  hf ⟨t, _, h, [2, a], rest, rfl, by simpa [spinSpec, spinOp, spinTrylock, arg] using e⟩

theorem fault_unlock {c : SConf} {t a : Nat} {rest : List (List Nat)} (h : absTh c t = some ([3, a] :: rest))
    (hf : ¬ c.Fault) : c.gh a = .held t := by
  by_contra e
  exact hf ⟨t, _, h, [3, a], rest, rfl, by simpa [spinSpec, spinOp, spinUnlock, arg] using e⟩

theorem absTh_of {c : SConf} {t : Nat} {p : List (List Nat) × Pc} (h : c.th t = some p) :
    absTh c t = some ((c.buf t).map (fun a => [3, a]) ++ p.1) := by
  simp [absTh, h]

/-- Moving thread `t` to another position with the same script keeps `absTh`. -/
theorem absTh_pc {c : SConf} {t : Nat} {s : List (List Nat)} {pc pc' : Pc} (h : c.th t = some (s, pc)) :
    absTh { c with th := setTh c t (s, pc') } = absTh c := by
  funext u
  by_cases e : u = t
  · subst e; simp [absTh, setTh, Heap.upd, h]
  · simp [absTh, setTh, Heap.upd, e]

/-- Thread `t` with an empty buffer finishing its current call. -/
theorem absTh_ret {c : SConf} {t : Nat} (hb : c.buf t = []) (x : List (List Nat) × Pc)
    (c' : SConf) (hth : c'.th = setTh c t x) (hbuf : c'.buf = c.buf) :
    absTh c' = Heap.upd (absTh c) t (some x.1) := by
  funext u
  by_cases e : u = t
  · subst e; simp [absTh, setTh, Heap.upd, hth, hbuf, hb]
  · simp [absTh, setTh, Heap.upd, hth, hbuf, e]

theorem inv_th {pol : Pol} {c : SConf} (hi : c.Inv pol) {t : Nat} (x : List (List Nat) × Pc) :
    ∀ u, setTh c t x u = none → c.buf u = [] := by
  intro u e
  by_cases h : u = t
  · subst h; simp [setTh, Heap.upd] at e
  · exact hi.2.1 u (by simpa [setTh, Heap.upd, h] using e)

/-- **The simulation.** -/
theorem sim {pol : Pol} {c c' : SConf} {C : Cfg U} (hf : ¬ c.Fault) (hs : SStep pol c c')
    (ha : (model pol).abs c C) : ∃ C', (C' = C ∨ Step U C C') ∧ (model pol).abs c' C' := by
  obtain ⟨hi, hth, hsp⟩ := ha
  obtain ⟨hk, hnb, hsc⟩ := hi
  cases hs with
  | enter h =>
    refine ⟨C, Or.inl rfl, ⟨hk, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, hsp⟩
    rw [absTh_pc h]; exact hth
  | @decOk t a rest h hb hv =>
    have hab : absTh c t = some ([1, a] :: rest) := by simp [absTh_of h, hb]
    obtain ⟨hu, -⟩ := fault_lock hab hf
    have hfree : c.gh a = .free := ((hk a hu).2).mp hv
    refine ⟨⟨Heap.upd C.th t (some rest), { C.mem with spin := Silmaril.Process.Mt.Pthread.set C.mem.spin a (.held t) }⟩,
      Or.inr (Step.atom (s := [1, a] :: rest) (by rw [hth]; exact hab) ⟨[1, a], 0, rfl, ?_⟩), ?_⟩
    · exact ⟨spinLock, rfl, by simp [spinLock, arg, hsp, hfree]⟩
    · refine ⟨⟨?_, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, ?_⟩
      · intro x hx
        by_cases e : x = a
        · subst e; simp [Heap.upd]
        · simpa [Heap.upd, e] using hk x (by simpa [Heap.upd, e] using hx)
      · funext u
        by_cases e : u = t
        · subst e; simp [absTh, setTh, Heap.upd, hb]; rfl
        · simp [absTh, setTh, Heap.upd, hth, e]; rfl
      · simp [hsp, upd_eq_set]
  | @decFail t a rest h hb hv =>
    refine ⟨C, Or.inl rfl, ⟨⟨?_, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, hsp⟩⟩
    · intro x hx
      by_cases e : x = a
      · subst e
        obtain ⟨h1, h2⟩ := hk x hx
        have hne : c.gh x ≠ .free := fun e => hv (h2.mpr e)
        simp [Heap.upd]
        exact ⟨by omega, fun e => absurd e (by omega), fun e => absurd e hne⟩
      · simpa [Heap.upd, e] using hk x hx
    · rw [hth]
      funext u
      by_cases e : u = t
      · subst e; simp [absTh, setTh, Heap.upd, h]
      · simp [absTh, setTh, Heap.upd, e]
  | spinRead h =>
    refine ⟨C, Or.inl rfl, ⟨hk, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, hsp⟩
    rw [absTh_pc h]; exact hth
  | @xchg t a rest h hb =>
    have hab : absTh c t = some ([2, a] :: rest) := by simp [absTh_of h, hb]
    have hu := fault_try hab hf
    by_cases hv : c.mem a = 1
    · have hfree : c.gh a = .free := ((hk a hu).2).mp hv
      refine ⟨⟨Heap.upd C.th t (some rest), { C.mem with spin := Silmaril.Process.Mt.Pthread.set C.mem.spin a (.held t) }⟩,
        Or.inr (Step.atom (s := [2, a] :: rest) (by rw [hth]; exact hab) ⟨[2, a], 0, rfl, ?_⟩), ?_⟩
      · exact ⟨spinTrylock, rfl, Or.inl (by simp [arg, hsp, hfree])⟩
      · refine ⟨⟨?_, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, ?_⟩
        · intro x hx
          by_cases e : x = a
          · subst e; simp [Heap.upd, hv]
          · simpa [hv, Heap.upd, e] using hk x (by simpa [hv, Heap.upd, e] using hx)
        · funext u
          by_cases e : u = t
          · subst e; simp [absTh, setTh, Heap.upd, hb]; rfl
          · simp [absTh, setTh, Heap.upd, hth, e]; rfl
        · simp [hsp, hv, upd_eq_set]
    · have hnf : c.gh a ≠ .free := fun e => hv (((hk a hu).2).mpr e)
      obtain ⟨u, hu'⟩ : ∃ u, c.gh a = .held u := by
        cases e : c.gh a with
        | uninit => exact absurd e hu
        | free => exact absurd e hnf
        | held u => exact ⟨u, rfl⟩
      refine ⟨⟨Heap.upd C.th t (some rest), C.mem⟩,
        Or.inr (Step.atom (s := [2, a] :: rest) (by rw [hth]; exact hab) ⟨[2, a], EBUSY, rfl, ?_⟩), ?_⟩
      · exact ⟨spinTrylock, rfl, Or.inr ⟨⟨u, by simp [arg, hsp, hu']⟩, rfl, rfl⟩⟩
      · refine ⟨⟨?_, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, ?_⟩
        · intro x hx
          by_cases e : x = a
          · subst e; simp [hv, Heap.upd, hu']
          · simpa [hv, Heap.upd, e] using hk x (by simpa [hv] using hx)
        · funext u
          by_cases e : u = t
          · subst e; simp [absTh, setTh, Heap.upd, hb]; rfl
          · simp [absTh, setTh, Heap.upd, hth, e]; rfl
        · simp [hsp, hv]
  | @storeSc t a rest hp h =>
    have hb : c.buf t = [] := hsc hp t
    have hab : absTh c t = some ([3, a] :: rest) := by simp [absTh_of h, hb]
    have hheld := fault_unlock hab hf
    refine ⟨⟨Heap.upd C.th t (some rest), { C.mem with spin := Silmaril.Process.Mt.Pthread.set C.mem.spin a .free }⟩,
      Or.inr (Step.atom (s := [3, a] :: rest) (by rw [hth]; exact hab) ⟨[3, a], 0, rfl, ?_⟩), ?_⟩
    · exact ⟨spinUnlock, rfl, by simp [spinUnlock, arg]⟩
    · refine ⟨⟨?_, inv_th ⟨hk, hnb, hsc⟩ _, hsc⟩, ?_, ?_⟩
      · intro x hx
        by_cases e : x = a
        · subst e; simp [Heap.upd]
        · simpa [Heap.upd, e] using hk x (by simpa [Heap.upd, e] using hx)
      · funext u
        by_cases e : u = t
        · subst e; simp [absTh, setTh, Heap.upd, hb]; rfl
        · simp [absTh, setTh, Heap.upd, hth, e]; rfl
      · simp [hsp, upd_eq_set]
  | @storeBuf t a rest hp h =>
    refine ⟨C, Or.inl rfl, ⟨⟨hk, ?_, fun e => by rw [hp] at e; cases e⟩, ?_, hsp⟩⟩
    · intro u e
      by_cases hu : u = t
      · subst hu; simp [setTh, Heap.upd] at e
      · simpa [Heap.upd, hu] using hnb u (by simpa [setTh, Heap.upd, hu] using e)
    · rw [hth]
      funext u
      by_cases e : u = t
      · subst e; simp [absTh, setTh, Heap.upd, h]
      · simp [absTh, setTh, Heap.upd, e]
  | @flush t a bs hp hb =>
    obtain ⟨p, hp'⟩ : ∃ p, c.th t = some p := by
      cases e : c.th t with
      | none => have := hnb t e; rw [hb] at this; cases this
      | some p => exact ⟨p, rfl⟩
    have hab : absTh c t = some ([3, a] :: (bs.map (fun a => [3, a]) ++ p.1)) := by
      simp [absTh_of hp', hb]
    have hheld := fault_unlock hab hf
    refine ⟨⟨Heap.upd C.th t (some (bs.map (fun a => [3, a]) ++ p.1)),
        { C.mem with spin := Silmaril.Process.Mt.Pthread.set C.mem.spin a .free }⟩,
      Or.inr (Step.atom (s := [3, a] :: (bs.map (fun a => [3, a]) ++ p.1)) (by rw [hth]; exact hab)
        ⟨[3, a], 0, rfl, ?_⟩), ?_⟩
    · exact ⟨spinUnlock, rfl, by simp [spinUnlock, arg]⟩
    · refine ⟨⟨?_, ?_, fun e => by rw [hp] at e; cases e⟩, ?_, ?_⟩
      · intro x hx
        by_cases e : x = a
        · subst e; simp [Heap.upd]
        · simpa [Heap.upd, e] using hk x (by simpa [Heap.upd, e] using hx)
      · intro u e
        by_cases hu : u = t
        · subst hu; rw [hp'] at e; cases e
        · simpa [Heap.upd, hu] using hnb u e
      · rw [hth]
        funext u
        by_cases e : u = t
        · subst e; simp [absTh, Heap.upd, hp']; rfl
        · simp [absTh, Heap.upd, e]; rfl
      · simp [hsp, upd_eq_set]

/-- A faulting machine configuration stands for a faulting abstract one. -/
theorem fault_abs {pol : Pol} {c : SConf} {C : Cfg U} (ha : (model pol).abs c C) (hf : c.Fault) :
    Fault U C := by
  obtain ⟨t, s, hs, args, rest, rfl, hfa⟩ := hf
  refine ⟨t, args :: rest, by rw [ha.2.1]; exact hs, Or.inr ⟨args, rest, rfl, ?_⟩⟩
  exact (fault_congr (by simp [ha.2.2])).mp hfa

/-- **Runs of the machine are runs of the specification.** -/
theorem reach {pol : Pol} {c₀ c : SConf} (r : Star (model pol).step c₀ c) :
    ∀ {C₀ : Cfg U}, (model pol).abs c₀ C₀ →
      ∃ C, Reach U C₀ C ∧ (model pol).abs c C ∧ ((model pol).fault c → Fault U C) := by
  induction r with
  | refl => intro C₀ ha; exact ⟨C₀, Star.refl, ha, fault_abs ha⟩
  | step h _ ih =>
    intro C₀ ha
    obtain ⟨C₁, h₁, ha₁⟩ := sim h.1 h.2 ha
    obtain ⟨C, hr, hac, hfc⟩ := ih ha₁
    refine ⟨C, ?_, hac, hfc⟩
    rcases h₁ with rfl | hst
    · exact hr
    · exact Star.step hst hr

/-- **glibc 2.39's spin lock implements the spin-lock specification** under `pol`. -/
theorem sound (pol : Pol) (I : HProp Unit Unit) (Q : Nat → U.St → Heap Unit Unit → Prop) :
    (model pol).Sound I Q := by
  intro c₀ c C₀ ha _ r
  exact reach r ha

end Silmaril.Proofs.Process.Mt.Pthread.Spin
