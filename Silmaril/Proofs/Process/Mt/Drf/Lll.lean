module

public import Silmaril.Process.Mt.Drf.Prim.Defs

/-!
# glibc's `lll_lock` mutex is correct under TSO and XL

A stuttering forward simulation of the implemented client (`Client.withImpl Glibc.mutexImpl`)
by the client with atomic mutex steps (`Client.withSpec (Glibc.mutexSpec locks)`), under the same
model `M`, step by step:

* buffers are equal: the implementations make no plain writes;
* memory is related by `absMem` (a held word is `1`);
* a thread inside `lll_lock` is at its caller's state until its `cmpxchg` or `xchg` reads `0`
  (the linearisation point), then at the continuation; a thread inside `lll_unlock` is at its
  caller's state until its `xchg 0`, then at the continuation.

Client steps and flushes map to themselves (the client and its buffers avoid lock words), the
linearising steps map to the atomic primitive step, and all other implementation steps stutter.
The client's precondition (`Client.CallsOk`) gives the lock word's lock-ness at the call and,
for `lll_unlock`, that the word is held at the `xchg 0`.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Drf.Lll

open Silmaril.Process.Mt.Drf
open Silmaril.Process.Mt.Drf.Glibc

theorem star_tail {α : Type} {r : α → α → Prop} {a b c : α} (h : Star r a b) (h' : r b c) :
    Star r a c := by
  induction h with
  | refl => exact Star.step h' Star.refl
  | step h _ ih => exact Star.step h (ih h')

theorem upd_eq_self {α : Type} {f : Nat → α} {t : Nat} {x : α} (h : f t = x) : upd f t x = f := by
  funext u; by_cases hu : u = t
  · subst hu; simp [upd, h]
  · simp [upd, hu]

theorem upd_same {α : Type} (f : Nat → α) (t : Nat) (x : α) : upd f t x t = x := by
  simp [upd]

theorem upd_ne {α : Type} {f : Nat → α} {t u : Nat} {x : α} (h : u ≠ t) : upd f t x u = f u := by
  simp [upd, h]

theorem set_self (m : Mem) (a : Nat) : m.set a (m a) = m := by
  funext x; by_cases hx : x = a
  · subst hx; simp [Mem.set]
  · simp [Mem.set, hx]

theorem step_eq {S : Sys} {M : Model} {N : Nat} {C D D' : BCfg S} (h : BStep M S N C D)
    (e : D' = D) : BStep M S N C D' := e ▸ h

theorem bcfg_ext {S : Sys} {C D : BCfg S} (h1 : C.ts = D.ts) (h2 : C.mem = D.mem)
    (h3 : C.buf = D.buf) : C = D := by
  cases C; cases D; simp only at h1 h2 h3; subst h1 h2 h3; rfl

/-! ## `absMem` -/

section
variable (locks : Nat → Bool)

theorem absMem_set_free {m : Mem} {a v : Nat} (ha : locks a = false) :
    absMem locks (m.set a v) = (absMem locks m).set a v := by
  funext x; by_cases hx : x = a
  · subst hx; simp [absMem, Mem.set, ha]
  · simp [absMem, Mem.set, hx]

theorem absMem_write_free {m : Mem} {ws : List (Nat × Nat)} (h : ∀ p ∈ ws, locks p.1 = false) :
    absMem locks (m.write ws) = (absMem locks m).write ws := by
  induction ws generalizing m with
  | nil => rfl
  | cons p ws ih =>
    simp only [Mem.write]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      absMem_set_free locks (h p List.mem_cons_self)]

theorem absMem_set_lock {m : Mem} {a v : Nat} (ha : locks a = true) :
    absMem locks (m.set a v) = (absMem locks m).set a (min v 1) := by
  funext x; by_cases hx : x = a
  · subst hx; simp [absMem, Mem.set, ha]
  · simp [absMem, Mem.set, hx]

theorem absMem_free {m : Mem} {a : Nat} (ha : locks a = false) : absMem locks m a = m a := by
  simp [absMem, ha]

theorem absMem_lock {m : Mem} {a : Nat} (ha : locks a = true) :
    absMem locks m a = min (m a) 1 := by
  simp [absMem, ha]

end

/-! ## Inversion of the implemented client's steps -/

theorem iloc_inv {cl : Client} {I : Nat → PrimImpl} {t : Nat} {x : IState cl I} {l : Lab}
    {y : IState cl I} (h : ILoc cl I t x l y) :
    (∃ s s', x = .cl s ∧ y = .cl s' ∧ cl.loc t s l s') ∨
    (∃ s p args k, x = .cl s ∧ l = .plain [] [] false ∧
      y = .inPrim p ((I p).start t args) s k ∧ cl.call t s p args k) ∨
    (∃ p s s' c k, x = .inPrim p s c k ∧ y = .inPrim p s' c k ∧ (I p).loc t s l s') ∨
    (∃ p s c k r, x = .inPrim p s c k ∧ l = .plain [] [] false ∧ y = .cl (k r) ∧
      (I p).ret s = some r) := by
  cases h with
  | cl h => exact Or.inl ⟨_, _, rfl, rfl, h⟩
  | call h => exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, rfl, h⟩)
  | prim h => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, h⟩))
  | ret h => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl, rfl, rfl, h⟩))

theorem isync_inv {cl : Client} {I : Nat → PrimImpl} {t : Nat} {ts : Nat → IState cl I}
    {rs ws : List (Nat × Nat)} {ts' : Nat → IState cl I} (h : ISync cl I t ts rs ws ts') :
    (∃ cts cts', (ts t).isCl = true ∧ (∀ u, (ts u).isCl = true → ts u = .cl (cts u)) ∧
      (∀ fill, cl.sync t (IState.fill ts cts fill) rs ws (IState.fill ts cts' fill)) ∧
      ts' = fun u => if (ts u).isCl then .cl (cts' u) else ts u) ∨
    (∃ p s c k s', ts t = .inPrim p s c k ∧ (I p).sync t s rs ws s' ∧
      ts' = upd ts t (.inPrim p s' c k)) := by
  cases h with
  | cl ht hcl h => exact Or.inl ⟨_, _, ht, hcl, h, rfl⟩
  | prim hts h => exact Or.inr ⟨_, _, _, _, _, hts, h, rfl⟩

/-! ## The simulation -/

/-- After the linearisation point. -/
def lin : Nat → PSt → Bool
  | 0, s => s.pc == 3
  | 1, s => s.pc == 1 || s.pc == 2
  | _, _ => false

/-- The abstract state of a thread. -/
def α {cl : Client} : IState cl mutexImpl → cl.St
  | .cl s => s
  | .inPrim p s c k => if lin p s then k 0 else c

theorem α_upd {cl : Client} (ts : Nat → IState cl mutexImpl) (t : Nat) (x : IState cl mutexImpl) :
    (fun u => α (upd ts t x u)) = upd (fun u => α (ts u)) t (α x) := by
  funext u; by_cases hu : u = t
  · subst hu; simp [upd]
  · simp [upd, hu]

/-- The abstract configuration. -/
def abst (locks : Nat → Bool) {cl : Client} (C : BCfg (cl.withImpl mutexImpl)) :
    BCfg (cl.withSpec (mutexSpec locks)) :=
  ⟨fun u => α (C.ts u), absMem locks C.mem, C.buf⟩

/-- What a thread inside a primitive knows. -/
def InPrimOk (locks : Nat → Bool) (cl : Client) (u p : Nat) (s : PSt) (c : cl.St)
    (k : Nat → cl.St) : Prop :=
  (p = 0 ∧ locks s.l = true ∧ (s.pc = 3 ∨ (s.pc < 3 ∧ cl.call u c 0 [s.l] k))) ∨
  (p = 1 ∧ locks s.l = true ∧ (s.pc = 1 ∨ s.pc = 2 ∨ (s.pc = 0 ∧ cl.call u c 1 [s.l] k)))

/-- The simulation invariant. -/
structure Inv (locks : Nat → Bool) (cl : Client) (C : BCfg (cl.withImpl mutexImpl)) : Prop where
  buf : ∀ u a v w, Ent.st a v w ∈ C.buf u → locks a = false
  prim : ∀ u p (s : PSt) c k, C.ts u = .inPrim p s c k → InPrimOk locks cl u p s c k

variable {locks : Nat → Bool} {cl : Client} {M : Model} {N : Nat}
  {D0 : Cfg (cl.withSpec (mutexSpec locks))}

theorem lin_start (p : Nat) (args : List Nat) : lin p (pstart args) = false := by
  unfold pstart; split <;> rcases p with _ | _ | p <;> simp [lin]

/-! ## Helpers -/

theorem mem_upd {b : Nat → List Ent} {t u : Nat} {l : List Ent} {e : Ent} (he : e ∈ upd b t l u) :
    (u = t ∧ e ∈ l) ∨ (u ≠ t ∧ e ∈ b u) := by
  by_cases hu : u = t
  · subst hu; exact Or.inl ⟨rfl, by simpa [upd] using he⟩
  · exact Or.inr ⟨hu, by simpa [upd, hu] using he⟩

theorem eq_upd {β : Type} {f : Nat → β} {t u : Nat} {x y : β} (h : upd f t x u = y) :
    (u = t ∧ x = y) ∨ (u ≠ t ∧ f u = y) := by
  by_cases hu : u = t
  · subst hu; exact Or.inl ⟨rfl, by simpa [upd] using h⟩
  · exact Or.inr ⟨hu, by simpa [upd, hu] using h⟩

theorem ts_upd (ts : Nat → IState cl mutexImpl) (t : Nat) (x : IState cl mutexImpl) (y : cl.St)
    (hx : α x = y) : (fun u => α (upd ts t x u)) = upd (fun u => α (ts u)) t y := by
  subst hx; exact α_upd ts t x

theorem ts_upd_self (ts : Nat → IState cl mutexImpl) (t : Nat) (x : IState cl mutexImpl)
    (hx : α x = α (ts t)) : (fun u => α (upd ts t x u)) = fun u => α (ts u) := by
  rw [ts_upd ts t x _ hx]; exact upd_eq_self rfl

theorem buf_nil (b : Nat → List Ent) (t : Nat) : upd b t (b t ++ ents [] false) = b :=
  upd_eq_self (by simp [ents])

theorem inv_cl_upd {C : BCfg (cl.withImpl mutexImpl)} (hI : Inv locks cl C) {t : Nat} {s : cl.St}
    {mem : Mem} {buf : Nat → List Ent} (hbuf : ∀ u a v w, Ent.st a v w ∈ buf u → locks a = false) :
    Inv locks cl ⟨upd C.ts t (IState.cl s), mem, buf⟩ := by
  refine ⟨hbuf, fun u p s' c k hu => ?_⟩
  rcases eq_upd hu with ⟨-, h⟩ | ⟨-, h⟩
  · cases h
  · exact hI.prim _ _ _ _ _ h

theorem inv_prim_upd {C : BCfg (cl.withImpl mutexImpl)} (hI : Inv locks cl C) {t p : Nat}
    {s : PSt} {c : cl.St} {k : Nat → cl.St} (hok : InPrimOk locks cl t p s c k) {mem : Mem}
    {buf : Nat → List Ent} (hbuf : ∀ u a v w, Ent.st a v w ∈ buf u → locks a = false) :
    Inv locks cl ⟨upd C.ts t (IState.inPrim p s c k), mem, buf⟩ := by
  refine ⟨hbuf, fun u p' s' c' k' hu => ?_⟩
  rcases eq_upd hu with ⟨rfl, h⟩ | ⟨-, h⟩
  · cases h; exact hok
  · exact hI.prim _ _ _ _ _ h

theorem mutexSync_inv {p : Nat} {s : PSt} {rs ws : List (Nat × Nat)} {s' : PSt}
    (h : MutexSync p s rs ws s') :
    (p = 0 ∧ LllLock 0 3 s rs ws s') ∨ (p = 1 ∧ LllUnlock 0 2 s rs ws s') := by
  cases h with
  | lock h => exact Or.inl ⟨rfl, h⟩
  | unlock h => exact Or.inr ⟨rfl, h⟩

theorem lllLock_inv {b n : Nat} {s : PSt} {rs ws : List (Nat × Nat)} {s' : PSt}
    (h : LllLock b n s rs ws s') :
    (s.pc = b ∧ ∃ v, rs = [(s.l, v)] ∧ ws = [(s.l, if v = 0 then 1 else v)] ∧
      s' = ⟨if v = 0 then n else b + 1, s.l⟩) ∨
    (s.pc = b + 1 ∧ ∃ v, rs = [(s.l, v)] ∧ ws = [(s.l, 2)] ∧
      s' = ⟨if v = 0 then n else b + 2, s.l⟩) ∨
    (s.pc = b + 2 ∧ rs = [] ∧ ws = [] ∧ s' = ⟨b + 1, s.l⟩) := by
  cases h with
  | cas h => exact Or.inl ⟨h, _, rfl, rfl, rfl⟩
  | xchg h => exact Or.inr (Or.inl ⟨h, _, rfl, rfl, rfl⟩)
  | wait h => exact Or.inr (Or.inr ⟨h, rfl, rfl, rfl⟩)

theorem lllUnlock_inv {b n : Nat} {s : PSt} {rs ws : List (Nat × Nat)} {s' : PSt}
    (h : LllUnlock b n s rs ws s') :
    (s.pc = b ∧ ∃ v, rs = [(s.l, v)] ∧ ws = [(s.l, 0)] ∧
      s' = ⟨if 1 < v then b + 1 else n, s.l⟩) ∨
    (s.pc = b + 1 ∧ rs = [] ∧ ws = [] ∧ s' = ⟨n, s.l⟩) := by
  cases h with
  | xchg h => exact Or.inl ⟨h, _, rfl, rfl, rfl⟩
  | wake h => exact Or.inr ⟨h, rfl, rfl, rfl⟩

theorem iloc_inv_m {t : Nat} {x : IState cl mutexImpl} {l : Lab} {y : IState cl mutexImpl}
    (h : ILoc cl mutexImpl t x l y) :
    (∃ s s', x = .cl s ∧ y = .cl s' ∧ cl.loc t s l s') ∨
    (∃ s p args k, x = .cl s ∧ l = .plain [] [] false ∧
      y = .inPrim p (pstart args) s k ∧ cl.call t s p args k) ∨
    (∃ (p : Nat) (s : PSt) (c : cl.St) (k : Nat → cl.St) (r : Nat), x = .inPrim p s c k ∧
      l = .plain [] [] false ∧ y = .cl (k r) ∧
      mutexRet p s = some r) := by
  rcases iloc_inv h with h | h | ⟨p, s, s', c, k, -, -, h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact (h : False).elim
  · exact Or.inr (Or.inr h)

theorem isync_inv_m {t : Nat} {ts : Nat → IState cl mutexImpl} {rs ws : List (Nat × Nat)}
    {ts' : Nat → IState cl mutexImpl} (h : ISync cl mutexImpl t ts rs ws ts') :
    (∃ cts cts', (ts t).isCl = true ∧ (∀ u, (ts u).isCl = true → ts u = .cl (cts u)) ∧
      (∀ fill, cl.sync t (IState.fill ts cts fill) rs ws (IState.fill ts cts' fill)) ∧
      ts' = fun u => if (ts u).isCl then .cl (cts' u) else ts u) ∨
    (∃ (p : Nat) (s : PSt) (c : cl.St) (k : Nat → cl.St) (s' : PSt), ts t = .inPrim p s c k ∧
      MutexSync p s rs ws s' ∧
      ts' = upd ts t (.inPrim p s' c k)) := by
  rcases isync_inv h with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- A linearising step of thread `t` inside a primitive is the primitive's atomic step. -/
theorem lin_step {C : BCfg (cl.withImpl mutexImpl)} {t p : Nat} {s0 s1 : PSt} {c : cl.St}
    {k : Nat → cl.St} (ht : t < N) (hts : C.ts t = .inPrim p s0 c k) (hl0 : lin p s0 = false)
    (hl1 : lin p s1 = true) (he : C.buf t = []) {rsa wsa : List (Nat × Nat)}
    (hcall : cl.call t c p [s0.l] k) (hspec : (mutexSpec locks p).step t [s0.l] rsa wsa 0)
    (hreads : (absMem locks C.mem).Reads rsa) {mem' : Mem}
    (hmem : absMem locks mem' = (absMem locks C.mem).write wsa) :
    BStep M (cl.withSpec (mutexSpec locks)) N (abst locks C)
      (abst locks ⟨upd C.ts t (IState.inPrim p s1 c k), mem', C.buf⟩) := by
  have hcall' : cl.call t ((abst locks C).ts t) p [s0.l] k := by
    show cl.call t (α (C.ts t)) p [s0.l] k
    rw [hts]; simpa [α, hl0] using hcall
  exact step_eq (BStep.sync (C := abst locks C) ht (Or.inr ⟨p, [s0.l], k, 0, hcall', hspec, rfl⟩)
    he hreads) (bcfg_ext (ts_upd C.ts t _ (k 0) (by simp [α, hl1])) hmem rfl)

/-- A non-linearising step of thread `t` inside a primitive stutters. -/
theorem stut {C : BCfg (cl.withImpl mutexImpl)} {t p : Nat} {s0 s1 : PSt} {c : cl.St}
    {k : Nat → cl.St} (hts : C.ts t = .inPrim p s0 c k) (hl : lin p s1 = lin p s0) {mem' : Mem}
    (hmem : absMem locks mem' = absMem locks C.mem) :
    abst locks ⟨upd C.ts t (IState.inPrim p s1 c k), mem', C.buf⟩ = abst locks C :=
  bcfg_ext (ts_upd_self C.ts t _ (by rw [hts]; simp [α, hl])) hmem rfl

/-- **One step.** -/
theorem step (hav : cl.Avoids (fun a => locks a = true))
    (hok : cl.CallsOk (mutexSpec locks) M N D0) {C C' : BCfg (cl.withImpl mutexImpl)}
    (hI : Inv locks cl C) (hr : BReach M (cl.withSpec (mutexSpec locks)) N D0.toB (abst locks C))
    (h : BStep M (cl.withImpl mutexImpl) N C C') :
    Inv locks cl C' ∧
      (BStep M (cl.withSpec (mutexSpec locks)) N (abst locks C) (abst locks C') ∨
        abst locks C' = abst locks C) := by
  cases h with
  | @plain t rs ws w s' ht hs hrd =>
    change ILoc cl mutexImpl t (C.ts t) (.plain rs ws w) s' at hs
    rcases iloc_inv_m hs with ⟨s0, s1, hct, rfl, h⟩ | ⟨s0, p, args, k, hct, hl, rfl, h⟩ |
      ⟨p, s0, c, k, r, hct, hl, rfl, h⟩
    · -- a client step
      have hfree : ∀ a ∈ (Lab.plain rs ws w).addrs, locks a = false := fun a ha => by
        simpa using hav.1 _ _ _ _ h a ha
      refine ⟨inv_cl_upd hI (fun u a v w' he => ?_), Or.inl ?_⟩
      · rcases mem_upd he with ⟨rfl, he⟩ | ⟨-, he⟩
        · rcases List.mem_append.1 he with he | he
          · exact hI.buf _ _ _ _ he
          · simp only [ents, List.mem_map] at he
            obtain ⟨q, hq, hqe⟩ := he
            cases hqe
            exact hfree _ (List.mem_append_right _ (List.mem_map_of_mem hq))
        · exact hI.buf _ _ _ _ he
      · have hs' : (cl.withSpec (mutexSpec locks)).loc t ((abst locks C).ts t) (.plain rs ws w)
            s1 := by
          show cl.loc t (α (C.ts t)) _ s1
          rw [hct]; exact h
        have hreads : (view (abst locks C).mem ((abst locks C).buf t)).Reads rs := by
          intro p hp
          have hp' : locks p.1 = false :=
            hfree p.1 (List.mem_append_left _ (List.mem_map_of_mem hp))
          have := hrd p hp
          simpa [view, abst, absMem_free locks hp'] using this
        exact step_eq (BStep.plain ht hs' hreads) (bcfg_ext (ts_upd C.ts t _ s1 rfl) rfl rfl)
    · -- a call
      obtain ⟨rfl, rfl, rfl⟩ : rs = [] ∧ ws = [] ∧ w = false := by simpa using hl
      have hcall : cl.call t ((abst locks C).ts t) p args k := by
        show cl.call t (α (C.ts t)) p args k
        rw [hct]; exact h
      have hpre := hok _ hr t ht p args k hcall
      have hok' : InPrimOk locks cl t p (pstart args) s0 k := by
        rcases p with _ | _ | p
        · obtain ⟨l, rfl, hl⟩ := hpre
          exact Or.inl ⟨rfl, hl, Or.inr ⟨by simp [pstart], h⟩⟩
        · obtain ⟨l, rfl, hl, -⟩ := hpre
          exact Or.inr ⟨rfl, hl, Or.inr (Or.inr ⟨rfl, h⟩)⟩
        · exact hpre.elim
      refine ⟨inv_prim_upd hI hok' (fun u a v w' he =>
        hI.buf u a v w' (by rw [← buf_nil C.buf t]; exact he)), Or.inr ?_⟩
      refine bcfg_ext (ts_upd_self C.ts t _ ?_) rfl (buf_nil C.buf t)
      rw [hct]
      show (if lin p (pstart args) then k 0 else s0) = s0
      rw [lin_start]; rfl
    · -- a return
      obtain ⟨rfl, rfl, rfl⟩ : rs = [] ∧ ws = [] ∧ w = false := by simpa using hl
      have hlin : lin p s0 = true ∧ r = 0 := by
        rcases p with _ | _ | p <;> simp only [mutexRet] at h
        · split at h
          · next hpc => cases h; exact ⟨by simp [lin, hpc], rfl⟩
          · cases h
        · split at h
          · next hpc => cases h; exact ⟨by simp [lin, hpc], rfl⟩
          · cases h
        · cases h
      refine ⟨inv_cl_upd hI (fun u a v w' he =>
        hI.buf u a v w' (by rw [← buf_nil C.buf t]; exact he)), Or.inr ?_⟩
      exact bcfg_ext (ts_upd_self C.ts t _ (by rw [hct]; simp [α, hlin.1, hlin.2])) rfl
        (buf_nil C.buf t)
  | @sfence t s' ht hs =>
    change ILoc cl mutexImpl t (C.ts t) .sfence s' at hs
    rcases iloc_inv_m hs with ⟨s0, s1, hct, rfl, h⟩ | ⟨s0, p, args, k, hct, hl, rfl, h⟩ |
      ⟨p, s0, c, k, r, hct, hl, rfl, h⟩
    · refine ⟨inv_cl_upd hI (fun u a v w' he => ?_), Or.inl ?_⟩
      · rcases mem_upd he with ⟨rfl, he⟩ | ⟨-, he⟩
        · rcases List.mem_append.1 he with he | he
          · exact hI.buf _ _ _ _ he
          · simp at he
        · exact hI.buf _ _ _ _ he
      · have hs' : (cl.withSpec (mutexSpec locks)).loc t ((abst locks C).ts t) .sfence s1 := by
          show cl.loc t (α (C.ts t)) _ s1
          rw [hct]; exact h
        exact step_eq (BStep.sfence ht hs') (bcfg_ext (ts_upd C.ts t _ s1 rfl) rfl rfl)
    · cases hl
    · cases hl
  | @sync t rs ws ts' ht hs he hrd =>
    change ISync cl mutexImpl t C.ts rs ws ts' at hs
    rcases isync_inv_m hs with ⟨cts, cts', hti, hcl, h, rfl⟩ | ⟨p, s0, c, k, s1, hts, h, rfl⟩
    · -- a client synchronising step
      have hfill : IState.fill C.ts cts (fun u => α (C.ts u)) = fun u => α (C.ts u) := by
        funext u; unfold IState.fill; split
        · next hu => rw [hcl u hu]; rfl
        · rfl
      have hfill' : IState.fill C.ts cts' (fun u => α (C.ts u)) =
          fun u => α (if (C.ts u).isCl then IState.cl (cts' u) else C.ts u) := by
        funext u; unfold IState.fill
        by_cases hu : (C.ts u).isCl = true <;> simp [hu, α]
      have h' := h (fun u => α (C.ts u))
      rw [hfill, hfill'] at h'
      have hfree : ∀ p ∈ rs ++ ws, locks p.1 = false := fun p hp => by
        simpa using hav.2 _ _ _ _ _ h' p hp
      have hreads : (abst locks C).mem.Reads rs := by
        intro p hp
        show absMem locks C.mem p.1 = p.2
        rw [absMem_free locks (hfree p (List.mem_append_left _ hp))]
        exact hrd p hp
      refine ⟨⟨hI.buf, fun u p s c k hu => ?_⟩, Or.inl ?_⟩
      · dsimp only at hu
        generalize hb : (C.ts u).isCl = b at hu
        cases b
        · exact hI.prim _ _ _ _ _ hu
        · cases hu
      · exact step_eq (BStep.sync (C := abst locks C) ht (Or.inl h') he hreads)
          (bcfg_ext rfl (absMem_write_free locks (fun p hp => hfree p (List.mem_append_right _ hp)))
            rfl)
    · -- a step inside a primitive
      have hip := hI.prim t p s0 c k hts
      rcases mutexSync_inv h with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
      · -- `lll_lock`
        have ⟨hl, hpc⟩ : locks s0.l = true ∧
            (s0.pc = 3 ∨ (s0.pc < 3 ∧ cl.call t c 0 [s0.l] k)) := by
          rcases hip with ⟨-, hl, hpc⟩ | ⟨h01, -⟩
          · exact ⟨hl, hpc⟩
          · exact absurd h01 (by decide)
        rcases lllLock_inv hm with ⟨hpc0, v, rfl, rfl, rfl⟩ | ⟨hpc1, v, rfl, rfl, rfl⟩ |
          ⟨hpc2, rfl, rfl, rfl⟩
        · have hcall : cl.call t c 0 [s0.l] k := by
            rcases hpc with h3 | ⟨-, hc⟩
            · omega
            · exact hc
          have hv : C.mem s0.l = v := hrd _ List.mem_cons_self
          by_cases hv0 : v = 0
          · subst hv0
            refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inl ?_⟩
            · exact Or.inl ⟨rfl, hl, Or.inl (by simp)⟩
            refine lin_step ht hts (by simp [lin, hpc0]) (by simp [lin]) he hcall
              (⟨s0.l, rfl, rfl, rfl, rfl⟩ : (mutexSpec locks 0).step t [s0.l] [(s0.l, 0)]
                [(s0.l, 1)] 0) ?_ ?_
            · intro q hq
              simp only [List.mem_singleton] at hq
              subst hq
              show absMem locks C.mem s0.l = 0
              rw [absMem_lock locks hl, hv]; rfl
            · show absMem locks (C.mem.set s0.l (if 0 = 0 then 1 else 0)) =
                (absMem locks C.mem).set s0.l 1
              rw [absMem_set_lock locks hl]; rfl
          · refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inr ?_⟩
            · exact Or.inl ⟨rfl, hl, Or.inr ⟨by simp [hv0], hcall⟩⟩
            refine stut hts (by simp [lin, hv0, hpc0]) ?_
            show absMem locks (C.mem.set s0.l (if v = 0 then 1 else v)) = absMem locks C.mem
            simp only [hv0, ite_false]
            rw [← hv, set_self]
        · have hcall : cl.call t c 0 [s0.l] k := by
            rcases hpc with h3 | ⟨-, hc⟩
            · omega
            · exact hc
          have hv : C.mem s0.l = v := hrd _ List.mem_cons_self
          by_cases hv0 : v = 0
          · subst hv0
            refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inl ?_⟩
            · exact Or.inl ⟨rfl, hl, Or.inl (by simp)⟩
            refine lin_step ht hts (by simp [lin, hpc1]) (by simp [lin]) he hcall
              (⟨s0.l, rfl, rfl, rfl, rfl⟩ : (mutexSpec locks 0).step t [s0.l] [(s0.l, 0)]
                [(s0.l, 1)] 0) ?_ ?_
            · intro q hq
              simp only [List.mem_singleton] at hq
              subst hq
              show absMem locks C.mem s0.l = 0
              rw [absMem_lock locks hl, hv]; rfl
            · show absMem locks (C.mem.set s0.l 2) = (absMem locks C.mem).set s0.l 1
              rw [absMem_set_lock locks hl]; rfl
          · refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inr ?_⟩
            · exact Or.inl ⟨rfl, hl, Or.inr ⟨by simp [hv0], hcall⟩⟩
            refine stut hts (by simp [lin, hv0, hpc1]) ?_
            show absMem locks (C.mem.set s0.l 2) = absMem locks C.mem
            have h1 : absMem locks C.mem s0.l = 1 := by
              rw [absMem_lock locks hl, hv]; omega
            rw [absMem_set_lock locks hl, show min 2 1 = 1 from rfl, ← h1, set_self]
        · have hcall : cl.call t c 0 [s0.l] k := by
            rcases hpc with h3 | ⟨-, hc⟩
            · omega
            · exact hc
          refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inr ?_⟩
          · exact Or.inl ⟨rfl, hl, Or.inr ⟨by simp, hcall⟩⟩
          · exact stut hts (by simp [lin, hpc2]) rfl
      · -- `lll_unlock`
        have ⟨hl, hpc⟩ : locks s0.l = true ∧
            (s0.pc = 1 ∨ s0.pc = 2 ∨ (s0.pc = 0 ∧ cl.call t c 1 [s0.l] k)) := by
          rcases hip with ⟨h01, -⟩ | ⟨-, hl, hpc⟩
          · exact absurd h01 (by decide)
          · exact ⟨hl, hpc⟩
        rcases lllUnlock_inv hm with ⟨hpc0, v, rfl, rfl, rfl⟩ | ⟨hpc1, rfl, rfl, rfl⟩
        · have hcall : cl.call t c 1 [s0.l] k := by
            rcases hpc with h1 | h2 | ⟨-, hc⟩
            · omega
            · omega
            · exact hc
          have hcall' : cl.call t ((abst locks C).ts t) 1 [s0.l] k := by
            show cl.call t (α (C.ts t)) 1 [s0.l] k
            rw [hts]; simpa [α, lin, hpc0] using hcall
          obtain ⟨l', hl', -, hheld⟩ := hok _ hr t ht 1 [s0.l] k hcall'
          simp only [List.cons.injEq, and_true] at hl'
          subst hl'
          refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inl ?_⟩
          · refine Or.inr ⟨rfl, hl, ?_⟩
            by_cases h1 : 1 < v <;> simp [h1]
          · refine lin_step ht hts (by simp [lin, hpc0]) (by by_cases h1 : 1 < v <;> simp [lin, h1])
              he hcall (⟨s0.l, _, rfl, hheld, rfl, rfl, rfl⟩ : (mutexSpec locks 1).step t [s0.l]
                [(s0.l, (abst locks C).mem s0.l)] [(s0.l, 0)] 0) ?_ ?_
            · intro q hq
              simp only [List.mem_singleton] at hq
              subst hq; rfl
            · show absMem locks (C.mem.set s0.l 0) = (absMem locks C.mem).set s0.l 0
              rw [absMem_set_lock locks hl]; rfl
        · refine ⟨inv_prim_upd hI ?_ hI.buf, Or.inr ?_⟩
          · exact Or.inr ⟨rfl, hl, Or.inr (Or.inl rfl)⟩
          · exact stut hts (by simp [lin, hpc1]) rfl
  | @flush t pre e post hb hp hm =>
    refine ⟨⟨fun u a v w' he' => ?_, fun u p s c k hu => hI.prim u p s c k hu⟩, Or.inl ?_⟩
    · rcases mem_upd (b := C.buf) (t := t) (l := pre ++ post) he' with ⟨rfl, h1⟩ | ⟨-, h1⟩
      · apply hI.buf u a v w'
        rw [hb]; rcases List.mem_append.1 h1 with h | h <;> simp [h]
      · exact hI.buf _ _ _ _ h1
    · refine step_eq (BStep.flush (C := abst locks C) hb hp hm) (bcfg_ext rfl ?_ rfl)
      cases e with
      | bar => rfl
      | st a v w =>
        have ha : locks a = false := hI.buf t a v w (by rw [hb]; simp)
        exact absMem_set_free locks ha

/-- **Runs.** -/
theorem reach (hav : cl.Avoids (fun a => locks a = true))
    (hok : cl.CallsOk (mutexSpec locks) M N D0) {C C' : BCfg (cl.withImpl mutexImpl)}
    (h : BReach M (cl.withImpl mutexImpl) N C C') :
    Inv locks cl C → BReach M (cl.withSpec (mutexSpec locks)) N D0.toB (abst locks C) →
      Inv locks cl C' ∧ BReach M (cl.withSpec (mutexSpec locks)) N D0.toB (abst locks C') := by
  induction h with
  | refl => exact fun hI hr => ⟨hI, hr⟩
  | step h _ ih =>
    intro hI hr
    obtain ⟨hI', hs⟩ := step hav hok hI hr h
    apply ih hI'
    rcases hs with hs | hs
    · exact star_tail hr hs
    · rw [hs]; exact hr

/-- **`lll_lock`/`lll_unlock` meet the atomic mutex specification under every model.** -/
theorem lllMutex (M : Model) : Task.lllMutex M := by
  intro locks cl N cts0 m0 hav hok C cts h hd hq
  have hI0 : Inv locks cl (⟨fun u => .cl (cts0 u), m0⟩ : Cfg (cl.withImpl mutexImpl)).toB :=
    ⟨fun _ _ _ _ he => (by simp [Cfg.toB] at he), fun _ _ _ _ _ hu => (by simp [Cfg.toB] at hu)⟩
  obtain ⟨-, hr⟩ := reach (D0 := ⟨cts0, absMem locks m0⟩) hav hok h hI0 Star.refl
  have : abst locks C = ⟨cts, absMem locks C.mem, fun _ => []⟩ :=
    bcfg_ext (funext fun u => show α (C.ts u) = cts u by rw [hq u]; rfl) rfl (funext hd)
  rwa [this] at hr

end Silmaril.Proofs.Process.Mt.Drf.Lll
