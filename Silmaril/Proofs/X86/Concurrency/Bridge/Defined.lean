module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Litmus.Extract.Thms
public import Silmaril.X86.Atomic9.Converse.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Thms

/-!
# The symbolic step is defined wherever the real step succeeds (gap 2): proofs

`Task.tvCfgDefined` and `Task.tvFxDefined` (header
`Silmaril.X86.Concurrency.Bridge.Thms`). The pieces:

* `writeOk_of_storeN`, `readOk_of_loadN` (and `storeN_none`, `loadN_none`): a store or load
  that succeeds was permitted by the regions, so `memStep`'s guards `writeOk`/`readOk` hold;
* `memForm`, `memStep_of_exec`: for every memory form of `memStep`, if `Atomic9.exec` returns
  `.ok` on a memory with regions `R`, then `memStep R dom` is defined (case split over
  `memStep`, unfolding the executor to `loadN`/`storeN`);
* `symDefined_of_exec`: at a fetched instruction that executes on a memory with the thread's
  regions, `stepSym` is defined if the instruction is a memory form or its accesses are inert
  (an inert instruction runs on `Thread.frame` as on the real memory: locality,
  `atomic9_local`, from the real memory to the frame);
* `kindOf_ok`, `fxKindOf_ok`: every form the tables accept is a listed base or atomic
  form, and a memory form or inert (the `ret` aside);
* `tvCfgDefined_holds`, `tvFxDefined_holds`: reachable cores sit at entries (`tvCfg_reach`,
  `tvFx_reach`), so the instruction at `rip` is one the checker accepted, and the converse of
  the listing law (`Atomic9.exec_of_step_base`, `exec_of_step_new`) turns the real step into an
  `.ok` executor result.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Mem RM leBytes leValue Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus
open Silmaril.X86.Concurrency.Bridge

theorem writeOk_of_storeN {R : List Region} {m : Memory} (hR : m.regions = R) {a : Word} {k : Nat}
    {v : Word} {m' : Memory} (h : Silmaril.X86.Ext.storeN m a k v = some m') :
    writeOk R a.toNat k = true := by
  unfold Silmaril.X86.Ext.storeN Memory.writeBytes at h
  split at h
  · rename_i hc
    rw [Silmaril.X86.Ext.length_leBytes] at hc
    subst hR
    simpa [writeOk, Memory.checkSpan, Memory.permits] using hc
  · cases h

theorem readOk_of_loadN {R : List Region} {m : Memory} (hR : m.regions = R) {a : Word} {k : Nat}
    {x : Word} (h : Silmaril.X86.Ext.loadN m a k = some x) :
    readOk R a.toNat k = true := by
  unfold Silmaril.X86.Ext.loadN Memory.readBytes Memory.readWith at h
  split at h
  · rename_i hc
    subst hR
    simpa [readOk, Memory.checkSpan, Memory.permits] using hc
  · cases h

theorem storeN_none {R : List Region} {m : Memory} (hR : m.regions = R) {a : Word} {k : Nat}
    (h : writeOk R a.toNat k = false) : ∀ v, Silmaril.X86.Ext.storeN m a k v = none := by
  intro v
  cases hs : Silmaril.X86.Ext.storeN m a k v with
  | none => rfl
  | some m' => rw [writeOk_of_storeN hR hs] at h; cases h

theorem loadN_none {R : List Region} {m : Memory} (hR : m.regions = R) {a : Word} {k : Nat}
    (h : readOk R a.toNat k = false) : Silmaril.X86.Ext.loadN m a k = none := by
  cases hs : Silmaril.X86.Ext.loadN m a k with
  | none => rfl
  | some x => rw [readOk_of_loadN hR hs] at h; cases h

theorem rw_guard {R : List Region} {a k : Nat} (h : (readOk R a k && writeOk R a k) = false) :
    readOk R a k = false ∨ writeOk R a k = false := Bool.and_eq_false_iff.mp h

/-- The memory forms of `memStep`. -/
def memForm : Atomic9.Instr → Bool
  | .open9 (.ext8 (.base (.mov _ (.mem _) _))) => true
  | .open9 (.ext8 (.base (.movI _ (.mem _) _))) => true
  | .open9 (.ext8 (.base (.load _ _ _))) => true
  | .new (.xadd _ _ (.mem _) _) => true
  | .new (.xchg _ (.mem _) _) => true
  | .new (.cmpxchg _ _ (.mem _) _) => true
  | .open9 (.ext8 (.base (.mov8 _ (.mem _)))) => true
  | .open9 (.ext8 (.base (.movI8 (.mem _) _))) => true
  | .open9 (.ext8 (.base (.incdec _ _ (.mem _)))) => true
  | .new (.lockIncDec _ _ _) => true
  | .new (.lockAluI _ op _ _) => op != .cmp
  | _ => false

theorem memStep_of_exec {R : List Region} {dom : List Nat} {m : Memory} (hR : m.regions = R)
    {i : Atomic9.Instr} {s c : State} {n : Nat} {m' : Memory}
    (hx : Atomic9.exec i s m n = .ok c m') (hi : memForm i = true) :
    (memStep R dom i s n).isSome = true := by
  unfold memStep
  dsimp only
  split
  all_goals
    simp only [memForm, Bool.false_eq_true] at hi
  all_goals
    simp only [Atomic9.exec, Atomic9.execNew, Ext9.exec, Silmaril.X86.Ext8.exec,
      Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM8, Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Atomic9.xaddStep, Atomic9.xchgStep,
      Atomic9.cmpxchgStep, Atomic9.incDecStep, Silmaril.X86.Ext.aluStep,
      Silmaril.X86.Ext.retire] at hx
  all_goals
    try rw [ite_eq_right (by simpa using hi)]
    try simp only [storeStep, store8Step, rmwStep]
    split
    · rfl
    rename_i hbad
    first
      | (simp only [Bool.not_eq_true] at hbad
         simp only [storeN_none hR hbad, Option.map_none] at hx
         simp at hx)
      | (simp only [Bool.not_eq_true] at hbad
         simp only [loadN_none hR hbad, Option.map_none] at hx
         simp [Option.map] at hx)
      | (simp only [Bool.not_eq_true] at hbad
         obtain hbad | hbad := rw_guard hbad
         · simp [loadN_none hR hbad] at hx
         · simp [storeN_none hR hbad] at hx
           revert hx
           generalize Option.map _ (Silmaril.X86.Ext.loadN m _ _) = q
           cases q <;> simp_all)


/-- **The symbolic step is defined at an instruction that executes**: if the instruction at
`rip` executes with `.ok` on some memory with the thread's regions, and it is a memory form of
`memStep` or its accesses are inert, then `stepSym` is defined. -/
theorem symDefined_of_exec {t : Thread} {s : State} {i : Atomic9.Instr} {n : Nat}
    (hf : t.fetch s = some (i, n)) {m : Memory} (hR : m.regions = t.regions) {c : State}
    {m' : Memory} (hx : Atomic9.exec i s m n = .ok c m')
    (hi : memForm i = true ∨ (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = true) :
    SymDefined t s := by
  refine ⟨[], ?_⟩
  unfold stepSym
  rw [hf]
  dsimp only
  split
  · rename_i hin
    have hl := MemEvent.atomic9_local i s n
    have hag : MemEvent.Agree (MemEvent.readSet (MemEvent.atomic9Accesses i s n)) m t.frame := by
      refine ⟨by simp [Thread.frame, hR], ?_⟩
      rintro a ⟨e, he, hr, -⟩
      have := List.all_eq_true.mp hin e he
      simp [Litmus.Event.inert, hr] at this
    have hrel := hl.congr m t.frame hag
    rw [hx] at hrel
    cases hfr : Atomic9.exec i s t.frame n <;> rw [hfr] at hrel <;>
      simp [MemEvent.extView, MemEvent.Rel] at hrel
    exact ⟨_, rfl⟩
  · rename_i hin
    rcases hi with hi | hi
    · exact Option.isSome_iff_exists.mp (memStep_of_exec hR hx hi)
    · exact absurd hi hin

/-! ## The forms the checkers accept -/

/-- A listed form of one of the two shapes the converse of the listing law covers. -/
def Shaped (i : Atomic9.Instr) : Prop :=
  (∃ b, i = .open9 (.ext8 (.base b))) ∨ ∃ j, i = .new j

/-- Every form of the table is a listed base or atomic form, and a memory form of `memStep`
or inert. -/
theorem kindOf_ok {i : Atomic9.Instr} {k : Silmaril.X86.Concurrency.Cir.TvCfg.Kind} (h : Silmaril.X86.Concurrency.Cir.TvCfg.kindOf i = some k) :
    Shaped i ∧ ∀ s n, memForm i = true ∨
      (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = true := by
  unfold Silmaril.X86.Concurrency.Cir.TvCfg.kindOf at h
  split at h
  all_goals first
    | (simp at h; done)
    | (refine ⟨by simp [Shaped], fun s n => ?_⟩
       simp [memForm, MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses,
         MemEvent.ext9Accesses, MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv,
         MemEvent.memEv, Litmus.Event.inert, MemEvent.Kind.reads, MemEvent.Kind.writes])

/-- Every form of the table other than `ret` is a listed base or atomic form, and a memory
form of `memStep` or inert. -/
theorem fxKindOf_ok {i : Atomic9.Instr} {k : Silmaril.X86.Concurrency.Cir.TvCfg.Fx.FKind} (h : Silmaril.X86.Concurrency.Cir.TvCfg.Fx.fxKindOf i = some k) :
    i = .open9 (.ext8 (.base .ret)) ∨ (Shaped i ∧ ∀ s n, memForm i = true ∨
      (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = true) := by
  unfold Silmaril.X86.Concurrency.Cir.TvCfg.Fx.fxKindOf at h
  split at h
  · exact .inr ⟨by simp [Shaped], fun s n => by simp [memForm]⟩
  · exact .inr ⟨by simp [Shaped], fun s n => by simp [memForm]⟩
  · refine .inr ⟨by simp [Shaped], fun s n => ?_⟩
    simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
      MemEvent.extAccesses, MemEvent.rmEv]
  · exact .inl rfl
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨k', hk', -⟩ := h
    exact .inr (kindOf_ok hk')

/-! ## Entries -/

theorem chkEntry_kind {t : Thread} {E : List Silmaril.X86.Concurrency.Cir.TvCfg.Entry} {e : Silmaril.X86.Concurrency.Cir.TvCfg.Entry}
    (h : Silmaril.X86.Concurrency.Cir.TvCfg.chkEntry t E e = true) (hne : e.off ≠ t.code.length) :
    ∃ i n k, Silmaril.X86.Concurrency.Cir.Tv.fetchAt t e.off = some (i, n) ∧ Silmaril.X86.Concurrency.Cir.TvCfg.kindOf i = some k := by
  unfold Silmaril.X86.Concurrency.Cir.TvCfg.chkEntry at h
  simp only [hne, ↓reduceIte] at h
  split at h
  · cases h
  rename_i i n hfa
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases hk : Silmaril.X86.Concurrency.Cir.TvCfg.kindOf i with
  | none => simp [hk] at h
  | some k => exact ⟨i, n, k, hfa, hk⟩

theorem chkEntryF_kind {t : Thread} {E : List Silmaril.X86.Concurrency.Cir.TvCfg.Fx.FEntry} {e : Silmaril.X86.Concurrency.Cir.TvCfg.Fx.FEntry}
    (h : Silmaril.X86.Concurrency.Cir.TvCfg.Fx.chkEntryF t E e = true) (hne : e.off ≠ t.code.length)
    (hsys : Silmaril.X86.Concurrency.Cir.TvCfg.Fx.isSysAt t e.off = false) :
    ∃ i n k, Silmaril.X86.Concurrency.Cir.Tv.fetchAt t e.off = some (i, n) ∧ Silmaril.X86.Concurrency.Cir.TvCfg.Fx.fxKindOf i = some k := by
  unfold Silmaril.X86.Concurrency.Cir.TvCfg.Fx.chkEntryF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  simp only [hne, hsys, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  rename_i i n hfa
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases hk : Silmaril.X86.Concurrency.Cir.TvCfg.Fx.fxKindOf i with
  | none => simp [hk] at h
  | some k => exact ⟨i, n, k, hfa, hk⟩

theorem off_of_rip {t : Thread} {s : State} {o : Nat} (h : s.rip = t.base + BitVec.ofNat 64 o)
    (ho : o < 2 ^ 64) : (s.rip - t.base).toNat = o := by
  have e : t.base + BitVec.ofNat 64 o - t.base = BitVec.ofNat 64 o := by bv_omega
  rw [h, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem fetchAt_spec {t : Thread} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (h : Silmaril.X86.Concurrency.Cir.Tv.fetchAt t o = some (i, n)) :
    o + n ≤ t.code.length ∧ Atomic9.decode ((t.code.drop o).take n) = some (i, n) := by
  unfold Silmaril.X86.Concurrency.Cir.Tv.fetchAt at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- **The real step at an accepted instruction is its executor.** -/
theorem exec_of_accepted {t : Thread} {s : State} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (hrip : s.rip = t.base + BitVec.ofNat 64 o) (hfa : Silmaril.X86.Concurrency.Cir.Tv.fetchAt t o = some (i, n))
    (hsh : Shaped i) {m : Memory} (hl : Loaded m t.base t.code) {s' : State} {m' : Memory}
    (hs : Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩) : Atomic9.exec i s m n = .ok s' m' := by
  obtain ⟨hfit, hdec⟩ := fetchAt_spec hfa
  rcases hsh with ⟨b, rfl⟩ | ⟨j, rfl⟩
  · exact Atomic9.exec_of_step_base (m := ⟨s, m⟩) (m' := ⟨s', m'⟩) hl hrip hfit hdec hs
  · exact Atomic9.exec_of_step_new (m := ⟨s, m⟩) (m' := ⟨s', m'⟩) hl hrip hfit hdec hs

/-! ## The two Tasks -/

/-- **`Task.tvCfgDefined` holds.** -/
theorem tvCfgDefined_holds : Task.tvCfgDefined := by
  intro t c hc s₀ s acc h0 hx hne m s' m' hR hl hs
  obtain ⟨e, he, hrip⟩ := Silmaril.X86.Concurrency.Cir.TvCfg.tvCfg_reach hc h0 hx
  simp only [Silmaril.X86.Concurrency.Cir.TvCfg.tvCfg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hlen, hall⟩, -⟩, -⟩ := hc
  obtain ⟨hoff, hchk⟩ := hall e he
  have hne' : e.off ≠ t.code.length := by
    intro h; apply hne; rw [hrip, h]; rfl
  obtain ⟨i, n, k, hfa, hk⟩ := chkEntry_kind hchk hne'
  have hf : t.fetch s = some (i, n) := by
    unfold Thread.fetch
    rw [off_of_rip hrip (Nat.lt_of_le_of_lt hoff hlen)]
    exact hfa
  obtain ⟨hsh, hmem⟩ := kindOf_ok hk
  exact symDefined_of_exec hf hR (exec_of_accepted hrip hfa hsh hl hs) (hmem s n)

/-- **`Task.tvFxDefined` holds.** -/
theorem tvFxDefined_holds : Task.tvFxDefined := by
  intro t c hc s₀ s acc h0 hx hret hsys m s' m' hR hl hs
  obtain ⟨e, he, hrip⟩ := Silmaril.X86.Concurrency.Cir.TvCfg.Fx.tvFx_reach hc h0 hx
  simp only [Silmaril.X86.Concurrency.Cir.TvCfg.Fx.tvFx, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hlen, hall⟩, -⟩, -⟩ := hc
  obtain ⟨hoff, hchk⟩ := hall e he
  have ho := off_of_rip hrip (Nat.lt_of_le_of_lt hoff hlen)
  have hne' : e.off ≠ t.code.length := by
    intro h; apply hret; left; rw [hrip, h]; rfl
  rw [ho] at hsys
  obtain ⟨i, n, k, hfa, hk⟩ := chkEntryF_kind hchk hne' hsys
  have hf : t.fetch s = some (i, n) := by
    unfold Thread.fetch
    rw [ho]
    exact hfa
  rcases fxKindOf_ok hk with rfl | ⟨hsh, hmem⟩
  · exact absurd (Or.inr ⟨n, hf⟩) hret
  · exact symDefined_of_exec hf hR (exec_of_accepted hrip hfa hsh hl hs) (hmem s n)

end Silmaril.Proofs.X86.Concurrency.Bridge
