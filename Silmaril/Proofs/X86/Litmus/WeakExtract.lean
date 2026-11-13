module

public import Silmaril.X86.Litmus.WeakExtract.Defs
public import Silmaril.X86.Litmus.Extract.Thms
public import Silmaril.X86.Weak9.Thms

/-!
# Soundness of litmus event extraction over `Weak9`

`wextract_sound`: every trace of `wextract` replays on `Weak9.step` (`WReplay`). Where the
fetch decodes, the step is `stepSym`, sound for `Atomic9.step` (`stepSym_sound`), hence
for `Weak9.step` (`Weak9.step_of_atomic9`). Otherwise the step is a pure transcription of
`Weak9.execWeak` or `Str9.execStr` (`weakStep_sound`, `strStep_sound`), and the listing law
`Weak9.step_of_listed` makes it one machine step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Litmus

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Mem leBytes Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemEvent (Event Kind)
open Silmaril.X86.Litmus

/-! ## Memories -/

theorem wcheckSpan_regions {m m' : Memory} (h : m.regions = m'.regions)
    (acc : Silmaril.Process.Access) (a k : Nat) : m.checkSpan acc a k = m'.checkSpan acc a k := by
  simp [Memory.checkSpan, Memory.permits, h]

theorem wwriteBytes_of_ok {R : List Region} {m : Memory} (hR : m.regions = R) {a : Nat}
    {bs : List Byte} (h : writeOk R a bs.length = true) :
    ∃ m', m.writeBytes a bs = some m' := by
  unfold writeOk at h
  rw [← hR, ← wcheckSpan_regions (m := m) (m' := ⟨m.regions, ∅⟩) rfl] at h
  exact ⟨{ m with bytes := Memory.install m.bytes a bs }, by simp [Memory.writeBytes, h]⟩

theorem wloadN_of_read {m : Memory} {a : Word} {k : Nat} {bs : List Byte}
    (h : m.readBytes a.toNat k = some bs) :
    Silmaril.X86.Ext.loadN m a k = some (ldVal bs) := by
  simp [Silmaril.X86.Ext.loadN, h, ldVal]

/-! ## Fetch -/

theorem wfetch_spec {t : Thread} {s : State} {i : Weak9.Instr} {n : Nat}
    (h : t.wfetch s = some (i, n)) :
    s.rip = t.base + BitVec.ofNat 64 (s.rip - t.base).toNat ∧
      (s.rip - t.base).toNat + n ≤ t.code.length ∧
      Weak9.decode ((t.code.drop (s.rip - t.base).toNat).take n) = some (i, n) := by
  unfold Thread.wfetch at h
  dsimp only at h
  refine ⟨?_, ?_⟩
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-! ## The new forms -/

/-- What a `Weak`/`Str9` branch satisfies: the machine's executor reaches the branch's core and
the branch's writes. -/
def WGood (m : Memory) (x : Memory → Silmaril.X86.Ext.Result) (o : List Act × State) : Prop :=
  Answers m o.1 → ∃ m', x m = .ok o.2 m' ∧ applyWrites m o.1 = some m'

theorem repStoreStep_sound {R : List Region} {k : Nat} {v : Word} {s : State} {next : Word}
    {outs : List (List Act × State)} (h : repStoreStep R k v s next = some outs)
    {o : List Act × State} (ho : o ∈ outs) {m : Memory} (hR : m.regions = R) :
    (s.read .rcx = 0 ∧ o.2 = { s with rip := next } ∧ applyWrites m o.1 = some m) ∨
      (s.read .rcx ≠ 0 ∧ ∃ m', Silmaril.X86.Ext.storeN m (s.read .rdi) k v = some m' ∧
        o.2 = repPost k false s next ∧ applyWrites m o.1 = some m') := by
  unfold repStoreStep at h
  split at h
  · rename_i hc
    cases h
    simp only [List.mem_singleton] at ho
    subst ho
    exact Or.inl ⟨hc, rfl, rfl⟩
  · rename_i hc
    dsimp only at h
    split at h
    · rename_i hw
      cases h
      simp only [List.mem_singleton] at ho
      subst ho
      have hw' : writeOk R (s.read .rdi).toNat (leBytes v k).length = true := by simpa using hw
      obtain ⟨m', hm'⟩ := wwriteBytes_of_ok hR hw'
      exact Or.inr ⟨hc, m', hm', rfl, by simp [applyWrites, MemEvent.Kind.writes, hm']⟩
    · cases h

theorem copyStep_sound {R : List Region} {dom : List Nat} {k : Nat} {s post : State}
    {outs : List (List Act × State)} (h : copyStep R dom k s post = some outs)
    {o : List Act × State} (ho : o ∈ outs) {m : Memory} (hR : m.regions = R)
    (hans : Answers m o.1) :
    ∃ x m', Silmaril.X86.Ext.loadN m (s.read .rsi) k = some x ∧
      Silmaril.X86.Ext.storeN m (s.read .rdi) k x = some m' ∧ o.2 = post ∧
      applyWrites m o.1 = some m' := by
  unfold copyStep at h
  dsimp only at h
  split at h
  · rename_i hw
    cases h
    simp only [List.mem_map] at ho
    obtain ⟨v, -, rfl⟩ := ho
    have hr := hans _ (List.mem_cons_self ..) (by simp [MemEvent.Kind.reads])
    simp only [Bool.and_eq_true] at hw
    have hw' : writeOk R (s.read .rdi).toNat (leBytes (ldVal (valBytes v k)) k).length = true := by
      simpa using hw.2
    obtain ⟨m', hm'⟩ := wwriteBytes_of_ok hR hw'
    exact ⟨_, m', wloadN_of_read hr, hm', rfl,
      by simp [applyWrites, MemEvent.Kind.writes, hm']⟩
  · cases h

theorem weakStep_sound {R : List Region} {i : Weak9.Weak} {s : State} {n : Nat}
    {outs : List (List Act × State)} (h : weakStep R i s n = some outs) {o : List Act × State}
    (ho : o ∈ outs) {m : Memory} (hR : m.regions = R) :
    WGood m (fun m => Weak9.execWeak i s m (s.rip + BitVec.ofNat 64 n)) o := by
  intro _
  unfold weakStep at h
  dsimp only at h
  split at h
  · rename_i sz dst src
    split at h
    · rename_i hw
      cases h
      simp only [List.mem_singleton] at ho
      subst ho
      have hw' : writeOk R (dst.addr s (s.rip + BitVec.ofNat 64 n)).toNat
          (leBytes ((sz.read s src).setWidth 64) sz.bytes).length = true := by simpa using hw
      obtain ⟨m', hm'⟩ := wwriteBytes_of_ok hR hw'
      refine ⟨m', ?_, by simp [applyWrites, MemEvent.Kind.writes, hm']⟩
      simp [Weak9.execWeak, Silmaril.X86.Ext.storeN, hm', Silmaril.X86.Ext.retire]
    · cases h
  · rcases repStoreStep_sound h ho hR with ⟨hc, ho2, hap⟩ | ⟨hc, m', hst, ho2, hap⟩
    · exact ⟨m, by simp [Weak9.execWeak, hc, ho2], hap⟩
    · refine ⟨m', ?_, hap⟩
      simp only [Weak9.execWeak, hc, ↓reduceIte, Weak9.stosbElem]
      rw [hst, ho2]
      rfl

theorem strStep_sound {R : List Region} {dom : List Nat} {i : Str9.Str} {s : State} {n : Nat}
    {outs : List (List Act × State)} (h : strStep R dom i s n = some outs) {o : List Act × State}
    (ho : o ∈ outs) {m : Memory} (hR : m.regions = R) :
    WGood m (fun m => Str9.execStr i s m (s.rip + BitVec.ofNat 64 n)) o := by
  intro hans
  unfold strStep at h
  dsimp only at h
  split at h
  · rcases repStoreStep_sound h ho hR with ⟨hc, ho2, hap⟩ | ⟨hc, m', hst, ho2, hap⟩
    · exact ⟨m, by simp [Str9.execStr, hc, ho2], hap⟩
    · refine ⟨m', ?_, hap⟩
      simp only [Str9.execStr, hc, ↓reduceIte, Str9.repElem]
      rw [hst, ho2]
      rfl
  · obtain ⟨x, m', hl, hst, ho2, hap⟩ := copyStep_sound h ho hR hans
    refine ⟨m', ?_, hap⟩
    simp only [Str9.execStr, hl, hst, ho2]
    rfl
  · split at h
    · rename_i hc
      cases h
      simp only [List.mem_singleton] at ho
      subst ho
      exact ⟨m, by simp [Str9.execStr, hc], rfl⟩
    · rename_i hc
      obtain ⟨x, m', hl, hst, ho2, hap⟩ := copyStep_sound h ho hR hans
      refine ⟨m', ?_, hap⟩
      simp only [Str9.execStr, hc, ↓reduceIte, hl, Str9.repElem, hst, ho2]
      rfl

/-! ## One symbolic step -/

theorem wstepSym_sound {t : Thread} {dom : List Nat} {s : State}
    {outs : List (List Act × State)} (h : wstepSym t dom s = some outs) {o : List Act × State}
    (ho : o ∈ outs) (m : Memory) (hR : m.regions = t.regions) (hl : Loaded m t.base t.code)
    (hans : Answers m o.1) :
    ∃ m', Weak9.step ⟨s, m⟩ = some ⟨o.2, m'⟩ ∧ applyWrites m o.1 = some m' := by
  unfold wstepSym at h
  split at h
  · obtain ⟨m', hst, hap⟩ := stepSym_sound h ho m hR hl hans
    exact ⟨m', Weak9.step_of_atomic9 hst, hap⟩
  · split at h
    · rename_i i n hf
      obtain ⟨hrip, hfit, hdec⟩ := wfetch_spec hf
      obtain ⟨m', hx, hap⟩ := weakStep_sound h ho hR hans
      exact ⟨m', Weak9.step_of_listed (m := ⟨s, m⟩) hl hrip hfit hdec hx, hap⟩
    · rename_i i n hf
      obtain ⟨hrip, hfit, hdec⟩ := wfetch_spec hf
      obtain ⟨m', hx, hap⟩ := strStep_sound h ho hR hans
      exact ⟨m', Weak9.step_of_listed (m := ⟨s, m⟩) hl hrip hfit hdec hx, hap⟩
    · cases h

/-! ## Exploration -/

theorem wmapM_mem {α β : Type} {f : α → Option (List β)} :
    ∀ {l : List α} {rss : List (List β)}, l.mapM f = some rss → ∀ {y : β}, y ∈ rss.flatten →
      ∃ x ∈ l, ∃ ys, f x = some ys ∧ y ∈ ys
  | [], rss, h, y, hy => by
    simp at h; subst h; simp at hy
  | x :: l, rss, h, y, hy => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ys, hx, rs, hl, rfl⟩ := h
    simp only [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ⟨x, by simp, ys, hx, hy⟩
    · obtain ⟨x', hx', ys', h', hy'⟩ := wmapM_mem hl hy
      exact ⟨x', by simp [hx'], ys', h', hy'⟩

theorem wexplore_sound {t : Thread} {dom : List Nat} :
    ∀ (fuel : Nat) {s : State} {trs : List Trace}, wexplore t dom fuel s = some trs →
      ∀ tr ∈ trs, WReplay t s tr.steps tr.final := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs h tr htr
    unfold wexplore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · cases h
  | succ f ih =>
    intro s trs h tr htr
    unfold wexplore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hs
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨o, ho, ys, hys, hy⟩ := wmapM_mem hm htr
        obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
        simp only [consStep, List.mem_map] at hy
        obtain ⟨tr', htr', rfl⟩ := hy
        exact .step s ⟨o.1, o.2⟩ tr'.steps tr'.final
          (fun m hR hl hans => wstepSym_sound hs ho m hR hl hans) (ih he tr' htr')

/-- **Extraction over `Weak9` is sound.** -/
theorem wextract_sound {t : Thread} {dom : List Nat} {fuel : Nat} {trs : List Trace}
    (h : wextract t dom fuel = some trs) : ∀ tr ∈ trs, WReplay t t.init tr.steps tr.final :=
  wexplore_sound fuel h

end Silmaril.Proofs.X86.Litmus
