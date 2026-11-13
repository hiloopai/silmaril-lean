module

public import Silmaril.X86.Litmus.Domain.Defs
public import Silmaril.X86.Litmus.Extract.Thms

/-!
# How extracted traces depend on the value domain: proofs

Proofs for `Silmaril/X86/Litmus/Domain/Thms.lean`.

* `memStep_restrict`, `stepSym_restrict`, `explore_restrict`: a trace extracted over one domain
  whose reads all lie in a second domain is extracted over the second (each read form has one
  branch per value, and the branch depends on the value only through its bytes);
* `explore_prefix`: a prefix of such a trace whose reads lie in the second domain extends to a
  trace over the second domain (when it is nonempty, `explore_ne_nil`);
* `explore_skel`: on straight-line code every trace has the code's skeleton.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Litmus

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Mem RM leBytes leValue Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemEvent (Event Kind)
open Silmaril.X86.Litmus

/-! ## Restriction of one branch -/

theorem valBytes_length (v k : Nat) : (valBytes v k).length = k := by
  simp [valBytes]

/-- The domain value a read's bytes come from. -/
theorem inDom_valBytes {D : List Nat} {v' k : Nat} (h : InDom D (valBytes v' k)) :
    ∃ v ∈ D, valBytes v k = valBytes v' k := by
  obtain ⟨v, hv, he⟩ := h
  rw [valBytes_length] at he
  exact ⟨v, hv, he⟩

theorem storeStep_eq {R : List Region} {sz : Sz} {a : Mem} {v : Word} {s : State} {next : Word}
    {outs outs' : List (List Act × State)} (h : storeStep R sz a v s next = some outs)
    (h' : storeStep R sz a v s next = some outs') : outs' = outs := by
  rw [h] at h'; cases h'; rfl

theorem rmwStep_restrict {R : List Region} {D D' : List Nat} {sz : Sz} {lk : Bool} {a : Mem}
    {s : State} {next : Word} {f : BitVec sz.bits → Word × State}
    {outs outs' : List (List Act × State)} (h : rmwStep R D sz lk a s next f = some outs)
    (h' : rmwStep R D' sz lk a s next f = some outs') {o : List Act × State} (ho : o ∈ outs')
    (hr : ∀ x ∈ o.1, x.ReadIn D) : o ∈ outs := by
  unfold rmwStep at h h'
  dsimp only at h h'
  split at h'
  · rename_i hc
    simp only [hc, ↓reduceIte] at h
    cases h; cases h'
    obtain ⟨v', -, rfl⟩ := List.mem_map.mp ho
    have := hr _ (List.mem_singleton_self _) (by simp [MemEvent.Kind.reads])
    obtain ⟨v, hv, he⟩ := inDom_valBytes this
    exact List.mem_map.mpr ⟨v, hv, by simp only [he]⟩
  · cases h'

/-- **A branch of a memory form whose read lies in a domain is a branch over that domain.** -/
theorem memStep_restrict {R : List Region} {D D' : List Nat} {i : Atomic9.Instr} {s : State}
    {n : Nat} {outs outs' : List (List Act × State)} (h : memStep R D i s n = some outs)
    (h' : memStep R D' i s n = some outs') {o : List Act × State} (ho : o ∈ outs')
    (hr : ∀ x ∈ o.1, x.ReadIn D) : o ∈ outs := by
  unfold memStep at h h'
  dsimp only at h h'
  split at h' <;> (try dsimp only at h)
  · rw [storeStep_eq h h'] at ho; exact ho
  · rw [storeStep_eq h h'] at ho; exact ho
  · split at h'
    · rename_i hc
      simp only [hc, ↓reduceIte] at h
      cases h; cases h'
      obtain ⟨v', -, rfl⟩ := List.mem_map.mp ho
      have hin := hr _ (List.mem_singleton_self _) (by simp [MemEvent.Kind.reads])
      obtain ⟨v, hv, hvb⟩ := inDom_valBytes hin
      exact List.mem_map.mpr ⟨v, hv, by simp only [hvb]⟩
    · cases h'
  · exact rmwStep_restrict h h' ho hr
  · exact rmwStep_restrict h h' ho hr
  · exact rmwStep_restrict h h' ho hr
  · split at h'
    · rename_i hc
      simp only [hc, ↓reduceIte] at h
      cases h; cases h'
      obtain ⟨v', -, rfl⟩ := List.mem_map.mp ho
      have hin := hr _ (List.mem_singleton_self _) (by simp [MemEvent.Kind.reads])
      obtain ⟨v, hv, hvb⟩ := inDom_valBytes hin
      exact List.mem_map.mpr ⟨v, hv, by simp only [hvb]⟩
    · cases h'
  · rw [h] at h'; cases h'; exact ho
  · exact rmwStep_restrict h h' ho hr
  · exact rmwStep_restrict h h' ho hr
  · split at h'
    · cases h'
    · rename_i hop
      simp only [hop, ↓reduceIte] at h
      exact rmwStep_restrict h h' ho hr
  · cases h'

/-- **A step's branch whose reads lie in a domain is a branch over that domain.** -/
theorem stepSym_restrict {t : Thread} {D D' : List Nat} {s : State}
    {outs outs' : List (List Act × State)} (h : stepSym t D s = some outs)
    (h' : stepSym t D' s = some outs') {o : List Act × State} (ho : o ∈ outs')
    (hr : ∀ x ∈ o.1, x.ReadIn D) : o ∈ outs := by
  unfold stepSym at h h'
  split at h'
  · cases h'
  · rename_i i n hf
    rw [hf] at h
    dsimp only at h h'
    split at h'
    · rename_i hin
      simp only [hin, ↓reduceIte] at h
      rw [h] at h'; cases h'; exact ho
    · rename_i hin
      simp only [hin] at h
      exact memStep_restrict h h' ho hr

/-! ## Nonempty branch lists -/

theorem rmwStep_ne_nil {R : List Region} {D : List Nat} (hD : D ≠ []) {sz : Sz} {lk : Bool}
    {a : Mem} {s : State} {next : Word} {f : BitVec sz.bits → Word × State}
    {outs : List (List Act × State)} (h : rmwStep R D sz lk a s next f = some outs) :
    outs ≠ [] := by
  unfold rmwStep at h
  dsimp only at h
  split at h
  · cases h; simpa using hD
  · cases h

theorem storeStep_ne_nil {R : List Region} {sz : Sz} {a : Mem} {v : Word} {s : State}
    {next : Word} {outs : List (List Act × State)} (h : storeStep R sz a v s next = some outs) :
    outs ≠ [] := by
  unfold storeStep at h
  dsimp only at h
  split at h
  · cases h; simp
  · cases h

theorem store8Step_ne_nil {R : List Region} {a : Mem} {v : Word} {s : State}
    {next : Word} {outs : List (List Act × State)} (h : store8Step R a v s next = some outs) :
    outs ≠ [] := by
  unfold store8Step at h
  dsimp only at h
  split at h
  · cases h; simp
  · cases h

theorem memStep_ne_nil {R : List Region} {D : List Nat} (hD : D ≠ []) {i : Atomic9.Instr}
    {s : State} {n : Nat} {outs : List (List Act × State)} (h : memStep R D i s n = some outs) :
    outs ≠ [] := by
  unfold memStep at h
  dsimp only at h
  split at h
  · exact storeStep_ne_nil h
  · exact storeStep_ne_nil h
  · split at h
    · cases h; simpa using hD
    · cases h
  · exact rmwStep_ne_nil hD h
  · exact rmwStep_ne_nil hD h
  · exact rmwStep_ne_nil hD h
  · split at h
    · cases h; simpa using hD
    · cases h
  · exact store8Step_ne_nil h
  · exact rmwStep_ne_nil hD h
  · exact rmwStep_ne_nil hD h
  · split at h
    · cases h
    · exact rmwStep_ne_nil hD h
  · cases h

theorem stepSym_ne_nil {t : Thread} {D : List Nat} (hD : D ≠ []) {s : State}
    {outs : List (List Act × State)} (h : stepSym t D s = some outs) : outs ≠ [] := by
  unfold stepSym at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · split at h
      · cases h; simp
      · cases h
    · exact memStep_ne_nil hD h

/-! ## Exploration -/

theorem mapM_some_mem' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = some rs → ∀ {x : α}, x ∈ l →
      ∃ y, f x = some y ∧ y ∈ rs
  | [], _, _, _, hx => by simp at hx
  | a :: l, rs, h, x, hx => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hl, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy, by simp⟩
    · obtain ⟨y', h', hm⟩ := mapM_some_mem' hl hx
      exact ⟨y', h', by simp [hm]⟩

theorem mapM_mem' {α β : Type} {f : α → Option (List β)} :
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
    · obtain ⟨x', hx', ys', h', hy'⟩ := mapM_mem' hl hy
      exact ⟨x', by simp [hx'], ys', h', hy'⟩

/-- The traces of one branch are traces of the step. -/
theorem mem_flatten_of_branch {outs : List (List Act × State)} {g : Nat}
    {t : Thread} {D : List Nat} {rss : List (List Trace)}
    (hm : outs.mapM (fun o => (explore t D g o.2).map (consStep o.1 o.2)) = some rss)
    {o : List Act × State} (ho : o ∈ outs) {trs : List Trace} (he : explore t D g o.2 = some trs)
    {tr : Trace} (htr : tr ∈ trs) : ⟨⟨o.1, o.2⟩ :: tr.steps, tr.final⟩ ∈ rss.flatten := by
  obtain ⟨ys, hys, hyr⟩ := mapM_some_mem' hm ho
  rw [he] at hys
  simp only [Option.map_some, Option.some.injEq] at hys
  subst hys
  exact List.mem_flatten.mpr ⟨_, hyr, List.mem_map.mpr ⟨tr, htr, rfl⟩⟩

/-- **Exploration is nonempty** over a nonempty domain. -/
theorem explore_ne_nil {t : Thread} {D : List Nat} (hD : D ≠ []) :
    ∀ (fuel : Nat) {s : State} {trs : List Trace}, explore t D fuel s = some trs → trs ≠ [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs h
    unfold explore at h
    split at h
    · cases h; simp
    · cases h
  | succ g ih =>
    intro s trs h
    unfold explore at h
    split at h
    · cases h; simp
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hs
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (stepSym_ne_nil hD hs)
        obtain ⟨ys, hys, -⟩ := mapM_some_mem' hm ho
        obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
        obtain ⟨tr, htr⟩ := List.exists_mem_of_ne_nil _ (ih he)
        exact List.ne_nil_of_mem (mem_flatten_of_branch hm ho he htr)

/-- **Restriction**: a trace over `D'` whose reads all lie in `D` is a trace over `D`. -/
theorem explore_restrict {t : Thread} {D D' : List Nat} :
    ∀ (fuel : Nat) {s : State} {trs trs' : List Trace}, explore t D fuel s = some trs →
      explore t D' fuel s = some trs' → ∀ {tr : Trace}, tr ∈ trs' →
      (∀ r ∈ tr.steps, r.ReadsIn D) → tr ∈ trs := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs trs' h h' tr htr _
    unfold explore at h h'
    split at h'
    · rename_i he; simp only [he, ↓reduceIte] at h; cases h; cases h'; exact htr
    · cases h'
  | succ g ih =>
    intro s trs trs' h h' tr htr hr
    unfold explore at h h'
    split at h'
    · rename_i he; simp only [he, ↓reduceIte] at h; cases h; cases h'; exact htr
    · rename_i he
      simp only [he, ↓reduceIte] at h
      dsimp only at h h'
      split at h'
      · cases h'
      · rename_i outs' hs'
        split at h
        · cases h
        · rename_i outs hs
          obtain ⟨rss', hm', rfl⟩ := Option.map_eq_some_iff.mp h'
          obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨o, ho', ys, hys, hy⟩ := mapM_mem' hm' htr
          obtain ⟨trs'', he'', rfl⟩ := Option.map_eq_some_iff.mp hys
          simp only [consStep, List.mem_map] at hy
          obtain ⟨tr', htr', rfl⟩ := hy
          have ho : o ∈ outs := stepSym_restrict hs hs' ho' (hr _ (List.mem_cons_self ..))
          obtain ⟨zs, hzs, -⟩ := mapM_some_mem' hm ho
          obtain ⟨trso, heo, rfl⟩ := Option.map_eq_some_iff.mp hzs
          exact mem_flatten_of_branch hm ho heo
            (ih heo he'' htr' fun r hr' => hr r (List.mem_cons_of_mem _ hr'))

/-- **Prefix extension**: the first `k` steps of a trace over `D'`, if their reads lie in a
nonempty `D`, are the first `k` steps of a trace over `D`. -/
theorem explore_prefix {t : Thread} {D D' : List Nat} (hD : D ≠ []) :
    ∀ (fuel : Nat) {s : State} {trs trs' : List Trace}, explore t D fuel s = some trs →
      explore t D' fuel s = some trs' → ∀ {tr : Trace}, tr ∈ trs' → ∀ k : Nat,
      (∀ r ∈ tr.steps.take k, r.ReadsIn D) → ∃ tr₂ ∈ trs, tr₂.steps.take k = tr.steps.take k := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs trs' h h' tr htr k _
    unfold explore at h h'
    split at h'
    · rename_i he; simp only [he, ↓reduceIte] at h; cases h; cases h'; exact ⟨tr, htr, rfl⟩
    · cases h'
  | succ g ih =>
    intro s trs trs' h h' tr htr k hr
    have h0 := h
    unfold explore at h h'
    split at h'
    · rename_i he; simp only [he, ↓reduceIte] at h; cases h; cases h'; exact ⟨tr, htr, rfl⟩
    · rename_i he
      simp only [he, ↓reduceIte] at h
      dsimp only at h h'
      split at h'
      · cases h'
      · rename_i outs' hs'
        split at h
        · cases h
        · rename_i outs hs
          obtain ⟨rss', hm', rfl⟩ := Option.map_eq_some_iff.mp h'
          obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
          cases k with
          | zero =>
            obtain ⟨tr₂, h2⟩ := List.exists_mem_of_ne_nil _ (explore_ne_nil hD _ h0)
            exact ⟨tr₂, h2, by simp⟩
          | succ k =>
            obtain ⟨o, ho', ys, hys, hy⟩ := mapM_mem' hm' htr
            obtain ⟨trs'', he'', rfl⟩ := Option.map_eq_some_iff.mp hys
            simp only [consStep, List.mem_map] at hy
            obtain ⟨tr', htr', rfl⟩ := hy
            have ho : o ∈ outs := stepSym_restrict hs hs' ho' (hr ⟨o.1, o.2⟩ (by simp))
            obtain ⟨zs, hzs, -⟩ := mapM_some_mem' hm ho
            obtain ⟨trso, heo, rfl⟩ := Option.map_eq_some_iff.mp hzs
            obtain ⟨tr₂, h2, h2e⟩ := ih heo he'' htr' k
              (fun r hr' => hr r (by simp only [List.take_succ_cons]; exact List.mem_cons_of_mem _ hr'))
            exact ⟨_, mem_flatten_of_branch hm ho heo h2, by simp [h2e]⟩

/-! ## Straight-line code -/

theorem fetch_rip (t : Thread) (s : State) : t.fetch s = t.fetch { t.init with rip := s.rip } :=
  rfl

theorem retire_rip {next : Word} {x : Option (State × Memory)} {c : State} {m : Memory}
    (h : Silmaril.X86.Ext.retire next x = .ok c m) : c.rip = next := by
  cases x with
  | none => simp [Silmaril.X86.Ext.retire] at h
  | some p => simp only [Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Result.ok.injEq] at h; rw [← h.1]

/-- A straight-line form falls through. -/
theorem straight_exec_rip {i : Atomic9.Instr} (hi : straightForm i = true) {s c : State}
    {m m' : Memory} {n : Nat} (hx : Atomic9.exec i s m n = .ok c m') :
    c.rip = s.rip + BitVec.ofNat 64 n := by
  unfold straightForm at hi
  split at hi <;>
    first
    | (exact absurd hi (by decide))
    | (simp only [Atomic9.exec, Atomic9.execNew, Ext9.exec, Silmaril.X86.Ext8.exec,
        Silmaril.X86.Ext.exec] at hx
       first
       | exact retire_rip hx
       | (split at hx
          · cases hx
          · exact retire_rip hx))

theorem addr_of_isAbs {a : Mem} (h : Mem.isAbs a = true) (s : State) (next : Word) :
    a.addr s next = a.disp.signExtend 64 := by
  unfold Mem.isAbs at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hb, hi⟩ := h
  simp only [Mem.addr, hi, Option.map_none, Option.getD_none, BitVec.add_zero]
  split at hb
  · rename_i heq; simp [heq, Silmaril.X86.Ext.Base.value]
  · cases hb

/-- The events of a straight-line form depend only on `rip`. -/
theorem straight_events {i : Atomic9.Instr} (hi : straightForm i = true) {s s' : State}
    (hs : s.rip = s'.rip) (n : Nat) :
    MemEvent.atomic9Accesses i s n = MemEvent.atomic9Accesses i s' n := by
  unfold straightForm at hi
  split at hi <;>
    first
    | (exact absurd hi (by decide))
    | (try simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
       simp [MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses, MemEvent.ext9Accesses,
        MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv,
        MemEvent.aluKind, Atomic9.tag, Atomic9.RM.isMem, addr_of_isAbs, hi, hs])

theorem memStep_post {R : List Region} {D : List Nat} {i : Atomic9.Instr} {s : State} {n : Nat}
    {outs : List (List Act × State)} (h : memStep R D i s n = some outs) {o : List Act × State}
    (ho : o ∈ outs) : o.2.rip = s.rip + BitVec.ofNat 64 n := by
  unfold memStep at h
  dsimp only at h
  split at h <;>
    first
    | (cases h)
    | (unfold storeStep at h; dsimp only at h; split at h
       · cases h; simp only [List.mem_singleton] at ho; subst ho; rfl
       · cases h)
    | (unfold store8Step at h; dsimp only at h; split at h
       · cases h; simp only [List.mem_singleton] at ho; subst ho; rfl
       · cases h)
    | (unfold rmwStep at h; dsimp only at h; split at h
       · cases h; obtain ⟨v, -, rfl⟩ := List.mem_map.mp ho; rfl
       · cases h)
    | (split at h
       · cases h; obtain ⟨v, -, rfl⟩ := List.mem_map.mp ho; rfl
       · cases h)
    | (split at h
       · cases h
       · unfold rmwStep at h; dsimp only at h; split at h
         · cases h; obtain ⟨v, -, rfl⟩ := List.mem_map.mp ho; rfl
         · cases h)

theorem stepSym_post {t : Thread} {D : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t D s = some outs) {i : Atomic9.Instr} {n : Nat}
    (hf : t.fetch s = some (i, n)) (hi : straightForm i = true) {o : List Act × State}
    (ho : o ∈ outs) : o.2.rip = s.rip + BitVec.ofNat 64 n := by
  unfold stepSym at h
  rw [hf] at h
  dsimp only at h
  split at h
  · split at h
    · rename_i c m₀ hx
      cases h
      simp only [List.mem_singleton] at ho
      subst ho
      exact straight_exec_rip hi hx
    · cases h
  · exact memStep_post h ho

/-- **On straight-line code every trace has the skeleton.** -/
theorem explore_skel {t : Thread} {D : List Nat} :
    ∀ (fuel : Nat) {s : State} {trs : List Trace}, explore t D fuel s = some trs →
      ∀ {f : Nat} {S : List (List Event)}, t.skelFrom f s.rip = some S →
      ∀ tr ∈ trs, tr.steps.map (fun r => r.acts.map Act.ev) = S := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs h f S hS tr htr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      unfold Thread.skelFrom at hS
      simp only [he, ↓reduceIte] at hS
      cases hS; rfl
    · cases h
  | succ g ih =>
    intro s trs h f S hS tr htr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      unfold Thread.skelFrom at hS
      simp only [he, ↓reduceIte] at hS
      cases hS; rfl
    · rename_i he
      dsimp only at h
      split at h
      · cases h
      · rename_i outs hs
        unfold Thread.skelFrom at hS
        simp only [he, ↓reduceIte] at hS
        cases f with
        | zero => cases hS
        | succ f =>
          dsimp only at hS
          split at hS
          · rename_i i n hf
            split at hS
            · rename_i hi
              obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.mp hS
              obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨o, ho, ys, hys, hy⟩ := mapM_mem' hm htr
              obtain ⟨trs', he', rfl⟩ := Option.map_eq_some_iff.mp hys
              simp only [consStep, List.mem_map] at hy
              obtain ⟨tr', htr', rfl⟩ := hy
              have hf' : t.fetch s = some (i, n) := by rw [fetch_rip]; exact hf
              obtain ⟨i', n', hf'', hev⟩ := stepSym_events hs ho
              rw [hf'] at hf''
              simp only [Option.some.injEq, Prod.mk.injEq] at hf''
              obtain ⟨rfl, rfl⟩ := hf''
              have hpost := stepSym_post hs hf' hi ho
              simp only [List.map_cons]
              rw [hev]
              exact congrArg₂ List.cons
                (straight_events hi (s := s) (s' := { t.init with rip := s.rip }) rfl n)
                (ih he' (by rw [hpost]; exact hS') tr' htr')
            · cases hS
          · cases hS

end Silmaril.Proofs.X86.Litmus
