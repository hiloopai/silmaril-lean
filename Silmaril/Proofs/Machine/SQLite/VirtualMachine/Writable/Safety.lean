module

public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine.Writable

variable {F : Footprint} {cat : Catalog}

theorem inv_initial (F : Footprint) (store : Store) : Inv F (Config.initial store) where
  transactions := fun _ _ h => by cases h
  cursors := fun _ _ h => by cases h

private theorem inv_of_eq {c c' : Config} (hinv : Inv F c)
    (ht : c'.transactions = c.transactions) (hc : c'.cursors = c.cursors) : Inv F c' where
  transactions := by rw [ht]; exact hinv.transactions
  cursors := by rw [ht, hc]; exact hinv.cursors

private theorem copyRegisters_eq :
    ∀ (count source destination : Nat) (c : Config),
      Config.copyRegisters count source destination c =
        {c with registers := (Config.copyRegisters count source destination c).registers}
  | 0, _, _, _ => rfl
  | count + 1, source, destination, c => by
      simp only [Config.copyRegisters]
      rw [copyRegisters_eq count (source + 1) (destination + 1)]
      rfl

private theorem inv_reposition {c : Config} {identifier : Nat} {cursor : Cursor}
    (hinv : Inv F c) (found : c.cursors identifier = some cursor) (position : Option Int) :
    Inv F (c.setCursor identifier {cursor with position := position}) where
  transactions := hinv.transactions
  cursors := by
    intro other cur h
    simp only [Config.setCursor] at h
    split at h
    · cases h; exact hinv.cursors identifier cursor found
    · exact hinv.cursors other cur h

private theorem inv_open {c : Config} {identifier : Nat} {table : TableId} {mode : Mode}
    (hinv : Inv F c) (allowed : F.allows (.table table mode) = true)
    (covered : Mode.covers (c.transactions table.db) mode = true) :
    Inv F (c.setCursor identifier ⟨table, mode, none⟩) where
  transactions := hinv.transactions
  cursors := by
    intro other cur h
    simp only [Config.setCursor] at h
    split at h
    · cases h; exact ⟨allowed, covered⟩
    · exact hinv.cursors other cur h

private theorem covers_upgrade (old : Option Mode) (mode wanted : Mode)
    (h : Mode.covers old wanted = true) : Mode.covers (some (Mode.upgrade old mode)) wanted = true := by
  cases old with
  | none => simp [Mode.covers] at h
  | some old => cases old <;> cases mode <;> cases wanted <;> simp_all [Mode.covers, Mode.upgrade]

private theorem upgrade_allowed {old : Option Mode} {mode : Mode} {db : DbId}
    (hold : ∀ m, old = some m → F.allows (.db db m) = true) (hnew : F.allows (.db db mode) = true) :
    F.allows (.db db (Mode.upgrade old mode)) = true := by
  cases old with
  | none => exact hnew
  | some old => cases old <;> simp [Mode.upgrade] <;> first | exact hnew | exact hold _ rfl

private theorem contract_silent {c c' : Config}
    (hw : c'.working = c.working) (hc : c'.committed = c.committed) : Contract F c [] c' where
  allowed := fun _ h => by cases h
  working := fun _ _ => by rw [hw]
  committed := Or.inl hc

private theorem silent {c c' : Config} (hinv : Inv F c)
    (hw : c'.working = c.working) (hc : c'.committed = c.committed)
    (ht : c'.transactions = c.transactions) (hcur : c'.cursors = c.cursors) :
    Contract F c [] c' ∧ Inv F c' :=
  ⟨contract_silent hw hc, inv_of_eq hinv ht hcur⟩

private theorem writeCursor_ok {c : Config} {identifier : Nat} {cursor : Cursor} {rows : Rows}
    (h : writeCursor c identifier = .ok (cursor, rows)) :
    c.cursors identifier = some cursor ∧ cursor.mode = .write ∧ c.working cursor.table = some rows := by
  unfold writeCursor at h
  split at h
  · cases h
  · rename_i cur found
    split at h
    · cases h
    · rename_i hmode
      split at h
      · cases h
      · rename_i rs hrows
        cases h
        refine ⟨found, ?_, hrows⟩
        revert hmode
        cases cursor.mode <;> simp

private theorem write_contract {c : Config} {cursor : Cursor} {identifier : Nat} {rows : Rows}
    (hinv : Inv F c) (found : c.cursors identifier = some cursor) (hmode : cursor.mode = .write) :
    Contract F c [.write cursor.table]
      {c with working := c.working.set cursor.table rows}.advance ∧
    Inv F {c with working := c.working.set cursor.table rows}.advance := by
  refine ⟨⟨?_, ?_, Or.inl rfl⟩, inv_of_eq hinv rfl rfl⟩
  · intro event h
    simp only [List.mem_singleton] at h
    subst h
    have := (hinv.cursors identifier cursor found).1
    rw [hmode] at this
    exact this
  · intro table h
    simp only [List.mem_singleton, Event.write.injEq] at h
    simp [Config.advance, Store.set, h]

private theorem openCursor_safe {c c' : Config} {events : List Event}
    {identifier root slot : Nat} {mode : Mode} (hinv : Inv F c)
    (h : openCursor F cat c identifier root slot mode = .ok (events, c')) :
    Contract F c events c' ∧ Inv F c' := by
  unfold openCursor at h
  split at h
  · cases h
  · rename_i table _
    split at h
    · cases h
    · rename_i hallow
      split at h
      · cases h
      · rename_i hcover
        split at h
        · cases h
        · cases h
          simp only [Bool.not_eq_false] at hallow hcover
          refine ⟨⟨?_, fun _ _ => rfl, Or.inl rfl⟩, ?_⟩
          · intro event hmem
            simp only [List.mem_singleton] at hmem
            subst hmem
            exact hallow
          · exact inv_of_eq (inv_open hinv hallow hcover) rfl rfl

/-- One modeled instruction meets the transition contract and preserves the
provenance invariant, whatever its operands. -/
theorem exec_safe {instr : Instr} {c c' : Config} {events : List Event}
    (hinv : Inv F c) (h : exec F cat instr c = .ok (events, c')) :
    Contract F c events c' ∧ Inv F c' := by
  cases instr with
  | init target => cases h; exact silent hinv rfl rfl rfl rfl
  | goto target => cases h; exact silent hinv rfl rfl rfl rfl
  | halt code =>
      simp only [exec] at h
      split at h
      · cases h
        refine ⟨⟨?_, fun _ _ => rfl, Or.inr ⟨List.mem_singleton_self _, rfl⟩⟩,
          inv_of_eq hinv rfl rfl⟩
        intro event hmem
        simp only [List.mem_singleton] at hmem
        subst hmem
        trivial
      · cases h; exact silent hinv rfl rfl rfl rfl
  | integer value destination => cases h; exact silent hinv rfl rfl rfl rfl
  | string8 value destination => cases h; exact silent hinv rfl rfl rfl rfl
  | null first last => cases h; exact silent hinv rfl rfl rfl rfl
  | copy source destination additional =>
      cases h
      rw [copyRegisters_eq]
      exact silent hinv rfl rfl rfl rfl
  | transaction slot mode =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i db _
        split at h
        · cases h
        · rename_i hallow
          cases h
          simp only [Bool.not_eq_false] at hallow
          refine ⟨⟨?_, fun _ _ => rfl, Or.inl rfl⟩, ?_⟩
          · intro event hmem
            simp only [List.mem_singleton] at hmem
            subst hmem
            exact hallow
          · constructor
            · intro other m hm
              simp only [Config.advance] at hm
              split at hm
              · rename_i heq
                subst heq
                cases hm
                exact upgrade_allowed (hinv.transactions _) hallow
              · exact hinv.transactions other m hm
            · intro identifier cursor hcur
              refine ⟨(hinv.cursors identifier cursor hcur).1, ?_⟩
              simp only [Config.advance]
              split
              · rename_i heq
                have hcov := (hinv.cursors identifier cursor hcur).2
                rw [heq] at hcov
                exact covers_upgrade _ _ _ hcov
              · exact (hinv.cursors identifier cursor hcur).2
  | openRead identifier root slot => exact openCursor_safe hinv h
  | openWrite identifier root slot => exact openCursor_safe hinv h
  | rewind identifier target =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i cursor found
        split at h
        · cases h
        · split at h
          · cases h
            exact ⟨contract_silent rfl rfl, inv_of_eq (inv_reposition hinv found none) rfl rfl⟩
          · cases h
            exact ⟨contract_silent rfl rfl, inv_of_eq (inv_reposition hinv found _) rfl rfl⟩
  | next identifier target =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i cursor found
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
              exact ⟨contract_silent rfl rfl, inv_of_eq (inv_reposition hinv found none) rfl rfl⟩
            · cases h
              exact ⟨contract_silent rfl rfl, inv_of_eq (inv_reposition hinv found _) rfl rfl⟩
  | seekRowid identifier target register =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i cursor found
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
              exact ⟨contract_silent rfl rfl, inv_of_eq (inv_reposition hinv found none) rfl rfl⟩
            · cases h
              exact ⟨contract_silent rfl rfl, inv_of_eq (inv_reposition hinv found _) rfl rfl⟩
        · cases h
  | column identifier index destination =>
      simp only [exec] at h
      split at h
      · cases h
      · cases h; exact silent hinv rfl rfl rfl rfl
  | rowid identifier destination =>
      simp only [exec] at h
      split at h
      · cases h
      · split at h
        · cases h; exact silent hinv rfl rfl rfl rfl
        · cases h
  | newRowid identifier destination =>
      simp only [exec] at h
      split at h
      · cases h
      · split at h
        · cases h; exact silent hinv rfl rfl rfl rfl
        · cases h
  | makeRecord first count destination =>
      simp only [exec] at h
      split at h
      · cases h
      · cases h; exact silent hinv rfl rfl rfl rfl
  | insert identifier record key =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i cursor rows hwc
        obtain ⟨found, hmode, -⟩ := writeCursor_ok hwc
        split at h
        · cases h; exact write_contract hinv found hmode
        · cases h
        · cases h
  | delete identifier =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i cursor rows hwc
        obtain ⟨found, hmode, -⟩ := writeCursor_ok hwc
        split at h
        · cases h
        · split at h
          · cases h
          · cases h; exact write_contract hinv found hmode
  | resultRow first count =>
      simp only [exec] at h
      split at h
      · cases h
      · cases h
        refine ⟨⟨?_, fun _ _ => rfl, Or.inl rfl⟩, inv_of_eq hinv rfl rfl⟩
        intro event hmem
        simp only [List.mem_singleton] at hmem
        subst hmem
        trivial

theorem step_safe {fallback : Fallback} (hfb : FallbackSafe F fallback) {code : RawProgram}
    {c c' : Config} {events : List Event} (hinv : Inv F c)
    (h : Step F cat fallback code c events c') : Contract F c events c' ∧ Inv F c' := by
  cases h with
  | modeled _ _ _ hexec => exact exec_safe hinv hexec
  | fallback _ _ _ hstep => exact hfb _ _ _ _ hinv hstep

/-- Prefix safety from any configuration that satisfies the invariant. -/
theorem trace_safe {fallback : Fallback} (hfb : FallbackSafe F fallback) {code : RawProgram}
    {c c' : Config} {events : List Event} (h : Trace F cat fallback code c events c')
    (hinv : Inv F c) :
    Inv F c' ∧ (∀ event ∈ events, event.Allowed F) ∧
      (∀ table, Event.write table ∉ events →
        c'.working table = c.working table ∧
          (c'.committed table = c.committed table ∨ c'.committed table = c.working table)) ∧
      (Event.commit ∉ events → c'.committed = c.committed) := by
  revert hinv
  induction h with
  | nil =>
      intro hinv
      exact ⟨hinv, (fun _ h => by cases h), (fun _ _ => ⟨rfl, Or.inl rfl⟩), fun _ => rfl⟩
  | @cons c₁ c₂ c₃ events₁ events₂ hstep _ ih =>
      intro hinv
      obtain ⟨contract, inv₂⟩ := step_safe hfb hinv hstep
      obtain ⟨inv₃, allowed, frame, commit⟩ := ih inv₂
      refine ⟨inv₃, ?_, ?_, ?_⟩
      · intro event hmem
        rcases List.mem_append.mp hmem with h | h
        · exact contract.allowed event h
        · exact allowed event h
      · intro table hnot
        have h₁ : Event.write table ∉ events₁ := fun h => hnot (List.mem_append_left _ h)
        have h₂ : Event.write table ∉ events₂ := fun h => hnot (List.mem_append_right _ h)
        have hw₂ := contract.working table h₁
        obtain ⟨hw₃, hc₃⟩ := frame table h₂
        refine ⟨hw₃.trans hw₂, ?_⟩
        rcases contract.committed with hc | ⟨_, hc⟩
        · rcases hc₃ with h | h
          · exact Or.inl (h.trans (congrFun hc table))
          · exact Or.inr (h.trans hw₂)
        · rcases hc₃ with h | h
          · exact Or.inr ((h.trans (congrFun hc table)).trans hw₂)
          · exact Or.inr (h.trans hw₂)
      · intro hnot
        have h₁ : Event.commit ∉ events₁ := fun h => hnot (List.mem_append_left _ h)
        have h₂ : Event.commit ∉ events₂ := fun h => hnot (List.mem_append_right _ h)
        rcases contract.committed with hc | ⟨hmem, _⟩
        · exact (commit h₂).trans hc
        · exact absurd hmem h₁

theorem trace_initial_safe {fallback : Fallback} (hfb : FallbackSafe F fallback)
    {code : RawProgram} {store : Store} {c' : Config} {events : List Event}
    (h : Trace F cat fallback code (Config.initial store) events c') :
    Inv F c' ∧ (∀ event ∈ events, event.Allowed F) ∧
      (∀ table, Event.write table ∉ events →
        c'.working table = store table ∧ c'.committed table = store table) ∧
      (Event.commit ∉ events → c'.committed = store) := by
  obtain ⟨inv, allowed, frame, commit⟩ := trace_safe hfb h (inv_initial F store)
  refine ⟨inv, allowed, fun table hnot => ?_, commit⟩
  obtain ⟨hw, hc⟩ := frame table hnot
  exact ⟨hw, by rcases hc with h | h <;> exact h⟩

theorem fallbackSafe_none (F : Footprint) : FallbackSafe F Fallback.none :=
  fun _ _ _ _ _ h => h.elim

private theorem step_ok {code : RawProgram} {c c' : Config} {events : List Event}
    (h : step F cat code c = .ok (events, c')) : Step F cat Fallback.none code c events c' := by
  unfold step at h
  split at h
  · cases h
  · rename_i hactive
    cases hfetch : code[c.pc]? with
    | none => simp [hfetch] at h
    | some raw =>
      simp only [hfetch] at h
      cases hdec : decode? raw with
      | none => simp [hdec] at h
      | some instr =>
        simp only [hdec] at h
        exact .modeled (by simpa using hactive) hfetch hdec h

/-- The executable runner produces a prefix of the relational semantics with
the empty fallback. -/
theorem run_trace (code : RawProgram) :
    ∀ (fuel : Nat) (c : Config),
      Trace F cat Fallback.none code c (run F cat code fuel c).events (run F cat code fuel c).config
  | fuel, c => by
      unfold run
      split
      · exact .nil c
      · cases fuel with
        | zero => exact .nil c
        | succ fuel =>
          simp only
          split
          · exact .nil c
          · rename_i events after hstep
            exact .cons (step_ok hstep) (run_trace code fuel after)

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable
