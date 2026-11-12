module

public import Silmaril.Libc.Ptmalloc.Version.Defs
public import Silmaril.Libc.Ptmalloc.Version.V236
public import Silmaril.Libc.Ptmalloc.Version.V240
public import Silmaril.Libc.Ptmalloc.Version.Facts

/-!
# ptmalloc: the pins satisfy the algorithm's sanity conditions

* `pin239_ok`, `Versions.pin236_ok`, `Versions.pin240_ok`: each pinned `Config` satisfies
  `Config.Ok`, so every theorem stated for `∀ C, C.Ok → …` instantiates at it with no new proof
  (`Versions.atPin`, `at236`, `at239`, `at240`, and one line per `Task.algo.*` below).
* `Versions.pin236_matches`, `pin239_matches`, `pin240_matches`: every number of the records
  (statics, TLS offsets, GOT slots, tunable ids, entries, inlined-away helpers, DWARF layouts,
  `mp_`'s initial words against `Config`) equals the generated facts of the pinned file.
* `Versions.symbols236`/`239`/`240`: `Task.versions.symbols` for each pin, from the same facts.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

theorem pin239_ok : pin239.config.Ok := by decide

namespace Versions

theorem pin236_ok : pin236.config.Ok := by decide

theorem pin240_ok : pin240.config.Ok := by decide

/-- 2.39 and 2.40 run the same algorithm (`malloc.c`/`arena.c` are identical). -/
theorem config240_eq : pin240.config = pin239.config := rfl

/-- The three pins share one struct layout (DWARF-checked by the `*_matches` theorems). -/
theorem layout_eq : pin236.layout = pin239.layout ∧ pin240.layout = pin239.layout := ⟨rfl, rfl⟩

/-! ## The records against the generated facts -/

theorem pin236_matches : Matches pin236 facts236 := by decide +kernel

theorem pin239_matches : Matches pin239 facts239 := by decide +kernel

theorem pin240_matches : Matches pin240 facts240 := by decide +kernel

/-- The fact keys of the names `Task.versions.symbols` uses. -/
def taskNames : List (String × String) :=
  [("sym:main_arena", "main_arena"), ("sym:mp_", "mp_"), ("sym:tcache_key", "tcache_key"),
   ("sym:__curbrk", "__curbrk"), ("sym:__libc_malloc", "malloc"), ("sym:__libc_free", "free"),
   ("sym:_int_malloc", "_int_malloc"), ("sym:_int_free", "_int_free")]

/-- The facts under the names `Task.versions.symbols` uses (`main_arena`, `malloc`, …). -/
def taskFacts (facts : List (String × Nat)) : List (String × Nat) :=
  facts.filterMap fun x => (taskNames.lookup x.1).map (·, x.2)

/-- The Boolean form of `Task.versions.symbols`' per-fact condition. -/
def symbolsCheck (P : Pin) (x : String × Nat) : Bool :=
  (x.1 != "main_arena" || P.syms.mainArena == x.2) && (x.1 != "mp_" || P.syms.mp == x.2) &&
  (x.1 != "tcache_key" || P.syms.tcacheKey == x.2) &&
  (x.1 != "__curbrk" || P.syms.curbrk == x.2) &&
  (x.1 != "malloc" || P.entries.malloc == x.2) && (x.1 != "free" || P.entries.free == x.2) &&
  (x.1 != "_int_malloc" || P.entries.intMalloc == some x.2) &&
  (x.1 != "_int_free" || P.entries.intFree == some x.2)

theorem symbols_of_check (P : Pin) (facts : List (String × Nat))
    (h : facts.all (symbolsCheck P) = true) : Task.versions.symbols P facts := by
  intro nm v hm
  have := List.all_eq_true.1 h _ hm
  simp only [symbolsCheck, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩ := this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hn <;> subst hn <;> simp_all

theorem symbols236 : Task.versions.symbols pin236 (taskFacts facts236) :=
  symbols_of_check _ _ (by decide +kernel)

theorem symbols239 : Task.versions.symbols pin239 (taskFacts facts239) :=
  symbols_of_check _ _ (by decide +kernel)

theorem symbols240 : Task.versions.symbols pin240 (taskFacts facts240) :=
  symbols_of_check _ _ (by decide +kernel)

/-! ## Instantiation: algorithm-level theorems hold at every pin with no new proof -/

/-- **Instantiation at a pin**: a statement proved for every configuration satisfying `Ok`
holds for the pin's configuration. -/
theorem atPin {Q : Config → Prop} (h : ∀ C, C.Ok → Q C) (P : Pin) (hP : P.config.Ok) :
    Q P.config :=
  h _ hP

theorem at236 {Q : Config → Prop} (h : ∀ C, C.Ok → Q C) : Q pin236.config := h _ pin236_ok
theorem at239 {Q : Config → Prop} (h : ∀ C, C.Ok → Q C) : Q pin239.config := h _ pin239_ok
theorem at240 {Q : Config → Prop} (h : ∀ C, C.Ok → Q C) : Q pin240.config := h _ pin240_ok

/-! Each `Task.algo.*` body obligation is `C.Ok → body`; at a pin its `ok` theorem discharges
the guard. The statements below restate the bodies so a caller sees them at the pin; the proofs
are the application (definitional unfolding checks the restatement). For `pin239` see the
`algo` piece's own theorems (`pin239_ok`). -/

section
variable (F : ∀ C, Ops C)

theorem noAbort236 (h : ∀ C, Task.algo.noAbort C (F C)) :
    ∀ l, LocalWF pin236.config l →
      (∀ n, ∃ r, (F pin236.config).intMalloc l n = .ok r) ∧
      (∀ p u, (p, u) ∈ l.arenaLive pin236.config →
        ∃ l', (F pin236.config).intFree l (p - pin236.config.hdr) = .ok l') :=
  h _ pin236_ok

theorem noAbort240 (h : ∀ C, Task.algo.noAbort C (F C)) :
    ∀ l, LocalWF pin240.config l →
      (∀ n, ∃ r, (F pin240.config).intMalloc l n = .ok r) ∧
      (∀ p u, (p, u) ∈ l.arenaLive pin240.config →
        ∃ l', (F pin240.config).intFree l (p - pin240.config.hdr) = .ok l') :=
  h _ pin240_ok

theorem wfIntMalloc236 (h : ∀ C, Task.algo.wfIntMalloc C (F C)) :
    ∀ l l' n p, LocalWF pin236.config l → (F pin236.config).intMalloc l n = .ok (p, l') →
      LocalWF pin236.config l' ∧ Footprint.Within {} l l' ∧
      MallocLive pin236.config n p (l.live pin236.config) (l'.live pin236.config) :=
  h _ pin236_ok

theorem wfIntMalloc240 (h : ∀ C, Task.algo.wfIntMalloc C (F C)) :
    ∀ l l' n p, LocalWF pin240.config l → (F pin240.config).intMalloc l n = .ok (p, l') →
      LocalWF pin240.config l' ∧ Footprint.Within {} l l' ∧
      MallocLive pin240.config n p (l.live pin240.config) (l'.live pin240.config) :=
  h _ pin240_ok

theorem wfIntFree236 (h : ∀ C, Task.algo.wfIntFree C (F C)) :
    ∀ l l' p u, LocalWF pin236.config l → (p, u) ∈ l.arenaLive pin236.config →
      (F pin236.config).intFree l (p - pin236.config.hdr) = .ok l' →
      LocalWF pin236.config l' ∧ Footprint.Within {} l l' ∧
      (l'.live pin236.config).Perm ((l.live pin236.config).erase (p, u)) :=
  h _ pin236_ok

theorem wfIntFree240 (h : ∀ C, Task.algo.wfIntFree C (F C)) :
    ∀ l l' p u, LocalWF pin240.config l → (p, u) ∈ l.arenaLive pin240.config →
      (F pin240.config).intFree l (p - pin240.config.hdr) = .ok l' →
      LocalWF pin240.config l' ∧ Footprint.Within {} l l' ∧
      (l'.live pin240.config).Perm ((l.live pin240.config).erase (p, u)) :=
  h _ pin240_ok

theorem wfWorld236 (h : ∀ C, Task.algo.wfWorld C (F C)) :
    ∀ w tid, WorldWF pin236.config w → tid ∈ w.tids →
      (∀ n p w', (F pin236.config).malloc w tid n = .ok (p, w') →
        WorldWF pin236.config w' ∧
        MallocLive pin236.config n p (w.live pin236.config) (w'.live pin236.config)) ∧
      (∀ p u w', (p, u) ∈ w.live pin236.config → (F pin236.config).free w tid p = .ok w' →
        WorldWF pin236.config w' ∧
        (w'.live pin236.config).Perm ((w.live pin236.config).erase (p, u))) :=
  h _ pin236_ok

theorem wfWorld240 (h : ∀ C, Task.algo.wfWorld C (F C)) :
    ∀ w tid, WorldWF pin240.config w → tid ∈ w.tids →
      (∀ n p w', (F pin240.config).malloc w tid n = .ok (p, w') →
        WorldWF pin240.config w' ∧
        MallocLive pin240.config n p (w.live pin240.config) (w'.live pin240.config)) ∧
      (∀ p u w', (p, u) ∈ w.live pin240.config → (F pin240.config).free w tid p = .ok w' →
        WorldWF pin240.config w' ∧
        (w'.live pin240.config).Perm ((w.live pin240.config).erase (p, u))) :=
  h _ pin240_ok

theorem mallocTotal236 (h : ∀ C, Task.algo.mallocTotal C (F C)) :
    ∀ w tid, WorldWF pin236.config w → tid ∈ w.tids →
      (∀ n, ∃ r, (F pin236.config).malloc w tid n = .ok r) ∧
      (∀ p u, (p, u) ∈ w.live pin236.config → ∃ w', (F pin236.config).free w tid p = .ok w') :=
  h _ pin236_ok

theorem mallocTotal240 (h : ∀ C, Task.algo.mallocTotal C (F C)) :
    ∀ w tid, WorldWF pin240.config w → tid ∈ w.tids →
      (∀ n, ∃ r, (F pin240.config).malloc w tid n = .ok r) ∧
      (∀ p u, (p, u) ∈ w.live pin240.config → ∃ w', (F pin240.config).free w tid p = .ok w') :=
  h _ pin240_ok

end

/-- The leaf lemmas are stated for all configurations: their pin instances are applications. -/
theorem leafTcacheGet236 (h : Task.algo.leafTcacheGet) :
    ∀ (l l' : Local) (i p : Nat), LocalWF pin236.config l →
      l.tcacheGet pin236.config i = some (p, l') →
      LocalWF pin236.config l' ∧
      Footprint.Within { arena := false, shared := false, kernel := false } l l' ∧
      ∃ u, ((l.thread.parked pin236.config).Perm ((p, u) :: l'.thread.parked pin236.config)) ∧
        p % pin236.config.align = 0 :=
  fun l l' i p => h _ l l' i p pin236_ok

theorem leafTcacheGet240 (h : Task.algo.leafTcacheGet) :
    ∀ (l l' : Local) (i p : Nat), LocalWF pin240.config l →
      l.tcacheGet pin240.config i = some (p, l') →
      LocalWF pin240.config l' ∧
      Footprint.Within { arena := false, shared := false, kernel := false } l l' ∧
      ∃ u, ((l.thread.parked pin240.config).Perm ((p, u) :: l'.thread.parked pin240.config)) ∧
        p % pin240.config.align = 0 :=
  fun l l' i p => h _ l l' i p pin240_ok

end Versions

end Silmaril.Libc.Ptmalloc
