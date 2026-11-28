module

public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Defs
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable.Footprint

/-! Prefix safety, frame and guard-transparency theorems for the writable VDBE
fragment.

The safety theorems quantify over every raw program, every catalog, every
store and every finite prefix, with no validity, admission or refusal premise
on the program. For the relation `Trace` the only premise is `FallbackSafe` for
the behavior of unmodeled raw instructions; the executable `run` has no
fallback and needs no premise.

Scope: one statement in simple autocommit over an in-memory store, with a fixed
catalog. Nothing here concerns termination, result correctness, SQL
compilation, rollback, durability, concurrency, or native SQLite. -/

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Writable

open Silmaril.Formats.Sqlite

/-! ### Every raw program -/

theorem inv_initial (F : Footprint) (store : Store) : Inv F (Config.initial store) :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.inv_initial F store

/-- One modeled instruction, with any operands, meets the transition contract. -/
theorem exec_safe {F : Footprint} {cat : Catalog} {instr : Instr} {c c' : Config}
    {events : List Event} (hinv : Inv F c) (h : exec F cat instr c = .ok (events, c')) :
    Contract F c events c' ∧ Inv F c' :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.exec_safe hinv h

theorem fallbackSafe_none (F : Footprint) : FallbackSafe F Fallback.none :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.fallbackSafe_none F

/-- Every finite prefix of every raw program from a fresh configuration:
* `Inv`: every open database was granted (`.db` touch in `F`) and every cursor
  was opened by a granted `.table` touch under a covering transaction;
* every event is permitted, so every `touch` is in `F` and every attempted
  write is to a table `F` lets the program write;
* a table with no `write` event is unchanged in the working and committed stores;
* without a `commit` event the committed store is the initial store. -/
theorem trace_safe {F : Footprint} {cat : Catalog} {fallback : Fallback}
    (hfb : FallbackSafe F fallback) {code : RawProgram} {store : Store} {c' : Config}
    {events : List Event} (h : Trace F cat fallback code (Config.initial store) events c') :
    Inv F c' ∧ (∀ event ∈ events, event.Allowed F) ∧
      (∀ table, Event.write table ∉ events →
        c'.working table = store table ∧ c'.committed table = store table) ∧
      (Event.commit ∉ events → c'.committed = store) :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.trace_initial_safe hfb h

/-- Unrelated-table frame: tables the footprint does not let the program write
are unchanged, in the working store and in the committed store. -/
theorem trace_frame {F : Footprint} {cat : Catalog} {fallback : Fallback}
    (hfb : FallbackSafe F fallback) {code : RawProgram} {store : Store} {c' : Config}
    {events : List Event} (h : Trace F cat fallback code (Config.initial store) events c') :
    Frame F.Writes store c'.working ∧ Frame F.Writes store c'.committed :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.trace_frame hfb h

/-- Only configured databases are opened, and every cursor reaches a table
through a configured database. -/
theorem trace_opens_configured {F : Footprint} {cat : Catalog} {fallback : Fallback}
    (hfb : FallbackSafe F fallback) {code : RawProgram} {store : Store} {c' : Config}
    {events : List Event} (h : Trace F cat fallback code (Config.initial store) events c') :
    (∀ db mode, c'.transactions db = some mode → F.allows (.db db mode) = true) ∧
      (∀ identifier cursor, c'.cursors identifier = some cursor →
        F.allows (.table cursor.table cursor.mode) = true ∧ F.Configured cursor.table.db) :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.trace_opens_configured hfb h

/-- The executable runner yields prefixes of `Trace` with no fallback. -/
theorem run_trace {F : Footprint} {cat : Catalog} (code : RawProgram) (fuel : Nat) (c : Config) :
    Trace F cat Fallback.none code c (run F cat code fuel c).events (run F cat code fuel c).config :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.run_trace code fuel c

/-- `trace_safe` for the executable runner: every raw program, store and fuel. -/
theorem run_safe (F : Footprint) (cat : Catalog) (code : RawProgram) (fuel : Nat) (store : Store) :
    let out := run F cat code fuel (Config.initial store)
    Inv F out.config ∧ (∀ event ∈ out.events, event.Allowed F) ∧
      (∀ table, Event.write table ∉ out.events →
        out.config.working table = store table ∧ out.config.committed table = store table) ∧
      (Event.commit ∉ out.events → out.config.committed = store) :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.run_initial_safe F cat code fuel store

theorem run_frame (F : Footprint) (cat : Catalog) (code : RawProgram) (fuel : Nat) (store : Store) :
    Frame F.Writes store (run F cat code fuel (Config.initial store)).config.committed :=
  (trace_frame (fallbackSafe_none F) (run_trace code fuel _)).2

/-- Under a read-only footprint nothing is written or committed differently. -/
theorem run_readOnly (F : Footprint) (cat : Catalog) (code : RawProgram) (fuel : Nat)
    (store : Store) :
    let out := run F.readOnly cat code fuel (Config.initial store)
    (∀ table, Event.write table ∉ out.events) ∧ out.config.working = store ∧
      out.config.committed = store :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.run_readOnly F cat code fuel store

/-! ### Bytecode footprint -/

/-- A permitted request behaves as without a guard. -/
theorem exec_eq_top {F : Footprint} {cat : Catalog} {instr : Instr} (c : Config)
    (h : (instr.touch? cat).all F.allows = true) :
    exec F cat instr c = exec Footprint.top cat instr c :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.exec_eq_top c h

theorem within_iff {F : Footprint} {cat : Catalog} {code : RawProgram} :
    within F cat code = true ↔
      (∀ raw ∈ code.toList, (decode? raw).isSome = true) ∧
        ∀ touch ∈ staticTouches cat code, F.allows touch = true :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.within_iff

theorem within_mono {small large : Footprint} (hle : small.Le large) {cat : Catalog}
    {code : RawProgram} (h : within small cat code = true) : within large cat code = true :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.within_mono hle h

/-- Guard transparency: code within the footprint runs identically with and
without the guard, so the guard never refuses it. -/
theorem run_eq_top {F : Footprint} {cat : Catalog} {code : RawProgram}
    (h : within F cat code = true) (fuel : Nat) (c : Config) :
    run F cat code fuel c = run Footprint.top cat code fuel c :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.run_eq_top h fuel c

/-- The syntactic restriction implies the semantic one, for every fallback. -/
theorem targetRestricted_of_within {F : Footprint} {cat : Catalog} {code : RawProgram}
    (h : within F cat code = true) : TargetRestricted F cat code :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.targetRestricted_of_within h

/-! ### Autocommit scripts -/

/-- Every list of raw programs, run in autocommit sequence: permitted events,
and the final store differs from the initial one only on logged writes. -/
theorem runScript_safe (F : Footprint) (cat : Catalog) (fuel : Nat) (codes : List RawProgram)
    (store : Store) :
    (∀ event ∈ (runScript F cat fuel codes store).1, event.Allowed F) ∧
      Frame (fun table => Event.write table ∈ (runScript F cat fuel codes store).1)
        store (runScript F cat fuel codes store).2 :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.runScript_safe F cat fuel codes store

theorem runScript_frame (F : Footprint) (cat : Catalog) (fuel : Nat) (codes : List RawProgram)
    (store : Store) : Frame F.Writes store (runScript F cat fuel codes store).2 :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.runScript_frame F cat fuel codes store

theorem runScript_eq_top {F : Footprint} {cat : Catalog} {fuel : Nat} {codes : List RawProgram}
    (h : ∀ code ∈ codes, within F cat code = true) (store : Store) :
    runScript F cat fuel codes store = runScript Footprint.top cat fuel codes store :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.runScript_eq_top h store

theorem frame_trans {small large : TableId → Prop} {s₁ s₂ s₃ : Store}
    (h₁ : Frame small s₁ s₂) (h₂ : Frame large s₂ s₃) :
    Frame (fun table => small table ∨ large table) s₁ s₃ :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.frame_trans h₁ h₂

theorem frame_mono {small large : TableId → Prop} (hle : ∀ table, small table → large table)
    {before after : Store} (h : Frame small before after) : Frame large before after :=
  fun table hl => h table fun hs => hl (hle table hs)

end Silmaril.Machine.SQLite.VirtualMachine.Writable
