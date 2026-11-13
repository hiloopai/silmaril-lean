module

public import Silmaril.Wasm.Component.FXRes.Handle.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.Handle.Basic

/-!
# Continuations as Component Model resources: results

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.Handle.Basic`.

For every run of the joint system (`JSteps`) from an empty handle table and an empty
continuation store:

* `jsteps_table_protocol`: **the `cont` handle table respects the handle protocol** in both
  roles: `resource.new` hands out a handle that is not live, and `take`, `drop` and `borrow` only
  touch live handles (no use after `take`, no use or drop after `drop`);
* `jsteps_own_protocol`: **the handles are owned resources**: the table history read as
  ownership events (`ownEv`) is accepted by `obProto`: a handle is used only while held and is
  consumed (`take`, `drop`) only while owned, so at most once per allocation;
* `jsteps_store_protocol`, `jsteps_one_shot`: **the continuations stay one-shot** across the
  component boundary: the continuation-store history (FX steps and built-ins) is accepted by the
  handle protocol, and each store index is consumed at most once.

For single built-ins:

* `take_dead`, `drop_dead`: after `take` or `drop` of handle `i`, `i` is dead in the table (every
  later built-in on `i` fails until `resource.new` hands `i` out again);
* `builtin_live`: `take`, `drop` and `borrow` succeed only on a live handle;
* `borrow_pure`: **a `borrow<cont>` consumes nothing**: the built-in leaves the state unchanged,
  so a borrowed continuation can be neither resumed nor dropped through the borrow;
* `new_moves`: `resource.new` **moves** the continuation: its store entry is consumed (so the
  stale `contRef` traps, `stale_resume_traps`), and the table holds it.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Resource
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **The `cont` handle table respects the handle protocol**, in both roles. -/
theorem jsteps_table_protocol {st st' : JState H} {tevs : List (Table.Event ContFX)}
    {sevs : List (HEv ℕ)} (h : JSteps P host fx st tevs sevs st') (h0 : st.tab = Table.empty)
    (r : Role) : (handleProto ℕ r).Accepts (tevs.map tableEv) := by
  have ht : Table.Steps Table.empty tevs st'.tab := h0 ▸ jsteps_tab h
  exact table_steps_accepts ht r

/-- **The `cont` handles are owned resources**: the ownership protocol accepts the history. -/
theorem jsteps_own_protocol {st st' : JState H} {tevs : List (Table.Event ContFX)}
    {sevs : List (HEv ℕ)} (h : JSteps P host fx st tevs sevs st') (h0 : st.tab = Table.empty) :
    (obProto ℕ).Accepts (tevs.map ownEv) := by
  have ht : Table.Steps Table.empty tevs st'.tab := h0 ▸ jsteps_tab h
  obtain ⟨L, hL, -⟩ := table_steps_run ht .client freeOK_empty tabRel_empty
  have ho : (obProto ℕ).run (some (owned [])) ((tevs.map tableEv).map hevOwn) =
      some (some (owned L)) := client_run_own List.nodup_nil hL
  have hmap : (tevs.map tableEv).map hevOwn = tevs.map ownEv := by
    rw [List.map_map]
    rfl
  show ((obProto ℕ).run (some []) _).isSome
  rw [← hmap]
  exact ho ▸ rfl

/-- **The continuation store respects the handle protocol across the boundary.** -/
theorem jsteps_store_protocol {st st' : JState H} {tevs : List (Table.Event ContFX)}
    {sevs : List (HEv ℕ)} (h : JSteps P host fx st tevs sevs st') (h0 : st.cfg.conts = [])
    (r : Role) : (handleProto ℕ r).Accepts sevs := by
  have hs : KSteps [] st'.cfg.conts sevs := h0 ▸ jsteps_store h
  obtain ⟨L, hL, -⟩ := ksteps_run hs r kRel_nil
  show ((handleProto ℕ r).run (some []) sevs).isSome
  rw [hL]
  rfl

/-- **One-shot across the boundary**: each continuation-store index is consumed at most once. -/
theorem jsteps_one_shot {st st' : JState H} {tevs : List (Table.Event ContFX)}
    {sevs : List (HEv ℕ)} (h : JSteps P host fx st tevs sevs st') (k : ℕ) :
    sevs.count (.free k) ≤ 1 :=
  ksteps_count_free (jsteps_store h) k

/-- After `take` of handle `i`, `i` is dead. -/
theorem take_dead {st st' : JState H} {i : ℕ} {C : ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st .take (.removed i C) sevs st') : st'.tab.get? i = none :=
  rstep_removed h

/-- After `drop` of handle `i`, `i` is dead. -/
theorem drop_dead {st st' : JState H} {i : ℕ} {C : ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st .drop (.removed i C) sevs st') : st'.tab.get? i = none :=
  rstep_removed h

/-- `take`, `drop` and `borrow` succeed only on a live handle. -/
theorem builtin_live {st st' : JState H} {o : ROp} {ev : Table.Event ContFX}
    {sevs : List (HEv ℕ)} (h : RStep st o ev sevs st') (ho : o ≠ .new) :
    ∃ i C, st.tab.get? i = some C ∧ (ev = .removed i C ∨ ev = .got i C) :=
  rstep_live h ho

/-- **A `borrow<cont>` consumes nothing.** -/
theorem borrow_pure {st st' : JState H} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st .borrow ev sevs st') : st' = st ∧ sevs = [] :=
  rstep_borrow h

/-- **`resource.new` moves the continuation** from the store into the table. -/
theorem new_moves {st st' : JState H} {ev : Table.Event ContFX} {sevs : List (HEv ℕ)}
    (h : RStep st .new ev sevs st') :
    ∃ k i C, st.cfg.conts[k]? = some (some C) ∧ Consumed st'.cfg.conts k ∧ ev = .added i C ∧
      st.tab.add? C = some (i, st'.tab) :=
  rstep_new h

/-- A stale continuation reference (consumed, e.g. moved into the table) traps on `resume`. -/
theorem stale_resume_traps {s : Store H} {K : KStore} {f : Frame} {k : ℕ}
    (hk : Consumed K k) (vs : List FVal) (ct : TypeIdx) (hs : List OnClause) :
    StepFX' P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K, f, [.core .trap]⟩ :=
  .resumeUsed hk

end Silmaril.Wasm.Component.FXRes
