module

public import Silmaril.Formats.Dasl.Arena.Prolly.Surface.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Surface

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.Surface
open Silmaril.Semantics.Prolly (Policy)

variable {Owner Kind Name Key Payload Authority : Type} {basis : Indexed Name Key Payload}
variable {view next : View Owner Kind basis}

theorem mount_valid {owner : Owner} {kind : Kind} (mounted : mount basis owner kind = some view) :
    view.Valid := by
  cases swept : Sweep.sweep? basis [] (List.range basis.blocks.size) with
  | none => simp [mount, swept, Bind.bind, Option.bind] at mounted
  | some resident =>
    simp [mount, swept, Bind.bind, Option.bind, Pure.pure] at mounted
    subst view
    exact swept

private theorem retained_slot (valid : view.Valid) (index : Nat) :
    (∃ block, view.resident.slots[index]? = some (some block)) ↔ index ∈ view.retained := by
  have spec := Sweep.sweep_spec valid
  rw [spec.2.2]
  by_cases kept : index ∈ view.retained
  · have ready := (Bool.and_eq_true_iff.mp spec.1).2
    have resident := List.all_eq_true.mp ready index kept
    cases found : basis.blocks[index]? with
    | none => simp [found] at resident
    | some block => simp [kept]
  · cases basis.blocks[index]? <;> simp [kept]

theorem resolve_local_iff [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    (token : Token Owner Kind) (ref : Handle Name) :
    view.resolve (.local token) = .ok ref ↔
      token.owner = view.owner ∧ token.kind = view.kind ∧ token.index ∈ view.retained ∧ ref = .local token.index := by
  by_cases owner : token.owner = view.owner
  · by_cases kind : token.kind = view.kind
    · rw [← retained_slot valid token.index]
      cases found : view.resident.slots[token.index]? with
      | none => simp [View.resolve, owner, kind, found]
      | some slot => cases slot <;> simp [View.resolve, owner, kind, found, eq_comm]
    · simp [View.resolve, owner, kind]
  · simp [View.resolve, owner]

private theorem resolve_retained [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    {target : Target Owner Kind Name} {ref : Handle Name} (checked : view.resolve target = .ok ref) :
    Sweep.kept view.retained ref = true := by
  cases target with
  | backing name => cases checked; rfl
  | «local» token =>
    obtain ⟨_, _, kept, rfl⟩ := (resolve_local_iff valid token ref).mp checked
    simpa [Sweep.kept] using kept

private theorem reroot (valid : view.Valid) (roots : List (Handle Name))
    (kept : ∀ ref ∈ roots, Sweep.kept view.retained ref = true) :
    ({view with roots} : View Owner Kind basis).Valid := by
  have ready := (Bool.and_eq_true_iff.mp (Sweep.sweep_spec valid).1).2
  have allRoots := List.all_eq_true.mpr kept
  have newCheck : Sweep.check basis roots view.retained = true := Bool.and_eq_true_iff.mpr ⟨allRoots, ready⟩
  simpa [View.Valid, Sweep.sweep?, newCheck, (Sweep.sweep_spec valid).1] using valid

theorem register_spec [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    {target : Target Owner Kind Name} (registered : view.register target = .ok next) :
    ∃ ref, view.resolve target = .ok ref ∧ next = {view with roots := ref :: view.roots} ∧ next.Valid := by
  unfold View.register at registered
  cases checked : view.resolve target with
  | error fault => simp [checked, Except.map] at registered
  | ok ref =>
    simp [checked, Except.map] at registered
    subst next
    refine ⟨ref, rfl, rfl, reroot valid _ ?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | prior
    · exact resolve_retained valid checked
    · exact Sweep.keep_reachable (Sweep.sweep_spec valid).1 (.root prior)

theorem unregister_spec [DecidableEq Owner] [DecidableEq Kind] [DecidableEq Name] (valid : view.Valid)
    {target : Target Owner Kind Name} (unregistered : view.unregister target = .ok next) :
    ∃ ref, view.resolve target = .ok ref ∧ next = {view with roots := view.roots.filter (· != ref)} ∧ next.Valid := by
  unfold View.unregister at unregistered
  cases checked : view.resolve target with
  | error fault => simp [checked, Except.map] at unregistered
  | ok ref =>
    simp [checked, Except.map] at unregistered
    subst next
    refine ⟨ref, rfl, rfl, reroot valid _ ?_⟩
    intro child member
    exact Sweep.keep_reachable (Sweep.sweep_spec valid).1 (.root (List.mem_filter.mp member).1)

theorem collect_spec (collected : view.collect = some next) :
    Sweep.markAndSweep? basis view.roots = some next.resident ∧
      next = {view with retained := Sweep.mark basis view.roots, resident := next.resident} ∧
      (∀ index ∈ next.retained, index ∈ view.retained) ∧ next.Valid := by
  unfold View.collect at collected
  by_cases retained : (Sweep.mark basis view.roots).all view.retained.contains = true
  · cases swept : Sweep.markAndSweep? basis view.roots with
    | none => simp [retained, swept, Bind.bind, Option.bind] at collected
    | some resident =>
      simp [retained, swept, Bind.bind, Option.bind, Pure.pure] at collected
      subst next
      exact ⟨rfl, rfl, fun index kept => List.contains_iff_mem.mp (List.all_eq_true.mp retained index kept), swept⟩
  · simp [retained] at collected

theorem collect_exists (valid : view.Valid) (ready : Sweep.Markable basis view.roots) :
    ∃ next, view.collect = some next := by
  obtain ⟨resident, swept⟩ := Sweep.markAndSweep_exists ready
  have retained : (Sweep.mark basis view.roots).all view.retained.contains = true := by
    refine List.all_eq_true.mpr fun index member => ?_
    simpa [Sweep.kept] using
      Sweep.keep_reachable (Sweep.sweep_spec valid).1 ((Sweep.mark_exact swept).mp member)
  simp [View.collect, retained, swept, Bind.bind, Option.bind, Pure.pure]

theorem lookup_registered [DecidableEq Owner] [DecidableEq Kind] [LinearOrder Key]
    (valid : view.Valid) (collected : view.collect = some next) (external : Reader Name Key Payload)
    (policy : Policy Key) (fuel : Nat) (key : Key) {target : Target Owner Kind Name} {ref : Handle Name}
    (resolved : view.resolve target = .ok ref) (registered : ref ∈ view.roots) :
    next.lookup external policy fuel target key = view.lookup external policy fuel target key := by
  obtain ⟨swept, frame, _, nextValid⟩ := collect_spec collected
  have nextRoots : next.roots = view.roots := by rw [frame]
  have nextOwner : next.owner = view.owner := by rw [frame]
  have nextKind : next.kind = view.kind := by rw [frame]
  have kept := Sweep.keep_reachable (Sweep.sweep_spec valid).1 (.root registered)
  have nextResolve : next.resolve target = .ok ref := by
    have nextKept := Sweep.keep_reachable (Sweep.sweep_spec nextValid).1 (.root (nextRoots ▸ registered))
    cases target with
    | backing name => exact resolved
    | «local» token =>
      obtain ⟨owner, kind, _, rfl⟩ := (resolve_local_iff valid token ref).mp resolved
      exact (resolve_local_iff nextValid token _).mpr
        ⟨owner.trans nextOwner.symm, kind.trans nextKind.symm,
          by simpa [Sweep.kept] using nextKept, rfl⟩
  have beforeRoute := Sweep.route_kept valid external policy.width fuel key
    (expected := none) kept
  have afterRoute := Sweep.route_marked swept external policy.width fuel key
    (expected := none) (.root registered)
  simp only [View.lookup, resolved, nextResolve, Bind.bind, Except.bind, View.read, Reader.lookup]
  rw [beforeRoute, afterRoute]

theorem collect_stale [DecidableEq Owner] [DecidableEq Kind] (collected : view.collect = some next)
    (token : Token Owner Kind) (owner : token.owner = view.owner) (kind : token.kind = view.kind)
    (inside : token.index < basis.blocks.size) (retired : token.index ∉ next.retained) :
    next.resolve (.local token) = .error .stale := by
  obtain ⟨_, frame, _, valid⟩ := collect_spec collected
  have nextOwner : token.owner = next.owner := by rw [frame]; exact owner
  have nextKind : token.kind = next.kind := by rw [frame]; exact kind
  obtain ⟨_, _, slots⟩ := Sweep.sweep_spec valid
  simp [View.resolve, nextOwner, nextKind, slots, retired, Array.getElem?_eq_getElem inside]

theorem stale_persists [DecidableEq Owner] [DecidableEq Kind] (valid : view.Valid)
    (collected : view.collect = some next) {token : Token Owner Kind}
    (stale : view.resolve (.local token) = .error .stale) : next.resolve (.local token) = .error .stale := by
  by_cases owner : token.owner = view.owner
  · by_cases kind : token.kind = view.kind
    · have absent : view.resident.slots[token.index]? = some none := by
        cases found : view.resident.slots[token.index]? with
        | none => simp [View.resolve, owner, kind, found] at stale
        | some slot => cases slot <;> simp_all [View.resolve]
      have inside : token.index < basis.blocks.size := by
        rw [← (Sweep.sweep_spec valid).2.1]
        exact Array.getElem?_eq_some_iff.mp absent |>.choose
      have notRetained : token.index ∉ view.retained := by
        intro kept
        obtain ⟨_, hit⟩ := (retained_slot valid token.index).mpr kept
        rw [absent] at hit
        cases hit
      exact collect_stale collected token owner kind inside (fun kept => notRetained ((collect_spec collected).2.2.1 _ kept))
    · simp [View.resolve, owner, kind] at stale
  · simp [View.resolve, owner] at stale

theorem layer_collect_spec {layer next : Layer Owner Kind Authority basis}
    (collected : layer.collect = some next) :
    layer.surface.collect = some next.surface ∧ next.authority = layer.authority := by
  unfold Layer.collect at collected
  cases swept : layer.surface.collect <;> simp [swept] at collected
  subst next
  exact ⟨rfl, rfl⟩

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Surface
