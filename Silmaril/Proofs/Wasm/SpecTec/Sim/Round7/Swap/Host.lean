module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.Encode
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Host
public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2.Thms

/-!
# Round 7, the export swap: `$hostcall` (round 2, pass 5)

Item 3 of the plan for `Round7.Swap.Task.stepErase` (`docs/projects/spectec/README.md`, §4): the `$hostcall` primitive and the swap set.

* `host_mods_sub`: **a finite, export-parametric host invents no module instance.** Every module
  of a store the host returns is a module of the store it was called in. Otherwise, rewriting
  only the exports of the new module (which `HostExportParam` allows) would give infinitely many
  distinct outcomes of one call, against `HostFinite`.
* `allIn_outcomeV_of_host`: so, if every module record of the calling store satisfies `Q`, every
  outcome image is `AllIn Q`. With `Q := QC c` this is "the outcomes stay in the swap set".
* `eraseV_outcomeV`: erasing an outcome image is the image of the stripped outcome.
* `hostcallCall_erase`: **`$hostcall` commutes with `eraseV` up to the order of its answer**. At
  the arguments of a host call whose store and stripped store have unique preimages under
  `storeV hn`, round 4's primitive answers lists `xs` (at the call) and `ys` (at the erased
  call) with `b ∈ ys ↔ ∃ a ∈ xs, eraseV a = b`, and every `a ∈ xs` is `AllIn Q` when the calling
  store's module records are. The uniqueness hypotheses are what `hostcallCall`'s choice of a
  preimage needs; `Round5.FwdRef2.storeV_inj_typed` gives them for stores with typed images.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

/-! ## A finite, export-parametric host invents no module -/

/-- The export-only rewriting that keeps the modules of `M` and gives every other module `k`
copies of `e` as its exports. -/
def padExp (M : List ModuleInst) (e : ExportInst) (k : Nat) (m : ModuleInst) : ModuleInst :=
  open Classical in
  if m ∈ M then m else { m with exports := List.replicate k e }

theorem exportOnly_padExp (M : List ModuleInst) (e : ExportInst) (k : Nat) :
    ExportOnly (padExp M e k) := by
  intro m
  unfold padExp
  split <;> rfl

theorem mapStore_padExp_of {M : List ModuleInst} {e : ExportInst} {k : Nat} {s : Store H}
    (hs : ∀ fi ∈ s.funcs, fi.module ∈ M) : mapStore (padExp M e k) s = s := by
  obtain ⟨tags, globals, mems, tables, funcs, datas, elems, structs, arrays, exns⟩ := s
  simp only [mapStore, Store.mk.injEq, and_true, true_and]
  conv => rhs; rw [← List.map_id funcs]
  refine List.map_congr_left fun fi hfi => ?_
  simp only [mapFI, padExp, hs fi hfi, ite_true, id]

/-- Two functions that agree on a list's images agree at each of its members. -/
theorem eq_of_map_eq {α β : Type} {f g : α → β} {l : List α} (h : l.map f = l.map g) {a : α}
    (ha : a ∈ l) : f a = g a :=
  List.map_inj_left.1 h a ha

/-- A list without duplicates is no longer than a list containing it. -/
theorem length_le_of_nodup_subset {α : Type} {l₁ l₂ : List α} (hn : l₁.Nodup)
    (hs : ∀ a ∈ l₁, a ∈ l₂) : l₁.length ≤ l₂.length := by
  classical
  exact (List.subperm_of_subset hn hs).length_le

/-- An injective map from `Nat` into the members of a list is impossible. -/
theorem not_inj_into_list {α : Type} (f : Nat → α) (hf : ∀ i j, f i = f j → i = j)
    (os : List α) (hm : ∀ k, f k ∈ os) : False := by
  have hnd : ((List.range (os.length + 1)).map f).Nodup :=
    (List.nodup_range).map_on fun i _ j _ h => hf i j h
  have hle := length_le_of_nodup_subset hnd fun a ha => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
    exact hm k
  simp only [List.length_map, List.length_range] at hle
  omega

/-- The `k`-th export padding of a returned outcome. -/
def padOut (M : List ModuleInst) (e : ExportInst) (s' : Store H) (r : Result) (k : Nat) :
    Silmaril.Wasm.Execution.Host.Outcome (Store H) Result :=
  .returned (mapStore (padExp M e k) s') r

/-- Every padding of an outcome of a call in a store whose modules are in `M` is an outcome. -/
theorem host_padOut {host : HostSemantics H} (hp : HostExportParam host) {h : H}
    {s s' : Store H} {vs : List Val} {r : Result} {M : List ModuleInst} (e : ExportInst)
    (hsM : ∀ fi ∈ s.funcs, fi.module ∈ M) (ho : host h s vs (.returned s' r)) (k : Nat) :
    host h s vs (padOut M e s' r k) := by
  have hk : host h (mapStore (padExp M e k) s) vs (mapOutcome (padExp M e k) (.returned s' r)) :=
    hp (padExp M e k) (exportOnly_padExp M e k) h s vs _ ho
  have hs : mapStore (padExp M e k) s = s := mapStore_padExp_of hsM
  rw [hs] at hk
  exact hk

/-- Distinct paddings differ, at a module of `s'` outside `M`. -/
theorem padOut_inj {M : List ModuleInst} (e : ExportInst) {s' : Store H} {r : Result}
    {fi₀ : FuncInst H} (hfi₀ : fi₀ ∈ s'.funcs) (hnot : fi₀.module ∉ M) (i j : Nat)
    (hij : padOut M e s' r i = padOut M e s' r j) : i = j := by
  have hst : mapStore (padExp M e i) s' = mapStore (padExp M e j) s' := by
    simpa only [padOut, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq, and_true] using hij
  have hfu : s'.funcs.map (mapFI (padExp M e i)) = s'.funcs.map (mapFI (padExp M e j)) :=
    congrArg Store.funcs hst
  have hfi : mapFI (padExp M e i) fi₀ = mapFI (padExp M e j) fi₀ := eq_of_map_eq hfu hfi₀
  have hex : (mapFI (padExp M e i) fi₀).module.exports.length =
      (mapFI (padExp M e j) fi₀).module.exports.length := by rw [hfi]
  simpa only [mapFI, padExp, hnot, ite_false, List.length_replicate] using hex

/-- **A finite, export-parametric host returns only modules of the calling store.** -/
theorem host_mods_sub {host : HostSemantics H} (hf : HostFinite host) (hp : HostExportParam host)
    {h : H} {s s' : Store H} {vs : List Val} {r : Result}
    (ho : host h s vs (.returned s' r)) :
    ∀ fi ∈ s'.funcs, fi.module ∈ s.funcs.map FuncInst.module := by
  intro fi₀ hfi₀
  refine Classical.byContradiction fun hnot => ?_
  have hsM : ∀ fi ∈ s.funcs, fi.module ∈ s.funcs.map FuncInst.module :=
    fun fi hfi => List.mem_map_of_mem hfi
  obtain ⟨os, hos⟩ : ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
      ∀ o, host h s vs o ↔ o ∈ os := hf h s vs
  have hmem : ∀ k, padOut (s.funcs.map FuncInst.module) ⟨"", .func 0⟩ s' r k ∈ os :=
    fun k => (hos _).1 (host_padOut hp _ hsM ho k)
  exact not_inj_into_list _ (padOut_inj _ hfi₀ hnot) os hmem

/-! ## The outcomes stay in the swap set -/

section Outcomes

variable {Q : Value → Prop}

/-- A module record of an `AllIn Q` store satisfies `Q`. -/
theorem q_of_allIn_storeV (hn : H → String) {s : Store H} (hs : AllIn Q (storeV hn s)) :
    ∀ fi ∈ s.funcs, Q (moduleInstToValue CT fi.module) := by
  intro fi hfi
  have hF : AllIn Q (.list (s.funcs.map (funcInstV hn))) := by
    simp only [storeV, AllIn_struct, AllInf_cons] at hs
    exact hs.2.2.2.2.2.1
  simp only [AllIn_list, allIns_iff, List.mem_map] at hF
  have hfv := hF _ ⟨fi, hfi, rfl⟩
  simp only [funcInstV, AllIn_struct, AllInf_cons] at hfv
  exact hfv.2.2.1.1 (by simp [hasExp])

@[simp] theorem nxB_resultV (r : Result) : nxB (resultV r) = true := by
  cases r <;> simp [resultV, nxB_valV]

/-- **The outcomes of a finite, export-parametric host stay in `AllIn Q`**, when the module
records of the calling store satisfy `Q`. -/
theorem allIn_outcomeV_of_host (hn : H → String) {host : HostSemantics H} (hf : HostFinite host)
    (hp : HostExportParam host) {h : H} {s : Store H} {vs : List Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result}
    (hs : ∀ fi ∈ s.funcs, Q (moduleInstToValue CT fi.module)) (ho : host h s vs o) :
    AllIn Q (outcomeV hn o) := by
  cases o with
  | diverged => simp [outcomeV, AllIns]
  | returned s' r =>
    have hsub := host_mods_sub hf hp ho
    have hs' : ∀ fi ∈ s'.funcs, Q (moduleInstToValue CT fi.module) := by
      intro fi hfi
      obtain ⟨fi₁, hfi₁, he⟩ := List.mem_map.1 (hsub fi hfi)
      rw [← he]
      exact hs fi₁ hfi₁
    simp only [outcomeV, AllIn_case, AllIn_tuple, AllIns_cons, AllIns_nil, and_true]
    exact ⟨allIn_storeV hn hs', allIn_of_nxB Q _ (nxB_resultV r)⟩

end Outcomes

/-! ## `$hostcall` up to the order of its answer -/

theorem eraseV_outcomeV (hn : H → String)
    (o : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result) :
    eraseV (outcomeV hn o) = outcomeV hn (stripOutcome o) := by
  cases o with
  | diverged => rfl
  | returned s r =>
    simp only [outcomeV, stripOutcome, eraseV_case, eraseV_tuple', List.map_cons, List.map_nil,
      eraseV_storeV, eraseV_of_nxB _ (nxB_resultV r)]
    rfl

/-- `eraseV` on an argument: values are erased, the rest is kept. -/
def eraseA : ArgV → ArgV
  | .val v => .val (eraseV v)
  | a => a

theorem eraseA_hostArgs (hn : H → String) (h : H) (s : Store H) (vs : List Val) :
    (Prims.hostArgs hn h s vs).map eraseA = Prims.hostArgs hn h (stripStore s) vs := by
  have hv : eraseV (.list (vs.map valV)) = .list (vs.map valV) :=
    eraseV_of_nxB _ (by simp [nxB_valV])
  simp only [Prims.hostArgs, List.map_cons, List.map_nil, eraseA, eraseV_case, eraseV_text,
    eraseV_storeV, hv]
  rfl

/-- A host call is determined by its arguments, when its store has a unique preimage. -/
theorem hostArgs_unique (hn : H → String) (hinj : Function.Injective hn) {h : H} {s : Store H}
    {vs : List Val} (hu : ∀ s', storeV hn s' = storeV hn s → s' = s) :
    ∀ p : H × Store H × List Val,
      Prims.hostArgs hn h s vs = Prims.hostArgs hn p.1 p.2.1 p.2.2 → p = (h, s, vs) := by
  rintro ⟨h', s', vs'⟩ hp
  have he : hn h = hn h' ∧ storeV hn s = storeV hn s' ∧ vs.map valV = vs'.map valV := by
    simpa only [Prims.hostArgs, List.cons.injEq, ArgV.val.injEq, Value.case.injEq,
      Value.text.injEq, Value.list.injEq, true_and, and_true] using hp
  have h₁ : h' = h := hinj he.1.symm
  have h₂ : s' = s := hu s' he.2.1.symm
  have h₃ : vs' = vs := (List.map_injective_iff.2 Typing.valV_injective) he.2.2.symm
  rw [h₁, h₂, h₃]

/-- The answer of round 4's `$hostcall` at the arguments of a call with a unique preimage, and a
finite host: the images of the call's outcomes, in some order. -/
theorem hostcallCall_at (hn : H → String) (hinj : Function.Injective hn) {host : HostSemantics H}
    (hf : HostFinite host) {h : H} {s : Store H} {vs : List Val}
    (hu : ∀ s', storeV hn s' = storeV hn s → s' = s) :
    ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
      (∀ o, host h s vs o ↔ o ∈ os) ∧
      Prims.hostcallCall hn host (Prims.hostArgs hn h s vs) = some (.list (os.map (outcomeV hn))) := by
  unfold Prims.hostcallCall
  have hex : ∃ p : H × Store H × List Val,
      Prims.hostArgs hn h s vs = Prims.hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os :=
    ⟨(h, s, vs), rfl, hf h s vs⟩
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hpe : hex.choose = (h, s, vs) := hostArgs_unique hn hinj hu _ hex.choose_spec.1
  have hspec := hex.choose_spec.2.choose_spec
  revert hspec
  generalize hex.choose_spec.2.choose = os
  intro hspec
  rw [hpe] at hspec
  exact ⟨os, hspec, rfl⟩

/-- **`$hostcall` commutes with `eraseV` up to the order of its answer.** At a host call whose
store and stripped store have unique preimages under `storeV hn`, for a finite, export-blind,
export-parametric host: the primitive answers `xs` at the call and `ys` at the erased call, every
member of `xs` is `AllIn Q` when the calling store's module records satisfy `Q`, and the members
of `ys` are exactly the erasures of the members of `xs`. -/
theorem hostcallCall_erase (hn : H → String) (hinj : Function.Injective hn)
    {host : HostSemantics H} (hf : HostFinite host) (hp : HostExportParam host)
    (hb : HostExportBlind host) {Q : Value → Prop} {h : H} {s : Store H} {vs : List Val}
    (hu : ∀ s', storeV hn s' = storeV hn s → s' = s)
    (hu' : ∀ s', storeV hn s' = storeV hn (stripStore s) → s' = stripStore s)
    (hs : ∀ fi ∈ s.funcs, Q (moduleInstToValue CT fi.module)) :
    ∃ xs ys : List Value,
      Prims.hostcallCall hn host (Prims.hostArgs hn h s vs) = some (.list xs) ∧
      Prims.hostcallCall hn host ((Prims.hostArgs hn h s vs).map eraseA) = some (.list ys) ∧
      (∀ a ∈ xs, AllIn Q a) ∧ (∀ b, b ∈ ys ↔ ∃ a ∈ xs, eraseV a = b) := by
  obtain ⟨os, hos, hcall⟩ := hostcallCall_at hn hinj hf (h := h) (vs := vs) hu
  obtain ⟨os', hos', hcall'⟩ := hostcallCall_at hn hinj hf (h := h) (vs := vs) hu'
  refine ⟨os.map (outcomeV hn), os'.map (outcomeV hn), hcall, ?_, ?_, ?_⟩
  · rw [eraseA_hostArgs]
    exact hcall'
  · intro a ha
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
    exact allIn_outcomeV_of_host hn hf hp hs ((hos o).2 ho)
  · intro b
    constructor
    · intro hbm
      obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hbm
      obtain ⟨o, ho, rfl⟩ := hb.2 h s vs o' ((hos' o').2 ho')
      exact ⟨outcomeV hn o, List.mem_map_of_mem ((hos o).1 ho), eraseV_outcomeV hn o⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
      rw [eraseV_outcomeV]
      exact List.mem_map_of_mem ((hos' _).1 (hb.1 h s vs o ((hos o).2 ho)))

/-- `hostcallCall_erase` with the uniqueness hypotheses discharged by typing: the calling store and
its stripped form have images typed `store` in some `simEnv B`
(`Round5.FwdRef2.storeV_inj_typed`). -/
theorem hostcallCall_erase_typed (hn : H → String) (hinj : Function.Injective hn)
    {host : HostSemantics H} (hf : HostFinite host) (hp : HostExportParam host)
    (hb : HostExportBlind host) {B : Builtins} {Q : Value → Prop} {h : H} {s : Store H}
    {vs : List Val} (ht : TypedV (simEnv B) storeT (storeV hn s))
    (ht' : TypedV (simEnv B) storeT (storeV hn (stripStore s)))
    (hs : ∀ fi ∈ s.funcs, Q (moduleInstToValue CT fi.module)) :
    ∃ xs ys : List Value,
      Prims.hostcallCall hn host (Prims.hostArgs hn h s vs) = some (.list xs) ∧
      Prims.hostcallCall hn host ((Prims.hostArgs hn h s vs).map eraseA) = some (.list ys) ∧
      (∀ a ∈ xs, AllIn Q a) ∧ (∀ b, b ∈ ys ↔ ∃ a ∈ xs, eraseV a = b) :=
  hostcallCall_erase hn hinj hf hp hb
    (fun _ he => (Round5.FwdRef2.storeV_inj_typed hinj ht he.symm).symm)
    (fun _ he => (Round5.FwdRef2.storeV_inj_typed hinj ht' he.symm).symm) hs

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
