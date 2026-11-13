module

public import Silmaril.Machine.Abi.LinkTags.Defs
public import Silmaril.Machine.Abi.LinkSim.Thms
public import Silmaril.X86.Link.Abi.Thms
/-! # The linker's ABI check carries ABI-correctness meaning

PROVED (standard axioms):

* `accepts_edge`: under a sound policy, a binding that B's `Policy.accepts` admits has C
  verdict `direct`, or `thunk` with a declared thunk;
* `checkAbi_edges`: **B's `checkAbi` acceptance gives C verdicts**: every cross-object binding
  the static linker can make (as in B's `AbiSound`) is an `Edge`;
* `edge_transfers`, `checkAbi_link_sound`: with a simulating adapter for every declared thunk
  (`Bridges`), every such binding `Transfers` ABI correctness (track C's `link_sound`, in
  the simulating form `Link.link_sound_sim`);
* `linkAbi_link_sound`: the same from a successful `linkAbi` run;
* `convPolicy_sound`: B's default vocabulary `Conv` with `Policy.exact` and any declared
  thunks is sound under the obvious tag map `convEndpoint`;
* `callMsBridges`: gcc's `call_ms` adapter supplies the bridges of every declared
  `sysv64 → ms64` thunk on prototypes with at most four parameters;
* round 4 (F7): `edge_direct`, `edge_within`: under a policy without thunks every edge is
  `direct`, and it transfers room-relative ABI correctness (`within … room`), which is the
  form the open-machine bridge `OpenMachine.sat_of_strict` produces;
* `checks_thunk_link_sound`: B's closed example `cross_abi_with_thunk` (a `sysv64` caller
  of an `ms64` `f`, admitted by a declared thunk) carries ABI correctness under
  `Interp.multi`, with gcc's adapter as the thunk (`checks_binding`: the binding exists).
-/

@[expose] public section
namespace Silmaril.Machine.Abi.LinkTags

open Silmaril.Formats.ELF (NameBytes ObjectFile)
open Silmaril.Logic.Institution.Bridges
open Silmaril.X86.Link.Abi (Policy Interface Conv checkAbi AbiSound definedGlobals
  undefinedGlobals checkAbi_sound)
open Silmaril.Machine.Abi.Link (Endpoint Verdict check Compatible Interp SimBridge SimThunk AbiTag
  link_sound_sim)
open Silmaril.Machine.Abi.SystemV (Proto vocab CallSite sysv)
open Silmaril.Machine.SystemV.Abi (Ffi.State)

variable {T : Type} [DecidableEq T]

theorem accepts_edge {ep : NameBytes → T → Option Endpoint} {policy : Policy T}
    (sound : PolicySound ep policy) {name : NameBytes} {ti te : T}
    (h : policy.accepts name ti te = true) : Edge ep policy name ti te := by
  intro i e hi he
  simp only [Policy.accepts, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with hc | hm
  · exact .inl (sound.compatible name ti te i e hc hi he)
  · have ne := sound.thunks _ hm i e hi he
    generalize hv : check i e = v at ne
    cases v with
    | direct => exact .inl rfl
    | thunk => exact .inr ⟨rfl, hm⟩
    | reject => exact absurd rfl ne

/-- The bindings of a link, as in B's `AbiSound`, with a property `E` of each binding. -/
def Bindings (policy : Policy T) (objects : List ObjectFile) (ifaces : List (Interface T))
    (E : NameBytes → T → T → Prop) : Prop :=
  ∀ (i : Nat) (object : ObjectFile) (iface : Interface T), objects[i]? = some object →
    ifaces[i]? = some iface →
    ∀ name ∈ undefinedGlobals object, ∃ importTag, (name, importTag) ∈ iface.imports ∧
      (∀ (j : Nat) (object' : ObjectFile) (iface' : Interface T), objects[j]? = some object' →
        ifaces[j]? = some iface' → name ∈ definedGlobals object' →
          ∃ exportTag, (name, exportTag) ∈ iface'.exports ∧ E name importTag exportTag) ∧
      (∀ exportTag, (name, exportTag) ∈ policy.externals → E name importTag exportTag)

omit [DecidableEq T] in
theorem bindings_mono {policy : Policy T} {objects : List ObjectFile}
    {ifaces : List (Interface T)} {E F : NameBytes → T → T → Prop}
    (hEF : ∀ name ti te, E name ti te → F name ti te) (h : Bindings policy objects ifaces E) :
    Bindings policy objects ifaces F := by
  intro i object iface ho hi name hn
  obtain ⟨ti, hmem, hexp, hext⟩ := h i object iface ho hi name hn
  refine ⟨ti, hmem, fun j o' i' ho' hi' hd => ?_, fun te hte => hEF _ _ _ (hext te hte)⟩
  obtain ⟨te, hte, he⟩ := hexp j o' i' ho' hi' hd
  exact ⟨te, hte, hEF _ _ _ he⟩

/-- B's `AbiSound` is `Bindings` with `Policy.accepts`. -/
theorem bindings_of_abiSound {policy : Policy T} {objects : List ObjectFile}
    {ifaces : List (Interface T)} (h : AbiSound policy objects ifaces) :
    Bindings policy objects ifaces fun name ti te => policy.accepts name ti te = true :=
  h

/-- **B's `checkAbi` acceptance gives C verdicts.** -/
theorem checkAbi_edges {ep : NameBytes → T → Option Endpoint} {policy : Policy T}
    {objects : List ObjectFile} {ifaces : List (Interface T)}
    (h : checkAbi policy objects ifaces = true) (sound : PolicySound ep policy) :
    Bindings policy objects ifaces (Edge ep policy) :=
  bindings_mono (fun _ _ _ => accepts_edge sound) (bindings_of_abiSound (checkAbi_sound h))

omit [DecidableEq T] in
/-- An edge with its bridges transfers ABI correctness. -/
theorem edge_transfers {I : Interp} {ep : NameBytes → T → Option Endpoint} {policy : Policy T}
    (bridges : Bridges I ep policy) {name : NameBytes} {ti te : T}
    (edge : Edge ep policy name ti te) : Transfers I ep name ti te := by
  intro i e A B hi he hA hB
  rcases edge i e hi he with hd | ⟨ht, hm⟩
  · exact ⟨.direct, hd, PUnit.unit, fun _ _ strict callee g =>
      link_sound_sim I hA hB hd PUnit.unit strict callee g⟩
  · let bridge := bridges ⟨name, ti, te⟩ hm i e A B hi he hA hB ht
    exact ⟨.thunk, ht, bridge, fun _ _ strict callee g =>
      link_sound_sim I hA hB ht bridge strict callee g⟩

/-- **The linker's ABI check carries ABI-correctness meaning.** If `checkAbi` accepts, the
policy is sound for C's check and every declared thunk has a simulating adapter, then every
binding the static linker can make transfers the exporter's translated contracts to the
importer. -/
theorem checkAbi_link_sound {I : Interp} {ep : NameBytes → T → Option Endpoint}
    {policy : Policy T} {objects : List ObjectFile} {ifaces : List (Interface T)}
    (h : checkAbi policy objects ifaces = true) (sound : PolicySound ep policy)
    (bridges : Bridges I ep policy) : Bindings policy objects ifaces (Transfers I ep) :=
  bindings_mono (fun _ _ _ => edge_transfers bridges) (checkAbi_edges h sound)

/-- The same from a successful run of B's `linkAbi`. -/
theorem linkAbi_link_sound {I : Interp} {ep : NameBytes → T → Option Endpoint}
    {policy : Policy T} {objects : List ObjectFile} {ifaces : List (Interface T)}
    {accepts : Silmaril.Formats.ELF.Header → Bool} {relocate : Silmaril.Formats.ELF.Link.Relocator}
    {layout : Silmaril.Formats.ELF.Link.Layout} {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols}
    {out : List Silmaril.Formats.ELF.Link.LinkedSection}
    (h : Silmaril.X86.Link.Abi.linkAbi accepts relocate policy objects ifaces layout absolute =
      some out)
    (sound : PolicySound ep policy) (bridges : Bridges I ep policy) :
    Bindings policy objects ifaces (Transfers I ep) :=
  checkAbi_link_sound (Silmaril.X86.Link.Abi.linkAbi_some h).1 sound bridges

/-! ## Policies without thunks (round 4, F7) -/

omit [DecidableEq T] in
/-- Under a policy that declares no thunks, every edge has C verdict `direct`. -/
theorem edge_direct {ep : NameBytes → T → Option Endpoint} {policy : Policy T}
    (hno : policy.thunks = []) {name : NameBytes} {ti te : T}
    (edge : Edge ep policy name ti te) {i e : Endpoint} (hi : ep name ti = some i)
    (he : ep name te = some e) : Compatible i e := by
  rcases edge i e hi he with hd | ⟨_, hm⟩
  · exact hd
  · rw [hno] at hm; cases hm

omit [DecidableEq T] in
/-- **A direct edge transfers room-relative ABI correctness.** Under a policy without
thunks, an exporter's `Contracts.Sat model (within ((B).translate p c) room)` is the
importer's `Contracts.Sat model (within ((A).translate p c) room)`, for every call relation,
contract and room (`Transfers` states the room-free form). -/
theorem edge_within {I : Interp} {ep : NameBytes → T → Option Endpoint} {policy : Policy T}
    (hno : policy.thunks = []) {name : NameBytes} {ti te : T}
    (edge : Edge ep policy name ti te) {i e : Endpoint}
    {A B : Convention vocab Ffi.State CallSite}
    (hi : ep name ti = some i) (he : ep name te = some e) (hA : I.conv i.abi = some A)
    (hB : I.conv e.abi = some B) {model : Contracts.Model Ffi.State Ffi.State}
    {c : Contracts.Contract (vocab.Args i.proto) (Option (vocab.Ret i.proto))}
    {room : Ffi.State → Prop}
    (h : Contracts.Sat model (within (B.translate i.proto c) room)) :
    Contracts.Sat model (within (A.translate i.proto c) room) := by
  rw [Link.compatible_translate_eq I (edge_direct hno edge hi he) hA hB c]
  exact h

/-! ## B's default vocabulary -/

theorem compatible_self (i : Endpoint) : Compatible i i := by
  simp [Compatible, check, Link.checkTags]

theorem convEndpoint_proto {protoOf : NameBytes → Option Proto} {name : NameBytes} {t : Conv}
    {i : Endpoint} (h : convEndpoint protoOf name t = some i) :
    protoOf name = some i.proto := by
  unfold convEndpoint at h
  split at h
  · cases h; assumption
  · cases h

/-- `Policy.exact` on `Conv` with any declared thunks is sound for C's check. -/
theorem convPolicy_sound (protoOf : NameBytes → Option Proto) (thunks : List (DeclThunk Conv)) :
    PolicySound (convEndpoint protoOf) (convPolicy thunks) where
  compatible name ti te i e hc hi he := by
    simp only [convPolicy, Policy.exact, decide_eq_true_eq] at hc
    subst hc
    rw [hi] at he
    cases he
    exact compatible_self i
  thunks th _ i e hi he := by
    have hp : i.proto = e.proto :=
      Option.some.inj ((convEndpoint_proto hi).symm.trans (convEndpoint_proto he))
    rw [Ne, Link.check_reject_iff, Ne, not_not, hp]

theorem convEndpoint_abi {protoOf : NameBytes → Option Proto} {name : NameBytes} {t : Conv}
    {i : Endpoint} (h : convEndpoint protoOf name t = some i) : abiTagOf t = some i.abi := by
  unfold convEndpoint at h
  split at h
  · cases h; assumption
  · cases h

/-- **gcc's `call_ms` supplies the bridges** of every declared `sysv64 → ms64` thunk whose
prototype has at most four parameters (under `Interp.multi`). -/
def callMsBridges (protoOf : NameBytes → Option Proto) (thunks : List (DeclThunk Conv))
    (only : ∀ th ∈ thunks, th.importTag = .sysv64 ∧ th.exportTag = .ms64)
    (small : ∀ name p, protoOf name = some p → CrossAbi.Small p) (rel : BitVec 32) :
    Bridges Interp.multi (convEndpoint protoOf) (convPolicy thunks) := by
  intro th hm i e A B hi he hA hB _
  obtain ⟨hti, hte⟩ := only th hm
  rw [hti] at hi
  rw [hte] at he
  have hia : i.abi = .sysv64 {} := (Option.some.inj (convEndpoint_abi hi)).symm
  have hea : e.abi = .ms64 := (Option.some.inj (convEndpoint_abi he)).symm
  rw [hia, Link.Interp.multi.sysv {} rfl] at hA
  rw [hea, Link.Interp.multi_ms64] at hB
  cases hA
  cases hB
  exact Link.callMsThunk {} (small _ _ (convEndpoint_proto hi)) rel

/-! ## B's closed example -/

theorem thunkPolicy_eq :
    Silmaril.X86.Link.Abi.thunkPolicy =
      convPolicy [⟨Silmaril.X86.Link.Abi.nameF, .sysv64, .ms64⟩] := rfl

/-- **B's accepted cross-ABI link carries ABI correctness.** The link of
`Checks.caller` (a `sysv64` import of `f`) with `Checks.callee` (an `ms64` export of `f`)
that B's `thunkPolicy` admits (`cross_abi_with_thunk`): for any prototype of `f` with at most
four parameters, every binding transfers the exporter's Microsoft x64 contract to the
importer's System V contract through gcc's `call_ms` adapter. -/
theorem checks_thunk_link_sound (p : Proto) (small : CrossAbi.Small p) (rel : BitVec 32) :
    Bindings Silmaril.X86.Link.Abi.thunkPolicy
      [Silmaril.X86.Linking.Checks.caller, Silmaril.X86.Linking.Checks.callee]
      [Silmaril.X86.Link.Abi.callerIface .sysv64, Silmaril.X86.Link.Abi.calleeIface .ms64]
      (Transfers Interp.multi (convEndpoint fun _ => some p)) := by
  rw [thunkPolicy_eq]
  refine linkAbi_link_sound (thunkPolicy_eq ▸ Silmaril.X86.Link.Abi.cross_abi_with_thunk)
    (convPolicy_sound _ _) (callMsBridges _ _ ?_ ?_ rel)
  · intro th hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, rfl⟩
  · intro _ q hq
    cases hq
    exact small

/-- Non-vacuity of `checks_thunk_link_sound`: the caller really imports `f` and the callee
really defines it, so the statement covers one cross-ABI binding. -/
theorem checks_binding :
    Silmaril.X86.Link.Abi.nameF ∈ undefinedGlobals Silmaril.X86.Linking.Checks.caller ∧
      Silmaril.X86.Link.Abi.nameF ∈ definedGlobals Silmaril.X86.Linking.Checks.callee := by
  decide

end Silmaril.Machine.Abi.LinkTags
