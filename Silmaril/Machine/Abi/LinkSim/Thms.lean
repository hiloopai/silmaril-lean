module

public import Silmaril.Machine.Abi.LinkSim.Defs
public import Silmaril.Machine.Abi.CrossAbi.Gcc.Thms
/-! # Link soundness with simulating thunks

PROVED (standard axioms):

* `link_sound_sim`: **track C's `link_sound` restated for `SimBridge`.** Whatever the verdict
  of `check imp exp`, an exporter that satisfies its own convention's translation of a
  strict C contract and provides the edge's guarantee, called through the edge's bridge,
  satisfies the importer's translation of the same contract on states meeting the edge's
  room assumption. For `direct` the room and guarantee are trivial; for `thunk` they are the
  adapter's; `reject` has no bridge.
* `toSim_wrap`, `toSim_room`, `toSim_guar`: an old `Bridge` becomes a `SimBridge` with the same
  wrapped relation and trivial room and guarantee;
* `link_sound_of_toSim`: so for strict contracts `link_sound_sim` recovers `link_sound`;
* `callMsBridge`, `callMs_link_sound`: gcc's `call_ms` adapter (track C2, rung 11) is a
  `SimBridge` for the System V → `ms_abi` edge, which `check` sends to `thunk`
  (`check_sysv_ms64`), so the linker's cross-ABI edge is now covered by a *realistic* adapter.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Link

open Silmaril.Machine.Abi.SystemV (Proto vocab sysv CallSite)
open Silmaril.Machine.SystemV.Abi (Ffi.State)
open Silmaril.Machine.Abi.Convention (Strict Guarantees)
open Silmaril.Logic.Institution.Bridges

/-- **Link soundness with simulating thunks.** -/
theorem link_sound_sim (I : Interp) {imp exp : Endpoint}
    {A B : Convention vocab Ffi.State CallSite}
    (hA : I.conv imp.abi = some A) (hB : I.conv exp.abi = some B)
    {v : Verdict} (hv : check imp exp = v) (bridge : SimBridge A B imp.proto v)
    {model : Contracts.Model Ffi.State Ffi.State}
    {c : Contracts.Contract (vocab.Args imp.proto) (Option (vocab.Ret imp.proto))}
    (strict : Strict c)
    (callee : Contracts.Sat model (B.translate imp.proto c))
    (guaranteed : Guarantees B imp.proto c model (SimBridge.guar v bridge)) :
    Contracts.Sat (SimBridge.wrap v bridge model)
      (within (A.translate imp.proto c) (SimBridge.room v bridge)) := by
  cases v with
  | direct =>
    exact (Convention.within_true _ _).2
      (((check_direct_agree I hv hA hB).sat_iff model c).2 callee)
  | thunk => exact bridge.simulates.sound strict callee guaranteed
  | reject => exact bridge.elim

variable {A B : Convention vocab Ffi.State CallSite} {p : Proto}

theorem toSim_wrap (v : Verdict) (b : Bridge A B p v) (model : Contracts.Model Ffi.State Ffi.State) :
    SimBridge.wrap v (Bridge.toSim v b) model = Bridge.wrap v b model := by
  cases v
  · rfl
  · rfl
  · exact b.elim

theorem toSim_room (v : Verdict) (b : Bridge A B p v) (s : Ffi.State) :
    SimBridge.room v (Bridge.toSim v b) s := by
  cases v
  · trivial
  · trivial
  · exact b.elim

theorem toSim_guar (v : Verdict) (b : Bridge A B p v) (s s' : Ffi.State) :
    SimBridge.guar v (Bridge.toSim v b) s s' := by
  cases v
  · trivial
  · trivial
  · exact b.elim

/-- For strict contracts, `link_sound_sim` applied to an old bridge gives track C's
`link_sound` conclusion. -/
theorem link_sound_of_toSim (I : Interp) {imp exp : Endpoint}
    (hA : I.conv imp.abi = some A) (hB : I.conv exp.abi = some B)
    (bridge : Bridge A B imp.proto (check imp exp))
    {model : Contracts.Model Ffi.State Ffi.State}
    {c : Contracts.Contract (vocab.Args imp.proto) (Option (vocab.Ret imp.proto))}
    (strict : Strict c) (callee : Contracts.Sat model (B.translate imp.proto c)) :
    Contracts.Sat (Bridge.wrap _ bridge model) (A.translate imp.proto c) := by
  have h := link_sound_sim I hA hB rfl (Bridge.toSim _ bridge) strict callee
    (fun _ _ _ _ _ _ => toSim_guar _ bridge _ _)
  rw [toSim_wrap] at h
  intro s pre
  exact h s ⟨pre, toSim_room _ bridge s⟩

/-! ## gcc's `call_ms` as a link bridge -/

/-- gcc's System V → `ms_abi` transition code as a simulating thunk (prototypes with at most
four parameters). -/
def callMsThunk (o : SysvOptions) (small : CrossAbi.Small p) (rel : BitVec 32) :
    SimThunk (sysv o.options) Win64.win64 p where
  thunk := CrossAbi.Gcc.callMs (sysv o.options) Win64.win64 p rel
  room := CrossAbi.Gcc.CallMs.Room
  guar := CrossAbi.Gcc.CallMs.Guar
  simulates := CrossAbi.sysvToMs_simulates o.options small
    (CrossAbi.Gcc.callMs_implements o.options rel) (CrossAbi.Gcc.callMs_progress o.options rel)

/-- The bridge for a System V importer of an `ms_abi` exporter: the verdict is `thunk`
(`check_sysv_ms64`), and gcc's adapter supplies it. -/
def callMsBridge (o : SysvOptions) (small : CrossAbi.Small p) (rel : BitVec 32) :
    SimBridge (sysv o.options) Win64.win64 p .thunk :=
  callMsThunk o small rel

/-- **The linker's System V → `ms_abi` edge with gcc's adapter is sound** (multi-ABI
interpretation of tags). -/
theorem callMs_link_sound (o : SysvOptions) (hx : o.x32 = false) (small : CrossAbi.Small p)
    (rel : BitVec 32) {model : Contracts.Model Ffi.State Ffi.State}
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    (callee : Contracts.Sat model (Win64.win64.translate p c))
    (keeps : Guarantees Win64.win64 p c model CrossAbi.Gcc.CallMs.Guar) :
    Contracts.Sat ((CrossAbi.Gcc.callMs (sysv o.options) Win64.win64 p rel).wrap model)
      (within ((sysv o.options).translate p c) CrossAbi.Gcc.CallMs.Room) :=
  link_sound_sim (imp := ⟨p, .sysv64 o⟩) (exp := ⟨p, .ms64⟩) Interp.multi
    (Interp.multi.sysv o hx) Interp.multi_ms64 check_sysv_ms64 (callMsBridge o small rel)
    strict callee keeps

end Silmaril.Machine.Abi.Link
