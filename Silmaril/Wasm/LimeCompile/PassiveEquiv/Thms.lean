module

public import Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.Lift
public import Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.MemInit
public import Silmaril.Wasm.LimeCompile.SimLift.Thms

/-!
# The passive-data container at module level: what is proved

An earlier step of the container track (docs/projects/wasm-wasi.md, "3.0 to Lime compiler"). An earlier step froze
module-level correctness of the passive-data container as `PassiveData.Task.exportEquiv`. This
file defines the store relation the lift needs (`Defs`) and splits the open statement into three
smaller open statements about it.

Proved:

* **`exportEquiv_of_tasks`**: `PassiveData.Task.exportEquiv` follows from `Task.inst`,
  `Task.runFwd` and `Task.runBack`. The proof goes through the generic lift of
  `Silmaril.Wasm.LimeCompile.SimLift`, with the session relation `SRelI K`. Its export and
  invocation parts are proved here: the target instance exports the same addresses
  (`exportFunc?_mi'`), and related stores accept the same invocations of exported functions
  (`srel_invokeOk_iff`, because exported functions take numeric parameters).
* **`memoryInit_rel`**: the local step of the simulation on related stores. A source frame of
  the source module runs `memory.init 0 y`; the related target frame runs a call of helper `y`.
  In bounds both return, and the final stores are `SRel`-related again. Out of bounds both trap
  on unchanged stores. This discharges the premises of `memoryInit_emulation` from `SRel` and
  `Ctx.Ok`: the target holds helper `y` at address `N + y`, the memories are equal, and
  `memoryInitLoop` changes only the memories. Its `MemOk` premise follows from the session
  invariants (`memOk_of_sinv`).

Open (frozen, results that use them are conditional):

* `Task.runFwd`, `Task.runBack`: a finished or diverging invocation of an exported function from
  `SRelI`-related stores is matched on the other side, finished runs with `SRelI`-related final
  stores. This is the closure of the simulation: the lock-step part for every rule of `Step`
  (frames of the source instance against frames of the target instance, function lists of
  different lengths, data instances that differ), the `memory.init` step above, and the
  invariants of `SInv`. For the converse direction, the target's steps inside a helper frame must
  be matched by source stuttering, which needs inversion of those steps.
* `Task.inst`: every instantiation of the source is matched by one of the target, and conversely,
  with a valid context and instantiation runs that transport both ways. The target's
  instantiation code runs `memory.init`/`data.drop` with an empty segment for every passive
  segment, and allocates the helper type and the helpers.

New statements over the proofs in `Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.PassiveEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (exportFunc? ExportEquiv)
open Silmaril.Wasm.LimeCompile.SimLift Silmaril.Wasm.LimeCompile.PassiveData
open Silmaril.Proofs.Wasm.LimeCompile.PassiveData (MemOk)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Exports and invocations -/

/-- The target instance exports the same function addresses. -/
theorem exportFunc?_mi' (K : Ctx) (x : String) : exportFunc? K.mi' x = exportFunc? K.mi x :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.exportFunc?_mi' K x

/-- Related stores accept the same invocations of exported functions. -/
theorem srel_invokeOk_iff {K : Ctx} {s t : Store H} (h : SRel K s t) {x : String} {a : Nat}
    (hx : exportFunc? K.mi x = some a) (vs : List Val) : InvokeOk s a vs ↔ InvokeOk t a vs :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.SRel.invokeOk_iff h hx vs

/-! ## The local step -/

/-- **`memory.init 0 y` against a call of helper `y`, on related stores.** -/
theorem memoryInit_rel {K : Ctx} (hK : K.Ok) {s t : Store H} (hS : SRel K s t) {f g : Frame}
    (hf : f.module = K.mi) (hg : g.module = K.mi') {y : DataIdx} {d : Data}
    (hd : K.m.data[y.toNat]? = some d) {ma : Nat} {mi : MemInst}
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hmi : MemOk mi) {i j n : BitVec 32} :
    ∃ di : DataInst, di.bytes.data.toList = effBytes d ∧
    (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size →
      ∃ s' t', Steps P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s', f, []⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n,
          .plain (.call (idx (helperBase K.m + y.toNat)))]⟩ ⟨t', g, []⟩ ∧ SRel K s' t') ∧
    (¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size) →
      Step P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s, f, [.trap]⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n,
          .plain (.call (idx (helperBase K.m + y.toNat)))]⟩ ⟨t, g, [.trap]⟩) :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.memoryInit_rel hK hS hf hg hd hm hmi

/-- The `MemOk` premise of `memoryInit_rel` holds in a store with the session invariants. -/
theorem memOk_of_sinv {K : Ctx} {s : Store H} (h : SInv K s) {f : Frame} (hf : f.module = K.mi)
    {ma : Nat} {mi : MemInst} (hm : s.mem? f (idx 0) = some (ma, mi)) : MemOk mi :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.memOk_of_sinv h hf hm

/-! ## The open statements -/

/-- The closed host: no host call returns or diverges. -/
abbrev closed (H : Type) : HostSemantics H := fun _ _ _ _ => False

/-- **Open (frozen):** forward transport of invocations from `SRelI`-related stores. -/
def Task.runFwd : Prop :=
  ∀ (H : Type) (P : Profile) (K : Ctx), K.Ok → ∀ (s t : Store H) (x : String) (a : Nat)
    (vs : List Val), SRelI K s t → exportFunc? K.mi x = some a → InvokeOk s a vs →
    RunTransport P (closed H) (SRelI K) (invoke s a vs) (invoke t a vs) ∧
      (Diverges P (closed H) (invoke s a vs) → Diverges P (closed H) (invoke t a vs))

/-- **Open (frozen):** backward transport of invocations from `SRelI`-related stores. -/
def Task.runBack : Prop :=
  ∀ (H : Type) (P : Profile) (K : Ctx), K.Ok → ∀ (s t : Store H) (x : String) (a : Nat)
    (vs : List Val), SRelI K s t → exportFunc? K.mi x = some a → InvokeOk t a vs →
    RunTransport P (closed H) (fun t s => SRelI K s t) (invoke t a vs) (invoke s a vs) ∧
      (Diverges P (closed H) (invoke t a vs) → Diverges P (closed H) (invoke s a vs))

/-- **Open (frozen):** instantiations of a valid source and of its valid output correspond,
with related instantiation configurations. -/
def Task.inst : Prop :=
  ∀ (H : Type) (P : Profile) (m : Module) (L : Lime1.Module),
    (∃ mt, ModuleOk m mt) → (∃ mt, ModuleOk L.toCore mt) → compile m = some L →
    ∀ (s : Store H) (xas : List ExternAddr), StoreOk s →
      (∀ c, Instantiate P (closed H) s m xas c → ∃ (d : Config H) (K : Ctx),
        Instantiate P (closed H) s (emuModule m) xas d ∧ InstRel P (closed H) K c d) ∧
      (∀ d, Instantiate P (closed H) s (emuModule m) xas d → ∃ (c : Config H) (K : Ctx),
        Instantiate P (closed H) s m xas c ∧ InstRel P (closed H) K c d)

/-- **`PassiveData.Task.exportEquiv` from the three open statements.** -/
theorem exportEquiv_of_tasks (hI : Task.inst) (hF : Task.runFwd) (hB : Task.runBack) :
    PassiveData.Task.exportEquiv := by
  intro H P m L hm hL hc
  have hcore : (Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod L = emuModule m := compile_toCore hc
  rw [hcore]
  refine exportEquiv_of_instTransport ⟨fun s xas c hs hI' => ?_, fun s xas d hs hI' => ?_⟩
    ⟨fun s xas d hs hI' => ?_, fun s xas c hs hI' => ?_⟩
  · obtain ⟨d, -, hd, -⟩ := (hI H P m L hm hL hc s xas hs).1 c hI'
    exact ⟨d, hd⟩
  · obtain ⟨c, K, hc', hK, hfc, hfd, -, -, hrun, hdiv⟩ := (hI H P m L hm hL hc s xas hs).2 d hI'
    refine ⟨c, fun t s => SRelI K s t, hc', hrun, hdiv, ?_⟩
    rw [hfc, hfd]
    exact Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.sessTransport_back
      (fun h hx hok => (hB H P K hK _ _ _ _ _ h hx hok).1)
      (fun h hx hok => (hB H P K hK _ _ _ _ _ h hx hok).2)
  · obtain ⟨c, -, hc', -⟩ := (hI H P m L hm hL hc s xas hs).2 d hI'
    exact ⟨c, hc'⟩
  · obtain ⟨d, K, hd, hK, hfc, hfd, hrun, hdiv, -⟩ := (hI H P m L hm hL hc s xas hs).1 c hI'
    refine ⟨d, SRelI K, hd, hrun, hdiv, ?_⟩
    rw [hfc, hfd]
    exact Silmaril.Proofs.Wasm.LimeCompile.PassiveEquiv.sessTransport_fwd
      (fun h hx hok => (hF H P K hK _ _ _ _ _ h hx hok).1)
      (fun h hx hok => (hF H P K hK _ _ _ _ _ h hx hok).2)

/-! ## Axiom audit -/

/-- info: 'Silmaril.Wasm.LimeCompile.PassiveEquiv.memoryInit_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memoryInit_rel

/-- info: 'Silmaril.Wasm.LimeCompile.PassiveEquiv.exportEquiv_of_tasks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exportEquiv_of_tasks

end Silmaril.Wasm.LimeCompile.PassiveEquiv
