module

public import Silmaril.Proofs.Wasm.Game.ULink.Backward
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux

/-!
# Worked example: a provider exporting a memory and a function

`exProv` exports its memory and `set` (stores `i32 42` at address `0`); `exCons` imports both
and exports `run` (calls `set`, then loads address `0` of the imported memory). Both are
validated and allocated by the spec's `prepare?` into **one** store (kernel evaluation),
the consumer against the provider's memory and function addresses.

* `shape`: the two functions of the linked store;
* `exS_layout`: the store has the link's layout;
* `run_linked`: for every profile, `$invoke(run)` runs to `i32 42` in the store `exS'` where
  `set` wrote: the consumer reads, through its imported memory, what the provider wrote.

New proofs, following `Silmaril.Proofs.Wasm.Game.UntypedExample`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.ULinkExample

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril.Wasm.Game.ULinkExample
  Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.ULink Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### Kernel-checked facts -/

theorem exProv_valid : (validate? exProv).isSome = true := by decide +kernel
theorem exCons_valid : (validate? exCons).isSome = true := by decide +kernel
theorem provPrep_some : (prepare? evalConst? ({} : Store Nat) exProv []).isSome = true := by
  decide +kernel
theorem consPrep_some :
    (prepare? evalConst? provPrep.1.store exCons [.mem 0, .func 0]).isSome = true := by
  decide +kernel
theorem t_len : exS.funcs.length = 2 := by decide +kernel
theorem t_mems : exS.mems.map (fun mi => mi.bytes.size) = [65536] := by decide +kernel
theorem t_addrs : exportFuncAddrs consPrep.1.frame.module = [1] := by decide +kernel
theorem t_mod : exS.funcs.map (fun fi => (fi.module.funcs, fi.module.mems)) =
    [([0], [0]), ([0, 1], [0])] := by decide +kernel
theorem t_expand : exS.funcs.map (fun fi => fi.type.expand?) =
    [some (.func (Ty.ofList []) (Ty.ofList [])),
      some (.func (Ty.ofList []) (Ty.ofList [.num (.int .i32)]))] := by decide +kernel

/-- The provider's `set`. -/
def isSetBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 a, .intConst .i32 b, .intStore .i32 none x arg]⟩ =>
    a == 0 && b == 42 && x.toNat == 0 && arg == memarg0
  | _ => false

/-- The consumer's `run`. -/
def isRunBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.call x, .intConst .i32 a, .intLoad .i32 none y arg]⟩ =>
    x.toNat == 0 && a == 0 && y.toNat == 0 && arg == memarg0
  | _ => false

/-- No host function. -/
def isWasm (fi : FuncInst Nat) : Bool := match fi.code with | .wasm _ => true | _ => false

theorem t_set : exS.funcs.map isSetBody = [true, false] := by decide +kernel
theorem t_run : exS.funcs.map isRunBody = [false, true] := by decide +kernel
theorem t_wasm : exS.funcs.map isWasm = [true, true] := by decide +kernel

/-! ### The shape of the linked store -/

theorem isSetBody_code {fi : FuncInst Nat} (h : isSetBody fi = true) :
    ∃ (t : TypeIdx) (y : MemIdx), fi.code = .wasm ⟨t, [], [.intConst .i32 0, .intConst .i32 42,
      .intStore .i32 none y memarg0]⟩ ∧ y.toNat = 0 := by
  unfold isSetBody at h
  split at h
  · rename_i t a b x arg hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hx⟩, rfl⟩ := h
    exact ⟨t, x, hc, hx⟩
  · cases h

theorem isRunBody_code {fi : FuncInst Nat} (h : isRunBody fi = true) :
    ∃ (t : TypeIdx) (x : FuncIdx) (y : MemIdx), fi.code = .wasm ⟨t, [], [.call x,
      .intConst .i32 0, .intLoad .i32 none y memarg0]⟩ ∧ x.toNat = 0 ∧ y.toNat = 0 := by
  unfold isRunBody at h
  split at h
  · rename_i t x a y arg hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hx, rfl⟩, hy⟩, rfl⟩ := h
    exact ⟨t, x, y, hc, hx, hy⟩
  · cases h

/-- The shape of the linked store. -/
structure Shape (fi₀ fi₁ : FuncInst Nat) (t₀ t₁ : TypeIdx) (x : FuncIdx) (y y' : MemIdx)
    (mi : MemInst) : Prop where
  funcs : exS.funcs = [fi₀, fi₁]
  code₀ : fi₀.code = .wasm ⟨t₀, [], [.intConst .i32 0, .intConst .i32 42,
    .intStore .i32 none y memarg0]⟩
  code₁ : fi₁.code = .wasm ⟨t₁, [], [.call x, .intConst .i32 0, .intLoad .i32 none y' memarg0]⟩
  ty₀ : Expand fi₀.type (.func (Ty.ofList []) (Ty.ofList []))
  ty₁ : Expand fi₁.type (.func (Ty.ofList []) (Ty.ofList [.num (.int .i32)]))
  hx : x.toNat = 0
  hy : y.toNat = 0
  hy' : y'.toNat = 0
  mod₀ : fi₀.module.mems = [0]
  mod₁ : fi₁.module.mems = [0] ∧ fi₁.module.funcs = [0, 1]
  mem : exS.mems = [mi]
  size : mi.bytes.size = 65536

theorem shape : ∃ fi₀ fi₁ t₀ t₁ x y y' mi, Shape fi₀ fi₁ t₀ t₁ x y y' mi := by
  obtain ⟨fi₀, fi₁, hf⟩ := List.length_eq_two.mp t_len
  have hset : [fi₀, fi₁].map isSetBody = [true, false] := hf ▸ t_set
  have hrun : [fi₀, fi₁].map isRunBody = [false, true] := hf ▸ t_run
  have hexp : [fi₀, fi₁].map (fun fi => fi.type.expand?) = _ := hf ▸ t_expand
  have hmod : [fi₀, fi₁].map (fun fi => (fi.module.funcs, fi.module.mems)) = _ := hf ▸ t_mod
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq] at hset hrun hexp hmod
  obtain ⟨t₀, y, hc₀, hy⟩ := isSetBody_code hset.1
  obtain ⟨t₁, x, y', hc₁, hx, hy'⟩ := isRunBody_code hrun.2.1
  obtain ⟨mi, hmi, hsz⟩ := List.map_eq_singleton_iff.mp t_mems
  exact ⟨fi₀, fi₁, t₀, t₁, x, y, y', mi, hf, hc₀, hc₁, Expand.iff.mpr hexp.1,
    Expand.iff.mpr hexp.2.1, hx, hy, hy', hmod.1.2, ⟨hmod.2.1.2, hmod.2.1.1⟩, hmi, hsz⟩

/-! ### Layout -/

theorem provCode_eq {fi₀ fi₁ : FuncInst Nat} {t₀ t₁ : TypeIdx} {x : FuncIdx} {y y' : MemIdx}
    {mi : MemInst} (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) : fi₀.code = .wasm provCode := by
  have hf : exS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  unfold provCode
  rw [hf, Option.map_some, h.code₀]

/-- **The linked store has the link's layout.** -/
theorem exS_layout : exLink.Layout exS := by
  obtain ⟨fi₀, fi₁, t₀, t₁, x, y, y', mi, h⟩ := shape
  have hw : [fi₀, fi₁].map isWasm = [true, true] := h.funcs ▸ t_wasm
  refine ⟨fun a fi k c ha hs => ?_, fun a fi k ha hc => ?_⟩
  · have ha0 : a = 0 := by
      by_contra hne
      simp [exLink, hne] at hs
    subst ha0
    have hs' : (0, provCode) = (k, c) := by simpa [exLink] using hs
    have hfi : fi = fi₀ := by rw [h.funcs] at ha; exact (Option.some.inj ha).symm
    rw [hfi, provCode_eq h, (Prod.mk.inj hs').2]
  · exfalso
    rw [h.funcs] at ha
    have hmem : fi ∈ [fi₀, fi₁] := List.mem_of_getElem? ha
    have hwf : isWasm fi = true := by
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hw
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact hw.1
      · rw [List.mem_singleton.mp hm]; exact hw.2.1
    simp [isWasm, hc] at hwf

/-! ### The linked run -/

section Run

variable {P : Silmaril.Wasm.Numerics.Profile} {fi₀ fi₁ : FuncInst Nat} {t₀ t₁ : TypeIdx}
  {x : FuncIdx} {y y' : MemIdx} {mi : MemInst}

local notation "noH" => (fun _ _ _ _ => False : HostSemantics Nat)

/-- The value `i32 42`. -/
abbrev v42 : Val := .num ⟨.int .i32, 42⟩

/-- A step of a head of the code, in front of a non-empty rest. -/
theorem step_head {host : HostSemantics Nat} {s s' : Store Nat} {f f' : Frame}
    {is is' rest : List Admin} (h : Execution.Core.Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hr : rest ≠ []) : Execution.Core.Step P host ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Step.ctxtInstrs (vs := []) (rest := rest) h (.inr hr)

/-- The frame of `run`. -/
abbrev F₁ (fi₁ : FuncInst Nat) : Frame := Frame.forCall fi₁.module [] []

/-- The frame of `set`. -/
abbrev F₀ (fi₀ : FuncInst Nat) : Frame := Frame.forCall fi₀.module [] []

/-- The rest of `run` after the call. -/
abbrev runRest (y' : MemIdx) : List Admin :=
  [.plain (.intConst .i32 0), .plain (.intLoad .i32 none y' memarg0)]

/-- The code of `set`. -/
abbrev setCode (y : MemIdx) : List Admin :=
  [.plain (.intConst .i32 0), .plain (.intConst .i32 42), .plain (.intStore .i32 none y memarg0)]

theorem run_enter (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Execution.Core.Step P noH (invoke exS 1 [])
      ⟨exS, {}, [.frame 1 (F₁ fi₁) [.label 1 [] (.plain (.call x) :: runRest y')]]⟩ := by
  have hf : exS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  exact Step.callRefFunc (P := P) (host := noH) (s := exS) (f := {})
    (c := .callRefType ((exS.funcs[1]?.map FuncInst.type).getD default)) (vs := [])
    trivial hf h.ty₁ rfl h.code₁

theorem run_call (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Execution.Core.Step P noH ⟨exS, F₁ fi₁, .plain (.call x) :: runRest y'⟩
      ⟨exS, F₁ fi₁, [.ref (.func 0), .callRefType fi₀.type] ++ runRest y'⟩ := by
  have hf0 : exS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hx : (F₁ fi₁).module.funcs[x.toNat]? = some 0 := by simp [Frame.forCall, h.mod₁.2, h.hx]
  exact step_head (is := [.plain (.call x)]) (Step.call hx hf0) (by simp)

theorem run_enter_set (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Execution.Core.Step P noH ⟨exS, F₁ fi₁, [.ref (.func 0), .callRefType fi₀.type] ++ runRest y'⟩
      ⟨exS, F₁ fi₁, [.frame 0 (F₀ fi₀) [.label 0 [] (setCode y)]] ++ runRest y'⟩ := by
  have hf0 : exS.funcs[0]? = some fi₀ := by rw [h.funcs]; rfl
  have hs := Step.callRefFunc (P := P) (host := noH) (s := exS) (f := F₁ fi₁)
    (c := .callRefType fi₀.type) (vs := []) trivial hf0 h.ty₀ rfl h.code₀
  exact step_head hs (by simp)

/-- The stored bytes. -/
theorem store_ok (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    ∃ b, Silmaril.Wasm.Execution.Memory.store mi.bytes (effAddr (0 : BitVec 32).toNat memarg0)
      (count := IntType.i32.width / 8) ((42 : BitVec IntType.i32.width).setWidth _) = some b :=
  Memory.store_of_le _ (by rw [h.size]; decide)

theorem exS'_eq (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) : exS' = exS.setMem 0 (store42 mi) := by
  unfold exS'
  rw [h.mem]
  rfl

/-- **`set` writes the shared memory.** -/
theorem run_store (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Execution.Core.Step P noH ⟨exS, F₀ fi₀, setCode y⟩ ⟨exS', F₀ fi₀, []⟩ := by
  obtain ⟨b, hb⟩ := store_ok h
  have hm : exS.mem? (F₀ fi₀) y = some (0, mi) := by
    simp [Store.mem?, Frame.forCall, h.mod₀, h.hy, h.mem]
  have hst : exS' = exS.setMem 0 { mi with bytes := b } := by
    rw [exS'_eq h]
    unfold store42
    rw [hb]
  rw [hst]
  exact Step.memory (MemoryStep.storeIntVal (a := .i32) (i := 0) (c := 42) hm hb)

/-- **`run` reads, through its imported memory, what `set` wrote.** -/
theorem run_load (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Execution.Core.Step P noH ⟨exS', F₁ fi₁, runRest y'⟩ ⟨exS', F₁ fi₁, vals [v42]⟩ := by
  obtain ⟨b, hb⟩ := store_ok h
  have hmi : store42 mi = { mi with bytes := b } := by unfold store42; rw [hb]
  have hm : exS'.mem? (F₁ fi₁) y' = some (0, { mi with bytes := b }) := by
    rw [exS'_eq h, hmi]
    simp [Store.mem?, Store.setMem, Frame.forCall, h.mod₁.1, h.hy', h.mem]
  have hl := Silmaril.Wasm.Execution.Memory.load_store _ _ _ _ _ hb
  exact Step.memory (MemoryStep.loadIntVal (a := .i32) (i := 0) hm hl)

/-- The inner steps of `run`, under its frame and label. -/
theorem run_inner (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Steps P noH ⟨exS, F₁ fi₁, .plain (.call x) :: runRest y'⟩ ⟨exS', F₁ fi₁, vals [v42]⟩ := by
  have h₂ := run_call (P := P) h
  have h₃ := run_enter_set (P := P) h
  have h₄ : Execution.Core.Step P noH
      ⟨exS, F₁ fi₁, [.frame 0 (F₀ fi₀) [.label 0 [] (setCode y)]] ++ runRest y'⟩
      ⟨exS', F₁ fi₁, [.frame 0 (F₀ fi₀) [.label 0 [] []]] ++ runRest y'⟩ :=
    step_head (Step.ctxtFrame (Step.ctxtLabel (run_store h))) (by simp)
  have h₅ : Execution.Core.Step P noH
      ⟨exS', F₁ fi₁, [.frame 0 (F₀ fi₀) [.label 0 [] (vals [])]] ++ runRest y'⟩
      ⟨exS', F₁ fi₁, [.frame 0 (F₀ fi₀) (vals [])] ++ runRest y'⟩ :=
    step_head (Step.ctxtFrame Step.labelVals) (by simp)
  have h₆ : Execution.Core.Step P noH ⟨exS', F₁ fi₁, [.frame 0 (F₀ fi₀) (vals [])] ++ runRest y'⟩
      ⟨exS', F₁ fi₁, vals [] ++ runRest y'⟩ := step_head (Step.frameVals rfl) (by simp)
  have h₇ := run_load (P := P) h
  exact h₂.steps.trans (h₃.steps.trans (h₄.steps.trans (h₅.steps.trans (h₆.steps.trans h₇.steps))))

/-- **The run of `run` in the linked module**, every profile: `i32 42` in the written store. -/
theorem run_linked (h : Shape fi₀ fi₁ t₀ t₁ x y y' mi) :
    Steps P noH ⟨exS, {}, [.frame 1 (F₁ fi₁) [.label 1 [] (.plain (.call x) :: runRest y')]]⟩
      ⟨exS', {}, vals [v42]⟩ := by
  have hin : Steps P noH
      ⟨exS, {}, [.frame 1 (F₁ fi₁) [.label 1 [] (.plain (.call x) :: runRest y')]]⟩
      ⟨exS', {}, [.frame 1 (F₁ fi₁) [.label 1 [] (vals [v42])]]⟩ :=
    Relation.ReflTransGen.lift (fun c : Config Nat => (⟨c.store, {}, [.frame 1 c.frame [.label 1 [] c.code]]⟩ : Config Nat))
      (fun a b hab => Step.ctxtFrame (Step.ctxtLabel hab)) _ _ (run_inner h)
  have h₈ : Execution.Core.Step P noH ⟨exS', {}, [.frame 1 (F₁ fi₁) [.label 1 [] (vals [v42])]]⟩
      ⟨exS', {}, [.frame 1 (F₁ fi₁) (vals [v42])]⟩ := Step.ctxtFrame Step.labelVals
  have h₉ : Execution.Core.Step P noH ⟨exS', {}, [.frame 1 (F₁ fi₁) (vals [v42])]⟩
      ⟨exS', {}, vals [v42]⟩ := Step.frameVals rfl
  exact hin.trans (h₈.steps.trans h₉.steps)

end Run

/-! ### The games -/

section Games

variable {P : Silmaril.Wasm.Numerics.Profile}

/-- Host-free Core runs between active threads are silent runs of an untyped instance. -/
theorem run_of_steps {U : UInstance} {q : U.F.Op} {c c' : Config Nat}
    (h : Steps P (fun _ _ _ _ => False) c c') :
    (U.lts P).Run (.running q c.store (.active c.frame c.code)) []
      (.running q c'.store (.active c'.frame c'.code)) := by
  induction h with
  | refl => exact .nil _
  | tail _ hst ih => exact ih.append (.tau (UInstance.Trans.tau ⟨_, _, rfl, hst⟩) (.nil _))

/-- **The linked module answers `run` with `i32 42`**, every profile. -/
theorem linked_play :
    [.inr (.ask runQ), .inr (.ans runQ runA)] ∈ exLink.U.strategy P := by
  obtain ⟨fi₀, fi₁, t₀, t₁, x, y, y', mi, h⟩ := shape
  have h₁ : InternalP P (exS, .pending 1 [])
      (exS, .active {} [.frame 1 (F₁ fi₁) [.label 1 [] (.plain (.call x) :: runRest y')]]) :=
    ⟨_, _, rfl, run_enter h⟩
  have hrun := run_of_steps (U := exLink.U) (q := runQ) (run_linked (P := P) h)
  have hfinal : ResultAt exS' (.active {} (vals [v42])) (.values [v42]) := rfl
  exact Untyped.mem_strategy_iff.2 ⟨.idle, .vis (UInstance.Trans.call runQ)
    (.tau (UInstance.Trans.tau h₁) (hrun.append (.vis (UInstance.Trans.oret hfinal) (.nil _))))⟩

/-- The written store keeps the layout. -/
theorem exS'_layout : exLink.Layout exS' := by
  obtain ⟨fi₀, fi₁, t₀, t₁, x, y, y', mi, h⟩ := shape
  exact Layout.of_funcs exS_layout (by rw [exS'_eq h]; rfl)

/-- The play's stores have the layout. -/
theorem play_layout : exLink.LayoutPlay [.inr (.ask runQ), .inr (.ans runQ runA)] := by
  intro m hm
  rcases List.mem_pair.mp hm with rfl | rfl
  · exact exS_layout
  · exact ⟨exS_layout, exS'_layout⟩

/-- **The composite of the provider and the consumer answers `run` with `i32 42`**, every
profile, in the stubbed store: the provider's `set` runs as the consumer's environment and
writes the memory the consumer then reads. -/
theorem comp_play :
    [.inr (.ask runQ), .inr (.ans runQ runA)].map exLink.stubUp ∈ exLink.compStrategy P :=
  link_le_comp play_layout linked_play

/-- **Core behaviour**: under every host, `$invoke(run)` may return `i32 42`, every profile. -/
theorem run_behaviour (host : HostSemantics Nat) :
    (Result.values [v42]).toBehaviour ∈ behaviours P host exS 1 [] := by
  obtain ⟨fi₀, fi₁, t₀, t₁, x, y, y', mi, h⟩ := shape
  have hs : Steps P (fun _ _ _ _ => False) (invoke exS 1 []) ⟨exS', {}, vals [v42]⟩ :=
    (run_enter (P := P) h).steps.trans (run_linked h)
  have hs' : Steps P host (invoke exS 1 []) ⟨exS', {}, vals [v42]⟩ :=
    Relation.ReflTransGen.mono (fun _ _ hab => Step.of_noHost host hab) _ _ hs
  rw [behaviours_eq]
  exact .inl ⟨_, _, hs', rfl, rfl⟩

end Games

end Silmaril.Proofs.Wasm.Game.ULinkExample
