module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegRun
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Closed
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Setup

/-!
# Spec instantiation with segments and global imports

For a module whose active-segment offsets are constant instructions (`OffsetsConst`), possibly
with global imports, instantiated by the specification into a host-free well-typed store:

* `spec_eq_once_seg`: if `instantiateOnce?` succeeds, the strategy and the closed program whose
  instantiation phase is the spec's `$instantiate` configuration (segment initialisation run by
  Core `Step P`, then the start call) are those whose instantiation phase runs only the start
  call from `instantiateOnce?`'s store and frame — every profile. The proof: the spec
  configuration is the renamed residue configuration (`prepare_residue_emb`, global
  embedding), whose segment code is a forced run (`segInit_ok`) to `instantiateOnce?`'s store
  (`instStrategyT_emb`, `instStrategyT_detTo`, and their closed versions).
* `spec_trap_seg`: if instead the direct initialisation traps (`initSegmentsT? = .trap`, the
  out-of-bounds case where `instantiateOnce?` fails), the spec configuration runs, forced, to a
  trap.

New.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

theorem external_id (x : ExternAddr) : external id x = x := by cases x <;> rfl

theorem map_external_id (xas : List ExternAddr) : xas.map (external id) = xas := by
  rw [show external id = (id : ExternAddr → ExternAddr) from funext external_id, List.map_id]

theorem withStart_eq (c : Config Nat) (st : Option FuncIdx) :
    c.withStart st = ⟨c.store, c.frame, c.code ++ startCode st⟩ := by
  cases st <;> simp only [Config.withStart, startCode, List.append_nil]

theorem admins_segCode (ρ : Nat → Nat) (m : Module) (st : Option FuncIdx) :
    admins ρ (segCode m ++ startCode st) = segCode m ++ startCode st := by
  cases st <;> simp only [segCode, startCode, admins_append, admins_expression, admins_cons,
    admins_nil, admin]

/-- The spec configuration's thread is the renamed residue thread. -/
theorem thread_seg {ι : Nat → Nat} {c c₁ : Config Nat} {m : Module} (hcode : c.code = segCode m)
    (hcode₁ : c₁.code = segCode m) (hframe : c.frame = frame ι c₁.frame) (st : Option FuncIdx) :
    configThread (c.withStart st) = thread ι (configThread (c₁.withStart st)) := by
  rw [withStart_eq, withStart_eq]
  simp only [configThread, thread, hcode, hcode₁, hframe, admins_segCode]

/-- The forced run of the residue configuration with its start call. -/
theorem residue_detTo {P : Profile} {c₁ : Config Nat} {m : Module} {s' : Store Nat} {f' : Frame}
    (hm : OffsetsConst m) (hcode₁ : c₁.code = segCode m)
    (hi : initSegments? evalConst? c₁.store c₁.frame m.globalResidue = some (s', f'))
    (st : Option FuncIdx) :
    DetTo P (c₁.withStart st) ((⟨s', f', []⟩ : Config Nat).withStart st) := by
  have hT : initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue = .ok (s', f') :=
    initSegmentsT?_ok_iff.2 hi
  have hd := segInit_ok (P := P) (startCode st) (m := m.globalResidue) hm hT
  rw [withStart_eq, hcode₁, Config.withStart_nil]
  exact hd

/-- **Spec instantiation with segments plays as single allocation**, every profile. -/
theorem spec_eq_once_seg {s s' : Store Nat} {m : Module} {xas : List ExternAddr} {f' : Frame}
    {st : Option FuncIdx} (hs : StoreOk s) (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length) (hm : OffsetsConst m)
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) K := by
  obtain ⟨s₁, f₁, vs, c₁, hg, hp, hi⟩ := once_inv' ho
  obtain ⟨c, ι, hc, hcode, hframe, hinj, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id (modDom_of_storeOk hs hw) hxb hg hp
  have hcode₁ : c₁.code = segCode m := residue_code hp
  have hcode' : c.code = segCode m := hcode.trans hcode₁
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← map_external_id xas]
    exact hc
  have hth := thread_seg hcode' hcode₁ hframe st
  have hst : (c.withStart st).store = c.store := withStart_store c st
  have hst₁ : (c₁.withStart st).store = c₁.store := withStart_store c₁ st
  refine ⟨c, hc', fun I P => ⟨?_, fun K => ?_⟩⟩
  · have hd := instStrategyT_detTo I (residue_detTo (P := P) hm hcode₁ hi st)
    show I.instStrategyT P (c.withStart st).store (configThread (c.withStart st)) = _
    rw [hth, hst, ← instStrategyT_emb I P hinj he, ← hst₁, hd, withStart_store]
  · have hd := closedInstT_detTo I (residue_detTo (P := P) hm hcode₁ hi st) K
    show I.closedInstT P (c.withStart st).store (configThread (c.withStart st)) K = _
    rw [hth, hst, ← closedInstT_emb I P hinj he _ K, ← hst₁, hd, withStart_store]

/-- **Trapping segment initialisation**: when the residue preparation of single allocation
succeeds but its direct segment initialisation traps (out of bounds; `instantiateOnce?` then
fails), the spec's instantiation plays as a thread stopped at the trap, every profile. -/
theorem spec_trap_seg {s : Store Nat} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length) (hm : OffsetsConst m)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    {s'' : Store Nat}
    (htrap : initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue = .trap s'') :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile), ∃ (W : List Val) (R : List Admin),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s'' (configThread ⟨s'', c₁.frame, vals W ++ .trap :: R⟩) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s'' (configThread ⟨s'', c₁.frame, vals W ++ .trap :: R⟩) K := by
  obtain ⟨c, ι, hc, hcode, hframe, hinj, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id (modDom_of_storeOk hs hw) hxb hg hp
  have hcode₁ : c₁.code = segCode m := residue_code hp
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← map_external_id xas]
    exact hc
  have hth := thread_seg (hcode.trans hcode₁) hcode₁ hframe st
  have hst : (c.withStart st).store = c.store := withStart_store c st
  have hst₁ : (c₁.withStart st).store = c₁.store := withStart_store c₁ st
  refine ⟨c, hc', fun I P => ?_⟩
  obtain ⟨W, R, hdet⟩ := segInit_trap (P := P) (startCode st) (m := m.globalResidue) hm htrap
  have hdet' : DetTo P (c₁.withStart st) ⟨s'', c₁.frame, vals W ++ .trap :: R⟩ := by
    rw [withStart_eq, hcode₁]
    exact hdet
  refine ⟨W, R, ?_, fun K => ?_⟩
  · have hd := instStrategyT_detTo I hdet'
    show I.instStrategyT P (c.withStart st).store (configThread (c.withStart st)) = _
    rw [hth, hst, ← instStrategyT_emb I P hinj he, ← hst₁, hd]
  · have hd := closedInstT_detTo I hdet' K
    show I.closedInstT P (c.withStart st).store (configThread (c.withStart st)) K = _
    rw [hth, hst, ← closedInstT_emb I P hinj he _ K, ← hst₁, hd]

end Silmaril.Proofs.Wasm.Game.SpecGlobals
