module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Shared helpers for the basic (pure/variable) head-rule simulation lemmas

For a Lime1 code sequence made only of `.source` instructions (which includes
all value instructions), the Core code related by `Sim` is exactly its image;
`pb_finish` packages "one Core step between images re-establishes `Sim`".
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution.ToCore

variable {H : Type}

/-- A Lime1 administrative instruction that is a source instruction. -/
def pb_IsSrc : Admin → Prop
  | .source _ => True
  | _ => False

@[simp] theorem pb_IsSrc_source (i : Instr) : pb_IsSrc (.source i) := trivial

@[simp] theorem pb_IsSrc_value (v : Value) : pb_IsSrc (value v) := by
  rcases v with ⟨⟨_ | _⟩, _⟩ <;> trivial

theorem pb_rigid (s : Silmaril.Wasm.Execution.Runtime.Store H) :
    (code : List Admin) → (∀ a ∈ code, pb_IsSrc a) →
      ∀ y ∈ Admin.listToCore s code, ToCore.Rigid y
  | [], _ => by simp
  | a :: as, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    intro y hy
    rw [listToCore_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · rcases a with i | _ | _ | _ | _ <;> simp [pb_IsSrc] at h
      simp only [source_toCore, List.mem_singleton] at hy
      subst hy; exact ToCore.Rigid.toCore i
    · exact pb_rigid s as h.2 y hy

/-- The Core code related to a source-only Lime1 code sequence is its image. -/
theorem pb_codeEq {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) (hsrc : ∀ a ∈ code, pb_IsSrc a) :
    cl = Admin.listToCore s code := by
  obtain ⟨hn, -⟩ := hs
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  exact ToCore.map_norm_eq_of_rigid (pb_rigid s code hsrc) hn.2.2

theorem pb_storeEq {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) : ToCore.Store.erase cs = s.toCore := by
  obtain ⟨hn, -⟩ := hs
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  exact hn.1

theorem pb_frameEq {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) : ToCore.Frame.erase cf = f.toCore := by
  obtain ⟨hn, -⟩ := hs
  rw [ToCore.Config.norm_eq_toCore_iff] at hn
  exact hn.2.1

/-- Re-establish `Sim` on an image code sequence. -/
theorem pb_sim {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    (hst : ToCore.Store.erase cs = s.toCore) (hfr : ToCore.Frame.erase cf = f.toCore)
    (hwf : ConfigWF (⟨s, f, code⟩ : Silmaril.Wasm.Execution.Runtime.Config H)) :
    Sim ⟨s, f, code⟩ ⟨cs, cf, Admin.listToCore s code⟩ := by
  refine ⟨?_, hwf⟩
  rw [ToCore.Config.norm_eq_toCore_iff]
  exact ⟨hst, hfr, map_norm_listToCore _ _ _⟩

/-- One Core step between images, with updated store/frame. -/
theorem pb_finish {P : Silmaril.Wasm.Numerics.Profile} {tgt : ToCore.CHostSemantics H}
    {s s' : Silmaril.Wasm.Execution.Runtime.Store H} {f f' : Frame} {before after : List Admin} {c : ToCore.CConfig H}
    {cs' : CStore H} {cf' : CFrame}
    (hs : Sim ⟨s, f, before⟩ c) (hsrc : ∀ a ∈ before, pb_IsSrc a)
    (hstep : Silmaril.Wasm.Execution.Core.Step P tgt
      ⟨c.store, c.frame, Admin.listToCore s before⟩ ⟨cs', cf', Admin.listToCore s' after⟩)
    (hst : ToCore.Store.erase cs' = s'.toCore) (hfr : ToCore.Frame.erase cf' = f'.toCore)
    (hwf : ConfigWF (⟨s', f', after⟩ : Silmaril.Wasm.Execution.Runtime.Config H)) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧
      Sim ⟨s', f', after⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hc := pb_codeEq hs hsrc
  subst hc
  exact ⟨_, .single hstep, pb_sim hst hfr hwf⟩

/-- One Core step between images, store and frame unchanged. -/
theorem pb_finish_same {P : Silmaril.Wasm.Numerics.Profile} {tgt : ToCore.CHostSemantics H}
    {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {before after : List Admin} {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, before⟩ c) (hsrc : ∀ a ∈ before, pb_IsSrc a)
    (hwf : Admin.listWF s after)
    (hstep : Silmaril.Wasm.Execution.Core.Step P tgt
      ⟨c.store, c.frame, Admin.listToCore s before⟩ ⟨c.store, c.frame, Admin.listToCore s after⟩) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step P tgt) c c' ∧
      Sim ⟨s, f, after⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  refine pb_finish hs hsrc hstep (pb_storeEq hs) (pb_frameEq hs) ?_
  exact ⟨hs.2.1, hs.2.2.1, hwf⟩

/-- Value sequences are well formed. -/
@[simp] theorem pb_listWF_value (s : Silmaril.Wasm.Execution.Runtime.Store H) (v : Value) (l : List Admin) :
    Admin.listWF s (value v :: l) ↔ Admin.listWF s l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ <;> simp [value, Admin.listWF, Admin.WF]

@[simp] theorem pb_listWF_source (s : Silmaril.Wasm.Execution.Runtime.Store H) (i : Instr) (l : List Admin) :
    Admin.listWF s (.source i :: l) ↔ Admin.listWF s l := by
  simp [Admin.listWF, Admin.WF]

@[simp] theorem pb_listWF_trap (s : Silmaril.Wasm.Execution.Runtime.Store H) (l : List Admin) :
    Admin.listWF s (.trap :: l) ↔ Admin.listWF s l := by
  simp [Admin.listWF, Admin.WF]

@[simp] theorem pb_listWF_nil (s : Silmaril.Wasm.Execution.Runtime.Store H) : Admin.listWF s [] := by
  simp [Admin.listWF]

/-- Normalise the image of a (short, explicit) Lime1 code sequence. -/
macro "pb_norm" : tactic =>
  `(tactic| simp only [listToCore_cons, listToCore_nil, value_toCore, source_toCore,
      trap_toCore, List.singleton_append, List.cons_append, List.nil_append, List.append_nil,
      Instr.toCore])

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
