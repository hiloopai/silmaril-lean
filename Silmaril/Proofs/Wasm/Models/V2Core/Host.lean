module

public import Silmaril.Wasm.Models.V2Core.Defs

/-!
# The induced Core host is compatible with the 2.0 host

* `toCore_eq_some`: the shape of a Core image of a 2.0 store; `erase_of_toCore`: images are
  fixed by `ToCore.Store.erase`; `toCore_isSome_of_funcs`: whether a store has an image depends
  only on its functions;
* `compatible`: `HostCompatible src (liftHost src)` for a host that preserves well-formedness
  and keeps functions;
* `keeps`, `throwsIn`: `liftHost src` keeps functions and never throws, so the image point lies
  in the domain of `core|S` as far as the host is concerned.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.V2.Execution (StoreWF HostPreserves HostCompatible HostOutcomeSim)

variable {H : Type}

/-- The image of the 2.0 store with functions `fs`. -/
def image (s : VStore H) (fs : List (Silmaril.Wasm.Execution.Core.FuncInst H)) : CStore H :=
  { tags := []
    globals := s.globals.map Silmaril.Wasm.V2.Execution.GlobalInst.toCore
    mems := s.mems.map Silmaril.Wasm.V2.Execution.MemInst.toCore
    tables := s.tables.map Silmaril.Wasm.V2.Execution.TableInst.toCore
    funcs := fs
    datas := s.datas.map Silmaril.Wasm.V2.Execution.DataInst.toCore
    elems := s.elems.map Silmaril.Wasm.V2.Execution.ElemInst.toCore
    structs := []
    arrays := []
    exns := [] }

theorem toCore_eq_some {s : VStore H} {X : CStore H} :
    Silmaril.Wasm.V2.Execution.Store.toCore s = some X ↔
      ∃ fs, s.funcs.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore = some fs ∧
        image s fs = X := by
  simp [Silmaril.Wasm.V2.Execution.Store.toCore, image]

/-- Every function of an image records a module instance without tags. -/
theorem funcInst_erase {fi : Silmaril.Wasm.V2.Execution.FuncInst H}
    {c : Silmaril.Wasm.Execution.Core.FuncInst H}
    (h : Silmaril.Wasm.V2.Execution.FuncInst.toCore fi = some c) :
    { c with module := Silmaril.Wasm.V2.Execution.ToCore.ModuleInst.erase c.module } = c := by
  unfold Silmaril.Wasm.V2.Execution.FuncInst.toCore at h
  split at h <;> simp_all [Option.map_eq_some_iff] <;> grind [
    Silmaril.Wasm.V2.Execution.ToCore.ModuleInst.erase,
    Silmaril.Wasm.V2.Execution.ModuleInst.toCore]

theorem funcs_erase {l : List (Silmaril.Wasm.V2.Execution.FuncInst H)}
    {fs : List (Silmaril.Wasm.Execution.Core.FuncInst H)}
    (h : l.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore = some fs) :
    fs.map (fun fi => { fi with
      module := Silmaril.Wasm.V2.Execution.ToCore.ModuleInst.erase fi.module }) = fs := by
  induction l generalizing fs with
  | nil => simp_all
  | cons a l ih =>
    cases ha : Silmaril.Wasm.V2.Execution.FuncInst.toCore a with
    | none => simp [List.mapM_cons, ha] at h
    | some c =>
      cases hl : l.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore with
      | none => simp [List.mapM_cons, ha, hl] at h
      | some cs =>
        have hfs : fs = c :: cs := by simpa [List.mapM_cons, ha, hl] using h.symm
        rw [hfs]
        simp [funcInst_erase ha, ih hl]

/-- Images are fixed by erasure. -/
theorem erase_of_toCore {s : VStore H} {X : CStore H}
    (h : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) :
    Silmaril.Wasm.V2.Execution.ToCore.Store.erase X = X := by
  obtain ⟨fs, hfs, rfl⟩ := toCore_eq_some.mp h
  have hf := funcs_erase hfs
  simp only [Silmaril.Wasm.V2.Execution.ToCore.Store.erase, image, hf]

theorem toCore_isSome_of_funcs {s s' : VStore H} (hf : s'.funcs = s.funcs)
    (h : (Silmaril.Wasm.V2.Execution.Store.toCore s).isSome) :
    (Silmaril.Wasm.V2.Execution.Store.toCore s').isSome := by
  simp only [Silmaril.Wasm.V2.Execution.Store.toCore, Option.isSome_map] at h ⊢
  rwa [hf]

/-- Replacing the functions of the image of `s'` by those of a Core store `S` whose erasure is
the image of `s`, where `s` and `s'` have the same functions, keeps it an image. -/
theorem toCore_withFuncs {s s' : VStore H} {S X : CStore H} (hf : s'.funcs = s.funcs)
    (hS : Silmaril.Wasm.V2.Execution.Store.toCore s =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S))
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s' = some X) :
    Silmaril.Wasm.V2.Execution.Store.toCore s' =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase { X with funcs := S.funcs }) := by
  obtain ⟨fs, hfs, hSe⟩ := toCore_eq_some.mp hS
  obtain ⟨fs', hfs', rfl⟩ := toCore_eq_some.mp hX
  have hff : fs' = fs := Option.some.inj (hfs'.symm.trans (hf ▸ hfs))
  have hfun : S.funcs.map (fun fi => { fi with
      module := Silmaril.Wasm.V2.Execution.ToCore.ModuleInst.erase fi.module }) = fs :=
    (congrArg Silmaril.Wasm.Execution.Core.Store.funcs hSe).symm
  rw [hX]
  simp only [Silmaril.Wasm.V2.Execution.ToCore.Store.erase, image, hfun, hff]

/-- The induced host matches every behaviour of the 2.0 host. -/
theorem lift_matches {src : VHost H} (hk : HostKeepsV src) {h : H} {s : VStore H}
    {vs : List VVal} {out : Silmaril.Wasm.V2.Execution.HostOutcome H} {S : CStore H}
    (hsrc : src h s vs out)
    (hS : Silmaril.Wasm.V2.Execution.Store.toCore s =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S)) :
    ∃ out', liftHost src h S (vs.map Silmaril.Wasm.V2.Execution.Val.toCore) out' ∧
      HostOutcomeSim out out' := by
  cases out with
  | diverged => exact ⟨.diverged, ⟨s, vs, hS, rfl, Or.inl ⟨hsrc, rfl⟩⟩, trivial⟩
  | returned s' r =>
    have hf : s'.funcs = s.funcs := hk h s vs s' r hsrc
    have hsome : (Silmaril.Wasm.V2.Execution.Store.toCore s').isSome :=
      toCore_isSome_of_funcs hf (by rw [hS]; rfl)
    obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hsome
    have hw := toCore_withFuncs hf hS hX
    exact ⟨.returned { X with funcs := S.funcs } _,
      ⟨s, vs, hS, rfl, Or.inr ⟨s', r, _, hsrc, rfl, hw, rfl⟩⟩, hw, rfl⟩

/-- **The induced host is compatible with the 2.0 host.** -/
theorem compatible {src : VHost H} (hp : HostPreserves src) (hk : HostKeepsV src) :
    HostCompatible src (liftHost src) :=
  ⟨hp, fun _ _ _ _ _ hsrc hS => lift_matches hk hsrc hS⟩

/-- The induced host keeps functions. -/
theorem keeps (src : VHost H) : Rt.HostKeeps (liftHost src) := by
  rintro h S args S' r ⟨s, vs, -, -, ⟨-, hout⟩ | ⟨s', r', S'', -, hout, -, hfun⟩⟩
  · cases hout
  · cases hout
    exact hfun

/-- The induced host never throws. -/
theorem throwsIn (S : FeatureSet) (src : VHost H) : Rt.HostThrowsIn S (liftHost src) := by
  rintro h X args X' a ⟨s, vs, -, -, ⟨-, hout⟩ | ⟨s', r', S'', -, hout, -, -⟩⟩
  · cases hout
  · cases r' <;> cases hout

end Silmaril.Proofs.Wasm.Models.V2Core
