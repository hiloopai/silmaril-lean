module

public import Silmaril.Wasm.Wit.Binary.Custom.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# The `producers` section reads back

`Producers.parse_encode : p.encode = some l → Producers.parse ⟨l.toArray⟩ = .ok p`,
from the verified grammar `producersG` of `Silmaril.Parse.ByteParse`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)
open Silmaril.Parse.ByteParse.Grammar

instance lawful_versionedG : versionedG.Lawful := by unfold versionedG; grammar_lawful
instance lawful_producerFieldG : producerFieldG.Lawful := by unfold producerFieldG; grammar_lawful
instance lawful_producersG : producersG.Lawful := by unfold producersG; grammar_lawful

theorem versioned_G {v : String × String} {l : Bytes}
    (h : (do let x ← Silmaril.Parse.ByteParse.Enc.name v.1; let y ← Silmaril.Parse.ByteParse.Enc.name v.2; pure (x ++ y)) = some l) :
    versionedG.G l v := by
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  exact seq_G (Silmaril.Parse.ByteParse.Enc.name_G hx) (Silmaril.Parse.ByteParse.Enc.name_G hy)

theorem producerField_G {f : String × List (String × String)} {l : Bytes}
    (h : (do
      let a ← Silmaril.Parse.ByteParse.Enc.name f.1
      let b ← Silmaril.Parse.ByteParse.Enc.vec (fun (v : String × String) => do
        let x ← Silmaril.Parse.ByteParse.Enc.name v.1
        let y ← Silmaril.Parse.ByteParse.Enc.name v.2
        pure (x ++ y)) f.2
      pure (a ++ b)) = some l) : producerFieldG.G l f := by
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact seq_G (Silmaril.Parse.ByteParse.Enc.name_G ha)
    (Silmaril.Parse.ByteParse.Enc.vec_G (hne := seq_nonEmpty name_nonEmpty) (fun _ _ _ hv => versioned_G hv) hb)

/-- **The producers section reads back.** -/
theorem Producers.parse_encode {p : Producers} {l : Bytes} (h : p.encode = some l) :
    Producers.parse ⟨l.toArray⟩ = .ok p :=
  GrammarE.runAll_complete (GrammarE.ofGrammar producersG)
    (Silmaril.Parse.ByteParse.Enc.vec_G (hne := seq_nonEmpty name_nonEmpty) (fun _ _ _ hf => producerField_G hf) h)

end Silmaril.Wasm.Wit.Binary
