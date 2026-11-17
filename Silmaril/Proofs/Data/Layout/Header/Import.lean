module

public import Silmaril.Data.Layout.Header.Import.Defs

/-! Proofs for `Silmaril.Data.Layout.Header.Import.Thms`. -/

public section

namespace Silmaril.Proofs.Data.Layout.Header.Import

open Silmaril.Data.Layout.Header
open Silmaril.Data.Layout.Header.Import

theorem importNodes_length (env : TyEnv) (ts : List Silmaril.Compiler.Clang.TotalJson.Tree) :
    (importNodes env ts).length = ts.length := by
  induction ts generalizing env with
  | nil => rfl
  | cons t ts ih => simp only [importNodes]; split <;> simp [ih]

theorem mem_names_of_proto {H : Header} {f : String} {cp : CProto} (h : H.proto? f = some cp) :
    f ∈ H.names := by
  unfold Header.proto? at h
  cases hf : H.protos.find? (·.1 == f) with
  | none => simp [hf] at h
  | some q =>
    have hm := List.mem_of_find?_eq_some hf
    have he : q.1 = f := by simpa using List.find?_some hf
    exact List.mem_map.mpr ⟨q, hm, he⟩

theorem ofJson_provenance (prov : Provenance) (json : String) :
    (Imported.ofJson prov json).provenance = prov := by
  unfold Imported.ofJson
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i ms _
        split <;> rfl
      · rfl

end Silmaril.Proofs.Data.Layout.Header.Import

end
