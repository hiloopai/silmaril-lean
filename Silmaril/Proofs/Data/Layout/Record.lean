module

public import Silmaril.Data.Layout.Record.Defs
public import Silmaril.Data.Layout.Thms

/-!
# Proofs: resolved record layouts are well-formed and follow their source

`ofDeclLayout` preserves well-formedness; `resolveEnv` succeeds record by record, so its
layouts are well-formed under a well-formed data model (`resolveEnv_wf`) and have the kinds,
names and member names of the source declarations, in order (`resolveEnv_names`).
-/

@[expose] public section

namespace Silmaril.Proofs.Data.Layout.Record

open Silmaril.Data.Layout Silmaril.Data.Layout.Record

theorem ofDeclLayout_wf {L : DeclLayout} (h : L.WF) : (ofDeclLayout L).WF := by
  obtain ⟨hs, hin, hal, hdvd, hp, hdis, hz⟩ := h
  refine ⟨hs.pow2, hs.dvd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [ofDeclLayout, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  · exact hin
  · exact hal
  · exact hdvd
  · exact hp
  · intro hk; exact List.pairwise_map.mpr (hdis hk)
  · exact hz

theorem traverse_nil {α β : Type} {f : α → Except String β} {l' : List β}
    (h : traverse f [] = .ok l') : l' = [] := by
  simp only [traverse, Except.ok.injEq] at h; exact h.symm

theorem traverse_cons {α β : Type} {f : α → Except String β} {a : α} {as : List α}
    {l' : List β} (h : traverse f (a :: as) = .ok l') :
    ∃ b bs, f a = .ok b ∧ traverse f as = .ok bs ∧ l' = b :: bs := by
  simp only [traverse] at h
  split at h
  · cases h
  · rename_i b hb
    split at h
    · cases h
    · rename_i bs hbs
      simp only [Except.ok.injEq] at h
      exact ⟨b, bs, hb, hbs, h.symm⟩

/-- One step of `resolveEnv`'s traversal: the record's layout is the forgetful image of its
declaration layout. -/
theorem resolveStep {dm : DataModel} {env : Env} {d : Decl} {R : RecordLayout}
    (h : (match declLayout dm env d with
      | .ok L => .ok (ofDeclLayout L)
      | .error e => .error s!"{d.tag}: {e}" : Except String RecordLayout) = .ok R) :
    ∃ L, declLayout dm env d = .ok L ∧ R = ofDeclLayout L := by
  split at h
  · rename_i L hL; simp only [Except.ok.injEq] at h; exact ⟨L, hL, h.symm⟩
  · cases h

theorem resolveEnv_wf_aux {dm : DataModel} (hdm : dm.WF) {env : Env} :
    ∀ {ds : Env} {Ls : List RecordLayout},
    traverse (fun d => match declLayout dm env d with
      | .ok L => .ok (ofDeclLayout L)
      | .error e => .error s!"{d.tag}: {e}") ds = .ok Ls → ∀ R ∈ Ls, R.WF
  | [], _, h => by rw [traverse_nil h]; simp
  | _ :: _, _, h => by
    obtain ⟨R, Rs, hR, hRs, rfl⟩ := traverse_cons h
    obtain ⟨L, hL, rfl⟩ := resolveStep hR
    intro R' hR'
    rcases List.mem_cons.mp hR' with rfl | hR'
    · exact ofDeclLayout_wf (declLayout_wf hdm hL)
    · exact resolveEnv_wf_aux hdm hRs R' hR'

theorem resolveEnv_wf {dm : DataModel} (hdm : dm.WF) {env : Env} {Ls : List RecordLayout}
    (h : resolveEnv dm env = .ok Ls) : ∀ R ∈ Ls, R.WF :=
  resolveEnv_wf_aux hdm h

theorem declLayout_names {dm : DataModel} {env : Env} {d : Decl} {L : DeclLayout}
    (h : declLayout dm env d = .ok L) :
    L.kind = d.kind ∧ L.tag = d.tag ∧ L.fields.map (·.name) = d.fields.map (·.name) := by
  obtain ⟨ms, hms, hk, -, hslots⟩ := declLayout_fields_slot h
  have hlen : L.fields.length = d.fields.length := by
    rw [← List.length_map (f := PlacedField.slot), hslots, ← fieldShapes_length hms]
    cases d.kind <;> simp [kindPlace, structPlace, unionPlace, place_length]
  simp only [declLayout] at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨rfl, rfl, ?_⟩
    simp only [List.map_map]
    have : ((·.name) ∘ fun (x : Field × Slot) =>
        ({ name := x.1.name, ty := x.1.ty, off := x.2.off, size := x.2.size,
           align := x.2.align } : PlacedField)) = (·.name) ∘ Prod.fst := by
      funext x; rfl
    rw [this, ← List.map_map, List.map_fst_zip]
    simp only [List.length_map, List.length_zip] at hlen
    omega

theorem resolveEnv_names_aux {dm : DataModel} {env : Env} :
    ∀ {ds : Env} {Ls : List RecordLayout},
    traverse (fun d => match declLayout dm env d with
      | .ok L => .ok (ofDeclLayout L)
      | .error e => .error s!"{d.tag}: {e}") ds = .ok Ls → Ls.map layoutNames = ds.map declNames
  | [], _, h => by rw [traverse_nil h]; rfl
  | d :: _, _, h => by
    obtain ⟨R, Rs, hR, hRs, rfl⟩ := traverse_cons h
    obtain ⟨L, hL, rfl⟩ := resolveStep hR
    obtain ⟨hk, ht, hn⟩ := declLayout_names hL
    simp only [List.map_cons, resolveEnv_names_aux hRs, layoutNames, declNames, ofDeclLayout,
      List.map_map, hk, ht, ← hn]
    rfl

theorem resolveEnv_names {dm : DataModel} {env : Env} {Ls : List RecordLayout}
    (h : resolveEnv dm env = .ok Ls) : Ls.map layoutNames = env.map declNames :=
  resolveEnv_names_aux h

end Silmaril.Proofs.Data.Layout.Record
