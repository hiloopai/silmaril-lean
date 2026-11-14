module

public import Silmaril.Net.Http.OpenApi.Defs

/-! Proofs for `Silmaril.Net.Http.OpenApi.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http.Proofs.OpenApi

open Silmaril.Net.Http Silmaril.Net.Http.OpenApi

theorem matchTemplate_sound : ∀ (t : PathTemplate) (ss vs : List Bytes),
    matchTemplate t ss = some vs → render t vs = ss
  | [], [], vs, h => by simp [matchTemplate] at h; subst h; rfl
  | [], _ :: _, _, h => by simp [matchTemplate] at h
  | .lit _ :: _, [], _, h => by simp [matchTemplate] at h
  | .param _ :: _, [], _, h => by simp [matchTemplate] at h
  | .lit l :: ts, s :: ss, vs, h => by
    simp only [matchTemplate] at h
    split_ifs at h with hl
    subst hl
    simp [render, matchTemplate_sound ts ss vs h]
  | .param n :: ts, s :: ss, vs, h => by
    simp only [matchTemplate] at h
    split_ifs at h with hs
    obtain ⟨ws, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [render, matchTemplate_sound ts ss ws hw]

theorem matchTemplate_length : ∀ (t : PathTemplate) (ss vs : List Bytes),
    matchTemplate t ss = some vs → vs.length = t.params.length
  | [], [], vs, h => by simp [matchTemplate] at h; subst h; rfl
  | [], _ :: _, _, h => by simp [matchTemplate] at h
  | .lit _ :: _, [], _, h => by simp [matchTemplate] at h
  | .param _ :: _, [], _, h => by simp [matchTemplate] at h
  | .lit l :: ts, s :: ss, vs, h => by
    simp only [matchTemplate] at h
    split_ifs at h with hl
    simpa [PathTemplate.params] using matchTemplate_length ts ss vs h
  | .param n :: ts, s :: ss, vs, h => by
    simp only [matchTemplate] at h
    split_ifs at h with hs
    obtain ⟨ws, hw, rfl⟩ := Option.map_eq_some_iff.1 h
    have := matchTemplate_length ts ss ws hw
    simp only [PathTemplate.params, List.filterMap_cons, List.length_cons] at this ⊢
    omega

theorem matchTemplate_render : ∀ (t : PathTemplate) (vs : List Bytes),
    vs.length = t.params.length → (∀ v ∈ vs, v ≠ []) → matchTemplate t (render t vs) = some vs
  | [], vs, h, _ => by
    simp only [PathTemplate.params, List.filterMap_nil, List.length_nil, List.length_eq_zero_iff] at h
    subst h; rfl
  | .lit l :: ts, vs, h, hv => by
    simp only [PathTemplate.params, List.filterMap_cons] at h
    simp [render, matchTemplate, matchTemplate_render ts vs h hv]
  | .param n :: ts, [], h, _ => by simp [PathTemplate.params] at h
  | .param n :: ts, v :: vs, h, hv => by
    simp only [PathTemplate.params, List.filterMap_cons, List.length_cons] at h
    have hv' : v ≠ [] := hv v (by simp)
    simp [render, matchTemplate, hv', matchTemplate_render ts vs (by simpa [PathTemplate.params] using h)
      (fun w hw => hv w (by simp [hw]))]

theorem findSome?_mem {α β : Type} {f : α → Option β} {l : List α} {b : β}
    (h : l.findSome? f = some b) : ∃ a ∈ l, f a = some b := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.findSome?_cons] at h
    split at h
    · next hx => cases h; exact ⟨x, by simp, hx⟩
    · obtain ⟨a, ha, hfa⟩ := ih h; exact ⟨a, by simp [ha], hfa⟩

theorem routePath_mem {d : Document} {path : Bytes} {p : PathItem} {vs : List Bytes}
    (h : routePath d path = some (p, vs)) :
    p ∈ d.paths ∧ matchTemplate p.template (segments path) = some vs := by
  unfold routePath at h
  simp only at h
  split at h
  · next r hr =>
    cases h
    obtain ⟨a, ha, hfa⟩ := findSome?_mem hr
    obtain ⟨ws, hw, he⟩ := Option.map_eq_some_iff.1 hfa
    cases he
    exact ⟨(List.mem_filter.1 ha).1, hw⟩
  · obtain ⟨a, ha, hfa⟩ := findSome?_mem h
    obtain ⟨ws, hw, he⟩ := Option.map_eq_some_iff.1 hfa
    cases he
    exact ⟨(List.mem_filter.1 ha).1, hw⟩

theorem route_mem {d : Document} {r : Request} {op : Operation} {p : PathItem} {vs : List Bytes}
    (h : route d r = some (op, p, vs)) :
    p ∈ d.paths ∧ op ∈ p.operations ∧ op.method = r.method ∧
      matchTemplate p.template (segments (pathPart (targetPq r.target))) = some vs := by
  unfold route at h
  obtain ⟨⟨p', vs'⟩, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨op', hop, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  obtain ⟨hp, hm⟩ := routePath_mem hr
  have hmem := List.mem_of_find?_eq_some hop
  have hmeth := List.find?_some hop
  exact ⟨hp, hmem, by simpa using hmeth, hm⟩

end Silmaril.Net.Http.Proofs.OpenApi
