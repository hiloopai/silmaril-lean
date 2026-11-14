module

public import Silmaril.Servers.OpenApi.Defs
public import Silmaril.Servers.Core.Thms
public import Silmaril.Net.Http.OpenApi.Thms

/-!
# Proofs: the OpenAPI institution
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.OpenApiInst

open Silmaril.Servers Silmaril.Servers.OpenApiInst
open Silmaril.Net.Http (Request Response)
open Silmaril.Net.Http.OpenApi

theorem sat_map_iff {A B : OpenApiInst.Sig} (σ : Sig.Hom A B) (M : OpenApiInst.Model B) :
    ∀ φ : OpenApiInst.Sen A, OpenApiInst.Sat M (φ.map σ) ↔ OpenApiInst.Sat (M.reduct σ) φ
  | .respOk _ => Iff.rfl
  | .closed _ => Iff.rfl
  | .rejects _ _ => Iff.rfl
  | .conj φ ψ => and_congr (sat_map_iff σ M φ) (sat_map_iff σ M ψ)
  | .neg φ => not_congr (sat_map_iff σ M φ)

theorem map_id {A : OpenApiInst.Sig} : ∀ φ : OpenApiInst.Sen A, φ.map ⟨id⟩ = φ
  | .respOk _ => rfl
  | .closed _ => rfl
  | .rejects _ _ => rfl
  | .conj φ ψ => by simp only [OpenApiInst.Sen.map, map_id φ, map_id ψ]
  | .neg φ => by simp only [OpenApiInst.Sen.map, map_id φ]

theorem map_comp {A B C : OpenApiInst.Sig} (σ : Sig.Hom A B) (τ : Sig.Hom B C) :
    ∀ φ : OpenApiInst.Sen A, φ.map ⟨τ.op ∘ σ.op⟩ = (φ.map σ).map τ
  | .respOk _ => rfl
  | .closed _ => rfl
  | .rejects _ _ => rfl
  | .conj φ ψ => by simp only [OpenApiInst.Sen.map, map_comp σ τ φ, map_comp σ τ ψ]
  | .neg φ => by simp only [OpenApiInst.Sen.map, map_comp σ τ φ]

/-- The one-exchange trace of the function server. -/
theorem ofFun_one (S : Service) (r : Request) :
    (Servers.Model.ofFun (A := Http.sig) S).Tr (Trace.seq (A := Http.sig) [(⟨0, 0⟩, r, S r)]) := by
  have h : ((Machine.ofFun (A := Http.sig) S).server ()).Tr
      (Trace.seq (A := Http.sig) [(⟨0, 0⟩, r, S r)]) :=
    (Machine.server_tr_iff _ _ _).2 ((Sen.lin_seq_iff _ (by simp)).2 ⟨(), .cons rfl (.nil _)⟩)
  exact (Servers.Model.ofFun_eq_server (A := Http.sig) S) ▸ h

/-- A function server satisfies an atomic sentence iff the relation holds of each request and
its answer. -/
theorem ofFun_sat_atomic_iff (S : Service) (R : Request → Response → Prop) :
    (Servers.Model.ofFun (A := Http.sig) S).Sat (Servers.Sen.atomic (A := Http.sig) R) ↔
      ∀ r, R r (S r) := by
  constructor
  · intro h r
    exact h _ (ofFun_one S r) ⟨0, 0⟩ r (S r) (by simp [Trace.seq]) (by simp [Trace.seq])
  · intro h t ht i r s hr hs
    have := ht.2 i r s hr hs
    rw [this]
    exact h r

theorem docOp_of_route {d : Document} {r : Request} {op : Operation} {p : PathItem}
    {vs : List Bytes} (h : route d r = some (op, p, vs)) : ∃ q ∈ d.paths, op ∈ q.operations :=
  ⟨p, (route_mem h).1, (route_mem h).2.1⟩

theorem conforms_iff (d : Document) (S : Service) :
    (∀ o : DocOp d, OpenApiInst.Sat (docModel d S) (.respOk o)) ↔ Conforms d S := by
  simp only [OpenApiInst.Sat, docModel, ofFun_sat_atomic_iff, respOkRel, Routed]
  constructor
  · intro h r op p vs hr hc
    exact h ⟨op, docOp_of_route hr⟩ r p vs hr hc
  · intro h o r p vs hr hc
    exact h r o.1 p vs hr hc

theorem closed_iff (d : Document) (S : Service) :
    (∀ o : DocOp d, OpenApiInst.Sat (docModel d S) (.closed o)) ↔ Closed d S := by
  simp only [OpenApiInst.Sat, docModel, ofFun_sat_atomic_iff, closedRel, Routed]
  constructor
  · intro h r op p vs hr
    exact h ⟨op, docOp_of_route hr⟩ r p vs hr
  · intro h o r p vs hr
    exact h r o.1 p vs hr

theorem sat_of_refines {A : OpenApiInst.Sig} {M : OpenApiInst.Model A} {N : Servers.Model Http.sig}
    (h : N.Refines M.server) :
    ∀ φ : OpenApiInst.Sen A, φ.Pos → OpenApiInst.Sat M φ → OpenApiInst.Sat { M with server := N } φ
  | .respOk _, _, hM => Servers.Model.sat_of_refines h hM
  | .closed _, _, hM => Servers.Model.sat_of_refines h hM
  | .rejects _ _, _, hM => Servers.Model.sat_of_refines h hM
  | .conj φ ψ, ⟨hφ, hψ⟩, ⟨h1, h2⟩ => ⟨sat_of_refines h φ hφ h1, sat_of_refines h ψ hψ h2⟩

end Silmaril.Proofs.Servers.OpenApiInst
