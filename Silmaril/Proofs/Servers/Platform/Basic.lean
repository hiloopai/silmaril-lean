module

public import Silmaril.Servers.Platform.Defs
import Silmaril.Servers.Reuse.Thms
import Silmaril.Servers.Cgi.Thms

/-!
# Platforms: proofs

For `Silmaril.Servers.Platform.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Platform

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers Silmaril.Servers.Reuse Silmaril.Servers.Platform

variable {σ : Type}

theorem seq_iff_forall (O : Origin σ) (H : Request → Response → Prop)
    (h₁ : ∀ s r resp s', O s r resp s' → H r resp)
    (h₂ : ∀ s r resp, H r resp → ∃ s', O s r resp s') :
    ∀ (s : σ) (l : Log), Seq O s l ↔ ∀ p ∈ l, H p.1 p.2 := by
  intro s l
  induction l generalizing s with
  | nil => exact ⟨fun _ => by simp, fun _ => .nil _⟩
  | cons p l ih =>
    obtain ⟨r, resp⟩ := p
    constructor
    · rintro (_ | ⟨hs, hl⟩)
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h₁ _ _ _ _ hs
      · exact (ih _).mp hl q hq
    · intro h
      obtain ⟨s', hs⟩ := h₂ s r resp (h (r, resp) List.mem_cons_self)
      exact .cons hs ((ih s').mpr fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem web_seq_iff (W : Origin.Web) (l : Log) :
    Seq (Origin.ofTargets W) () l ↔ ∀ p ∈ l, p.2 = Origin.webAnswer W p.1 :=
  seq_iff_forall _ (fun r resp => resp = Origin.webAnswer W r)
    (fun _ _ _ _ h => (Prod.mk.inj h).1.symm) (fun _ _ _ h => ⟨(), by rw [h]⟩) () l

theorem web_host_iff (W : Origin.Web) (l : Log) :
    HostRuns (Origin.ofTargets W) () l ↔ ∀ p ∈ l, p.2 = Origin.webAnswer W p.1 :=
  ⟨hostRuns_of_forall (fun r resp => resp = Origin.webAnswer W r)
      (fun _ _ _ _ h => (Prod.mk.inj h).1.symm),
    fun h => seq_hostRuns ((web_seq_iff W l).mpr h)⟩

theorem cgi_hello_iff (g : Cgi.Gateway) (fs : Fs) (l : Log) :
    Seq (Cgi.origin g Cgi.hello) fs l ↔
      ∀ p ∈ l, p.2 = Origin.webAnswer (fun _ => Cgi.helloResponse) p.1 :=
  seq_iff_forall (Cgi.origin g Cgi.hello)
    (fun r resp => resp = Origin.webAnswer (fun _ => Cgi.helloResponse) r)
    (fun s r resp s' h => ((Cgi.hello_origin_iff g s r resp s').mp h).1)
    (fun s r resp h => ⟨s, (Cgi.hello_origin_iff g s r resp s).mpr ⟨h, rfl⟩⟩) fs l

theorem interleave_nil_right {α : Type} : ∀ l : List α, Interleave l [] l
  | [] => .nil
  | _ :: l => .left (interleave_nil_right l)

end Silmaril.Proofs.Servers.Platform
