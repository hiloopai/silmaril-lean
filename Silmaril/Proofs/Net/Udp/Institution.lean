module

public import Silmaril.Net.Udp.Institution.Defs
public import Silmaril.Net.Udp.Network.Thms

/-! Proofs for `Silmaril.Net.Udp.Institution.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Udp.Proofs.Institution

open CategoryTheory Silmaril.Net.Channel Silmaril.Net.Udp Silmaril.Net.Udp.Network
open Silmaril.Net.Ip
open Silmaril.Net.Udp.Inst

theorem sat_map_iff {A B : Sig} (σ : A ⟶ B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ := by
  induction φ with
  | neg φ ih => simp only [Sen.map, Sat, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Sen.map, Sat, ih₁, ih₂]
  | _ => rfl

theorem map_id {A : Sig} (φ : Sen A) : φ.map (𝟙 A) = φ := by
  induction φ with
  | neg φ ih => simp only [Sen.map, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Sen.map, ih₁, ih₂]
  | _ => rfl

theorem map_comp {A B C : Sig} (σ : A ⟶ B) (τ : B ⟶ C) (φ : Sen A) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ := by
  induction φ with
  | neg φ ih => simp only [Sen.map, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Sen.map, ih₁, ih₂]
  | _ => rfl

/-! ## The network model: what it satisfies -/

theorem net_sendsWF {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) : Sat (Model.net C ep kind) .sendsWF := by
  intro t ht m hm
  exact (traces_local ht _ hm).1

theorem net_addressed {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) : Sat (Model.net C ep kind) (.addressed e) := by
  intro t ht m hm
  exact (traces_local ht _ hm).1.symm

theorem net_hostCore {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) : SatAll (Model.net C ep kind) (hostCore e) := by
  intro φ hφ
  simp only [hostCore, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl
  · exact net_sendsWF C ep kind
  · exact net_addressed C ep kind e

theorem okFrom_recv_mem (a : Endpoint) (m : Msg) (post : List Obs) :
    ∀ (pre : List Obs) (seen : List Msg), okFrom seen (toChan (pre ++ Obs.recv a m :: post)) →
      m ∈ seen ∨ m ∈ sentMsgs pre := by
  intro pre
  induction pre with
  | nil =>
    intro seen h
    exact Or.inl h.1
  | cons o pre ih =>
    intro seen h
    cases o with
    | send x =>
      rcases ih (x :: seen) h with h' | h'
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    | recv b x => exact ih seen h.2
    | sendErr x e => exact ih seen h
    | err b e => exact ih seen h

theorem net_authentic {A : Sig} {C : Config} (hC : C.offPath = false) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) : Sat (Model.net C ep kind) (.authentic e) := by
  intro t ht pre m post rfl
  have h := ((traces_iff hC _).mp ht).2
  rcases okFrom_recv_mem _ m post pre [] h with h' | h'
  · cases h'
  · exact h'

/-! ## The network model: what it violates -/

theorem src_mk' (a b : Endpoint) (d : List UInt8) : (Msg.mk' a b d).src = a := by cases a; rfl
theorem dst_mk' (a b : Endpoint) (d : List UInt8) : (Msg.mk' a b d).dst = b := by cases b; rfl
theorem data_mk' (a b : Endpoint) (d : List UInt8) : (Msg.mk' a b d).data = d := rfl

theorem wf_mk' (a : Endpoint) (d : List UInt8) (h : 8 + d.length < 65536) :
    (Msg.mk' a a d).WF := ⟨rfl, h⟩

theorem net_not_authentic {A : Sig} {C : Config} (hC : C.offPath = true) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (hb : C.bound (ep e) = true) :
    ¬ Sat (Model.net C ep kind) (.authentic e) := by
  intro h
  let m := Msg.mk' (ep e) (ep e) []
  have ht : [Obs.recv (ep e) m] ∈ traces C := by
    refine (traces_offPath_iff hC _).mpr ?_
    simp only [List.mem_singleton, forall_eq]
    exact ⟨(dst_mk' _ _ _).symm, hb, wf_mk' _ _ (by decide)⟩
  have := h _ ht [] m [] rfl
  cases this

theorem net_not_noDup {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (hb : C.bound (ep e) = true) :
    ¬ Sat (Model.net C ep kind) (.noDup e) := by
  intro h
  let a := ep e
  let m := Msg.mk' a a []
  have hl : Local C (.send m) := ⟨wf_mk' _ _ (by decide), by rw [src_mk']; exact hb⟩
  have hr : Local C (.recv a m) := ⟨(dst_mk' _ _ _).symm, hb, wf_mk' _ _ (by decide)⟩
  have ht : [Obs.send m, Obs.recv a m, Obs.recv a m] ∈ traces C := by
    refine mem_traces_of_spec ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro o (rfl | rfl | rfl) <;> assumption
    · show okFrom [] [.send m, .recv m, .recv m]
      simp [okFrom]
  have := h _ ht _ (List.prefix_refl _) m
  simp [recvAt, sentMsgs, Model.net, a] at this

theorem net_not_fifo {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (hb : C.bound (ep e) = true) :
    ¬ Sat (Model.net C ep kind) (.fifo e e) := by
  intro h
  let a := ep e
  let m₁ := Msg.mk' a a []
  let m₂ := Msg.mk' a a [0]
  have hs₁ : Local C (.send m₁) := ⟨wf_mk' _ _ (by decide), by rw [src_mk']; exact hb⟩
  have hs₂ : Local C (.send m₂) := ⟨wf_mk' _ _ (by decide), by rw [src_mk']; exact hb⟩
  have hr₁ : Local C (.recv a m₁) := ⟨(dst_mk' _ _ _).symm, hb, wf_mk' _ _ (by decide)⟩
  have hr₂ : Local C (.recv a m₂) := ⟨(dst_mk' _ _ _).symm, hb, wf_mk' _ _ (by decide)⟩
  have ht : [Obs.send m₁, Obs.send m₂, Obs.recv a m₂, Obs.recv a m₁] ∈ traces C := by
    refine mem_traces_of_spec ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro o (rfl | rfl | rfl | rfl) <;> assumption
    · show okFrom [] [.send m₁, .send m₂, .recv m₂, .recv m₁]
      simp [okFrom]
  have hne : m₁ ≠ m₂ := by
    intro heq
    have := congrArg Msg.data heq
    simp [m₁, m₂, data_mk'] at this
  have := h _ ht
  simp only [Model.net, FifoLink, List.filterMap_cons, List.filterMap_nil, Obs.link, src_mk', dst_mk',
    and_self, ↓reduceIte, a, m₁, m₂] at this
  simp [Fifo, fifoFrom] at this
  exact hne this.1

theorem net_not_onlyKind {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (k : A.Kind) (hb : C.bound (ep e) = true)
    (bs : List UInt8) (hbs : 8 + bs.length < 65536) (hk : kind k bs = false) :
    ¬ Sat (Model.net C ep kind) (.onlyKind e k) := by
  intro h
  let a := ep e
  let m := Msg.mk' a a bs
  have hl : Local C (.send m) := ⟨wf_mk' _ _ hbs, by rw [src_mk']; exact hb⟩
  have hr : Local C (.recv a m) := ⟨(dst_mk' _ _ _).symm, hb, wf_mk' _ _ hbs⟩
  have ht : [Obs.send m, Obs.recv a m] ∈ traces C := by
    refine mem_traces_of_spec ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro o (rfl | rfl) <;> assumption
    · show okFrom [] [.send m, .recv m]
      simp [okFrom]
  have := h _ ht m (by simp [Model.net, a])
  simp only [Model.net, data_mk', m] at this
  rw [hk] at this
  cases this

end Silmaril.Net.Udp.Proofs.Institution
