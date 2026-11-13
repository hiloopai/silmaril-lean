module

public import Silmaril.Elf.Effects.Defs
import Silmaril.Elf.Link.ElfBind.Thms

/-! Proofs for `Silmaril.Elf.Effects`: the code is loaded (`codeLoaded_of`), reachability against
a listed node set, and effects read off reachable nodes. -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Effects

open Silmaril.X86 (Word)
open Silmaril.X86.Flow (FlowDec)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf
open Silmaril.Elf.Effects

variable {σ : Type}

/-- **The code is loaded**, from `CodeAt` rows, the placement and code stability. -/
theorem codeLoaded_of {W : World σ} {D : FlowDec} {F : Blob} {base : Word} {P : Cert}
    {keep : σ → Prop} {s₀ : σ}
    (hcode : ∀ f C, (f, C) ∈ P.fns → ∀ b ∈ C.blocks, Link.ElfBind.CodeAt F b.start b.bytes)
    (hp : Link.ElfBind.Placement F base) (hs : CodeStable W D F base keep s₀) :
    CodeLoaded W D base P keep s₀ := by
  intro es u hrun f C hfC b hb
  exact (Link.ElfBind.code_loaded (hcode f C hfC b hb) hp (hs es u hrun)).1

/-- Reachable nodes are in a listed set closed under the edges and holding the roots. -/
theorem reaches_mem {G : CallGraph} {roots L : List Node} (hc : G.closedB L = true)
    (hr : ∀ n ∈ roots, n ∈ L) {n : Node} (h : G.Reaches roots n) : n ∈ L := by
  induction h with
  | root h => exact hr _ h
  | edge _ he ih =>
    simp only [CallGraph.closedB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.contains_iff_mem] at hc
    rcases hc _ he with h | h
    · simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
      exact absurd ih (fun hm => h _ hm rfl)
    · exact h

/-- Reachability is monotone in the graph. -/
theorem reaches_mono {G H : CallGraph} (hle : G.Le H) {roots : List Node} {n : Node}
    (h : G.Reaches roots n) : H.Reaches roots n := by
  induction h with
  | root h => exact .root h
  | edge _ he ih => exact .edge ih (hle _ he)

/-- `ReachIn` is monotone in the node set. -/
theorem reach_mono {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N N' : Node → Prop} (h : ReachIn W D base keep s₀ N) (hle : ∀ n, N n → N' n) :
    ReachIn W D base keep s₀ N' := by
  intro es y hr e he n hn
  rcases h es y hr e he n hn with h | ⟨h1, h2⟩
  · exact Or.inl (hle _ h)
  · exact Or.inr ⟨h1, hle _ h2⟩

/-- **Effects from reachable nodes**: if every node of `N` makes only system calls satisfying
`ok`, so does every run. -/
theorem syscalls_of_reach {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N : Node → Prop} {summ : Summ} {ok : Nat → Prop} (h : ReachIn W D base keep s₀ N)
    (hN : ∀ n, N n → n.SysOk summ ok) : SyscallsOk W D base keep s₀ summ ok := by
  intro es y hr e he n hn
  rcases h es y hr e he n hn with h | ⟨_, h2⟩
  · exact hN _ h
  · exact absurd (hN _ h2) (by simp [Node.SysOk])

/-- **Imports from reachable nodes.** -/
theorem foreign_of_reach {W : World σ} {D : FlowDec} {base : Word} {keep : σ → Prop} {s₀ : σ}
    {N : Node → Prop} {I : Ref → Prop} (h : ReachIn W D base keep s₀ N)
    (hN : ∀ r, N (.ext r) → I r) : ForeignIn W D base keep s₀ I := by
  intro es y hr e he r hn
  rcases h es y hr e he _ hn with h | ⟨⟨_, h1⟩, _⟩
  · exact hN _ h
  · cases h1

theorem okB_sound {summ : Summ} {ok : Nat → Bool} {n : Node} (h : n.okB summ ok = true) :
    n.SysOk summ (fun k => ok k = true) := by
  cases n with
  | fn => trivial
  | ext r =>
    simp only [Node.okB] at h
    split at h
    · rename_i ns hl; exact ⟨ns, hl, by simpa [List.all_eq_true] using h⟩
    · cases h
  | sys k => exact h
  | sysAny => cases h
  | unresolved => cases h

theorem sysOk_mono {summ : Summ} {ok ok' : Nat → Prop} {n : Node} (h : n.SysOk summ ok)
    (hle : ∀ k, ok k → ok' k) : n.SysOk summ ok' := by
  cases n with
  | fn => trivial
  | ext r => obtain ⟨ns, hl, hns⟩ := h; exact ⟨ns, hl, fun k hk => hle _ (hns k hk)⟩
  | sys k => exact hle _ h
  | sysAny => exact h
  | unresolved => exact h

theorem fnOk_mono {D : FlowDec} {P P' : Cert} {a : Nat} {C : Silmaril.X86.Cfg.Graph Ref}
    (h : P.fnOk D a C = true) (he : P.graph.Le P'.graph) (hh : ∀ b, P.has b = true → P'.has b = true) :
    P'.fnOk D a C = true := by
  simp only [Cert.fnOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h ⊢
  refine ⟨h.1, fun e hm => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 e hm
  refine ⟨he _ h1, ?_⟩
  revert h2; cases e.2 <;> simp_all

theorem has_union {P Q : Cert} {b : Nat} : (P.union Q).has b = (P.has b || Q.has b) := by
  simp [Cert.has, Cert.union, List.any_append]

/-- **Composition**: two checked certificates give a checked union. -/
theorem check_union {D : FlowDec} {P Q : Cert} {r₁ r₂ : List Nat} (hP : P.check D r₁ = true)
    (hQ : Q.check D r₂ = true) : (P.union Q).check D (r₁ ++ r₂) = true := by
  simp only [Cert.check, Bool.and_eq_true, List.all_eq_true] at hP hQ ⊢
  have leP : P.graph.Le (P.union Q).graph := fun e he => List.mem_append_left _ he
  have leQ : Q.graph.Le (P.union Q).graph := fun e he => List.mem_append_right _ he
  refine ⟨fun x hx => ?_, fun b hb => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact fnOk_mono (hP.1 x hx) leP (fun b h => by rw [has_union, h]; rfl)
    · exact fnOk_mono (hQ.1 x hx) leQ (fun b h => by rw [has_union, h]; simp)
  · rw [has_union]
    rcases List.mem_append.1 hb with hb | hb
    · rw [hP.2 b hb]; rfl
    · rw [hQ.2 b hb]; simp

end Silmaril.Proofs.Elf.Effects
