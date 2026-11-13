module

public import Silmaril.Elf.Effects.Shapes.Defs
public import Silmaril.Elf.Effects.Thms

/-! Proofs for `Silmaril.Elf.Effects.Shapes`: the effect shapes from a checked certificate. -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Effects.Shapes

open Silmaril.Project (Value)
open Silmaril.X86 (Word)
open Silmaril.X86.Flow (FlowDec UMach)
open Silmaril.Elf.Shapes (file)
open Silmaril.Elf
open Silmaril.Elf.Effects
open Silmaril.Elf.Effects.Shapes

variable {σ V : Type}

theorem reach_sub {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert} {esc : List Nat} {v : Nat}
    {L : List Node} (h : CertOk D X loc P esc v L) {n : Node} (hn : P.reach v esc n) : n ∈ L :=
  reaches_mem h.closed (fun n hn => by
    have := h.roots; simp only [List.all_eq_true, List.contains_iff_mem] at this; exact this n hn) hn

/-- **The calls from the function stay in the certificate's graph.** -/
theorem reachIn {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert} {esc : List Nat}
    {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) {keep : σ → Prop} {W : World σ}
    {base : Word} {s₀ : σ} (hA : Admissible J D (file X) P esc W base v keep s₀) :
    ReachIn W D base keep s₀ (P.reach v esc) :=
  sound {
    law := by rw [hA.mach]; exact hA.law
    stable := h.stable
    check := h.check
    root := .root (List.mem_cons_self ..)
    escapes := fun e he => .root (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
    closed := fun e he hN => .edge hN he
    noUnres := fun hu => by
      have := reach_sub h hu
      have h2 := h.noUnres
      rw [List.contains_iff_mem.2 this] at h2; cases h2
    start := hA.start
    code := codeLoaded_of h.code hA.placement hA.stable
    image := hA.image
    kernel := hA.kernel
    lib := hA.lib
    ind := hA.ind
    ret := hA.ret }

theorem callGraphSub {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) :
    CallGraphSub J D X loc P esc := by
  intro w hw W base s₀ hA
  obtain rfl := h.at_ w hw
  exact reachIn h hA

/-- **Effects from the call graph**: every reachable node satisfies `ok`. -/
theorem syscalls {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {summ : Summ} {ok : Nat → Prop}
    (hG : CallGraphSub J D X loc P esc)
    (hN : ∀ v, Func.At ⟨file X, loc⟩ v → ∀ n, P.reach v esc n → n.SysOk summ ok) :
    ForFunc J D X loc P esc fun W base keep s₀ _ => SyscallsOk W D base keep s₀ summ ok :=
  fun v hv W base s₀ hA => syscalls_of_reach (hG v hv W base s₀ hA) (hN v hv)

theorem okOfList {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert} {esc : List Nat} {v : Nat}
    {L : List Node} (h : CertOk D X loc P esc v L) {summ : Summ} {ok : Nat → Bool}
    (hok : L.all (Node.okB summ ok) = true) :
    ∀ w, Func.At ⟨file X, loc⟩ w → ∀ n, P.reach w esc n → n.SysOk summ (fun k => ok k = true) := by
  intro w hw n hn
  obtain rfl := h.at_ w hw
  simp only [List.all_eq_true] at hok
  exact okB_sound (hok n (reach_sub h hn))

theorem foreignCalls {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) :
    ForeignCalls J D X loc P esc (importsOf L) := by
  intro w hw W base s₀ hA
  obtain rfl := h.at_ w hw
  exact foreign_of_reach (reachIn h hA) fun r hr => by
    simp only [importsOf, List.mem_filterMap]
    exact ⟨_, reach_sub h hr, rfl⟩

theorem syscallSet_of_imports {J : UMach σ} {D : FlowDec} {X : Value V} {loc : Loc} {P : Cert}
    {esc : List Nat} {v : Nat} {L : List Node} (h : CertOk D X loc P esc v L) {summ : Summ}
    {S : List Nat} (hnodes : L.all (directOk S) = true)
    (himp : ∀ r ∈ importsOf L, ∃ ns, summ.lookup r = some ns ∧ ∀ n ∈ ns, n ∈ S) :
    SyscallSet J D X loc P esc summ S := by
  refine syscalls (callGraphSub h) fun w hw n hn => ?_
  obtain rfl := h.at_ w hw
  have hm := reach_sub h hn
  simp only [List.all_eq_true] at hnodes
  have hd := hnodes n hm
  cases n with
  | fn => trivial
  | ext r => exact himp r (by simp only [importsOf, List.mem_filterMap]; exact ⟨_, hm, rfl⟩)
  | sys k => show k ∈ S; simpa [directOk] using hd
  | sysAny => simp [directOk] at hd
  | unresolved => simp [directOk] at hd

end Silmaril.Proofs.Elf.Effects.Shapes
