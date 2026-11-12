module

public import Silmaril.Elf.Link.Dyn.Proc.Thms

/-! # The library's callback gate: one rule per job -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)

variable {W : World} {Q : PState → Prop} {s : PState}

theorem must_gate_call {f a1 a2 a3 : Word} {js : List Job} (hd : s.g.done = none)
    (hg : s.m.core.rip = W.gate) (hout : ¬ W.InImage W.gate.toNat)
    (hj : s.g.jobs = .call f a1 a2 a3 :: js)
    (h : ∀ t, Enters W s t f → t.m.core.read .rdi = a1 → t.m.core.read .rsi = a2 →
      t.m.core.read .rdx = a3 → t.g = { s.g with jobs := js } → MustQ W Q t) : MustQ W Q s :=
  must_contract (pre := True) (post := fun t => Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = { s.g with jobs := js }) hd (by rw [hg]; exact hout)
    (fun r => by rw [extStep_gate hg r]; unfold gateStep; rw [hj]) trivial
    (fun t ⟨h1, h2, h3, h4, h5⟩ => h t h1 h2 h3 h4 h5)

theorem must_gate_call0 {f : Word} {js : List Job} (hd : s.g.done = none)
    (hg : s.m.core.rip = W.gate) (hout : ¬ W.InImage W.gate.toNat) (hj : s.g.jobs = .call0 f :: js)
    (h : ∀ t, Enters W s t f → t.g = { s.g with jobs := js } → MustQ W Q t) : MustQ W Q s :=
  must_contract (pre := True) (post := fun t => Enters W s t f ∧ t.g = { s.g with jobs := js } ∧ W.atCall t ∧ W.atGate s t) hd (by rw [hg]; exact hout)
    (fun r => by rw [extStep_gate hg r]; unfold gateStep; rw [hj]) trivial
    (fun t ⟨h1, h2, _⟩ => h t h1 h2)

theorem must_gate_main {f argc argv envp : Word} {js : List Job} (hd : s.g.done = none)
    (hg : s.m.core.rip = W.gate) (hout : ¬ W.InImage W.gate.toNat)
    (hj : s.g.jobs = .main f argc argv envp :: js)
    (h : ∀ t, Enters W s t f → t.m.core.read .rdi = argc → t.m.core.read .rsi = argv →
      t.m.core.read .rdx = envp → t.g = { s.g with jobs := .exitRax :: js } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract (pre := True) (post := fun t => Enters W s t f ∧ t.m.core.read .rdi = argc ∧ t.m.core.read .rsi = argv ∧
      t.m.core.read .rdx = envp ∧ t.g = { s.g with jobs := .exitRax :: js } ∧ W.atMain t) hd (by rw [hg]; exact hout)
    (fun r => by rw [extStep_gate hg r]; unfold gateStep; rw [hj]) trivial
    (fun t ⟨h1, h2, h3, h4, h5, _⟩ => h t h1 h2 h3 h4 h5)

theorem must_gate_exitRax {js : List Job} (hd : s.g.done = none)
    (hg : s.m.core.rip = W.gate) (hout : ¬ W.InImage W.gate.toNat) (hj : s.g.jobs = .exitRax :: js)
    (h : ∀ t, AtGate W s t →
      t.g = { s.g with jobs := [.exit ((low32 (s.m.core.read .rax)).setWidth 64)] } → MustQ W Q t)
    (hpend : ∀ s p, W.pending s p → p = [] := by intro _ _ h; exact h) :
    MustQ W Q s :=
  gate_exitRax hd (by rw [hg]; exact hout) hg hj h hpend

theorem must_gate_exit {st : Word} {js : List Job} (hd : s.g.done = none)
    (hg : s.m.core.rip = W.gate) (hout : ¬ W.InImage W.gate.toNat) (hj : s.g.jobs = .exit st :: js)
    (h : ∀ t, AtGate W s t → t.g = { s.g with jobs := exitJobs W s.g st, atexit := [] } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract (pre := True) (post := fun t => AtGate W s t ∧ t.g = { s.g with jobs := exitJobs W s.g st, atexit := [] } ∧
      W.atGate s t) hd (by rw [hg]; exact hout)
    (fun r => by rw [extStep_gate hg r]; unfold gateStep; rw [hj]) trivial
    (fun t ⟨h1, h2, _⟩ => h t h1 h2)

theorem must_gate_halt {st : Word} {js : List Job} (hd : s.g.done = none)
    (hg : s.m.core.rip = W.gate) (hout : ¬ W.InImage W.gate.toNat) (hj : s.g.jobs = .halt st :: js)
    (h : ∀ t (w : List Byte), w <+: s.g.out → (W.reliable = true → w = s.g.out) →
      t.g = { s.g with jobs := [], done := some (st.toNat % 256, w) } → MustQ W Q t) :
    MustQ W Q s :=
  must_contract (pre := True) (post := fun t => ∃ w, w <+: s.g.out ∧ (W.reliable = true → w = s.g.out) ∧
      t.g = { s.g with jobs := [], done := some (st.toNat % 256, w) }) hd (by rw [hg]; exact hout)
    (fun r => by rw [extStep_gate hg r]; unfold gateStep; rw [hj]) trivial
    (fun t ⟨w, h1, h2, h3⟩ => h t w h1 h2 h3)

end Silmaril.Elf.Link.Dyn.Proc
