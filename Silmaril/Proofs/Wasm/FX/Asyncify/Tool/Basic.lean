module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Sim

/-!
# Machine lemmas: straight-line segments, `if`, steps of the closed systems
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-! ## Steps -/

theorem Steps.trans {E : Env} {m n : Nat} {a b c : Cfg} (h1 : Steps E m a b) (h2 : Steps E n b c) :
    Steps E (m + n) a c := by
  induction h1 with
  | refl => simpa using h2
  | cons hs _ ih => rw [Nat.add_right_comm]; exact .cons hs (ih h2)

theorem Steps.one {E : Env} {a b : Cfg} (h : step E a = .next b) : Steps E 1 a b := .cons h (.refl b)

theorem Steps.tgt {σ : Type} {E : Env} {H : Host σ} {n : Nat} {a b : Cfg} (h : Steps E n a b)
    (s : σ) (e : Nat) (as : List W) :
    runN (tgtStep E H) n ⟨a, s, e, as⟩ = .next ⟨b, s, e, as⟩ := by
  induction h with
  | refl => rfl
  | cons hs _ ih => simp only [runN, tgtStep, hs]; exact ih

theorem Steps.src {σ : Type} {E : Env} {H : Host σ} {n : Nat} {a b : Cfg} (h : Steps E n a b)
    (s : σ) : runN (srcStep E H) n (a, s) = .next (b, s) := by
  induction h with
  | refl => rfl
  | cons hs _ ih => simp only [runN, srcStep, hs]; exact ih

/-! ## Straight-line segments -/

/-- A straight-line segment. -/
def runSeg : List Instr → LS → Option LS
  | [], s => some s
  | i :: is, s => (segStep i s).bind (runSeg is)

/-- The configuration with top frame `fr` in state `s` and code `code`. -/
def cfgOf (fr : Frame) (rest : List Frame) (s : LS) (code : List Instr) : Cfg :=
  ⟨{ fr with locals := s.locals, ops := s.ops, code := code } :: rest, s.globals, s.mem⟩

theorem exec_seg {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {s' : LS} {i : Instr}
    {code : List Instr} (h : segStep i (fr.ls c) = some s') :
    exec E c fr i code rest =
      .next ⟨{ fr with locals := s'.locals, ops := s'.ops, code := code } :: rest, s'.globals,
        s'.mem⟩ := by
  unfold segStep at h
  unfold exec
  cases hc : ctlOf i with
  | some k => rw [hc] at h; cases h
  | none => rw [hc] at h; simp only [h]

theorem step_seg {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {s' : LS} {i : Instr}
    {code : List Instr} (hf : c.frames = fr :: rest) (hcode : fr.code = i :: code)
    (h : segStep i (fr.ls c) = some s') :
    step E c = .next ⟨{ fr with locals := s'.locals, ops := s'.ops, code := code } :: rest,
        s'.globals, s'.mem⟩ := by
  simp only [step, hf, hcode]
  exact exec_seg h

/-- Segments run as machine steps. -/
theorem steps_seg {E : Env} : ∀ {is : List Instr} {fr : Frame} {rest : List Frame} {code : List Instr}
    {g : List W} {m : Nat → W} {s' : LS},
    runSeg is ⟨fr.locals, fr.ops, g, m⟩ = some s' →
    Steps E is.length ⟨{ fr with code := is ++ code } :: rest, g, m⟩
      ⟨{ fr with locals := s'.locals, ops := s'.ops, code := code } :: rest, s'.globals, s'.mem⟩
  | [], fr, rest, code, g, m, s', h => by
    simp only [runSeg, Option.some.injEq] at h
    subst h
    exact .refl _
  | i :: is, fr, rest, code, g, m, s', h => by
    simp only [runSeg, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    have hs := step_seg (E := E) (c := ⟨{ fr with code := (i :: is) ++ code } :: rest, g, m⟩)
      (fr := { fr with code := (i :: is) ++ code }) (rest := rest) (s' := s1) (i := i)
      (code := is ++ code) rfl rfl h1
    have ih := steps_seg (E := E) (is := is) (fr := { fr with locals := s1.locals, ops := s1.ops })
      (rest := rest) (code := code) (g := s1.globals) (m := s1.mem) (s' := s') h2
    simp only [List.length_cons]
    exact .cons hs ih

theorem step_if {E : Env} {c : Cfg} {fr : Frame} {rest : List Frame} {t e code : List Instr}
    {x : W} {ops : List W} (hf : c.frames = fr :: rest)
    (hcode : fr.code = .if_ .empty t e :: code) (hops : fr.ops = x :: ops) :
    step E c = .next ⟨{ fr with ops := ops, code := (if x = 0 then e else t) ++ code } :: rest,
      c.globals, c.mem⟩ := by
  simp [step, hf, hcode, exec, ctlOf, hops, Cfg.setTop]

end Silmaril.Wasm.FX.Asyncify.Tool
