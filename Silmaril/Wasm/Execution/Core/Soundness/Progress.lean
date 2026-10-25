module

public import Silmaril.Wasm.Execution.Core.Soundness.Parametric
public import Silmaril.Wasm.Execution.Core.Soundness.Numeric
public import Silmaril.Wasm.Execution.Core.Soundness.Vector
public import Silmaril.Wasm.Execution.Core.Soundness.Table
public import Silmaril.Wasm.Execution.Core.Soundness.Memory
public import Silmaril.Wasm.Execution.Core.Soundness.Reference
public import Silmaril.Wasm.Execution.Core.Soundness.Aggregate
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressControl

@[expose] public section

/-! # Progress for Core 3.0

A typed configuration is terminal or steps. Decompose the code into values, a
redex and a rest; the family instructions use `<Family>InstrOk.progress`
(`Soundness/<Family>.lean`); control, calls, exceptions, variables and
administrative forms are handled here.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Progress. -/
theorem Config.progress {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) :
    c.Terminal ∨ ∃ c', Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := hc
  obtain ⟨hL, hR, -⟩ := FrameOk.ctx_fields hf
  have h := progress_aux (P := P) hhost hs hcode f [] (CtxOk.ofFrame₀ hf) .nil
  simp only [vals, List.map_nil, List.nil_append, hL, hR] at h
  rcases h with ⟨vs, rfl, -⟩ | ⟨c', hc'⟩ | ⟨vs, rest, rfl⟩ | ⟨vs, a, rest, rfl⟩ |
    ⟨vs, l, rest, tl, -, h1, -⟩ | ⟨vs, rest, rt, -, h1, -⟩ |
    ⟨vs, r, c, rest, rt, -, -, h1, -⟩
  · exact .inl ⟨.values vs, rfl⟩
  · exact .inr ⟨c', hc'⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := f) vs rest with
      ⟨rfl, rfl⟩ | hst
    · exact .inl ⟨.trap, rfl⟩
    · exact .inr hst
  · rcases throw_or_step (P := P) (host := host) (s := s) (f := f) vs a rest with
      ⟨rfl, rfl⟩ | hst
    · exact .inl ⟨.throw a, rfl⟩
    · exact .inr hst
  · simp at h1
  · simp at h1
  · simp at h1

end Silmaril.Wasm.Execution.Core
