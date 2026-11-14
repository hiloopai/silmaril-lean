module

public import Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.Catalogue
public import Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.Paper
public import Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.Own
public import Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts.Loose

/-!
# Litmus verdicts: the whole corpus

The per-test checks collected over `Corpus.all`: every x86-TSO-covered test passes
`Test.checkTsoBytes`, and every loose corner passes `Test.checkXlLoose`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Litmus.Corpus

set_option maxRecDepth 100000

theorem all_tso : ∀ t ∈ Corpus.all, t.coverage = .tso → t.checkTsoBytes = true := by
  intro t ht hc
  simp only [Corpus.all, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact «check_SB»
  · exact «check_SB+mfence+po»
  · exact «check_SB+mfences»
  · exact «check_SB+rfi-pos»
  · exact «check_MP»
  · exact «check_MP+mfence+po»
  · exact «check_MP+po+mfence»
  · exact «check_MP+mfences»
  · exact «check_LB»
  · exact «check_LB+mfence+po»
  · exact «check_LB+mfences»
  · exact «check_R»
  · exact «check_R+mfence+po»
  · exact «check_R+po+mfence»
  · exact «check_R+mfences»
  · exact «check_R+mfence+rfi-po»
  · exact «check_S»
  · exact «check_S+mfence+po»
  · exact «check_S+po+mfence»
  · exact «check_S+mfences»
  · exact «check_2+2W»
  · exact «check_2+2W+mfence+po»
  · exact «check_2+2W+mfences»
  · exact «check_A011»
  · exact «check_A013»
  · exact «check_A014»
  · exact «check_iwp2.1/amd1»
  · exact «check_iwp2.2/amd2»
  · exact «check_iwp2.3.a/amd4»
  · exact «check_iwp2.3.b»
  · exact «check_iwp2.4/amd9»
  · exact «check_iwp2.5/amd8»
  · exact «check_amd3»
  · exact «check_iwp2.6»
  · exact «check_amd6»
  · exact «check_iwp2.7/amd7»
  · exact «check_iwp2.8.a»
  · exact «check_iwp2.8.b»
  · exact «check_n8»
  · exact «check_n3»
  · exact «check_amd10»
  · exact «check_amd5»
  · exact «check_n6»
  · exact «check_n5»
  · exact «check_n4»
  · exact «check_n7»
  · exact «check_n1»
  · exact «check_n2»
  · exact «check_rwc-unfenced»
  · exact «check_rwc-fenced»
  · exact «check_IRIW+mfences»
  · exact «check_SB+lock-adds»
  · exact «check_SB+lock-xadds»
  · exact «check_SB+lock-cmpxchgs»
  · exact «check_RMW+lock-xadds»
  · exact «check_RMW+lock-xadds-final»
  · exact «check_RMW+lock-cmpxchgs»
  · exact «check_RMW+xchgs»
  · exact «check_RMW+lock-inc+W»
  · exact «check_RMW+inc+W»
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)

theorem all_xl : ∀ t ∈ Corpus.all, t.coverage = .xl → t.checkXlLoose = true := by
  intro t ht hc
  simp only [Corpus.all, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact «check_MS+halves»
  · exact «check_MIS+straddle»
  · exact «check_MP+movnti»
  · exact «check_MP+movnti+sfence»
  · exact «check_MP+movnti+lock»
  · exact «check_MP+stosb»
  · exact «check_MP+stosb+sfence»
  · exact «check_STOS+internal»

end Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts
