module

public import Silmaril.Wasm.Binaryen.MergeBackSimulation
public import Silmaril.Wasm.Binaryen.MergeBackTransport
public import Silmaril.Wasm.Binaryen.MergeChecked

@[expose] public section

/-! # Exact N-ary merge equivalence at every numerical profile

The concrete chosen-target backward simulation supplies finite-run and
divergence transport. It removes the numerical-determinism premise while
retaining the existing namespace, import-resolution and GC fragment checks.
Arguments are unrestricted; no invocation-typing premise is introduced.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics Link.GC

variable {H : Type}

namespace MergeUntyped

theorem bwd_step {P : Profile} {mode : AdminRelation.Mode} {S T T' : Config H}
    (h : Step P Simulation.noHost T T') (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    ∃ S', Step P Simulation.noHost S S' ∧ Simulation.Matching mode S' T' ∧
      XAs S'.frame.module S'.code ∧ StoreSc S'.store :=
  bwd_step_of back_matching h hm hsc hs

theorem bwd_steps {P : Profile} {mode : AdminRelation.Mode} {S T T' : Config H}
    (h : Steps P Simulation.noHost T T') (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    ∃ S', Steps P Simulation.noHost S S' ∧ Simulation.Matching mode S' T' ∧
      XAs S'.frame.module S'.code ∧ StoreSc S'.store :=
  bwd_steps_of back_matching h hm hsc hs

theorem bwd_diverges {P : Profile} {mode : AdminRelation.Mode} {S T : Config H}
    (hm : Simulation.Matching mode S T) (hsc : XAs S.frame.module S.code)
    (hs : StoreSc S.store) (hd : Diverges P Simulation.noHost T) :
    Diverges P Simulation.noHost S :=
  bwd_diverges_of back_matching hm hsc hs hd

theorem matching_behavioursOf_profile {P : Profile} {mode : AdminRelation.Mode}
    {S T : Config H} (hm : Simulation.Matching mode S T)
    (hsc : XAs S.frame.module S.code) (hs : StoreSc S.store) :
    behavioursOf P Simulation.noHost T = behavioursOf P Simulation.noHost S :=
  matching_behavioursOf_of_back_matching back_matching hm hsc hs

/-- Every argument list has the same results and divergence at the same
arbitrary numerical profile. Only stored-body scope is required. -/
theorem related_behaviours_profile {P : Profile} {s t : Store H}
    (rel : StoreRelation.Related s t) (hs : StoreSc s) (a : Nat) (vs : List Val) :
    Execution.Core.behaviours P Simulation.noHost t a vs = Execution.Core.behaviours P Simulation.noHost s a vs :=
  related_behaviours_of_back_matching back_matching rel hs a vs

end MergeUntyped

namespace MergeChain

theorem Link.behaviours_profile {P : Profile} {s t : Store H} (h : Link s t)
    (a : Nat) (vs : List Val) :
    Execution.Core.behaviours P Simulation.noHost t a vs = Execution.Core.behaviours P Simulation.noHost s a vs := by
  cases h with
  | related h ok => exact MergeUntyped.related_behaviours_profile h (MergeUntyped.storeSc_of_ok ok) a vs
  | renamed h _ _ => exact MergeUntyped.renamed_behaviours h a vs

theorem Chain.behaviours_profile {P : Profile} {s u : Store H} (h : Chain s u)
    (a : Nat) (vs : List Val) :
    Execution.Core.behaviours P Simulation.noHost u a vs = Execution.Core.behaviours P Simulation.noHost s a vs := by
  induction h with
  | refl => rfl
  | cons hl _ ih => rw [ih, hl.behaviours_profile]

end MergeChain

/-- N-ary merge preserves exact separate-instantiation behavior sets under the
same arbitrary numerical profile and the closed host. The existing linker's
syntactic fragment and graph-resolution conditions remain in force. -/
theorem merge_sound_profile {prog : List (String × Module)} {r : Module}
    (h : merge? (prog.map Prod.snd) = some r) (hback : ImportsBackward prog)
    (hres : ImportsResolve prog) (hprof : ∀ p ∈ prog, inProfile p.2 = true)
    (hnames : (prog.map Prod.fst).Nodup) (P : Profile)
    {n x : String} {vs : List Val}
    (hx : ∃ p ∈ prog, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    Program.beh P (SingleThreaded.Det.noHost (H := H)) prog n x vs =
      (moduleEntryPoints P (SingleThreaded.Det.noHost (H := H)) closedEnv).beh r x vs := by
  have hne : prog ≠ [] := by
    rintro rfl
    obtain ⟨p, hp, -⟩ := hx
    simp at hp
  have hpre := MergeProof.prefix_sound (H := H) (P := P) hback hres hprof
    hnames prog.reverse (by simpa using hne) (rest := []) (by simp) (by simpa using h)
  rw [List.reverse_reverse] at hpre
  obtain ⟨hprofR, hA, hB⟩ := hpre
  ext b
  simp only [Program.beh, moduleEntryPoints, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, insts, mi, a, hsep, hlook, hexp, hb⟩
    obtain ⟨sA, miA, -, hready, hchain, hinv⟩ := hA hsep
    refine ⟨{}, [], sA, miA, a, by unfold closedEnv; exact ⟨rfl, rfl⟩, hready, ?_, ?_⟩
    · rw [← hexp]
      exact ((MergeProof.export_agree hinv hnames hx).2 mi hlook).symm
    · rw [MergeChain.Chain.behaviours_profile hchain]
      exact hb
  · rintro ⟨s0, xas, s', mi, a, ⟨rfl, rfl⟩, hready, hexp, hb⟩
    have hprep := MergeChain.prepare_of_ready (as := []) hprofR hready
    obtain ⟨s, insts, hsep⟩ := hB (MergeChain.moduleOk_of_ready hready) hprep
    obtain ⟨sA, miA, hprepA, -, hchain, hinv⟩ := hA hsep
    obtain ⟨rfl, rfl⟩ := MergeProof.prep_inj (hprep.symm.trans hprepA)
    obtain ⟨mi_n, hlook⟩ := (MergeProof.export_agree hinv hnames hx).1
    refine ⟨s, insts, mi_n, a, hsep, hlook, ?_, ?_⟩
    · rw [(MergeProof.export_agree hinv hnames hx).2 mi_n hlook]
      exact hexp
    · rw [← MergeChain.Chain.behaviours_profile hchain]
      exact hb

/-- The actual executable checker supplies every condition for exact equality
at all semantic profiles; its fragment and validation guards are retained. -/
theorem checkedMerge?_sound_profile {prog : List (String × Module)} {result : Module}
    (h : checkedMerge? prog = some result) (P : Profile)
    {n x : String} {vs : List Val}
    (hx : ∃ p ∈ prog, p.1 = n ∧ ∃ e ∈ p.2.exports, e.name = x) :
    Program.beh P (SingleThreaded.Det.noHost (H := H)) prog n x vs =
      (moduleEntryPoints P (SingleThreaded.Det.noHost (H := H)) closedEnv).beh result x vs := by
  obtain ⟨hm, hb, hr, hp, -, hn, -⟩ := checkedMerge?_conditions h
  exact merge_sound_profile hm hb hr hp hn P hx

end Silmaril.Wasm.Binaryen
