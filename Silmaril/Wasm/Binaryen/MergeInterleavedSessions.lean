module

public import Silmaril.Wasm.Binaryen.MergeSessions

@[expose] public section

/-! # Persistent merge sessions across source namespaces

Each request chooses its original source namespace and export. All requests
share the store produced by separate initialization, including stores left by
earlier calls to other namespaces. The merged instance runs the script with
only the namespace labels erased. Initialization must succeed on both sides;
external host contexts and the existing checked merge feature boundary remain
unchanged.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Link.GC

variable {H : Type}

/-- One request names a source namespace, export and argument list. -/
abbrev NamedCall := String × Call

def Program.exportFunc? (insts : List (String × ModuleInst)) (n x : String) : Option Nat := do
  let mi ← insts.lookup n
  _root_.Silmaril.Wasm.Binaryen.exportFunc? mi x

/-- Stateful requests may switch namespace at every call. As for `Session`,
an invalid request stops, divergence ends the session, and completed calls
retain their actual final stores for the remaining requests. -/
inductive ProgramSession (P : Profile) (host : HostSemantics H)
    (insts : List (String × ModuleInst)) :
    Store H → List NamedCall → List (Behaviour Val) → Prop where
  | nil {s : Store H} : ProgramSession P host insts s [] []
  | stop {s : Store H} {n x : String} {vs : List Val} {rest : List NamedCall}
      (invalid : ∀ a, Program.exportFunc? insts n x = some a → ¬ InvokeOk s a vs) :
      ProgramSession P host insts s ((n, x, vs) :: rest) []
  | done {s : Store H} {n x : String} {vs : List Val} {rest : List NamedCall} {a : Nat}
      {c : Config H} {r : Result} {bs : List (Behaviour Val)}
      (lookup : Program.exportFunc? insts n x = some a) (ok : InvokeOk s a vs)
      (run : Steps P host (invoke s a vs) c) (result : c.code = r.toAdmin)
      (tail : ProgramSession P host insts c.store rest bs) :
      ProgramSession P host insts s ((n, x, vs) :: rest) (r.toBehaviour :: bs)
  | diverge {s : Store H} {n x : String} {vs : List Val} {rest : List NamedCall} {a : Nat}
      (lookup : Program.exportFunc? insts n x = some a) (ok : InvokeOk s a vs)
      (diverges : Diverges P host (invoke s a vs)) :
      ProgramSession P host insts s ((n, x, vs) :: rest) [.diverges]

namespace MergeChain

theorem SessionChain.programSession_forward {P : Profile}
    {insts : List (String × ModuleInst)} {target : ModuleInst}
    {s : Store H} {script : List NamedCall} {bs : List (Behaviour Val)}
    (session : ProgramSession P Simulation.noHost insts s script bs) :
    ∀ {t : Store H}, SessionChain s t →
      (∀ call ∈ script, Program.exportFunc? insts call.1 call.2.1 =
        exportFunc? target call.2.1) →
      Session P Simulation.noHost target t (script.map Prod.snd) bs := by
  induction session with
  | nil => exact fun _ _ => .nil
  | @stop s n x vs rest invalid =>
    intro t chain exports
    apply Session.stop
    intro a lookup ok
    apply invalid a
    · rw [exports (n, x, vs) (by simp)]
      exact lookup
    · exact (chain.invokeOk_iff a vs).mpr ok
  | @done s n x vs rest a c r bs lookup ok run result _ ih =>
    intro t chain exports
    obtain ⟨d, run', result', chain'⟩ := chain.invoke_result_forward run result
    exact .done (by rw [← exports (n, x, vs) (by simp)]; exact lookup)
      ((chain.invokeOk_iff a vs).mp ok) run' result'
      (ih chain' (fun call mem => exports call (List.mem_cons_of_mem _ mem)))
  | @diverge s n x vs rest a lookup ok diverges =>
    intro t chain exports
    have targetDiverges : Behaviour.diverges ∈ behaviours P Simulation.noHost t a vs := by
      rw [chain.behaviours_profile]
      exact .inr ⟨rfl, diverges⟩
    rcases targetDiverges with ⟨_, r, _, _, impossible⟩ | ⟨_, diverges'⟩
    · exact (Result.toBehaviour_ne_diverges r impossible.symm).elim
    · exact .diverge (by rw [← exports (n, x, vs) (by simp)]; exact lookup)
        ((chain.invokeOk_iff a vs).mp ok) diverges'

theorem SessionChain.programSession_backward {P : Profile}
    {insts : List (String × ModuleInst)} {target : ModuleInst}
    {script : List NamedCall} :
    ∀ {s t : Store H} {bs : List (Behaviour Val)},
      Session P Simulation.noHost target t (script.map Prod.snd) bs → SessionChain s t →
      (∀ call ∈ script, Program.exportFunc? insts call.1 call.2.1 =
        exportFunc? target call.2.1) →
      ProgramSession P Simulation.noHost insts s script bs := by
  induction script with
  | nil =>
    intro s t bs session _ _
    cases session
    exact .nil
  | cons request rest ih =>
    obtain ⟨n, x, vs⟩ := request
    intro s t bs session chain exports
    cases session with
    | stop invalid =>
      apply ProgramSession.stop
      intro a lookup ok
      apply invalid a
      · rw [← exports (n, x, vs) (by simp)]
        exact lookup
      · exact (chain.invokeOk_iff a vs).mp ok
    | done lookup ok run result tail =>
      obtain ⟨c, run', result', chain'⟩ := chain.invoke_result_backward run result
      exact .done (by rw [exports (n, x, vs) (by simp)]; exact lookup)
        ((chain.invokeOk_iff _ vs).mpr ok) run' result'
        (ih tail chain' (fun call mem => exports call (List.mem_cons_of_mem _ mem)))
    | @diverge _ _ _ _ a lookup ok diverges =>
      have sourceDiverges : Behaviour.diverges ∈ behaviours P Simulation.noHost s a vs := by
        rw [← chain.behaviours_profile]
        exact .inr ⟨rfl, diverges⟩
      rcases sourceDiverges with ⟨_, r, _, _, impossible⟩ | ⟨_, diverges'⟩
      · exact (Result.toBehaviour_ne_diverges r impossible.symm).elim
      · exact .diverge (by rw [exports (n, x, vs) (by simp)]; exact lookup)
          ((chain.invokeOk_iff _ vs).mpr ok) diverges'

/-- Exact observations of an interleaved script, retaining the store relation
after every completed call and without a numerical-determinism assumption. -/
theorem Chain.programSession_iff_profile {P : Profile} {s t : Store H}
    {insts : List (String × ModuleInst)} {target : ModuleInst} (chain : Chain s t)
    {script : List NamedCall} {bs : List (Behaviour Val)}
    (exports : ∀ call ∈ script, Program.exportFunc? insts call.1 call.2.1 =
      exportFunc? target call.2.1) :
    Session P Simulation.noHost target t (script.map Prod.snd) bs ↔
      ProgramSession P Simulation.noHost insts s script bs :=
  ⟨fun session => chain.sessionChain.programSession_backward session exports,
    fun session => chain.sessionChain.programSession_forward session exports⟩

end MergeChain

/-- Every request names an export declared by its own source namespace.
Arguments are unrestricted; an empty script has no artificial export premise. -/
def Program.NamedScriptExports (prog : List (String × Module)) (script : List NamedCall) : Prop :=
  ∀ call ∈ script, ∃ p ∈ prog, p.1 = call.1 ∧ ∃ e ∈ p.2.exports, e.name = call.2.1

/-- Separately initialize the source modules once, then interleave requests
against their instances in the actual shared final store. -/
def Program.interleavedSessionBeh (P : Profile) (host : HostSemantics H)
    (prog : List (String × Module)) (script : List NamedCall) : Set (List (Behaviour Val)) :=
  {bs | ∃ (s : Store H) (insts : List (String × ModuleInst)),
    SeparateReady P host {} [] prog s insts ∧ ProgramSession P host insts s script bs}

namespace MergeProof

theorem named_script_exports_agree {ps : List (String × Module)}
    {insts : List (String × ModuleInst)} {acc : Module} {miA : ModuleInst}
    (hinv : Inv ps insts acc miA) (hnames : (ps.map Prod.fst).Nodup)
    {script : List NamedCall} (hscript : Program.NamedScriptExports ps script) :
    ∀ call ∈ script, Program.exportFunc? insts call.1 call.2.1 = exportFunc? miA call.2.1 := by
  intro call hcall
  obtain ⟨p, hp, hn, he⟩ := hscript call hcall
  obtain ⟨mi, hlook⟩ := module_lookup hinv hnames ⟨p, hp, hn⟩
  unfold Program.exportFunc?
  rw [hlook]
  exact (export_agree hinv hnames ⟨p, hp, hn, he⟩).2 mi hlook

end MergeProof

/-- The actual in-order N-ary merge preserves persistent scripts that may
switch source namespace at every request. Successful initialization, the
closed host and all existing checked-merge feature restrictions remain. -/
theorem merge_interleaved_sessions_sound_profile {prog : List (String × Module)} {result : Module}
    (h : merge? (prog.map Prod.snd) = some result) (hback : ImportsBackward prog)
    (hres : ImportsResolve prog) (hprof : ∀ p ∈ prog, inProfile p.2 = true)
    (hnames : (prog.map Prod.fst).Nodup) (P : Profile)
    {script : List NamedCall} (hscript : Program.NamedScriptExports prog script) :
    Program.interleavedSessionBeh P (SingleThreaded.Det.noHost (H := H)) prog script =
      moduleReadySessions P (SingleThreaded.Det.noHost (H := H)) closedEnv result
        (script.map Prod.snd) := by
  have hne : prog ≠ [] := by
    rintro rfl
    simp [merge?] at h
  have hpre := MergeProof.prefix_sound (H := H) (P := P) hback hres hprof
    hnames prog.reverse (by simpa using hne) (rest := []) (by simp) (by simpa using h)
  rw [List.reverse_reverse] at hpre
  obtain ⟨hprofR, hA, hB⟩ := hpre
  ext bs
  simp only [Program.interleavedSessionBeh, moduleReadySessions, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, insts, hsep, hb⟩
    obtain ⟨sA, miA, -, hready, hchain, hinv⟩ := hA hsep
    refine ⟨{}, [], sA, miA, by unfold closedEnv; exact ⟨rfl, rfl⟩, hready, ?_⟩
    exact (hchain.programSession_iff_profile
      (MergeProof.named_script_exports_agree hinv hnames hscript)).mpr hb
  · rintro ⟨s0, xas, s', mi, ⟨rfl, rfl⟩, hready, hb⟩
    have hprep := MergeChain.prepare_of_ready (as := []) hprofR hready
    obtain ⟨s, insts, hsep⟩ := hB (MergeChain.moduleOk_of_ready hready) hprep
    obtain ⟨sA, miA, hprepA, -, hchain, hinv⟩ := hA hsep
    obtain ⟨rfl, rfl⟩ := MergeProof.prep_inj (hprep.symm.trans hprepA)
    exact ⟨s, insts, hsep, (hchain.programSession_iff_profile
      (MergeProof.named_script_exports_agree hinv hnames hscript)).mp hb⟩

/-- The executable merge checks discharge every graph/profile premise. -/
theorem checkedMerge?_interleaved_sessions_profile {prog : List (String × Module)}
    {result : Module} (h : checkedMerge? prog = some result) (P : Profile)
    {script : List NamedCall} (hscript : Program.NamedScriptExports prog script) :
    Program.interleavedSessionBeh P (SingleThreaded.Det.noHost (H := H)) prog script =
      moduleReadySessions P (SingleThreaded.Det.noHost (H := H)) closedEnv result
        (script.map Prod.snd) := by
  obtain ⟨hm, hb, hr, hp, -, hn, -⟩ := checkedMerge?_conditions h
  exact merge_interleaved_sessions_sound_profile hm hb hr hp hn P hscript

end Silmaril.Wasm.Binaryen
