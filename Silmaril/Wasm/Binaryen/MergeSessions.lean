module

public import Silmaril.Wasm.Binaryen.MergeSessionTransport

@[expose] public section

/-! # Namespace-scoped persistent sessions through checked N-ary merge

The source modules initialize separately, then every request runs against one
chosen source namespace in the resulting shared store. The merged instance
initializes once and runs that same script in its shared store. Only successful
initialization is observed here; initialization traps/divergence and external
host contexts are outside this observation. Requested names must be declared by
the chosen source module, since the merge also exposes other modules' exports.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Link.GC

variable {H : Type}

/-- The selected namespace exists, including for an empty script, and every
requested name is declared by that source module. Arguments are unrestricted. -/
def Program.ScriptExports (prog : List (String × Module)) (n : String)
    (script : List Call) : Prop :=
  ∃ p ∈ prog, p.1 = n ∧ ∀ call ∈ script, ∃ e ∈ p.2.exports, e.name = call.1

/-- Repeated calls to one source namespace after successful separate
initialization. All invocations share the actual resulting store. -/
def Program.sessionBeh (P : Profile) (host : HostSemantics H)
    (prog : List (String × Module)) (n : String) (script : List Call) :
    Set (List (Behaviour Val)) :=
  {bs | ∃ (s : Store H) (insts : List (String × ModuleInst)) (mi : ModuleInst),
    SeparateReady P host {} [] prog s insts ∧ insts.lookup n = some mi ∧
      Session P host mi s script bs}

/-- Export sessions after a successful module instantiation in `Env`.
Initialization itself does not contribute an observation to this set. -/
def moduleReadySessions (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop)
    (m : Module) (script : List Call) : Set (List (Behaviour Val)) :=
  {bs | ∃ s xas s' mi, Env m s xas ∧ Ready P host s m xas s' mi ∧
    Session P host mi s' script bs}

namespace MergeProof

/-- The source-instance lookup does not require a nonempty script or any
export. This handles the empty-session case without inventing an export name. -/
theorem module_lookup {ps : List (String × Module)} {insts : List (String × ModuleInst)}
    {acc : Module} {miA : ModuleInst} (hinv : Inv ps insts acc miA)
    (hnames : (ps.map Prod.fst).Nodup) {n : String}
    (hn : ∃ p ∈ ps, p.1 = n) : ∃ mi, insts.lookup n = some mi := by
  have hkeys := inv_keys hinv hnames
  obtain ⟨p, hp, hpn⟩ := hn
  obtain ⟨⟨n', mi⟩, hmem, hn', -⟩ := MergeChain.forall₂_mem_left hinv p hp
  have heq : n' = n := hn'.symm.trans hpn
  have hmem' : (n, mi) ∈ insts := by
    rw [← heq]
    exact List.mem_reverse.mp hmem
  exact ⟨mi, lookup_of_mem hkeys hmem'⟩

theorem script_exports_agree {ps : List (String × Module)}
    {insts : List (String × ModuleInst)} {acc : Module} {miA mi : ModuleInst}
    (hinv : Inv ps insts acc miA) (hnames : (ps.map Prod.fst).Nodup)
    {n : String} {script : List Call} (hscript : Program.ScriptExports ps n script)
    (hlook : insts.lookup n = some mi) :
    ∀ call ∈ script, exportFunc? mi call.1 = exportFunc? miA call.1 := by
  obtain ⟨p, hp, hn, hcalls⟩ := hscript
  intro call hcall
  exact (export_agree hinv hnames ⟨p, hp, hn, hcalls call hcall⟩).2 mi hlook

end MergeProof

/-- The actual N-ary merge preserves exact persistent session observations at
the same arbitrary profile, for scripts in one source namespace and the closed
host. The existing syntactic, dependency and successful-initialization scope
remains in force. -/
theorem merge_sessions_sound_profile {prog : List (String × Module)} {result : Module}
    (h : merge? (prog.map Prod.snd) = some result) (hback : ImportsBackward prog)
    (hres : ImportsResolve prog) (hprof : ∀ p ∈ prog, inProfile p.2 = true)
    (hnames : (prog.map Prod.fst).Nodup) (P : Profile)
    {n : String} {script : List Call} (hscript : Program.ScriptExports prog n script) :
    Program.sessionBeh P (SingleThreaded.Det.noHost (H := H)) prog n script =
      moduleReadySessions P (SingleThreaded.Det.noHost (H := H)) closedEnv result script := by
  have hne : prog ≠ [] := by
    rintro rfl
    obtain ⟨p, hp, -⟩ := hscript
    simp at hp
  have hpre := MergeProof.prefix_sound (H := H) (P := P) hback hres hprof
    hnames prog.reverse (by simpa using hne) (rest := []) (by simp) (by simpa using h)
  rw [List.reverse_reverse] at hpre
  obtain ⟨hprofR, hA, hB⟩ := hpre
  ext bs
  simp only [Program.sessionBeh, moduleReadySessions, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, insts, mi, hsep, hlook, hb⟩
    obtain ⟨sA, miA, -, hready, hchain, hinv⟩ := hA hsep
    refine ⟨{}, [], sA, miA, by unfold closedEnv; exact ⟨rfl, rfl⟩, hready, ?_⟩
    exact (hchain.session_iff_profile
      (MergeProof.script_exports_agree hinv hnames hscript hlook)).mpr hb
  · rintro ⟨s0, xas, s', mi, ⟨rfl, rfl⟩, hready, hb⟩
    have hprep := MergeChain.prepare_of_ready (as := []) hprofR hready
    obtain ⟨s, insts, hsep⟩ := hB (MergeChain.moduleOk_of_ready hready) hprep
    obtain ⟨sA, miA, hprepA, -, hchain, hinv⟩ := hA hsep
    obtain ⟨rfl, rfl⟩ := MergeProof.prep_inj (hprep.symm.trans hprepA)
    have hscriptCopy := hscript
    obtain ⟨p, hp, hn, -⟩ := hscriptCopy
    obtain ⟨mi_n, hlook⟩ := MergeProof.module_lookup hinv hnames ⟨p, hp, hn⟩
    refine ⟨s, insts, mi_n, hsep, hlook, ?_⟩
    exact (hchain.session_iff_profile
      (MergeProof.script_exports_agree hinv hnames hscript hlook)).mp hb

/-- Executable graph, fragment and validation checks supply every merge
condition; only the namespace-scoped script guard remains explicit. -/
theorem checkedMerge?_sessions_profile {prog : List (String × Module)} {result : Module}
    (h : checkedMerge? prog = some result) (P : Profile)
    {n : String} {script : List Call} (hscript : Program.ScriptExports prog n script) :
    Program.sessionBeh P (SingleThreaded.Det.noHost (H := H)) prog n script =
      moduleReadySessions P (SingleThreaded.Det.noHost (H := H)) closedEnv result script := by
  obtain ⟨hm, hb, hr, hp, -, hn, -⟩ := checkedMerge?_conditions h
  exact merge_sessions_sound_profile hm hb hr hp hn P hscript

end Silmaril.Wasm.Binaryen
