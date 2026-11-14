module

public import Silmaril.X86.MemoryModel.Litmus.Weak.Defs
public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs
public import Silmaril.X86.Litmus.WeakExtract.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# Litmus traces over `Weak9`: what is proved

PROVED (standard axioms):

* `wtraces_sound`: when `Test.wtraces` succeeds, every trace of every thread **replays on
  `Weak9.step`** (`WReplay`, from `wextract_sound`).
* `hand_writers_extracted` (`decide`): each writer trace that was transcribed by hand
  (`Hand.mpMovnti`, ..., `Hand.stosInternal`) is, action for action (kind, address, size,
  `locked`, flavour, bytes read and written), one of the traces extracted from the writer's
  bytes over `Weak9`. So the hand transcription was right, and it is no longer needed: the
  verdicts use the extracted traces (`Test.looseTraces`).
* `weak_writers_flavoured` (`decide`): the extracted `movnti` writers have exactly one
  non-temporal store each and the `rep stosb` writers one string store per element.
* `mpMov_plain_xl_forbidden` (`decide`, as a check): **the flavour is
  load-bearing**. Replacing the writer's `movnti` bytes (`0F C3 /r`) by the plain
  `mov m32, r32` (`89 /r`, same operand) gives plain flavours only, and over the extracted
  traces XL then **forbids** the MP witness that it allows for the real `MP+movnti` bytes.
  So the loose verdict really comes from the decoded `nt` flavour, not from the model alone.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86.Litmus (Flavor Trace)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

theorem mapM_id_getElem? {β : Type} :
    ∀ {L : List (Option β)} {T : List β}, L.mapM id = some T →
      ∀ (k : Nat) (o : Option β), L[k]? = some o → ∃ y, o = some y ∧ T[k]? = some y
  | [], _, _, k, o, hk => by simp at hk
  | a :: L, T, h, k, o, hk => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, rfl, ys, hl, rfl⟩ := h
    cases k with
    | zero => simp at hk; exact ⟨y, hk.symm, rfl⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      exact mapM_id_getElem? hl k o hk

/-- **Every trace of `Test.wtraces` replays on `Weak9.step`.** -/
theorem wtraces_sound {t : Test} {T : List (List XTrace)} (h : t.wtraces = some T) :
    ∀ k (th : Thread), t.threads[k]? = some th → ∃ trs, T[k]? = some trs ∧
      ∀ tr ∈ trs, Silmaril.X86.Litmus.WReplay (t.xthread k th) (t.xthread k th).init
        tr.steps tr.final := by
  intro k th hk
  unfold Test.wtraces Test.wextractOver at h
  obtain ⟨trs, he, hT⟩ := mapM_id_getElem? h k
    (Silmaril.X86.Litmus.wextract (t.xthread k th) t.wdomain t.wfuel)
    (by simp [List.getElem?_mapIdx, hk])
  exact ⟨trs, hT, Silmaril.X86.Litmus.wextract_sound he⟩

/-- The actions of the traces of thread `k` of `wtraces`. -/
def Test.wactsOf (t : Test) (k : Nat) : List (List Silmaril.X86.Litmus.Act) :=
  ((t.wtraces.getD []).getD k []).map Trace.acts

set_option maxRecDepth 100000 in
/-- **The six hand-transcribed writers are traces of the writers' bytes.** -/
theorem hand_writers_extracted :
    Hand.mpMovnti.acts ∈ Corpus.«MP+movnti».wactsOf 0 ∧
      Hand.mpMovntiSfence.acts ∈ Corpus.«MP+movnti+sfence».wactsOf 0 ∧
      Hand.mpMovntiLock.acts ∈ Corpus.«MP+movnti+lock».wactsOf 0 ∧
      Hand.mpStosb.acts ∈ Corpus.«MP+stosb».wactsOf 0 ∧
      Hand.mpStosbSfence.acts ∈ Corpus.«MP+stosb+sfence».wactsOf 0 ∧
      Hand.stosInternal.acts ∈ Corpus.«STOS+internal».wactsOf 0 := by
  decide +kernel

/-- The flavours of a thread's actions, per trace. -/
def Test.wflavours (t : Test) (k : Nat) : List (List Flavor) :=
  (t.wactsOf k).map (·.map Silmaril.X86.Litmus.Act.flavor)

set_option maxRecDepth 100000 in
/-- **The extracted writers carry the weak flavours**: one non-temporal store per `movnti`, one
string store per `rep stosb` element (the other actions are plain). -/
theorem weak_writers_flavoured :
    Corpus.«MP+movnti».wflavours 0 = [[.nonTemporal, .plain]] ∧
      Corpus.«MP+movnti+sfence».wflavours 0 = [[.nonTemporal, .plain, .plain]] ∧
      Corpus.«MP+stosb».wflavours 0 = [[.string, .string, .string, .string, .plain]] ∧
      Corpus.«STOS+internal».wflavours 0 = [[.string, .string]] := by
  decide +kernel

/-- Mutant of `MP+movnti`: the writer's `movnti` bytes replaced by the plain
`mov m32, r32` with the same operand (`89 04 25 00 00 01 00`), recorded XL verdict `forbidden`.
The name is kept, so `Test.looseTraces` still extracts it over `Weak9`. -/
def Mutant.mpMov : Test :=
  { Corpus.«MP+movnti» with
    threads := match Corpus.«MP+movnti».threads with
      | w :: rest =>
        match w.insns with
        | i :: is => { w with insns := { i with bytes := [0x89, 0x04, 0x25, 0x00, 0x00, 0x01, 0x00] }
            :: is } :: rest
        | [] => w :: rest
      | [] => []
    xl := .forbidden }

set_option maxRecDepth 100000 in
theorem mpMov_check :
    Mutant.mpMov.wflavours 0 = [[.plain, .plain]] ∧ Mutant.mpMov.checkXlLoose = true := by
  decide +kernel

/-- **The `nt` flavour is load-bearing**: with `movnti` replaced by a plain `mov`, the writer's
extracted stores are all plain and XL forbids the MP witness over the extracted traces (TSO and
SC too, and some SC execution exists), while for the real bytes XL allows it
(`corpus_loose_xl`, `Corpus.«MP+movnti».xl = .allowed`). -/
theorem mpMov_plain_xl_forbidden :
    Mutant.mpMov.wflavours 0 = [[.plain, .plain]] ∧
      ∃ T, Mutant.mpMov.looseTraces = some T ∧
        Verdict.forbidden.Holds Mutant.mpMov (AxReach Mutant.mpMov T Exec.Xl) ∧
        ∃ f, AxReach Mutant.mpMov T Exec.Sc f := by
  obtain ⟨hf, h⟩ := mpMov_check
  refine ⟨hf, ?_⟩
  unfold Test.checkXlLoose at h
  split at h
  · rename_i T hT
    obtain ⟨hx, -, -, hs⟩ := loose_of_check h
    exact ⟨T, hT, hx, hs⟩
  · cases h

end Silmaril.X86.MemoryModel.Litmus
