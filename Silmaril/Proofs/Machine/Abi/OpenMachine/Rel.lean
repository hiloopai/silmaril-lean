module

public import Silmaril.Machine.Abi.OpenMachine.Rel.Defs
public import Silmaril.Machine.Abi.OpenMachine.Thms
public import Silmaril.X86.FnContract.Must.Thms
/-!
# Proofs: the ABI call relation of a relational machine

Names are in `Silmaril.Machine.Abi.OpenMachine`, so that the header `OpenMachine/Rel/Thms.lean`
exports them.

* `runsInR_ofIsa_open_iff`, `returnedV_mstate_iff`, `firstReturnR_ofIsa_open_iff`,
  `callModelR_ofIsa`: on `ofIsa Open.isa` the relational call relation *is* `callModel`;
* `RelIsa.Must.result_of_runsInR`: a demonic property bounds every run that avoids a guard
  `G` until it hits it (the generic core of "every first return is a result");
* `callModelR_of_must`, `callModelR_of_mustC`: **a demonic contract is what `callModelR`
  reads**: an outcome exists (given `Progress`) and *every* outcome is a `Spec.ResultV`;
* `sat_of_outcomes`: the System V satisfaction theorem for an arbitrary call relation whose
  outcomes all carry the FFI-only state and are call results;
* `sat_of_must`: `Contracts.Sat (callModelR C) (within ((sysv o).translate p c) room)` from a
  demonic contract on any `A` with `Le C A` and `Progress C`;
* rung 01: `clamp_must`, `sat_must`, `clamp_mustLoosen`, `sat_mustLoosen`,
  `clamp_i32_satR`, `sat_add_u32_satR` (for every `C ≤ loosen Open.isa ⊤` with `Progress`),
  and the instances on `ofIsa Open.isa`, `ofIsa Open9.isa` and `callModel`.

Apart from `clamp_i32_rejects_idR` (which rewrites the existing mutation check
`clamp_i32_rejects_id`) and `clamp_i32_rejects_id_loosen` (which goes through it), none of these proofs uses `callModel_subsingleton`, `mem_callModel`
or `firstReturn_unique`, transitively (checked on the private oleans; see
the design notes).
-/

@[expose] public section

namespace Silmaril.Machine.Abi.OpenMachine

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86
open Silmaril.X86.Ladder.LeafArith
open Silmaril.X86.RelIsa (Views ofIsa loosen Le Progress RunsInR)
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)

/-! ## The deterministic open machine -/

theorem runsInR_ofIsa_open_iff {P : MState → Prop} {s t : MState} :
    RunsInR (ofIsa Open.isa) P s t ↔ RunsIn P s t := by
  constructor
  · intro r
    induction r with
    | refl m => exact .refl m
    | step hp hs _ ih => exact .step hp (RelIsa.ofIsa_step_ok.1 hs) ih
  · intro r
    induction r with
    | refl m => exact .refl m
    | step hp hs _ ih => exact .step hp (RelIsa.ofIsa_step_ok.2 hs) ih

theorem returnedV_mstate_iff {s m : MState} :
    FnContract.ReturnedV Views.mstate s m ↔ Returned s m := Iff.rfl

theorem firstReturnR_ofIsa_open_iff {s t : MState} :
    FirstReturnR (ofIsa Open.isa) s t ↔ FirstReturn s t :=
  and_congr runsInR_ofIsa_open_iff Iff.rfl

/-- **On the deterministic open machine, `callModelR` is `callModel`.** -/
theorem callModelR_ofIsa : callModelR (ofIsa Open.isa) = callModel := by
  funext s
  ext t
  exact and_congr firstReturnR_ofIsa_open_iff Iff.rfl

/-! ## Demonic contracts and first returns -/

/-- A demonic property `Must C R Q s` whose step states avoid a guard `G` and whose goal
states satisfy it bounds every run that avoids `G` until it ends in `G`: the end is a `Q`
state. (No determinism: the run is any run of `C`.) -/
theorem _root_.Silmaril.X86.RelIsa.Must.result_of_runsInR {σ : Type} {C : RelIsa σ}
    {R Q G : σ → Prop} (hRG : ∀ m, R m → ¬ G m) (hQG : ∀ m, Q m → G m) {s t : σ}
    (h : RelIsa.Must C R Q s) (r : RunsInR C (fun m => ¬ G m) s t) (ht : G t) : Q t := by
  induction r with
  | refl m =>
    cases h with
    | done hq => exact hq
    | step hr _ _ => exact absurd ht (hRG _ hr)
  | step hp hs _ ih =>
    cases h with
    | done hq => exact absurd (hQG _ hq) hp
    | step _ _ k => exact ih (k _ hs) ht

theorem runsInR_mono {σ : Type} {C : RelIsa σ} {P Q : σ → Prop} (h : ∀ m, P m → Q m)
    {s t : σ} (r : RunsInR C P s t) : RunsInR C Q s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step (h _ hp) hs ih

theorem returnedV_of_resultV {σ : Type} {V : Views σ} {S : FnContract.Spec σ} {s t : σ}
    (h : S.ResultV V s t) : FnContract.ReturnedV V s t :=
  ⟨h.abi.pc, h.abi.stack⟩

/-- **A demonic contract on `C` is what `callModelR C` reads**: from an entry state, if `C`
always has an outcome there is a `callModelR` outcome, and *every* outcome is a call result. -/
theorem callModelR_of_mustC {S : FnContract.Spec MState} {C : RelIsa MState} (h : S.Must C)
    (hp : Progress C) {s : Ffi.State} (hl : C.live s.machine)
    (ha : FnContract.AbiEntry (C.core s.machine) (C.mem s.machine)) (he : S.entry s.machine) :
    (∃ t, t ∈ callModelR C s) ∧
      ∀ t ∈ callModelR C s, S.ResultV C.toViews s.machine t.machine := by
  have m := h s.machine hl ha he
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨u, run, res⟩ := RelIsa.Must.exists_run hp hl m
    exact ⟨{ s with machine := u }, ⟨runsInR_mono (fun _ (hm : _ ∧ _) => hm.1) run,
      returnedV_of_resultV res⟩, rfl⟩
  · exact RelIsa.Must.result_of_runsInR (G := FnContract.ReturnedV C.toViews s.machine)
      (fun _ (hm : _ ∧ _) => hm.1) (fun _ hq => returnedV_of_resultV hq) m ht.1.1 ht.1.2

/-- **`callModelR_of_mustC` along refinement**: a demonic contract on `A` is read by
`callModelR C` for every `C` with fewer behaviours and `Progress` (replaces the
`callModel_subsingleton` argument of `callModel_of_strict`). -/
theorem callModelR_of_must {S : FnContract.Spec MState} {A C : RelIsa MState} (h : S.Must A)
    (hle : Le C A) (hp : Progress C) {s : Ffi.State} (hl : C.live s.machine)
    (ha : FnContract.AbiEntry (C.core s.machine) (C.mem s.machine)) (he : S.entry s.machine) :
    (∃ t, t ∈ callModelR C s) ∧
      ∀ t ∈ callModelR C s, S.ResultV C.toViews s.machine t.machine :=
  callModelR_of_mustC (FnContract.Spec.Must.of_le hle h) hp hl ha he

/-! ## The System V sentence -/

variable {o : Options} {p : Proto}

/-- **System V satisfaction for any call relation** whose outcomes carry the FFI-only state
and are call results of `S` on the open-machine views, when one exists. This is
`sat_of_firstReturn` without the uniqueness of the outcome. -/
theorem sat_of_outcomes {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    {S : FnContract.Spec MState} {room : Ffi.State → Prop}
    {M : Contracts.Model Ffi.State Ffi.State}
    (outcomes : ∀ a s, (sysv o).Entry p a s → c.pre a → room s →
      (∃ t, t ∈ M s) ∧ ∀ t ∈ M s,
        t = { s with machine := t.machine } ∧ S.Result Open.isa s.machine t.machine)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → S.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat M (within ((sysv o).translate p c) room) := by
  rintro s ⟨⟨a, entry, pre⟩, roomy⟩
  obtain ⟨ex, all⟩ := outcomes a s entry pre roomy
  refine ⟨ex, ?_⟩
  intro t' ran a' entry' pre' ob observed
  obtain ⟨eq, res⟩ := all t' ran
  rw [eq] at observed
  have ret := return_of_result entry' res
  obtain ⟨⟨r, at_⟩, reflect⟩ := post a' s t'.machine entry' pre' roomy res.post
  cases ob with
  | none => exact absurd ⟨ret, r, at_⟩ observed
  | some r' => exact reflect r' observed.2

/-- **The System V sentence from a demonic contract.** A demonic contract `S.Must A` on a
relational machine with the open-machine views gives `Contracts.Sat (callModelR C)` of the
translated C contract, for every `C` with fewer behaviours than `A` and `Progress`. -/
theorem sat_of_must {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))}
    {S : FnContract.Spec MState} {room : Ffi.State → Prop} {A C : RelIsa MState}
    (h : S.Must A) (hle : Le C A) (hp : Progress C) (hv : A.toViews = Views.mstate)
    (entry : ∀ a s, (sysv o).Entry p a s → c.pre a → room s → S.entry s.machine)
    (post : ∀ a s t, (sysv o).Entry p a s → c.pre a → room s → S.post s.machine t →
      (∃ r, (sysv o).ResultAt p s { s with machine := t } r) ∧
        ∀ r, (sysv o).ResultAt p s { s with machine := t } r → c.post a (some r)) :
    Contracts.Sat (callModelR C) (within ((sysv o).translate p c) room) := by
  have hv' : C.toViews = Views.ofIsa Open.isa := hle.views.trans hv
  refine sat_of_outcomes (S := S) (fun a s e pre roomy => ?_) post
  have hl : C.live s.machine := by rw [hv']; trivial
  have ha : FnContract.AbiEntry (C.core s.machine) (C.mem s.machine) := by
    have := abiEntry_of_entry e
    rw [show C.core = Views.mstate.core from congrArg Views.core (hle.views.trans hv),
      show C.mem = Views.mstate.mem from congrArg Views.mem (hle.views.trans hv)]
    exact this
  obtain ⟨ex, all⟩ := callModelR_of_must h hle hp hl ha (entry a s e pre roomy)
  refine ⟨ex, fun t ht => ⟨ht.2, ?_⟩⟩
  have res := all t ht
  rw [hv'] at res
  exact FnContract.Spec.resultV_ofIsa.1 res

/-! ## Rung 01 through `callModelR` -/

/-- The System V argument registers of `clamp_i32` (copied from the proofs of `OpenMachine`,
whose lemma `clamp_args` the `OpenMachine` header does not export). -/
theorem clamp_argsR {x lo hi : BitVec 32} {s : Ffi.State}
    (entry : (sysv o).Entry clampProto (.cons x (.cons lo (.cons hi .nil))) s) :
    r32 .rdi s.machine = x ∧ r32 .rsi s.machine = lo ∧ r32 .rdx s.machine = hi := by
  obtain ⟨_, e⟩ := entry
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, ⟨-, b2, e2, c2⟩, -⟩ := e.argumentsAt
  subst e0 e1 e2
  exact ⟨(chunk32_iff _ .rdi _).1 c0, (chunk32_iff _ .rsi _).1 c1, (chunk32_iff _ .rdx _).1 c2⟩

/-- The System V argument registers of `sat_add_u32` (copied, as `clamp_argsR`). -/
theorem sat_argsR {a b : BitVec 32} {s : Ffi.State}
    (entry : (sysv o).Entry satProto (.cons a (.cons b .nil)) s) :
    r32 .rdi s.machine = a ∧ r32 .rsi s.machine = b := by
  obtain ⟨_, e⟩ := entry
  obtain ⟨⟨-, b0, e0, c0⟩, ⟨-, b1, e1, c1⟩, -⟩ := e.argumentsAt
  subst e0 e1
  exact ⟨(chunk32_iff _ .rdi _).1 c0, (chunk32_iff _ .rsi _).1 c1⟩

/-- Rung 01 `clamp_i32` as a demonic contract on the deterministic open machine. -/
theorem clamp_must :
    (clampSpec'.restrict (FnContract.RetOutside Open.isa base code.length)).Must
      (ofIsa Open.isa) :=
  FnContract.Spec.Strict.must clamp_strict

/-- Rung 01 `sat_add_u32` as a demonic contract on the deterministic open machine. -/
theorem sat_must :
    (satSpec.restrict (FnContract.RetOutside Open.isa base code.length)).Must
      (ofIsa Open.isa) :=
  FnContract.Spec.Strict.must sat_strict

/-- Rung 01 `clamp_i32` as a demonic contract on the everywhere-loosened open machine. -/
theorem clamp_mustLoosen :
    (clampSpec'.restrict (FnContract.RetOutside Open.isa base code.length)).Must
      (loosen Open.isa fun _ => True) :=
  FnContract.Spec.Strict.mustLoosen clamp_strict

/-- Rung 01 `sat_add_u32` as a demonic contract on the everywhere-loosened open machine. -/
theorem sat_mustLoosen :
    (satSpec.restrict (FnContract.RetOutside Open.isa base code.length)).Must
      (loosen Open.isa fun _ => True) :=
  FnContract.Spec.Strict.mustLoosen sat_strict

/-- **gcc -O2 `clamp_i32` is System V-correct on every machine that refines the loosened
open machine** and always has an outcome, through `callModelR`. -/
theorem clamp_i32_satR (o : Options) {C : RelIsa MState}
    (hle : Le C (loosen Open.isa fun _ => True)) (hp : Progress C) :
    Contracts.Sat (callModelR C)
      (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) := by
  refine sat_of_must clamp_mustLoosen hle hp rfl
    (fun _ _ _ _ roomy => ⟨⟨roomy.loaded, roomy.pc⟩, roomy.retOutside⟩) ?_
  intro a s t entry _ _ hpost
  match a, entry with
  | .cons x (.cons lo (.cons hi .nil)), entry =>
    obtain ⟨hx, hl, hh⟩ := clamp_argsR entry
    have hrax : (t.core.read .rax).setWidth 32 = clampSpec x lo hi := by
      rw [show t.core.read .rax = _ from hpost, ← hx, ← hl, ← hh]
      simp
    refine ⟨⟨clampSpec x lo hi, (resultAt_int32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
    have := (resultAt_int32 _ _ _ _ _).1 at_
    exact congrArg some (this.symm.trans hrax)

/-- **gcc -O2 `sat_add_u32` is System V-correct on every machine that refines the loosened
open machine** and always has an outcome, through `callModelR`. -/
theorem sat_add_u32_satR (o : Options) {C : RelIsa MState}
    (hle : Le C (loosen Open.isa fun _ => True)) (hp : Progress C) :
    Contracts.Sat (callModelR C)
      (within ((sysv o).translate satProto satC) (Room base code 0x90)) := by
  refine sat_of_must sat_mustLoosen hle hp rfl
    (fun _ _ _ _ roomy => ⟨⟨roomy.loaded, roomy.pc⟩, roomy.retOutside⟩) ?_
  intro a s t entry _ _ hpost
  match a, entry with
  | .cons x (.cons y .nil), entry =>
    obtain ⟨hx, hy⟩ := sat_argsR entry
    have hrax : (t.core.read .rax).setWidth 32 = satAddSpec x y := by
      rw [show t.core.read .rax = _ from hpost, ← hx, ← hy]
      simp
    refine ⟨⟨satAddSpec x y, (resultAt_uint32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
    have := (resultAt_uint32 _ _ _ _ _).1 at_
    exact congrArg some (this.symm.trans hrax)

/-- `clamp_i32` through `callModelR (ofIsa Open.isa)`. -/
theorem clamp_i32_sat_ofIsa (o : Options) :
    Contracts.Sat (callModelR (ofIsa Open.isa))
      (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) :=
  clamp_i32_satR o RelIsa.le_loosen RelIsa.progress_ofIsa

/-- `sat_add_u32` through `callModelR (ofIsa Open.isa)`. -/
theorem sat_add_u32_sat_ofIsa (o : Options) :
    Contracts.Sat (callModelR (ofIsa Open.isa))
      (within ((sysv o).translate satProto satC) (Room base code 0x90)) :=
  sat_add_u32_satR o RelIsa.le_loosen RelIsa.progress_ofIsa

/-- **`clamp_i32_sat` re-derived through `callModelR`**, with no subsingleton argument. -/
theorem clamp_i32_sat_viaR (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) :=
  callModelR_ofIsa ▸ clamp_i32_sat_ofIsa o

/-- **`sat_add_u32_sat` re-derived through `callModelR`**, with no subsingleton argument. -/
theorem sat_add_u32_sat_viaR (o : Options) :
    Contracts.Sat callModel (within ((sysv o).translate satProto satC) (Room base code 0x90)) :=
  callModelR_ofIsa ▸ sat_add_u32_sat_ofIsa o

/-- `clamp_i32` through `callModelR` of the deterministic `Ext9` open machine, with no `Open9`
proof (`loosen_open9_le_open`). -/
theorem clamp_i32_sat_open9 (o : Options) :
    Contracts.Sat (callModelR (ofIsa Open9.isa))
      (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) :=
  clamp_i32_satR o (RelIsa.le_loosen.trans RelIsa.loosen_open9_le_open) RelIsa.progress_ofIsa

/-- `sat_add_u32` through `callModelR` of the deterministic `Ext9` open machine. -/
theorem sat_add_u32_sat_open9 (o : Options) :
    Contracts.Sat (callModelR (ofIsa Open9.isa))
      (within ((sysv o).translate satProto satC) (Room base code 0x90)) :=
  sat_add_u32_satR o (RelIsa.le_loosen.trans RelIsa.loosen_open9_le_open) RelIsa.progress_ofIsa

/-- **Non-vacuity on every refinement**: the concrete `clamp_i32(5, 0, 3)` entry of
`clamp_i32_nonvacuous` meets the precondition, and `callModelR C` has an outcome from it on
every `C ≤ loosen Open.isa ⊤` with `Progress` (the loosened machine itself included). -/
theorem clamp_i32_satR_nonvacuous (o : Options) {C : RelIsa MState}
    (hle : Le C (loosen Open.isa fun _ => True)) (hp : Progress C) :
    ∃ s, (within ((sysv o).translate clampProto clampC) (Room base code 0x30)).pre s ∧
      ∃ t, t ∈ callModelR C s := by
  obtain ⟨s, hpre, -⟩ := clamp_i32_nonvacuous o
  exact ⟨s, hpre, (clamp_i32_satR o hle hp s hpre).1⟩

/-- The mutated contract `clampIdC` is refuted through `callModelR (ofIsa Open.isa)` too. -/
theorem clamp_i32_rejects_idR (o : Options) :
    ¬ Contracts.Sat (callModelR (ofIsa Open.isa))
      (within ((sysv o).translate clampProto clampIdC) (Room base code 0x30)) := by
  rw [callModelR_ofIsa]
  exact clamp_i32_rejects_id o

/-! ## Review additions: monotonicity, the loosened machine itself, mutation off `ofIsa` -/

/-- Runs of a refinement are runs of the abstract machine (from a live state). -/
theorem runsInR_of_le {σ : Type} {C A : RelIsa σ} (hle : Le C A) {P : σ → Prop} {s t : σ}
    (hl : C.live s) (r : RunsInR C P s t) : RunsInR A P s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step hp (hle.step hl hs) (ih (C.live_step hl hs))

/-- **`callModelR` is monotone along refinement** (from a live entry): a machine with fewer
behaviours has fewer call outcomes. -/
theorem callModelR_mono {C A : RelIsa MState} (hle : Le C A) {s : Ffi.State}
    (hl : C.live s.machine) : callModelR C s ⊆ callModelR A s := by
  rintro t ⟨⟨run, ret⟩, eq⟩
  refine ⟨⟨?_, ?_⟩, eq⟩
  · rw [← hle.views]; exact runsInR_of_le hle hl run
  · rw [← hle.views]; exact ret

/-- `clamp_i32` through `callModelR` of the loosened open machine itself (which allows every
outcome wherever `Open.isa` stops): `clamp_i32_satR` instantiated, with
`FnContract.progress_loosen` discharging `Progress`. -/
theorem clamp_i32_sat_loosen (o : Options) :
    Contracts.Sat (callModelR (loosen Open.isa fun _ => True))
      (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) :=
  clamp_i32_satR o (RelIsa.Le.refl _) FnContract.progress_loosen

/-- `sat_add_u32` through `callModelR` of the loosened open machine itself. -/
theorem sat_add_u32_sat_loosen (o : Options) :
    Contracts.Sat (callModelR (loosen Open.isa fun _ => True))
      (within ((sysv o).translate satProto satC) (Room base code 0x90)) :=
  sat_add_u32_satR o (RelIsa.Le.refl _) FnContract.progress_loosen

/-- **Mutation check on the loosened machine**: the mutated contract `clampIdC` is refuted
through `callModelR (loosen Open.isa ⊤)` too. If it held there, every outcome of the
deterministic machine would meet it (`callModelR_mono`, `le_loosen`), and those outcomes exist
(`clamp_i32_sat_ofIsa`), contradicting `clamp_i32_rejects_idR`. -/
theorem clamp_i32_rejects_id_loosen (o : Options) :
    ¬ Contracts.Sat (callModelR (loosen Open.isa fun _ => True))
      (within ((sysv o).translate clampProto clampIdC) (Room base code 0x30)) := by
  intro hs
  apply clamp_i32_rejects_idR o
  intro s hpre
  obtain ⟨⟨a, entry, -⟩, roomy⟩ := hpre
  refine ⟨(clamp_i32_sat_ofIsa o s ⟨⟨a, entry, trivial⟩, roomy⟩).1, ?_⟩
  intro t ht
  exact (hs s ⟨⟨a, entry, trivial⟩, roomy⟩).2 t
    (callModelR_mono (C := ofIsa Open.isa) RelIsa.le_loosen trivial ht)

/-- `clamp_i32` through `callModelR (ofIsa Open.isa)` **directly from `clamp_must`** (the
demonic contract on the deterministic machine itself, `Le.refl`, `progress_ofIsa`), the literal
form of the P6 acceptance item; `clamp_i32_sat_ofIsa` goes through the loosened machine. -/
theorem clamp_i32_sat_ofIsa_must (o : Options) :
    Contracts.Sat (callModelR (ofIsa Open.isa))
      (within ((sysv o).translate clampProto clampC) (Room base code 0x30)) := by
  refine sat_of_must clamp_must (RelIsa.Le.refl _) RelIsa.progress_ofIsa rfl
    (fun _ _ _ _ roomy => ⟨⟨roomy.loaded, roomy.pc⟩, roomy.retOutside⟩) ?_
  intro a s t entry _ _ hpost
  match a, entry with
  | .cons x (.cons lo (.cons hi .nil)), entry =>
    obtain ⟨hx, hl, hh⟩ := clamp_argsR entry
    have hrax : (t.core.read .rax).setWidth 32 = clampSpec x lo hi := by
      rw [show t.core.read .rax = _ from hpost, ← hx, ← hl, ← hh]
      simp
    refine ⟨⟨clampSpec x lo hi, (resultAt_int32 _ _ _ _ _).2 hrax⟩, fun r at_ => ?_⟩
    have := (resultAt_int32 _ _ _ _ _).1 at_
    exact congrArg some (this.symm.trans hrax)

end Silmaril.Machine.Abi.OpenMachine
