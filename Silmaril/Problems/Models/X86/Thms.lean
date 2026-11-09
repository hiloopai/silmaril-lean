module

public import Silmaril.Problems.Models.X86.Defs
public import Silmaril.Problems.Core.Thms
public import Silmaril.X86.Loose.Thms
public import Silmaril.X86.Loose.Listing.Thms
public import Silmaril.X86.Exact.Thms
import Silmaril.Proofs.Problems.Models.X86.Loose

/-!
# Machine models for problem statements: what is proved

Proved with the standard axioms; the longer proofs are in
`Silmaril/Proofs/Problems/Models/X86/Loose.lean`. Names in `Silmaril.Problems.Models.X86`.

**The loose top.**

* `looseRel_progress`, `str9Part_prefixFree`, **`looseSv1_progress`**: the loose top over a
  prefix-free listing table whose `Str9` part is functional has `RelIsa.Progress`;
  `looseSv1_progress_table`: so does the top over `table bs` for every `bs` passing
  `tableOk`; `looseSv1_admissible`: the top is a member of its own down-set, so its
  `Class.below` is inhabited.
* `mem_str9Part_int`, `mem_str9Part_str`: table membership of one listed byte string, by
  `classify`.

**The institution view** (`Silmaril.X86.Institution`, over any signature `G`):
`looseSv1_eq_top` (`looseSv1 D` is the top of `Exact.Sig.sv1 (str9Part D)`),
`admissible_iff_model`, `fnJ_iff_sat`, **`fnCorrect_below_iff_thm`** (`FnCorrect` over the
down-set of a signature's top is validity in its room) and **`refutesOn_below_iff_csa`** (a
`RefutesOn` over the down-set is a countermodel). Given `Task.sv1Tight` and the decoder check
of the table, `open9_le_looseSv1` and `str9_le_looseSv1` put `Open9` and `Str9` below the
top, and `fnCorrectDet_open9`, `fnCorrectDet_str9` turn a loose solution into the
deterministic `Spec.Total` form on them.

**Step lemmas for function proofs.**

* `admits_regs`, `jcc_admits`, `jmp_admits`, `ret_admits`, `wordAt_of_abiEntry`: what an
  admitted successor of a register-only, branch or `ret` form is;
* `must_step`, `step_ok`: the one-instruction `Must` rule and the ok-step inversion of the
  loose machine with `Σ v1` on `MState`, over a core, a memory and an effect form.
-/

@[expose] public section

namespace Silmaril.Problems.Models.X86

open Silmaril.X86 (MState State Word Byte Reg RelIsa)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Must Views Le)
open Silmaril.X86.Loose
open Silmaril.X86.Loose.Listing
open Silmaril.X86.Institution (Sig Model Sen Sat room)
open Silmaril.X86.FnContract (Spec)
open Silmaril.Problems

/-! ## `Progress` of the loose top -/

/-- **The loose machine over a prefix-free, functional table has `Progress`** (for any form
specifications, on any views with `live = True`). -/
theorem looseRel_progress {Φ σ : Type} [DecidableEq Φ] (D : DTable Φ) (S : Silmaril.X86.Loose.Sigma Φ)
    (V : Views σ) (hp : D.prefixFree = true) (hf : D.functional = true)
    (hl : ∀ t, V.live t) : (X86Loose.rel D S V).Progress :=
  Silmaril.Proofs.Problems.Models.X86.looseRel_progress D S V hp hf hl

/-- `str9Part` of a prefix-free table is prefix-free. -/
theorem str9Part_prefixFree {D : DTable LForm} (hp : D.prefixFree = true) :
    (str9Part D).prefixFree = true :=
  Silmaril.Proofs.Problems.Models.X86.str9Part_prefixFree hp

/-- **The loose top over a prefix-free table with a functional `Str9` part has
`Progress`.** -/
theorem looseSv1_progress {D : DTable LForm} (hp : D.prefixFree = true)
    (hf : (str9Part D).functional = true) : (looseSv1 D).Progress :=
  looseRel_progress (str9Part D) Sv1 Views.mstate (str9Part_prefixFree hp) hf fun _ => trivial

/-- The loose top over a listing that passes `tableOk` has `Progress`. -/
theorem looseSv1_progress_table {bs : List (List Nat)} (h : tableOk bs = true) :
    (looseSv1 (table bs)).Progress :=
  looseSv1_progress (table_prefixFree h) (str9Part_functional bs)

/-- The loose top is a member of its own down-set. -/
theorem looseSv1_admissible {D : DTable LForm} (hp : D.prefixFree = true)
    (hf : (str9Part D).functional = true) : Admissible (looseSv1 D) (looseSv1 D) :=
  admissible_self (looseSv1_progress hp hf)

/-! ## Table membership -/

/-- A listed byte string that `classify` reads as the integer form `i` is in the `Str9` part
of the listing's table. -/
theorem mem_str9Part_int {bs : List (List Nat)} {b : List Nat} {i : Silmaril.X86.Ext9.Instr}
    (hb : b ∈ bs) (hc : classify (toBytes b) = .loose (.int i)) :
    (⟨toBytes b, .ext9 i⟩ : DEntry Silmaril.X86.Str9.Instr) ∈ str9Part (table bs) :=
  Silmaril.Proofs.Problems.Models.X86.mem_str9Part_int hb hc

/-- A listed byte string that `classify` reads as the string form `s` is in the `Str9` part
of the listing's table. -/
theorem mem_str9Part_str {bs : List (List Nat)} {b : List Nat} {s : Silmaril.X86.Str9.Str}
    (hb : b ∈ bs) (hc : classify (toBytes b) = .str s) :
    (⟨toBytes b, .str s⟩ : DEntry Silmaril.X86.Str9.Instr) ∈ str9Part (table bs) :=
  Silmaril.Proofs.Problems.Models.X86.mem_str9Part_str hb hc

/-! ## The institution view -/

section
variable {Φ σ : Type} {V : Views σ} {G : Sig Φ}

/-- The loose top is the top of the `Σ v1` signature over the `Str9` part of the listing. -/
theorem looseSv1_eq_top (D : DTable LForm) :
    looseSv1 D = (Silmaril.X86.Exact.Sig.sv1 (str9Part D)).top Views.mstate :=
  rfl

/-- The admissible members of the down-set of a signature's top are its models. -/
theorem admissible_iff_model {C : RelIsa σ} :
    Admissible (G.top V) C ↔ ∃ M : Model V G, M.1 = C :=
  ⟨fun h => ⟨⟨C, h⟩, rfl⟩, fun ⟨M, hM⟩ => hM ▸ M.2⟩

/-- The judgement `FnJ` is satisfaction. -/
theorem fnJ_iff_sat {φ : Sen σ} {C : RelIsa σ} : FnJ φ C ↔ Sat C φ :=
  Iff.rfl

/-- **`FnCorrect` over the down-set of a signature's top is validity in its room.** -/
theorem fnCorrect_below_iff_thm {φ : Sen σ} :
    FnCorrect (Class.below (G.top V)) φ ↔ ∀ M : (room V G).Mod, (room V G).Sat M φ :=
  ⟨fun h M => h M.1 M.2, fun h C hC => h ⟨C, hC⟩⟩

/-- **A `RefutesOn` over the down-set of a signature's top is a countermodel in its room.** -/
theorem refutesOn_below_iff_csa {φ : Sen σ} :
    (∃ ref, RefutesOn (Class.below (G.top V)) ref (FnJ φ)) ↔
      ∃ M : (room V G).Mod, ¬ (room V G).Sat M φ :=
  ⟨fun ⟨ref, hm, hn⟩ => ⟨⟨ref, hm⟩, hn⟩, fun ⟨M, hn⟩ => ⟨M.1, M.2, hn⟩⟩

end

section
variable {D : DTable LForm}

/-- Given `Task.sv1Tight`, `Open9` is below the loose top over a table whose `Str9` part
`Open9.decode` reads. -/
theorem open9_le_looseSv1 (h : Silmaril.X86.Exact.Task.sv1Tight)
    (hD : Silmaril.X86.Exact.DTable.okOpen9 (str9Part D) = true) :
    Le (RelIsa.ofIsa Silmaril.X86.Open9.isa) (looseSv1 D) :=
  (Silmaril.X86.Exact.open9_le_exact hD).trans
    (Sig.top_le _ (Silmaril.X86.Exact.sv1_le_exact h _))

/-- Given `Task.sv1Tight`, `Str9` is below the loose top over a table whose `Str9` part
`Str9.decode` reads. -/
theorem str9_le_looseSv1 (h : Silmaril.X86.Exact.Task.sv1Tight)
    (hD : Silmaril.X86.Exact.DTable.decodes Silmaril.X86.Str9.isa (str9Part D) = true) :
    Le (RelIsa.ofIsa Silmaril.X86.Str9.isa) (looseSv1 D) :=
  (Silmaril.X86.Exact.str9_le_exact hD).trans
    (Sig.top_le _ (Silmaril.X86.Exact.sv1_le_exact h _))

/-- A loose solution gives the deterministic form on `Open9` (given `Task.sv1Tight`). -/
theorem fnCorrectDet_open9 (h : Silmaril.X86.Exact.Task.sv1Tight)
    (hD : Silmaril.X86.Exact.DTable.okOpen9 (str9Part D) = true) {S : Word → Spec MState}
    (hS : FnCorrect (Class.below (looseSv1 D)) S) : FnCorrectDet Silmaril.X86.Open9.isa S :=
  fnCorrectDet_of_fnCorrect hS (open9_le_looseSv1 h hD)

/-- A loose solution gives the deterministic form on `Str9` (given `Task.sv1Tight`). -/
theorem fnCorrectDet_str9 (h : Silmaril.X86.Exact.Task.sv1Tight)
    (hD : Silmaril.X86.Exact.DTable.decodes Silmaril.X86.Str9.isa (str9Part D) = true)
    {S : Word → Spec MState} (hS : FnCorrect (Class.below (looseSv1 D)) S) :
    FnCorrectDet Silmaril.X86.Str9.isa S :=
  fnCorrectDet_of_fnCorrect hS (str9_le_looseSv1 h hD)

end

/-! ## Effects -/

/-- An admitted successor of an effect that havocs nothing and writes no memory: the same
memory, the effect's `rip`, allowed flags, and each register as the effect lists it. -/
theorem admits_regs {e : Effect} {c c' : State} {m m' : Memory}
    (h : e.Admits c m c' m') (hh : e.havocRegs = []) (hw : e.writes = []) :
    m' = m ∧ c'.rip = e.rip ∧ e.flags.Allows c.flags c'.flags ∧
      ∀ r, c'.read r = e.regAfter c r :=
  Silmaril.Proofs.Problems.Models.X86.admits_regs h hh hw

/-- **`jcc`**: memory and registers kept; `rip` is the target when the condition holds. -/
theorem jcc_admits {cc : Silmaril.X86.Ext.Cond} {d : Word} {c c' : State} {m m' : Memory}
    {l : Nat} (h : ((Ctl.jccSpec cc d).eff c m l).Admits c m c' m') :
    m' = m ∧ c'.rip = (if cc.eval c.flags = some true then c.rip + BitVec.ofNat 64 l + d
      else c.rip + BitVec.ofNat 64 l) ∧ ∀ r, c'.read r = c.read r :=
  Silmaril.Proofs.Problems.Models.X86.jcc_admits h

/-- **`jmp`**: memory and registers kept; `rip` is the target. -/
theorem jmp_admits {d : Word} {c c' : State} {m m' : Memory} {l : Nat}
    (h : ((Ctl.jmpSpec d).eff c m l).Admits c m c' m') :
    m' = m ∧ c'.rip = c.rip + BitVec.ofNat 64 l + d ∧ ∀ r, c'.read r = c.read r :=
  Silmaril.Proofs.Problems.Models.X86.jmp_admits h

/-- **`ret`**: memory kept; `rip` is the stack word, `rsp + 8`, every other register kept. -/
theorem ret_admits {c c' : State} {m m' : Memory} {l : Nat}
    (h : (Ctl.retSpec.eff c m l).Admits c m c' m') :
    m' = m ∧ c'.rip = (Ctl.wordAt m (c.read .rsp)).getD 0 ∧
      c'.read .rsp = c.read .rsp + 8#64 ∧ ∀ r, r ≠ .rsp → c'.read r = c.read r :=
  Silmaril.Proofs.Problems.Models.X86.ret_admits h

/-- At a System V entry the return address is a readable stack word. -/
theorem wordAt_of_abiEntry {c : State} {m : Memory}
    (h : Silmaril.X86.FnContract.AbiEntry c m) :
    Ctl.wordAt m (c.read .rsp) = some (Silmaril.X86.FnContract.retOf c m) :=
  Silmaril.Proofs.Problems.Models.X86.wordAt_of_abiEntry h

/-! ## The loose machine with `Σ v1` on `MState` -/

/-- **The one-instruction `Must` rule** for the loose machine with `Σ v1` on `MState`, at an
entry whose form is the effect form `F`. -/
theorem must_step {D : DTable Silmaril.X86.Str9.Instr} {R Q : MState → Prop} {c : State}
    {m : Memory} {e : DEntry Silmaril.X86.Str9.Instr} {F : EffSpec} (hm : e ∈ D)
    (hat : m.fetchBytes c.rip.toNat e.bytes.length = some e.bytes) (hF : sv1Eff e.form = some F)
    (hu : ¬ F.unspecified c m e.bytes.length) (hR : R ⟨c, m⟩)
    (h : ∀ c' m', (F.eff c m e.bytes.length).Admits c m c' m' →
      Must (X86Loose.rel D Sv1 Views.mstate) R Q ⟨c', m'⟩) :
    Must (X86Loose.rel D Sv1 Views.mstate) R Q ⟨c, m⟩ :=
  X86Loose.must_of_spec (V := Views.mstate) (s := ⟨c, m⟩) (F := F.toFormSpec) hR hm hat
    (by simp [Sv1, hF]) hu h

/-- **The ok-steps of the loose machine** with `Σ v1` from a specified entry, on `MState`. -/
theorem step_ok {D : DTable Silmaril.X86.Str9.Instr} {c : State} {m : Memory} {t : MState}
    {e : DEntry Silmaril.X86.Str9.Instr} {F : EffSpec} (hm : e ∈ D)
    (hat : m.fetchBytes c.rip.toNat e.bytes.length = some e.bytes) (hF : sv1Eff e.form = some F)
    (hu : ¬ F.unspecified c m e.bytes.length)
    (h : (X86Loose.rel D Sv1 Views.mstate).step ⟨c, m⟩ (.ok t)) :
    (F.eff c m e.bytes.length).Admits c m t.core t.memory := by
  obtain ⟨c', m', rfl, ha⟩ := X86Loose.step_ok_of_spec (V := Views.mstate) (s := ⟨c, m⟩)
    (F := F.toFormSpec) hm hat (by simp [Sv1, hF]) hu h
  exact ha

end Silmaril.Problems.Models.X86
