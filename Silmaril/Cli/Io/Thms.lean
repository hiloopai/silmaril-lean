module

public import Silmaril.Cli.Io.Defs
public import Silmaril.Cli.Behaviour.Thms

/-!
# CLI programs in Lean: evaluation lemmas and pure cores

* `exec_bind`: evaluation of `p >>= f` runs `p`, then `f` on its value (`Prog.after`).
* Evaluation of every operation (`exec_getArgs_bind`, …; `simp` lemmas), of `getEnvs`, of
  `readAll` (`St.readAll`: on the files of the invocation, the answers are `Input.fileAt` and
  the paths read `Input.readPath`) and of `writeAll` (`St.writeAll`).
* **`obs_ofCore`**, **`sat_ofCore_iff`**: a program built from a pure core is observed as the
  core's result (`Result.obs`), so it satisfies a spec iff the core does on every input.
* **`obs_ofTool`**, **`sat_ofTool_iff`**: the same for tools that read input files.
* `Prog.sat_iff_det_le` (satisfaction is refinement of the program's deterministic spec),
  `Prog.Sat.mono` (along refinement), `Prog.Sat.inf` (two requirements at once).
* `Result.obs_nil`: a result with no files is observed as its outputs and code, files kept.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io

open Silmaril.Cli Silmaril.Cli.Spec

namespace Prog

variable {α β : Type}

/-! ## Satisfaction and refinement -/

/-- **Satisfaction is refinement** of the program's deterministic specification. -/
theorem sat_iff_det_le (p : Prog ExitCode) (S : Spec) : p.Sat S ↔ det p.obs ≤ S :=
  det_le_iff.symm

/-- **Satisfaction is transported along refinement.** -/
theorem Sat.mono {p : Prog ExitCode} {S T : Spec} (h : p.Sat S) (hST : S ≤ T) : p.Sat T :=
  fun i => hST i _ (h i)

/-- Two requirements at once. -/
theorem Sat.inf {p : Prog ExitCode} {S T : Spec} (hS : p.Sat S) (hT : p.Sat T) : p.Sat (S ⊓ T) :=
  fun i => ⟨hS i, hT i⟩

/-! ## Evaluation -/

@[simp] theorem bind_eq (p : Prog α) (f : α → Prog β) : (p >>= f) = p.bind f := rfl

@[simp] theorem pure_eq (a : α) : (Pure.pure a : Prog α) = .pure a := rfl

@[simp] theorem pure_bind (a : α) (f : α → Prog β) : (Prog.pure a).bind f = f a := rfl

/-- Continue an evaluation with `f`. -/
def after (i : Input) (f : α → Prog β) : St × Option α → St × Option β
  | (st, some a) => exec i (f a) st
  | (st, none) => (st, none)

/-- **Evaluation of a bind.** -/
theorem exec_bind (i : Input) (p : Prog α) (f : α → Prog β) (st : St) :
    exec i (p.bind f) st = after i f (exec i p st) := by
  induction p generalizing st with
  | pure a => rfl
  | args k ih => exact ih _ st
  | env n k ih => exact ih _ st
  | stdin k ih => exact ih _ _
  | out s b k ih => exact ih _
  | read p k ih => exact ih _ _
  | write p b k ih => exact ih _ _
  | exit c => rfl

/-- Binds associate under evaluation. -/
theorem exec_bind_bind {γ : Type} (i : Input) (p : Prog α) (g : α → Prog β) (f : β → Prog γ)
    (st : St) : exec i ((p.bind g).bind f) st = exec i (p.bind fun a => (g a).bind f) st := by
  rw [exec_bind, exec_bind, exec_bind]
  rcases exec i p st with ⟨st', _ | a⟩
  · rfl
  · exact (exec_bind i (g a) f st').symm

@[simp] theorem exec_getArgs_bind (i : Input) (f : List String → Prog β) (st : St) :
    exec i (getArgs.bind f) st = exec i (f i.args) st := rfl

@[simp] theorem exec_getEnv_bind (i : Input) (n : String) (f : Option String → Prog β)
    (st : St) : exec i ((getEnv n).bind f) st = exec i (f (i.getEnv n)) st := rfl

@[simp] theorem exec_readStdin_bind (i : Input) (f : Bytes → Prog β) (st : St) :
    exec i (readStdin.bind f) st = exec i (f st.rest) st.takeStdin := rfl

@[simp] theorem exec_print_bind (i : Input) (b : Bytes) (f : Unit → Prog β) (st : St) :
    exec i ((print b).bind f) st = exec i (f ()) { st with obs := st.obs.emit .stdout b } := rfl

@[simp] theorem exec_eprint_bind (i : Input) (b : Bytes) (f : Unit → Prog β) (st : St) :
    exec i ((eprint b).bind f) st = exec i (f ()) { st with obs := st.obs.emit .stderr b } := rfl

@[simp] theorem exec_readFile_bind (i : Input) (p : String) (f : Option Bytes → Prog β)
    (st : St) : exec i ((readFile p).bind f) st =
      exec i (f (readObs i st.obs p).2) { st with obs := (readObs i st.obs p).1 } := rfl

@[simp] theorem exec_writeFile_bind (i : Input) (p : String) (b : Bytes) (f : Bool → Prog β)
    (st : St) : exec i ((writeFile p b).bind f) st =
      exec i (f (writeObs i st.obs p b).2) { st with obs := (writeObs i st.obs p b).1 } := rfl

@[simp] theorem exec_pure (i : Input) (a : α) (st : St) :
    exec i (Prog.pure a) st = (st, some a) := rfl

@[simp] theorem exec_exit (i : Input) (c : ExitCode) (st : St) :
    exec i (exit (α := α) c) st = ({ st with obs := { st.obs with exit := c } }, none) := rfl

/-- **Environment variables** are answered from the invocation. -/
theorem exec_getEnvs_bind (i : Input) (ns : List String)
    (f : List (String × Option String) → Prog β) (st : St) :
    exec i ((getEnvs ns).bind f) st = exec i (f (ns.map fun n => (n, i.getEnv n))) st := by
  induction ns generalizing f with
  | nil => rfl
  | cons n ns ih =>
    show exec i (((getEnvs ns).bind fun vs => Prog.pure ((n, i.getEnv n) :: vs)).bind f) st = _
    rw [exec_bind_bind]
    exact ih _

/-- **Writing files** runs `writeAllObs`. -/
theorem exec_writeAll_bind (i : Input) (fs : List (String × Bytes)) (f : Bool → Prog β)
    (st : St) : exec i ((writeAll fs).bind f) st =
      exec i (f (writeAllObs i st.obs fs).2) { st with obs := (writeAllObs i st.obs fs).1 } := by
  induction fs generalizing st with
  | nil => rfl
  | cons pb fs ih =>
    obtain ⟨p, b⟩ := pb
    show exec i ((fun ok => (if ok then writeAll fs else Prog.pure false).bind f)
      (writeObs i st.obs p b).2) { st with obs := (writeObs i st.obs p b).1 } = _
    rcases h : writeObs i st.obs p b with ⟨o', _ | _⟩
    · simp [writeAllObs, h]
    · simp only [ite_true, writeAllObs, h]
      exact ih _

end Prog

/-! ## Reading files -/

/-- Read files in the model. -/
def readAllObs (i : Input) : Obs → List String → Obs × List (String × Option Bytes)
  | o, [] => (o, [])
  | o, p :: ps =>
    ((readAllObs i (readObs i o p).1 ps).1,
      (p, (readObs i o p).2) :: (readAllObs i (readObs i o p).1 ps).2)

namespace Prog

variable {β : Type}

/-- **Reading files** runs `readAllObs`. -/
theorem exec_readAll_bind (i : Input) (ps : List String)
    (f : List (String × Option Bytes) → Prog β) (st : St) :
    exec i ((readAll ps).bind f) st =
      exec i (f (readAllObs i st.obs ps).2) { st with obs := (readAllObs i st.obs ps).1 } := by
  induction ps generalizing st f with
  | nil => rfl
  | cons p ps ih =>
    show exec i (((readAll ps).bind fun bs =>
      Prog.pure ((p, (readObs i st.obs p).2) :: bs)).bind f)
      { st with obs := (readObs i st.obs p).1 } = _
    rw [exec_bind_bind]
    exact ih _ _

end Prog

/-- A read on the invocation's files answers `Input.fileAt` and records `Input.readPath`. -/
theorem readObs_eq (i : Input) (o : Obs) (s : String) (h : o.fs = i.fs) :
    readObs i o s =
      ({ o with reads := o.reads ++ (i.readPath s).toList, log := o.log ++ (i.readEv s).toList },
        i.fileAt s) := by
  obtain ⟨⟩ := o
  subst h
  unfold readObs Input.readEv Input.readPath Input.fileAt
  rcases hr : i.resolve s with _ | q
  · simp
  · rcases hq : i.fs q with _ | b
    · simp [hq, Option.filter]
    · simp [hq, Option.filter]

/-- **Reads on the invocation's files**: the answers are `Input.fileAt`, the paths read
`Input.readPath`, nothing else changes. -/
theorem readAllObs_eq (i : Input) (ps : List String) (o : Obs) (h : o.fs = i.fs) :
    readAllObs i o ps =
      ({ o with reads := o.reads ++ ps.filterMap i.readPath,
                log := o.log ++ ps.filterMap i.readEv },
        ps.map fun p => (p, i.fileAt p)) := by
  induction ps generalizing o with
  | nil => simp [readAllObs]
  | cons p ps ih =>
    simp only [readAllObs]
    rw [readObs_eq i o p h,
      ih { o with reads := o.reads ++ (i.readPath p).toList,
                  log := o.log ++ (i.readEv p).toList } h]
    rcases hp : i.readPath p with _ | q <;> simp [hp, Input.readEv]

/-! ## Emitting a result -/

namespace Prog

/-- **Evaluation of `emit`.** -/
theorem exec_emit (i : Input) (r : Result) (st : St) :
    exec i (emit r) st =
      ({ st with obs := (writeAllObs i ((st.obs.emit .stdout r.stdout).emit .stderr r.stderr)
          r.files).1 },
        some (if (writeAllObs i ((st.obs.emit .stdout r.stdout).emit .stderr r.stderr)
          r.files).2 then r.exit else 1)) := by
  show exec i ((print r.stdout).bind fun _ => (eprint r.stderr).bind fun _ =>
    (writeAll r.files).bind fun ok => Prog.pure (if ok then r.exit else 1)) st = _
  rw [exec_print_bind, exec_eprint_bind, exec_writeAll_bind, exec_pure]

/-- The observation of `emit r` from a state whose observation is empty but for its files,
consumption and reads. -/
theorem finish_exec_emit (i : Input) (r : Result) (c : Nat) (rd : List FPath) (lg : List FileEv)
    (rs : Bytes) :
    finish (exec i (emit r)
      { obs := { fs := i.fs, consumed := c, reads := rd, log := lg }, rest := rs }) =
      r.obs i c rd lg := by
  rw [exec_emit]
  rfl

/-! ## Pure cores -/

/-- **The observation of a program built from a pure core** is the core's result. -/
theorem obs_ofCore (core : List String → Bytes → Result) (i : Input) :
    (ofCore core).obs i = (core i.args i.stdin).obs i i.stdin.length := by
  show finish (exec i (getArgs.bind fun a => readStdin.bind fun s => emit (core a s))
    (St.init i)) = _
  rw [exec_getArgs_bind, exec_readStdin_bind]
  have hst : (St.init i).takeStdin =
      { obs := { fs := i.fs, consumed := i.stdin.length, reads := [] }, rest := [] } := by
    simp [St.init, St.takeStdin]
  rw [hst]
  exact finish_exec_emit i _ _ _ [] _

/-- **A program built from a pure core satisfies `S` iff its core does on every input.** -/
theorem sat_ofCore_iff (core : List String → Bytes → Result) (S : Spec) :
    (ofCore core).Sat S ↔ ∀ i, S i ((core i.args i.stdin).obs i i.stdin.length) := by
  simp only [Sat, obs_ofCore]

/-- The inputs a tool reads, as the core sees them. -/
def readsOf (reads : List String → List String) (i : Input) : List (String × Option Bytes) :=
  (reads i.args).map fun p => (p, i.fileAt p)

/-- **The observation of a tool built from a pure core**: the core's result, having read the
files that are there. -/
theorem obs_ofTool (reads : List String → List String)
    (core : List String → List (String × Option Bytes) → Result) (i : Input) :
    (ofTool reads core).obs i =
      (core i.args (readsOf reads i)).obs i 0 ((reads i.args).filterMap i.readPath)
        ((reads i.args).filterMap i.readEv) := by
  show finish (exec i (getArgs.bind fun a => (readAll (reads a)).bind fun fs =>
    emit (core a fs)) (St.init i)) = _
  rw [exec_getArgs_bind, exec_readAll_bind, readAllObs_eq i _ _ rfl]
  exact finish_exec_emit i _ _ _ _ _

/-- **A tool built from a pure core satisfies `S` iff its core does on every input.** -/
theorem sat_ofTool_iff (reads : List String → List String)
    (core : List String → List (String × Option Bytes) → Result) (S : Spec) :
    (ofTool reads core).Sat S ↔
      ∀ i, S i ((core i.args (readsOf reads i)).obs i 0 ((reads i.args).filterMap i.readPath)
        ((reads i.args).filterMap i.readEv)) := by
  simp only [Sat, obs_ofTool]

end Prog

/-- **A result with no files** is observed as its outputs and exit code, the files kept. -/
@[simp] theorem Result.obs_nil (r : Result) (i : Input) (c : Nat) (rd : List FPath)
    (lg : List FileEv) (h : r.files = []) :
    r.obs i c rd lg =
      { stdout := r.stdout, stderr := r.stderr, exit := r.exit, consumed := c, reads := rd,
        fs := i.fs, log := lg } := by
  simp [Result.obs, h, writeAllObs]

end Silmaril.Cli.Io

end
