module

public import Silmaril.Wasi.Cli.Host2.Defs
public import Silmaril.Wasi.Cli.Main.Thms

/-!
# The WASI 0.2 view on the traces of the host's programs

Proofs for `Silmaril.Wasi.Cli.Host2.Thms`. The events of `api2`'s programs are calls of
`get-arguments`, `get-environment`, `get-stdout`, `get-stderr` and
`blocking-write-and-flush`, the export call and its return. On such traces `p2View` reads no
stdin and no file (`Plain2`), so its observation is determined by the successful writes, the
`get-stderr` handles, the exit code and the failed writes (`obs2_plain`). Each of these is
computed event by event (`write2_*`, `handles_*`, `endCode_*`, `failedWrite2_*`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host2

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli
open Silmaril.Wasm.Component (Val)

/-! ## Functions the view does not read -/

/-- A function whose answers `p2View` reads neither as stdin nor as a file operation. -/
def Plain2 (f : FnName) : Prop :=
  f ≠ Versions.P2.isRead ∧ f ≠ Versions.P2.isBread ∧ f ≠ Versions.P2.getStdin ∧ f ≠ getDirs ∧ f ≠ openAt ∧ f ≠ fdRead ∧ f ≠ fdWrite

instance (f : FnName) : Decidable (Plain2 f) := by unfold Plain2; infer_instance

/-- An event `p2View` reads neither as stdin nor as a file operation. -/
def PlainEv (e : WEv) : Prop :=
  read2 e = none ∧ handles Versions.P2.getStdin [e] = [] ∧ ∀ ds, fdStep ds e = ds ∧ fileEff ds e = none

theorem plainEv_imp {f : FnName} (a : List Val) (n : Option (List Val)) (hf : Plain2 f) :
    PlainEv (.imp f a n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  refine ⟨?_, ?_, fun ds => ⟨?_, ?_⟩⟩
  · unfold read2; split <;> simp_all
  · unfold handles
    refine List.filterMap_eq_nil_iff.2 fun e he => ?_
    rw [List.mem_singleton.1 he]; split <;> simp_all
  · unfold fdStep; split <;> simp_all
  · unfold fileEff; split <;> simp_all

theorem plainEv_req (f : FnName) (a : List Val) : PlainEv (.req f a) :=
  ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem plainEv_call (f : FnName) (a : List Val) : PlainEv (.call f a) :=
  ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem plainEv_ret (f : FnName) (a : List Val) (r : Option (List Val)) :
    PlainEv (.ret f a r) :=
  ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-! ## The view on plain traces -/

theorem handles_append (f : FnName) (t u : List WEv) :
    handles f (t ++ u) = handles f t ++ handles f u := List.filterMap_append

theorem handles_cons (f : FnName) (e : WEv) (t : List WEv) :
    handles f (e :: t) = handles f [e] ++ handles f t := handles_append f [e] t

theorem fileEffs_plain {t : List WEv} (ht : ∀ e ∈ t, PlainEv e) (ds : Fds) :
    fileEffs ds t = [] := by
  induction t generalizing ds with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨-, -, hf⟩ := ht e List.mem_cons_self
    rw [fileEffs, (hf ds).1, (hf ds).2, ih (fun e' he' => ht e' (List.mem_cons_of_mem _ he'))]
    rfl

theorem stdin2_plain {t : List WEv} (ht : ∀ e ∈ t, PlainEv e) : stdin2 t = [] := by
  have h : t.filterMap read2 = [] :=
    List.filterMap_eq_nil_iff.2 fun e he => (ht e he).1
  simp [stdin2, h]

/-- **`p2View` on a trace that reads neither stdin nor files.** -/
theorem obs2_plain (i : Input) {t : List WEv} (ht : ∀ e ∈ t, PlainEv e) :
    p2View.obs i t =
      { stdout := toBytes (written2 false t), stderr := toBytes (written2 true t),
        exit := (exitOf cliRun (some Versions.P2.cliExit) t).getD 0, fs := i.fs,
        refused := t.any failedWrite2 } := by
  have hf : fileEffs [] t = [] := fileEffs_plain ht []
  have hs : stdin2 t = [] := stdin2_plain ht
  simp only [View.obs, p2View, hf, hs, List.filterMap_nil, List.any_nil, Bool.or_false]
  rfl

/-! ## Event by event -/

theorem write2_req (f : FnName) (a : List Val) : write2 (.req f a) = none := rfl
theorem write2_call (f : FnName) (a : List Val) : write2 (.call f a) = none := rfl
theorem write2_ret (f : FnName) (a : List Val) (r : Option (List Val)) :
    write2 (.ret f a r) = none := rfl

theorem write2_imp {f : FnName} (a : List Val) (n : Option (List Val)) (h1 : f ≠ Versions.P2.osWrite)
    (h2 : f ≠ streamWrite) : write2 (.imp f a n) = none := by
  unfold write2; split <;> simp_all

theorem okUnit_iff (n : Option (List Val)) : okUnit n = true ↔ n = some [.variant 0 none] := by
  unfold okUnit; split <;> simp_all

theorem bytesOf_bytesV (c : List (BitVec 8)) : bytesOf (bytesV c) = c := by
  simp [bytesOf, bytesV, List.filterMap_map]

theorem write2_bwf (h : BitVec 32) (c : List (BitVec 8)) (n : Option (List Val)) :
    write2 (.imp streamWrite [.u32 h, bytesV c] n) = if okUnit n then some (h, c) else none := by
  unfold okUnit
  split
  · simp [write2, bytesOf_bytesV]
  · unfold write2; split <;> simp_all

theorem handles_imp_ne {f g : FnName} (a : List Val) (n : Option (List Val)) (h : f ≠ g) :
    handles g [.imp f a n] = [] := by
  unfold handles
  refine List.filterMap_eq_nil_iff.2 fun e he => ?_
  rw [List.mem_singleton.1 he]; split <;> simp_all

theorem handles_req (g f : FnName) (a : List Val) : handles g [.req f a] = [] := rfl
theorem handles_call (g f : FnName) (a : List Val) : handles g [.call f a] = [] := rfl
theorem handles_ret (g f : FnName) (a : List Val) (r : Option (List Val)) :
    handles g [.ret f a r] = [] := rfl

theorem handles_get (g : FnName) (a : List Val) (n : Option (List Val)) :
    handles g [.imp g a n] = (u32Of n).toList := by
  unfold handles u32Of; simp only [List.filterMap_cons, List.filterMap_nil]
  split <;> split <;> simp_all

theorem endCode_imp (f : FnName) (a : List Val) (n : Option (List Val)) :
    endCode cliRun (some Versions.P2.cliExit) (.imp f a n) = none := rfl
theorem endCode_call (f : FnName) (a : List Val) :
    endCode cliRun (some Versions.P2.cliExit) (.call f a) = none := rfl

theorem endCode_req {f : FnName} (a : List Val) (h : f ≠ Versions.P2.cliExit) :
    endCode cliRun (some Versions.P2.cliExit) (.req f a) = none := by
  unfold endCode; split <;> simp_all

theorem endCode_ret (a : List Val) (r : Option (List Val)) :
    endCode cliRun (some Versions.P2.cliExit) (.ret cliRun a r) = some (retCode r) := by
  simp [endCode]

theorem failedWrite2_req (f : FnName) (a : List Val) : failedWrite2 (.req f a) = false := rfl
theorem failedWrite2_call (f : FnName) (a : List Val) : failedWrite2 (.call f a) = false := rfl
theorem failedWrite2_ret (f : FnName) (a : List Val) (r : Option (List Val)) :
    failedWrite2 (.ret f a r) = false := rfl

theorem failedWrite2_imp {f : FnName} (a : List Val) (n : Option (List Val)) (h1 : f ≠ Versions.P2.osWrite)
    (h2 : f ≠ streamWrite) : failedWrite2 (.imp f a n) = false := by
  unfold failedWrite2; split <;> simp_all

theorem failedWrite2_ok (a : List Val) {n : Option (List Val)} (hn : okUnit n = true) :
    failedWrite2 (.imp streamWrite a n) = false := by
  rw [(okUnit_iff n).1 hn]; rfl

end Silmaril.Wasi.Cli.Host2

end
