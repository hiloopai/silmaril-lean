module

public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasi.Versions.P2.Io.Thms
public import Silmaril.Wasi.Versions.WitImport.RCli2.Thms

@[expose] public section

/-!
# WASI 0.2: the command theory, its readings, and the base WASI theory's slices

* `p2_loose_of_strict`, `p2_strict_ne_loose`: the strict reading of the WASI 0.2 theory refines
  the loose one, strictly (the `wasi:io` separation `sepTrace` lifts).
* **Relation to the base WASI theory** (`Silmaril.Wasi.Theory`):
  * `fits_cliWorld` / `toCliWorld : p2Command ⟶ cliWorld`: the base WASI theory's `cliWorld` fits the WASI 0.2
    command world (its imports are among `p2Imports`, it exports `run`), so every component of
    `cliWorld` is a component of `p2Command`, and sentences transfer along `World.ag_map`.
  * `p2_clockTh`, `p2_fsTyped`: the theory contains the base WASI theory's clock and filesystem theories.
  * `p2_stdoutTyped`: answer sequences of the WASI 0.2 theory are well typed for the base WASI theory's stdout
    theory, provided no `blocking-write-and-flush` traps. The proviso is needed:
    `p2_bwf_trap` is a WASI 0.2 answer sequence (a trap on a 4097-byte
    `blocking-write-and-flush`, which the WIT limits to 4096 bytes) that `stdoutTyped` rejects
    (`not_stdoutTyped_bwfTrap`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open CategoryTheory
open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Readings -/

/-- **The strict WASI 0.2 theory refines the loose one.** -/
theorem p2_loose_of_strict {t : List WEv} (h : (p2Th .strict).Accepts t) :
    (p2Th .loose).Accepts t := by
  have h' := (Protocol.accepts_prod_iff _ _ t).1 h
  exact (Protocol.accepts_prod_iff _ _ t).2 ⟨loose_of_strict h'.1, h'.2⟩

/-- The loose WASI 0.2 theory accepts `sepTrace`. -/
theorem p2_loose_sepTrace : (p2Th .loose).Accepts sepTrace :=
  (Protocol.acceptsB_iff _ _).1 (by decide)

/-- **The strict WASI 0.2 theory is strictly stronger than the loose one.** -/
theorem p2_strict_ne_loose : ∃ t, (p2Th .loose).Accepts t ∧ ¬ (p2Th .strict).Accepts t :=
  ⟨sepTrace, p2_loose_sepTrace, fun h =>
    not_strict_sepTrace ((Protocol.accepts_prod_iff _ _ _).1 h).1⟩

/-! ## the base WASI theory's worlds -/

/-- **the base WASI theory's `cliWorld` fits the WASI 0.2 command world.** -/
theorem fits_cliWorld : World.Fits p2Command cliWorld := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · simp only [cliWorld, World.union, clocksWorld, stdoutWorld, fsWorld, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    simp only [p2Command, p2Imports, ioImports_eq, cliImports_eq, clockImports_eq, fsImports_eq,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hf with ((h | h | h | h) | h | h | h | h | h) <;> subst h <;> simp
  · simp only [p2Command, Set.mem_singleton_iff] at hf
    subst hf
    simp [cliWorld, World.union, clocksWorld, stdoutWorld, fsWorld]

/-- The world morphism: a component of `cliWorld` is a component of `p2Command`. -/
def toCliWorld : p2Command ⟶ cliWorld := ⟨fits_cliWorld⟩

/-! ## the base WASI theory's theories -/

/-- The WASI 0.2 theory contains the base WASI theory's clock theory. -/
theorem p2_clockTh {r : Reading} {t : List WEv} (h : (p2Th r).Accepts t) : clockTh.Accepts t :=
  ((Protocol.accepts_prod_iff _ _ _).1 ((Protocol.accepts_prod_iff _ _ _).1 h).2).1

/-- The WASI 0.2 theory contains the base WASI theory's filesystem typing theory. -/
theorem p2_fsTyped {r : Reading} {t : List WEv} (h : (p2Th r).Accepts t) : fsTyped.Accepts t :=
  ((Protocol.accepts_prod_iff _ _ _).1
    ((Protocol.accepts_prod_iff _ _ _).1 ((Protocol.accepts_prod_iff _ _ _).1 h).2).2).2

/-- The WASI 0.2 theory's `p2Ok` part. -/
theorem p2_p2Ok {r : Reading} {t : List WEv} (h : (p2Th r).Accepts t) :
    ∀ e ∈ t, p2Ok e = true :=
  (pointwise_accepts_iff p2Ok t).1 ((Protocol.accepts_prod_iff _ _ _).1
    ((Protocol.accepts_prod_iff _ _ _).1 ((Protocol.accepts_prod_iff _ _ _).1 h).2).2).1

/-- Every answer of an accepted `wasi:io` sequence is admissible in some state. -/
theorem io_ansOk_of_mem {r : Reading} {t : List WEv} (h : (ioTh r).Accepts t) {f : FnName}
    {a : List Val} {res : Option (List Val)} (he : WEv.imp f a res ∈ t) :
    ∃ s, ansOk r s (ioOp f) a res = true := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem he
  have hp : (ioTh r).Accepts (u ++ [WEv.imp f a res]) :=
    h.of_prefix ⟨v, by simp⟩
  obtain ⟨q, -, q', hq'⟩ := (Protocol.accepts_concat_iff _ _ _).1 hp
  refine ⟨q, ?_⟩
  by_contra hok
  have hstep : ioStep r q (.imp f a res) = none := by simp [ioStep, hok]
  exact absurd hq' (by rw [show (ioTh r).step = ioStep r from rfl, hstep]; simp)

/-- `blocking-write-and-flush` is classified as such. -/
theorem ioOp_bwf : ioOp streamWrite = .bwf := by decide

/-- A non-trap `blocking-write-and-flush` answer admissible in the `wasi:io` theory is well
typed for the base WASI theory. -/
theorem stdoutOk_bwf {r : Reading} {s : IoSt} {a : List Val} {res : Option (List Val)}
    (h : ansOk r s .bwf a res = true) (hn : res ≠ none) :
    stdoutOk (.imp streamWrite a res) = true := by
  have hu : unitAns res = true := by
    cases res with
    | none => exact absurd rfl hn
    | some l =>
      have h2 : stickyOk s (selfOf a) (some l) = true ∧ unitAns (some l) = true := by
        simpa [ansOk] using h
      exact h2.2
  rw [unitAns_eq_hand] at hu
  unfold unitAnsH at hu
  split at hu <;> simp_all [stdoutOk, streamWrite, getStdout]

/-- `p2Ok` on the functions `wasi:io` does not classify is `cliOk`. -/
theorem p2Ok_of_other {f : FnName} {a : List Val} {r : Option (List Val)} (h : ioOp f = .other) :
    p2Ok (.imp f a r) = cliOk f r := by
  simp [p2Ok, h]

/-- A `get-stdout` answer admissible for `p2Ok` is well typed for the base WASI theory. -/
theorem stdoutOk_getStdout {a : List Val} {res : Option (List Val)}
    (hp : p2Ok (.imp getStdout a res) = true) : stdoutOk (.imp getStdout a res) = true := by
  have hx : ∃ x, res = some [.u32 x] := by
    have hc : cliOk getStdout res = true := p2Ok_of_other (f := getStdout) (by decide) ▸ hp
    simp only [cliOk_eq_hand, cliOkH, getStdout, cliExit, getEnv, getArgs, initialCwd, getStdin] at hc
    repeat' split at hc
    all_goals simp_all
  obtain ⟨x, rfl⟩ := hx
  simp [stdoutOk]

/-- A drop answer admissible for `p2Ok` is well typed for the base WASI theory. -/
theorem stdoutOk_drop {a : List Val} {res : Option (List Val)}
    (hp : p2Ok (.imp streamDrop a res) = true) : stdoutOk (.imp streamDrop a res) = true := by
  have hx : res = some [] := by
    have hc : cliOk streamDrop res = true := p2Ok_of_other (f := streamDrop) (by decide) ▸ hp
    simp only [cliOk_eq_hand, cliOkH, streamDrop, getStdout, cliExit, getEnv, getArgs, initialCwd, getStdin,
      getStderr, monoSubInstant, monoSubDuration, getTermStdin, getTermStdout, getTermStderr,
      monoRes, wallNow, wallRes, fdReadStream, fdWriteStream, fdAppendStream, fdGetType] at hc
    repeat' split at hc
    all_goals simp_all
  subst hx
  simp [stdoutOk, streamDrop, getStdout, streamWrite]

/-- One answer of an accepted WASI 0.2 sequence is well typed for the base WASI theory, unless it is a trapping
`blocking-write-and-flush`. -/
theorem stdoutOk_imp {r : Reading} {t : List WEv} (h : (p2Th r).Accepts t)
    (hnt : ∀ a, WEv.imp streamWrite a none ∉ t) {f : FnName} {a : List Val}
    {res : Option (List Val)} (he : WEv.imp f a res ∈ t) : stdoutOk (.imp f a res) = true := by
  have hp : p2Ok (.imp f a res) = true := p2_p2Ok h _ he
  by_cases hw : f = streamWrite
  · subst hw
    have hio : (ioTh r).Accepts t := ((Protocol.accepts_prod_iff _ _ _).1 h).1
    obtain ⟨s, hs⟩ := io_ansOk_of_mem hio he
    have hn : res ≠ none := fun hr => hnt a (hr ▸ he)
    exact stdoutOk_bwf (ioOp_bwf ▸ hs) hn
  by_cases hg : f = getStdout
  · exact hg ▸ stdoutOk_getStdout (hg ▸ hp)
  by_cases hd : f = streamDrop
  · exact hd ▸ stdoutOk_drop (hd ▸ hp)
  simp [stdoutOk, hg, hw, hd]

/-- **The WASI 0.2 theory is well typed for the base WASI theory's stdout theory**, when no
`blocking-write-and-flush` traps. -/
theorem p2_stdoutTyped {r : Reading} {t : List WEv} (h : (p2Th r).Accepts t)
    (hnt : ∀ a, WEv.imp streamWrite a none ∉ t) : stdoutTyped.Accepts t := by
  refine (pointwise_accepts_iff stdoutOk t).2 fun e he => ?_
  cases e
  case imp f a res => exact stdoutOk_imp h hnt he
  all_goals rfl

/-- A trapping `blocking-write-and-flush` of 4097 bytes. -/
def bwfTrap : List WEv := [.imp streamWrite [.u32 0, bytesV (List.replicate 4097 0)] none]

/-- **The proviso of `p2_stdoutTyped` is needed**: the WASI 0.2 theory admits a trap on an
oversized `blocking-write-and-flush`. -/
theorem p2_bwf_trap : (p2Th .strict).Accepts bwfTrap :=
  (Protocol.acceptsB_iff _ _).1 (by decide +kernel)

/-- the base WASI theory's stdout theory rejects it. -/
theorem not_stdoutTyped_bwfTrap : ¬ stdoutTyped.Accepts bwfTrap := fun h =>
  absurd ((Protocol.acceptsB_iff _ _).2 h) (by decide +kernel)

end Silmaril.Wasi.Versions.P2
