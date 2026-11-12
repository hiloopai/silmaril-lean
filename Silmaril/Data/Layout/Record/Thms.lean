module

public import Silmaril.Data.Layout.Record.Defs
public import Silmaril.Data.Layout.Thms
import Silmaril.Proofs.Data.Layout.Record

/-!
# Resolved record layouts: well-formedness, names, targets

PROVED in `Silmaril.Proofs.Data.Layout.Record`:

* `resolveEnv_wf`: under a well-formed data model every resolved layout is
  `RecordLayout.WF` (from `declLayout_wf`).
* `resolveEnv_names`: resolved layouts have the kinds, names and member names of the source
  declarations, in order.

Here: the five targets of the existing data models with the Clang triples they are compared
against, and what `Agrees` gives about each member.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Record

open Silmaril.Data.Layout

theorem resolveEnv_wf {dm : DataModel} (hdm : dm.WF) {env : Env} {Ls : List RecordLayout}
    (h : resolveEnv dm env = .ok Ls) : ∀ R ∈ Ls, R.WF :=
  Silmaril.Proofs.Data.Layout.Record.resolveEnv_wf hdm h

theorem resolveEnv_names {dm : DataModel} {env : Env} {Ls : List RecordLayout}
    (h : resolveEnv dm env = .ok Ls) : Ls.map layoutNames = env.map declNames :=
  Silmaril.Proofs.Data.Layout.Record.resolveEnv_names h

/-- The certificate form used by `c_layout`. -/
theorem resolveEnv_of_toOption {dm : DataModel} {env : Env} {Ls : List RecordLayout}
    (h : (resolveEnv dm env).toOption = some Ls) : resolveEnv dm env = .ok Ls := by
  cases hr : resolveEnv dm env <;> simp_all [Except.toOption]

/-- An agreeing observation reports every member of every computed record at its computed
offset, in bits. -/
theorem Agrees.field {Ls : List RecordLayout} {obs : List ObservedRecord} (h : Agrees Ls obs)
    {R : RecordLayout} (hR : R ∈ Ls) {e : Entry} (he : e ∈ R.entries) :
    ∃ o ∈ obs, o.kind = R.kind ∧ o.name = R.name ∧ o.size = 8 * R.size ∧
      o.align = 8 * R.align ∧ { name := e.name, offset := 8 * e.offset } ∈ o.fields := by
  subst h
  exact ⟨R.observe, List.mem_map_of_mem hR, rfl, rfl, rfl, rfl,
    List.mem_map_of_mem
      (f := fun e : Entry => ({ name := e.name, offset := 8 * e.offset } : ObservedField)) he⟩

/-! ## Targets -/

def Target.x86_64 : Target := ⟨"x86_64", sysvX86_64, sysvX86_64_wf, "x86_64-unknown-linux-gnu"⟩
def Target.i386 : Target := ⟨"i386", i386Ilp32, i386Ilp32_wf, "i386-unknown-linux-gnu"⟩
def Target.aarch64 : Target := ⟨"aarch64", aapcs64, aapcs64_wf, "aarch64-unknown-linux-gnu"⟩
def Target.riscv64 : Target := ⟨"riscv64", rv64Lp64, rv64Lp64_wf, "riscv64-unknown-linux-gnu"⟩
def Target.wasm32 : Target := ⟨"wasm32", Layout.wasm32, wasm32_wf, "wasm32-unknown-unknown"⟩

end Silmaril.Data.Layout.Record
