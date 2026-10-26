module

public import Silmaril.Process.LPS.NativeX86All
public import Silmaril.Process.LPS.NativeX86Budget

/-! # One x86-64 refusal and allocation-budget dispatch, one x86-64 `access_ok`

The lanes left two x86-64 readings of LPS `Run.v`'s refusal machinery: the memory-management
lane's hard-coded `MmRunX86` (`allocBudgetRefusedBX86`, `mmInjectedTableX86`,
`mmRefusalBX86`, alloc rows only) and #3476's renumbering adapters (`NativeX86.allocBudgetRefusedB`,
`NativeX86.refusalFilter`), which go through the native catalogue `NativeX86.numbers` to LPS's
own `allocBudgetRefusedB`, `injectedTable`, `refusalB` and `spuriousRefusalCfg`. This module
keeps the renumbering form as the definition and proves the hard-coded one equal to it:

* `NativeX86.allocBudgetRefusedBX86_eq` (in `NativeX86Budget`): the budget dispatchers agree on
  every input;
* `mmRefusalBX86_eq`: `MmRunX86`'s `refusal_b` is `refusalBX86` on the alloc rows;
* `mmInjectedTableX86_eq`: `MmRunX86`'s rows are the alloc rows of `injectedTableX86`, the
  renumbering of all of LPS's `injected_table`;
* `spuriousRefusalCfgX86` is `spurious_refusal_cfg` at native numbers, with the **native**
  table's specification in its existential (the reference adapter `NativeX86.refusalFilter`
  takes the riscv64 one); `refusalFilter_eq` shows the adapter is the instance at the
  renumbered reference specification.

The two `access_ok` spellings (`Uaccess.accessOkbX86` and
`accessOkbFor x86AddressSpace`) agree on every length a call can pass, an `unsigned long`
(`accessOkbX86_uns`, `accessOkbX86_nat`).

Calls outside the catalogue (the extensions) have no injected-failure family in LPS. Two
readings exist. `spuriousRefusalCfgX86` never refuses them, which only keeps behaviours (a
filter removes behaviours): a statement must then hold even when `fork` spuriously answers
`EAGAIN`, which LPS's reading excludes for `clone`. `spuriousRefusalCfgX86Ext` gives each
extension the injected family of the reference call whose kernel path it is
(`extensionRefusalNo`): `open`/`creat` are `do_sys_open` (`openat`), `access` is
`do_faccessat` (`faccessat`), `unlink`/`rmdir` are `do_unlinkat`/`do_rmdir` (`unlinkat`),
`pipe` is `do_pipe2` (`pipe2`), `fork`/`vfork` are `kernel_clone` (`clone`). The other
extensions share a path with a reference call that has no injected family (`stat`, `lstat`,
`getdents`, `readlink`, `dup2`, `poll`, `select`, `epoll_create`, `epoll_wait`, `eventfd`,
`getrlimit`) or none (`arch_prctl`), so both readings agree on them. The extended filter
refuses at least what the catalogue-only one refuses (`spuriousRefusalCfgX86_le_ext`), so the
catalogue-only reading is the weaker lattice point and every statement proved under it holds
under the extended one; `system` uses the extended reading, `systemCatalogue` the other.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.All

open Silmaril.Process.LPS

/-- LPS `Run.v:1358` `injected_table` at native numbers. -/
def injectedTableX86 : List InjectedArm :=
  injectedTable.filterMap fun a =>
    (numbers.find? (·.referenceNo = a.no)).map fun row => { a with no := row.nativeNo }

/-- LPS `Run.v:1418` `refusal_b` at a native number. -/
def refusalBX86 (i : SyscallInput) (m : Model) (ret : Word) : Bool :=
  match referenceInput i with
  | some source => refusalB source m ret
  | none => false

/-- LPS `Run.v:1533` `injected_family_off` at a native number. -/
def injectedFamilyOffX86 (cfg : SpuriousCfg) (i : SyscallInput) : Bool :=
  match referenceInput i with
  | some source => injectedFamilyOff cfg source
  | none => false

/-- LPS `Run.v:1544` `spurious_refusal_cfg` at native numbers, over a native specification. -/
def spuriousRefusalCfgX86 (spec : Sys SyscallEffect) (cfg : SpuriousCfg) : RefusalFilter :=
  fun i m eff =>
    injectedFamilyOffX86 cfg i = true ∧ refusalBX86 i m eff.ret = true ∧
      ∃ eff' m' evs', spec i m (.ok eff' m' evs') ∧ refusalBX86 i m eff'.ret = false

/-- The renumbered reference specification, `unmodeled` off the catalogue. -/
def renumbered (reference : Sys SyscallEffect) : Sys SyscallEffect := fun i =>
  match referenceInput i with
  | some source => reference source
  | none => Sys.unmodeled i

/-- #3476's reference adapter is the native reading at the renumbered reference spec. -/
theorem refusalFilter_eq (reference : Sys SyscallEffect) (cfg : SpuriousCfg)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    refusalFilter reference cfg i m eff ↔
      spuriousRefusalCfgX86 (renumbered reference) cfg i m eff := by
  unfold refusalFilter spuriousRefusalCfgX86 renumbered injectedFamilyOffX86 refusalBX86
  cases referenceInput i with
  | none => simp
  | some source => simp [spuriousRefusalCfg]

/-- Off the catalogue nothing is refused. -/
theorem spuriousRefusalCfgX86_extension (spec : Sys SyscallEffect) (cfg : SpuriousCfg)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (h : referenceInput i = none) :
    ¬ spuriousRefusalCfgX86 spec cfg i m eff := by
  simp [spuriousRefusalCfgX86, injectedFamilyOffX86, h]

/-- A stronger reading refuses more (LPS `scfg` monotonicity, at native numbers). -/
theorem spuriousRefusalCfgX86_le_noFilter (spec : Sys SyscallEffect) (cfg : SpuriousCfg)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    noFilter i m eff → spuriousRefusalCfgX86 spec cfg i m eff := fun h => h.elim

/-- `MmRunX86`'s rows are the alloc rows of the renumbered LPS table, in order. -/
theorem mmInjectedTableX86_eq :
    mmInjectedTableX86.map (fun a => (a.no, a.errnos)) =
      (injectedTableX86.filter (fun a => a.no ∈ allocMarkSysnosX86)).map
        (fun a => (a.no, a.errnos)) := by
  decide +kernel

theorem mmInjectedTableX86_alloc : ∀ a ∈ mmInjectedTableX86, a.family = .alloc := by decide

theorem injectedTableX86_alloc_rows :
    ∀ a ∈ injectedTableX86, a.no ∈ allocMarkSysnosX86 → a.family = .alloc := by decide +kernel

/-- `MmRunX86`'s `refusal_b` is `refusalBX86` at every alloc number. -/
theorem mmRefusalBX86_eq (i : SyscallInput) (m : Model) (ret : Word)
    (h : i.sysno.toNat ∈ allocMarkSysnosX86) : mmRefusalBX86 i m ret = refusalBX86 i m ret := by
  have word {k : Nat} (hk : k < 2 ^ 64) (h : i.sysno.toNat = k) : i.sysno = BitVec.ofNat 64 k :=
    BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk])
  simp only [allocMarkSysnosX86, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · simp only [mmRefusalBX86, refusalBX86, referenceInput, word (by decide) h]; rfl
  · simp only [mmRefusalBX86, refusalBX86, referenceInput, word (by decide) h]; rfl
  · simp only [mmRefusalBX86, refusalBX86, referenceInput, word (by decide) h]; rfl
  · simp only [mmRefusalBX86, refusalBX86, referenceInput, word (by decide) h]; rfl

/-! ## Injected families for the extensions -/

/-- The reference (riscv64) number whose injected-failure family an x86-64 extension shares:
the call whose kernel path the extension takes. -/
def extensionRefusalNo : Nat → Option Nat
  | 2 => some 56 | 85 => some 56
  | 21 => some 48
  | 84 => some 35 | 87 => some 35
  | 22 => some 59
  | 57 => some 220 | 58 => some 220
  | _ => none

/-- Each mapped extension is an extension arm, and its target is the catalogue row named. -/
theorem extensionRefusalNo_rows :
    [(2, "open", "openat"), (85, "creat", "openat"), (21, "access", "faccessat"),
      (84, "rmdir", "unlinkat"), (87, "unlink", "unlinkat"), (22, "pipe", "pipe2"),
      (57, "fork", "clone"), (58, "vfork", "clone")].all (fun (no, ext, ref) =>
        ((lookupArm extensionArms no).map (·.name) == some ext) &&
          ((extensionRefusalNo no).bind (fun r => (numbers.find? (·.referenceNo = r)).map
            (·.name)) == some ref)) = true := by
  decide +kernel

/-- Exactly these eight extensions get a family, and each target has one in LPS's
`injected_table`. -/
theorem extensionRefusalNo_injected :
    (armNumbers extensionArms).filter (fun n => (extensionRefusalNo n).isSome) =
        [2, 21, 85, 84, 87, 22, 57, 58] ∧
      [56, 48, 35, 59, 220].all (fun r => (injectedArm r).isSome) = true := by
  decide +kernel

/-- The input whose refusal family a native call has: the renumbered reference input in the
catalogue, the shared reference call for a mapped extension. Only the number changes;
`refusal_b` reads arguments only for `brk`, which no extension maps to. -/
def refusalInputExt (i : SyscallInput) : Option SyscallInput :=
  match referenceInput i with
  | some source => some source
  | none => (extensionRefusalNo i.sysno.toNat).map fun r => { i with sysno := zw r }

/-- `refusal_b` with the extensions' families. -/
def refusalBX86Ext (i : SyscallInput) (m : Model) (ret : Word) : Bool :=
  match refusalInputExt i with
  | some source => refusalB source m ret
  | none => false

/-- `injected_family_off` with the extensions' families. -/
def injectedFamilyOffX86Ext (cfg : SpuriousCfg) (i : SyscallInput) : Bool :=
  match refusalInputExt i with
  | some source => injectedFamilyOff cfg source
  | none => false

/-- `spurious_refusal_cfg` at native numbers with the extensions' families. -/
def spuriousRefusalCfgX86Ext (spec : Sys SyscallEffect) (cfg : SpuriousCfg) : RefusalFilter :=
  fun i m eff =>
    injectedFamilyOffX86Ext cfg i = true ∧ refusalBX86Ext i m eff.ret = true ∧
      ∃ eff' m' evs', spec i m (.ok eff' m' evs') ∧ refusalBX86Ext i m eff'.ret = false

/-- On the catalogue the two readings coincide. -/
theorem spuriousRefusalCfgX86Ext_catalogue (spec : Sys SyscallEffect) (cfg : SpuriousCfg)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (source : SyscallInput)
    (h : referenceInput i = some source) :
    spuriousRefusalCfgX86Ext spec cfg i m eff ↔ spuriousRefusalCfgX86 spec cfg i m eff := by
  simp [spuriousRefusalCfgX86Ext, spuriousRefusalCfgX86, injectedFamilyOffX86Ext,
    injectedFamilyOffX86, refusalBX86Ext, refusalBX86, refusalInputExt, h]

/-- The extended filter refuses at least what the catalogue-only one does. -/
theorem spuriousRefusalCfgX86_le_ext (spec : Sys SyscallEffect) (cfg : SpuriousCfg)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : spuriousRefusalCfgX86 spec cfg i m eff) : spuriousRefusalCfgX86Ext spec cfg i m eff := by
  cases e : referenceInput i with
  | none => exact absurd h (spuriousRefusalCfgX86_extension spec cfg i m eff e)
  | some source => exact (spuriousRefusalCfgX86Ext_catalogue spec cfg i m eff source e).2 h

/-- A mapped extension is filtered as its reference call is (for instance `fork` as `clone`). -/
theorem spuriousRefusalCfgX86Ext_extension (spec : Sys SyscallEffect) (cfg : SpuriousCfg)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (r : Nat)
    (hnone : referenceInput i = none) (hr : extensionRefusalNo i.sysno.toNat = some r) :
    spuriousRefusalCfgX86Ext spec cfg i m eff ↔
      injectedFamilyOff cfg { i with sysno := zw r } = true ∧
        refusalB { i with sysno := zw r } m eff.ret = true ∧
        ∃ eff' m' evs', spec i m (.ok eff' m' evs') ∧
          refusalB { i with sysno := zw r } m eff'.ret = false := by
  simp [spuriousRefusalCfgX86Ext, injectedFamilyOffX86Ext, refusalBX86Ext, refusalInputExt,
    hnone, hr]

/-! ## `access_ok` -/

/-- The lanes' x86-64 `access_ok` is the profile check on every `unsigned long` length. -/
theorem accessOkbX86_uns (base len : Word) :
    accessOkbX86 base (uns len) = accessOkbFor x86AddressSpace base (uns len) :=
  accessOkbX86_eq_accessOkbFor base _ (Int.natCast_nonneg _)
    (by unfold uns twoPow64; exact_mod_cast len.isLt)

theorem accessOkbX86_nat (base : Word) (len : Nat) (h : len < 2 ^ 64) :
    accessOkbX86 base len = accessOkbFor x86AddressSpace base len :=
  accessOkbX86_eq_accessOkbFor base _ (Int.natCast_nonneg _)
    (by unfold twoPow64; exact_mod_cast h)

/-! ## The native system -/

/-- The catalogue-only x86-64 refusal reading: none in the plain reading, LPS's spurious
refusals at native numbers over the native table in an environment reading, never for an
extension. -/
def refusalsCatalogue : Option SpuriousCfg → RefusalFilter
  | none => noFilter
  | some cfg => spuriousRefusalCfgX86 (dispatch nativeTable) cfg

/-- The x86-64 refusal reading of a statement: as `refusalsCatalogue`, with the extensions'
families (`spuriousRefusalCfgX86Ext`). -/
def refusals : Option SpuriousCfg → RefusalFilter
  | none => noFilter
  | some cfg => spuriousRefusalCfgX86Ext (dispatch nativeTable) cfg

/-- `refusals` refuses at least what `refusalsCatalogue` refuses. -/
theorem refusalsCatalogue_le (reading : Option SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : refusalsCatalogue reading i m eff) : refusals reading i m eff := by
  cases reading with
  | none => exact h
  | some cfg => exact spuriousRefusalCfgX86_le_ext _ cfg i m eff h

/-- The complete native system: all ninety reference slots and the twenty extensions, with
boundary, configuration and version chaos, and the native refusal reading. -/
def system (reading : Option SpuriousCfg) : System :=
  ⟨nativeTable, nativeTable_numbers_nodup, refusals reading⟩

/-- The same system with the catalogue-only refusal reading (the weaker lattice point). -/
def systemCatalogue (reading : Option SpuriousCfg) : System :=
  ⟨nativeTable, nativeTable_numbers_nodup, refusalsCatalogue reading⟩

theorem system_spec (reading : Option SpuriousCfg) : (system reading).spec = dispatch nativeTable := rfl

end Silmaril.Process.LPS.NativeX86.All
