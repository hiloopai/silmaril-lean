module

public import Silmaril.Apps.Sha256sum.Binary.Image
public import Silmaril.Process.CLI.X86Linux8

/-! # Coverage of `sha256sum-min` by the `Ext8` variant

`walk` is the linear sweep that `Process.CLI.X86Linux8.step` performs on a byte
string: `syscall` (`0F 05`) first, then `X86.Ext8.decode`. `textInstrs` is the
whole executable segment of `sha256sum-min` (`PT_LOAD` 1, 17355 bytes at
`0x401000`, which is exactly `.text`), decoded instruction by instruction:

* `walk_text`: the sweep consumes **every byte** of the segment, in 4003
  instructions (the count `objdump -d` gives);
  27 of them are forms that `X86.Ext` lacks and the variant adds, and one is
  `syscall`; the other 3975 are `X86.Ext` instructions;
* `ext_walk_text_fails`: `X86.Ext` alone stops (first at `and %dl,0x32(%rsp)`,
  `0x401f12`), so the variant is needed.

Since every instruction boundary of `.text` decodes, and all of the program's code is
in `.text`, every reachable instruction is in the model: coverage is 100% of the
reachable code (which is a subset of the sweep).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Ext8Cover

open Silmaril.X86 (Byte)

/-- What the sweep reads at an offset. -/
inductive Item where
  | syscall
  | base
  | new
  deriving DecidableEq, Repr

/-- The linear sweep: `syscall` first, then the variant's decoder. -/
def walk : Nat → List Byte → Option (List (Item × Nat))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bytes =>
    if bytes.take 2 = Silmaril.Process.CLI.X86Linux.syscallBytes then
      (walk fuel (bytes.drop 2)).map ((.syscall, 2) :: ·)
    else
      match Silmaril.X86.Ext8.decode bytes with
      | none => none
      | some (i, n) =>
        if n = 0 then none
        else
          let it : Item := match i with | .base _ => .base | .new _ => .new
          (walk fuel (bytes.drop n)).map ((it, n) :: ·)

/-- The same sweep with `X86.Ext` only. -/
def extWalk : Nat → List Byte → Option Nat
  | _, [] => some 0
  | 0, _ => none
  | fuel + 1, bytes =>
    if bytes.take 2 = Silmaril.Process.CLI.X86Linux.syscallBytes then
      (extWalk fuel (bytes.drop 2)).map (· + 1)
    else
      match Silmaril.X86.Ext.decode bytes with
      | none => none
      | some (_, n) => if n = 0 then none else (extWalk fuel (bytes.drop n)).map (· + 1)

/-- The bytes of the executable segment (`.text`). -/
def text : List Byte := Image.seg1.fileBytes

/-- A successful sweep accounts for every byte. -/
theorem sum_walk : ∀ (fuel : Nat) {bytes : List Byte} {items : List (Item × Nat)},
    walk fuel bytes = some items → (items.map (·.2)).sum = bytes.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes items h
    cases bytes with
    | nil => simp [walk] at h; subst h; rfl
    | cons b t => simp [walk] at h
  | succ fuel ih =>
    intro bytes items h
    cases bytes with
    | nil => simp [walk] at h; subst h; rfl
    | cons b t =>
      simp only [walk] at h
      split at h
      · rename_i hs
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨rest, hr, rfl⟩ := h
        have := ih hr
        have h2 : 2 ≤ (b :: t).length := by
          have := congrArg List.length hs
          simp [Silmaril.Process.CLI.X86Linux.syscallBytes] at this
          simp; omega
        simp [this] at *
        omega
      · split at h
        · simp at h
        · rename_i i n hd
          split at h
          · simp at h
          · simp only [Option.map_eq_some_iff] at h
            obtain ⟨rest, hr, rfl⟩ := h
            have := ih hr
            have hn : n ≤ (b :: t).length := by
              unfold Silmaril.X86.Ext8.decode at hd
              split at hd
              · rename_i i' n' he
                simp only [Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨-, rfl⟩ := hd
                exact (Silmaril.X86.Ext.decode_length he).2.2.2
              · simp only [Option.map_eq_some_iff] at hd
                obtain ⟨⟨j, m⟩, hj, he⟩ := hd
                simp only [Prod.mk.injEq] at he
                obtain ⟨-, rfl⟩ := he
                unfold Silmaril.X86.Ext8.decodeNew at hj
                split at hj
                · split at hj
                  · simp at hj
                  · simp only [Option.map_eq_some_iff] at hj
                    obtain ⟨_, -, he⟩ := hj
                    simp only [Prod.mk.injEq] at he
                    omega
                · simp at hj
            simp [this] at *
            omega

theorem length_text : text.length = 17355 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The sweep of `.text`, checked by the kernel (about 35 s). -/
theorem walk_text_check : (match walk 17355 text with
    | some l => l.length == 4003 && (l.filter (·.1 = .new)).length == 27 &&
        (l.filter (·.1 = .syscall)).length == 1
    | none => false) = true := by decide +kernel

/-- **Coverage**: the sweep reads all of `.text`, in 4003 instructions, 27 of
them new forms and one `syscall`. -/
theorem walk_text : ∃ items, walk 17355 text = some items ∧ items.length = 4003 ∧
    (items.map (·.2)).sum = 17355 ∧
    (items.filter (·.1 = .new)).length = 27 ∧ (items.filter (·.1 = .syscall)).length = 1 := by
  have h := walk_text_check
  cases hw : walk 17355 text with
  | none => rw [hw] at h; simp at h
  | some l =>
    rw [hw] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨l, rfl, h.1.1, (sum_walk _ hw).trans length_text, h.1.2, h.2⟩

set_option maxRecDepth 100000 in
/-- `X86.Ext` alone does not cover `.text`. -/
theorem ext_walk_text_fails : extWalk 17355 text = none := by decide +kernel

end Silmaril.Apps.Sha256sum.Binary.Ext8Cover
