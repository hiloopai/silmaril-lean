module

public import Silmaril.Elf.Link.Dyn.Proc.Thms
public import Silmaril.Elf.Link.Dyn.Image.Thms

/-! # The process machine always has an outcome (`Progress`)

The library contracts of `Proc` are relations; a contract whose postcondition could not be
met would make the machine stuck there, and every `Must` statement through it vacuous. This
file shows that this does not happen: **every state of `proc W` has an outcome**
(`proc_progress`), provided the executable's image leaves address space for a stack
(`W.base.toNat + W.size ≤ 2^62`, and the argument area below `2^62`), the lazy-binding slot list is not absurdly long, and the
`named` contracts (if any) have outcomes. Each contract's postcondition is met by an explicit
state: a System V return (`puts`, `__cxa_finalize`), the library resuming at the gate
(`__libc_start_main`, `exit`, the exit jobs), a callback on a freshly mapped stack
(`exists_stack`), the resolver's binding of the slot, and the end of the process.

With `RelIsa.Must.exists_run`, a `Must` theorem about `proc W` therefore yields an actual run
(`run_of_must`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.RelIsa (Res Must)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)

/-- A fresh stack: a new mapping of two pages around `sp`, outside the image, whose top word
is `v`. -/
theorem exists_stack (W : World) (hW : W.base.toNat + W.size ≤ 2 ^ 62)
    (hA : ∀ a, W.args a ∨ W.tls a → a < 2 ^ 62) (mem : Memory) (v : Word) :
    ∃ sp : Word, ∃ mem' : Memory, sp.toNat % 16 = 8 ∧
      mem'.readBytes sp.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) ∧
      StackRoom W mem' sp ∧ Keeps W.Kept mem mem' := by
  -- a stack page above the image and the argument area
  obtain ⟨sp, hsp, hlo, hhi, hfar⟩ : ∃ sp : Word, sp.toNat % 16 = 8 ∧ 4096 ≤ sp.toNat ∧
      sp.toNat + 4096 < 2 ^ 64 ∧ ∀ a, sp.toNat - 4096 ≤ a → a < sp.toNat + 4096 → ¬ W.Kept a := by
    refine ⟨BitVec.ofNat 64 (2 ^ 63 + 8), by decide, by decide, by decide, fun a h1 h2 h => ?_⟩
    simp only [BitVec.toNat_ofNat] at h1 h2
    rcases h with h | h | h
    · simp only [World.InImage] at h; omega
    · have := hA a (Or.inl h); omega
    · have := hA a (Or.inr h); omega
  let R : Region := ⟨sp.toNat - 4096, 8192, ⟨true, true, false⟩⟩
  let mem' : Memory := ⟨R :: mem.regions,
    Memory.install mem.bytes sp.toNat (Silmaril.Machine.LittleEndian.encodeWords [v])⟩
  have hperm : ∀ acc, acc = Access.read ∨ acc = Access.write → ∀ a, sp.toNat - 4096 ≤ a →
      a < sp.toNat + 4096 → mem'.permits acc a = true := by
    intro acc hacc a h1 h2
    simp only [Memory.permits, mem', List.any_cons, Bool.or_eq_true]
    left
    rcases hacc with rfl | rfl <;> simp [R, Region.Contains, Permissions.allows] <;> omega
  refine ⟨sp, mem', hsp, ?_, ⟨hlo, by omega, fun a h1 h2 => ⟨hperm _ (Or.inl rfl) a h1 (by omega),
    hperm _ (Or.inr rfl) a h1 (by omega), hfar a h1 (by omega)⟩⟩, ?_⟩
  · have := readWith_of_points (mem := mem') (acc := .read)
      (l := Silmaril.Machine.LittleEndian.encodeWords [v]) (a := sp.toNat) (by simp; omega) (by omega)
      (fun k hk => by
        simp only [Silmaril.X86.length_encodeWords_singleton] at hk
        exact ⟨hperm _ (Or.inl rfl) _ (by omega) (by omega),
          Memory.install_get _ _ _ _ (by simpa using hk)⟩)
    simpa [Memory.readBytes] using this
  · intro a ha
    have hout : ¬ (sp.toNat - 4096 ≤ a ∧ a < sp.toNat + 4096) := fun h => hfar a h.1 h.2 ha
    refine ⟨Memory.install_outside _ _ _ _ (by simp; omega), fun acc => ?_⟩
    simp only [Memory.permits, mem', List.any_cons]
    have : (decide (R.Contains a) && R.permissions.allows acc) = false := by
      simp only [R, Region.Contains]; simp; omega
    rw [this, Bool.false_or]

/-- The System V return from a call entered at `s`, with `rax := v`. -/
def retState (s : PState) (v : Word) (g : Ghost) : PState :=
  ⟨⟨{ ((s.m.core.write .rsp (s.m.core.read .rsp + 8#64)).write .rax v) with
      rip := retOf s.m.core s.m.memory }, s.m.memory⟩, g⟩

theorem retState_returns (W : World) (s : PState) (v : Word) (g : Ghost) :
    Returns W s (retState s v g) := by
  refine ⟨⟨rfl, ?_, ?_⟩, Keeps.refl _ _⟩
  · simp [retState]
  · intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [retState]

/-- The library resuming at the gate. -/
def gateState (W : World) (s : PState) (g : Ghost) : PState :=
  ⟨⟨{ s.m.core with rip := W.gate }, s.m.memory⟩, g⟩

theorem gateState_at (W : World) (s : PState) (g : Ghost) : AtGate W s (gateState W s g) :=
  ⟨rfl, Keeps.refl _ _, rfl⟩

/-- A callback of `f` with arguments `a1 a2 a3` on a fresh stack. -/
theorem exists_enters (W : World) (hW : W.base.toNat + W.size ≤ 2 ^ 62)
    (hA : ∀ a, W.args a ∨ W.tls a → a < 2 ^ 62) (s : PState) (f a1 a2 a3 : Word)
    (g : Ghost) : ∃ t, Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = g := by
  obtain ⟨sp, mem', h1, h2, h3, h4⟩ := exists_stack W hW hA s.m.memory W.gate
  refine ⟨⟨⟨{ ((((s.m.core.write .rsp sp).write .rdi a1).write .rsi a2).write .rdx a3) with rip := f },
    mem'⟩, g⟩, ⟨rfl, ?_, ?_, ?_, h4, rfl⟩, by simp, by simp, by simp, rfl⟩
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem loadN_encode {m : Memory} {a v : Word}
    (h : m.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    Silmaril.X86.Ext.loadN m a 8 = some v := by
  rw [← Silmaril.X86.Ext.leBytes_eight] at h
  simp only [Silmaril.X86.Ext.loadN, h, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt v.isLt]

/-- The resolver's binding: the slot holds `e.2` and control is at `e.2` with the caller's
stack. -/
theorem exists_resolved (W : World) (s : PState) (e : Nat × Word) (hpre : SlotRW W e s) :
    ∃ t, ResPost W e s t := by
  obtain ⟨a, ha⟩ : ∃ a, (W.base + BitVec.ofNat 64 e.1).toNat = a := ⟨_, rfl⟩
  let mem' : Memory := ⟨s.m.memory.regions,
    Memory.install s.m.memory.bytes a (Silmaril.Machine.LittleEndian.encodeWords [e.2])⟩
  have hr := hpre.1
  rw [ha, Memory.Permitted, Memory.checkSpan_iff] at hr
  refine ⟨⟨⟨{ s.m.core.write .rsp (s.m.core.read .rsp + 16#64) with rip := e.2 }, mem'⟩, s.g⟩,
    rfl, by simp, ?_, ?_, ?_, fun _ _ _ _ => rfl, rfl, fun _ _ _ _ => rfl⟩
  · intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply loadN_encode
    show mem'.readWith .read (W.base + BitVec.ofNat 64 e.1).toNat 8 = _
    rw [ha]
    have := readWith_of_points (mem := mem') (acc := .read)
      (l := Silmaril.Machine.LittleEndian.encodeWords [e.2]) (a := a)
      (by rw [Silmaril.X86.length_encodeWords_singleton]; exact hr.2.1)
      hr.1 (fun k hk => by
        simp only [Silmaril.X86.length_encodeWords_singleton] at hk
        exact ⟨hr.2.2 k hk, Memory.install_get _ _ _ _ (by simpa using hk)⟩)
    rwa [Silmaril.X86.length_encodeWords_singleton] at this
  · intro x hx
    rw [ha] at hx
    refine ⟨Memory.install_outside _ _ _ _ (by simp only [Silmaril.X86.length_encodeWords_singleton]; omega),
      fun _ => rfl⟩

/-- **Every contract can be met, so the machine always has an outcome** (given that `main` can
be entered with the library's guarantee `World.atMain`, `hM`). -/
theorem proc_progressM (W : World) (hW : W.base.toNat + W.size ≤ 2 ^ 62)
    (hA : ∀ a, W.args a ∨ W.tls a → a < 2 ^ 62)
    (hslots : ∀ res slots, W.lazy = some (res, slots) → slots.length ≤ 2 ^ 64)
    (hN : ∀ n s, ∃ r, W.named n s r)
    (hM : ∀ s f a1 a2 a3 g, ∃ t, Enters W s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = g ∧ W.atMain t)
    (hK : ∀ s f g, ∃ t, Enters W s t f ∧ t.g = g ∧ W.atCall t)
    (hP : ∀ s, ∃ p, W.pending s p) (hG0 : ∀ s t, W.atGate s t := by intro _ _; trivial) :
    Silmaril.X86.RelIsa.Progress (proc W) := by
  intro s _
  simp only [proc, step]
  cases hd : s.g.done with
  | some _ => exact ⟨.stop, rfl⟩
  | none =>
    simp only
    by_cases hin : W.InImage s.m.core.rip.toNat
    · simp only [hin, ↓reduceIte]
      cases Silmaril.X86.Open9.step s.m with
      | some m' => exact ⟨_, rfl⟩
      | none => exact ⟨.stop, rfl⟩
    · simp only [hin, ↓reduceIte]
      -- the library: every contract has a state meeting its postcondition
      have hC : ∀ {pre : Prop} {post : PState → Prop}, (pre → ∃ t, post t) → ∃ r, Contract pre post r := by
        intro pre post h
        by_cases hp : pre
        · obtain ⟨t, ht⟩ := h hp; exact ⟨.ok t, fun _ => ⟨t, rfl, ht⟩⟩
        · exact ⟨.stop, fun h => absurd h hp⟩
      have hfn : ∀ f, ∃ r, fnStep W f s r := by
        intro f
        cases f with
        | puts =>
          exact hC fun ⟨_, str, hstr⟩ => ⟨retState s 0 { s.g with out := s.g.out ++ str ++ [10] },
            retState_returns W s 0 _, str, hstr, rfl, rfl, hd, ⟨rfl, rfl⟩,
            Or.inl ⟨rfl, by simp [retState, low32]⟩⟩
        | libcStartMain => exact hC fun _ => ⟨gateState W s _, gateState_at W s _, rfl⟩
        | cxaFinalize => exact hC fun _ => ⟨retState s 0 s.g, retState_returns W s 0 _, rfl, rfl⟩
        | exit => exact hC fun _ => ⟨gateState W s _, gateState_at W s _, rfl⟩
        | named n => exact hN n s
      have hfns : ∃ r, (match W.fns.find? (·.1 == s.m.core.rip) with
          | some (_, f) => fnStep W f s r
          | none => r = .stop) := by
        cases W.fns.find? (·.1 == s.m.core.rip) with
        | none => exact ⟨.stop, rfl⟩
        | some p => exact hfn p.2
      unfold extStep
      by_cases hg : s.m.core.rip = W.gate
      · simp only [hg, ↓reduceIte]
        unfold gateStep
        cases hj : s.g.jobs with
        | nil => exact ⟨.stop, trivial⟩
        | cons j js =>
          cases j with
          | call f a1 a2 a3 =>
            exact hC fun _ => exists_enters W hW hA s f a1 a2 a3 _
          | call0 f => exact hC fun _ =>
              (hK s f { s.g with jobs := js }).elim fun t h => ⟨t, h.1, h.2.1, h.2.2, hG0 s t⟩
          | main f a1 a2 a3 => exact hC fun _ => hM s f a1 a2 a3 _
          | exitRax =>
            exact hC fun _ => (hP s).elim fun p hp => ⟨gateState W s _, p, hp, gateState_at W s _, rfl, hG0 _ _⟩
          | exit st => exact hC fun _ => ⟨gateState W s _, gateState_at W s _, rfl, hG0 _ _⟩
          | halt st => exact hC fun _ => ⟨gateState W s { s.g with jobs := [], done := some (st.toNat % 256, s.g.out) },
              s.g.out, List.prefix_refl _, fun _ => rfl, rfl⟩
      · simp only [hg, ↓reduceIte]
        cases hl : W.lazy with
        | none => exact hfns
        | some p =>
          obtain ⟨res, slots⟩ := p
          simp only
          by_cases hr : s.m.core.rip = res
          · simp only [hr, ↓reduceIte]
            have hlen := hslots res slots hl
            unfold resolveStep
            cases hv : Silmaril.X86.Ext.loadN s.m.memory (s.m.core.read .rsp + 8#64) 8 with
            | none => exact ⟨.stop, fun j hj => by cases hj⟩
            | some v =>
              -- the only index the word can name
              have huniq : ∀ j, BitVec.ofNat 64 j = v → j < slots.length → j = v.toNat := by
                intro j hj hjl
                rw [← hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              by_cases hj0 : v.toNat < slots.length
              · obtain ⟨r, hr'⟩ := hC (pre := SlotRW W slots[v.toNat] s) (post := ResPost W slots[v.toNat] s)
                  (fun hpre => exists_resolved W s _ hpre)
                refine ⟨r, fun j hj e he => ?_⟩
                have hjl : j < slots.length := by
                  by_contra hc; rw [List.getElem?_eq_none (by omega)] at he; cases he
                have := huniq j (Option.some.inj hj).symm hjl
                subst this
                rw [List.getElem?_eq_getElem hj0, Option.some.injEq] at he
                subst he
                exact hr'
              · refine ⟨.stop, fun j hj e he => ?_⟩
                have hjl : j < slots.length := by
                  by_contra hc; rw [List.getElem?_eq_none (by omega)] at he; cases he
                exact absurd (huniq j (Option.some.inj hj).symm hjl ▸ hjl) hj0
          · simp only [hr, ↓reduceIte]
            exact hfns

/-- **Every contract can be met, so the machine always has an outcome** (for a world whose
`atMain` holds everywhere, as by default). -/
theorem proc_progress (W : World) (hW : W.base.toNat + W.size ≤ 2 ^ 62)
    (hA : ∀ a, W.args a ∨ W.tls a → a < 2 ^ 62)
    (hslots : ∀ res slots, W.lazy = some (res, slots) → slots.length ≤ 2 ^ 64)
    (hN : ∀ n s, ∃ r, W.named n s r) (hM0 : ∀ t, W.atMain t := by intro _; trivial)
    (hK0 : ∀ t, W.atCall t := by intro _; trivial)
    (hP : ∀ s, ∃ p, W.pending s p := by exact fun _ => ⟨[], rfl⟩)
    (hG0 : ∀ s t, W.atGate s t := by intro _ _; trivial) :
    Silmaril.X86.RelIsa.Progress (proc W) :=
  proc_progressM W hW hA hslots hN (hP := hP) (fun s f a1 a2 a3 g => by
    obtain ⟨t, h⟩ := exists_enters W hW hA s f a1 a2 a3 g
    exact ⟨t, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hM0 t⟩) (fun s f g => by
    obtain ⟨t, h1, -, -, -, h5⟩ := exists_enters W hW hA s f 0 0 0 g
    exact ⟨t, h1, h5, hK0 t⟩) hG0

end Silmaril.Elf.Link.Dyn.Proc
