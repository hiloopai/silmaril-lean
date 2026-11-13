module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.TcGet

/-!
# ptmalloc x86sim: the frame of `LocalAt` under machine writes

`localAt_ww`: a run that writes only bytes the representation does not touch (no cell of the
arena's, thread's or shared fragments, no cell of the surroundings, no byte of a heap span)
keeps `LocalAt` (any version, any block): this is how stack pushes and pops, and every block
that writes no heap state, are framed. `localAt_mem`: `LocalAt` reads only the memory.
`cell_byte0`: the first byte of a cell holding a value below 256 (e.g. `__malloc_initialized`
read with `cmpb`).
-/

@[expose] public section

open Silmaril.X86 (MState Word)
open Silmaril.Process (Memory)
open Silmaril.Data
namespace Silmaril.Libc.Ptmalloc.X86sim

/-- **The bytes `LocalAt C P · x` reads**: the cells of the representation and of the
surroundings, and the heap's spans. -/
def RepTouches (C : Config) (P : RepAt) (x : AState) (a : Nat) : Prop :=
  a ∈ (arenaRep C P.layout x.1.shared.init x.1.avAddr x.1.av ++
      threadFrag C P.layout P.tls x.1.avAddr x.1.shared.key x.1.shared.init x.1.thread ++
      sharedFrag C P.layout P.statics x.1.shared).bytes ∨
    a ∈ (envFrag C P.layout P.env x.2.1).bytes ∨
    ∃ s ∈ spansOf x.1.av, s.1 ≤ a ∧ a < s.1 + s.2

theorem mem_bytes_append {f g : Frag} {a : Nat} : a ∈ (f ++ g).bytes ↔ a ∈ f.bytes ∨ a ∈ g.bytes := by
  simp [Frag.bytes, List.flatMap_append]

/-- **The frame of `LocalAt`**: writes that miss every byte it reads keep it. -/
theorem localAt_ww {C : Config} {P : RepAt} {x : AState} {s s' : MState} {fp : Nat → Prop}
    (h : LocalAt C P fsMach x s) (hw : s.memory.WritesWithin s'.memory fp)
    (hout : ∀ a, fp a → ¬ RepTouches C P x a) : LocalAt C P fsMach x s' := by
  obtain ⟨hwf, ⟨hfa, hft, hfs, hback, hnd⟩, henv, hsurr, hap⟩ := h
  have ag := within_of_ww hw
  have hin : ∀ a, RepTouches C P x a → ¬ fp a := fun a hr hf => hout a hf hr
  refine ⟨hwf, ⟨?_, ?_, ?_, ?_, hnd⟩, ?_, hsurr, hap⟩
  · exact Frag.holds_frame hfa fun a ha => ag a (hin a (.inl (mem_bytes_append.2
      (.inl (mem_bytes_append.2 (.inl ha))))))
  · exact Frag.holds_frame hft fun a ha => ag a (hin a (.inl (mem_bytes_append.2
      (.inl (mem_bytes_append.2 (.inr ha))))))
  · exact Frag.holds_frame hfs fun a ha => ag a (hin a (.inl (mem_bytes_append.2 (.inr ha))))
  · intro sp hsp k hk
    have hb := hback sp hsp k hk
    have hn := ag (sp.1 + k) (hin _ (.inr (.inr ⟨sp, hsp, by omega, by omega⟩)))
    exact ⟨hn.1 ▸ hb.1, hn.2 ▸ hb.2⟩
  · exact Frag.holds_frame henv fun a ha => ag a (hin a (.inr (.inl ha)))

/-- `LocalAt` reads only the memory. -/
theorem localAt_mem {C : Config} {P : RepAt} {x : AState} {s s' : MState}
    (h : LocalAt C P fsMach x s) (he : s'.memory = s.memory) : LocalAt C P fsMach x s' := by
  have : fsMach.view s' = fsMach.view s := by simp [fsMach, he]
  unfold LocalAt at h ⊢
  rw [this]; exact h

/-- `LocalAt` does not read the block arguments. -/
theorem localAt_args {C : Config} {P : RepAt} {x : AState} {args : List Nat} {s : MState}
    (h : LocalAt C P fsMach x s) : LocalAt C P fsMach (x.1, x.2.1, args) s := h

/-- **The first byte of a small cell.** -/
theorem cell_byte0 {v : MemView} {c : Cell} (h : c.Holds v) (hk : 0 < c.width) (hv : c.val < 256) :
    (⟨c.addr, 1, c.val⟩ : Cell).Holds v := by
  obtain ⟨hl, hw⟩ := h
  obtain ⟨k, hk'⟩ : ∃ k, c.width = k + 1 := ⟨c.width - 1, by omega⟩
  rw [hk'] at hl hw
  refine ⟨?_, fun i hi => by
    have hi' : i < 1 := hi
    simpa using hw i (by omega)⟩
  simp only [MemView.load] at hl ⊢
  cases hb : v.byte c.addr with
  | none => simp [hb] at hl
  | some b =>
    cases hr : v.load (c.addr + 1) k with
    | none => simp [hb, hr] at hl
    | some r =>
      simp only [hb, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at hl
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
      omega

end Silmaril.Libc.Ptmalloc.X86sim
