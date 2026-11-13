module

public import Silmaril.Proofs.Wasm.Det.GrowTrap.Doom
public import Silmaril.Wasm.SingleThreaded.Profile

/-!
# Subset 2 (allocation failure traps): steps are deterministic-profile steps or doomed

**`step_transfer`**: on code of the subset (`GAs`, with `GrowSeq` in the continuation `K`),
every host-free Core step at an **arbitrary** profile `P` is

* a step of the deterministic profile `profile neverFail` (`$ND = false`, canonical NaNs, a
  grow succeeds whenever the new size is valid), or
* a `memory.grow` that fails although it could have succeeded, after which the code (followed
  by `K`) is at the first stage of its guard (`Dm`).

Only the numeric, vector, table and memory rules mention the profile. Float numerics and
conversions, vector and table instructions are not in the subset; the integer numeric rules
and all memory rules other than `memory.grow` have no profile premise; a `memory.grow` that
succeeds at `P` succeeds at `profile neverFail`, and one that fails because the new size is
invalid fails there too. This follows the case split of `Silmaril.Proofs.Wasm.Interp.step_profile`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.GrowTrap
open Silmaril.Wasm.Numerics (Profile)

variable {G : Nat → Prop}

/-- The deterministic profile under which a valid grow never fails. -/
abbrev PD : Profile := profile neverFail

/-! ## `Dm` under values and after a failed grow -/

theorem Dm.vals_append {l : List Admin} (h : Dm l) (vs : List Val) : Dm (vals vs ++ l) := by
  cases h with
  | trap ws rest => simpa using Dm.trap (vs ++ ws) rest
  | unr ws rest => simpa using Dm.unr (vs ++ ws) rest
  | blk ws bt th rest => simpa using Dm.blk (vs ++ ws) bt th rest
  | ift ws c hc bt th el rest => simpa using Dm.ift (vs ++ ws) c hc bt th el rest
  | rel ws a t bt th el rest => simpa using Dm.rel (vs ++ ws) a t bt th el rest
  | set ws a t k bt th el rest => simpa using Dm.set (vs ++ ws) a t k bt th el rest
  | tee ws a t k bt th el rest => simpa using Dm.tee (vs ++ ws) a t k bt th el rest
  | label ws n k body rest h => simpa using Dm.label (vs ++ ws) n k body rest h
  | frame ws n fr body rest h => simpa using Dm.frame (vs ++ ws) n fr body rest h

theorem guardRestA_shape {K : List Admin} (h : guardRestA K = true) :
    ∃ t bt th el rest, K = (m1 t).toAdmin :: relIf t bt th el rest := by
  unfold guardRestA at h
  split at h
  · rename_i t c t' bt th el rest
    have h' : t = t' ∧ c = BitVec.allOnes _ := by simpa using h
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨t, bt, th, el, rest, rfl⟩
  · cases h

/-- **A failed `memory.grow` before its guard is at the first stage of the guard.** -/
theorem dm_of_guard {K : List Admin} (h : guardA K = true) (a : AddrType) :
    Dm (aconst a (BitVec.allOnes _) :: K) := by
  have ha : aconst a (BitVec.allOnes _) = (m1 a.intType).toAdmin := rfl
  rw [ha]
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨t, bt, th, el, rest, rfl⟩ := guardRestA_shape h
    simpa [relIf] using Dm.rel [] a.intType t bt th el rest
  · match K, h with
    | .plain (.localTee k) :: l, h =>
      obtain ⟨t, bt, th, el, rest, rfl⟩ := guardRestA_shape (by simpa [teeGuardA] using h)
      simpa [relIf] using Dm.tee [] a.intType t k bt th el rest

/-! ## The families -/

theorem NumericStep.transfer {P : Profile} {fs : List Nat} {l l' : List Admin}
    (h : NumericStep P l l') (hA : GAs G fs l) : NumericStep PD l l' := by
  cases h with
  | intUnOp => exact .intUnOp
  | intBinOp hz => exact .intBinOp hz
  | intBinOpTrap he => exact .intBinOpTrap he
  | intTestOp => exact .intTestOp
  | intRelOp => exact .intRelOp
  | _ => exfalso; simp_all [GA, instrOk, flatOk, Val.toAdmin]

/-- A memory step of the subset is a step of `PD`, or a grow failing although the new size is
valid. -/
theorem MemoryStep.transfer {P : Profile} {c c' : Config Nat} (h : MemoryStep P c c') :
    MemoryStep PD c c' ∨ ∃ (a : AddrType) (n : BitVec a.intType.width) (x : MemIdx),
      c.code = [aconst a n, .plain (.memoryGrow x)] ∧ c'.code = [aconst a (BitVec.allOnes _)] := by
  cases h with
  | loadIntOob hm h => exact .inl (.loadIntOob hm h)
  | loadIntVal hm hl => exact .inl (.loadIntVal hm hl)
  | loadPackOob hm h => exact .inl (.loadPackOob hm h)
  | loadPackVal hm hl => exact .inl (.loadPackVal hm hl)
  | loadFloatOob hm h => exact .inl (.loadFloatOob hm h)
  | loadFloatVal hm hl => exact .inl (.loadFloatVal hm hl)
  | vecLoadOob hm h => exact .inl (.vecLoadOob hm h)
  | vecLoadVal hm hl => exact .inl (.vecLoadVal hm hl)
  | vecLoadLaneOob hm h => exact .inl (.vecLoadLaneOob hm h)
  | vecLoadLaneVal hm hl => exact .inl (.vecLoadLaneVal hm hl)
  | storeIntOob hm h => exact .inl (.storeIntOob hm h)
  | storeIntVal hm hs => exact .inl (.storeIntVal hm hs)
  | storePackOob hm h => exact .inl (.storePackOob hm h)
  | storePackVal hm hs => exact .inl (.storePackVal hm hs)
  | storeFloatOob hm h => exact .inl (.storeFloatOob hm h)
  | storeFloatVal hm hs => exact .inl (.storeFloatVal hm hs)
  | vecStoreOob hm h => exact .inl (.vecStoreOob hm h)
  | vecStoreVal hm hs => exact .inl (.vecStoreVal hm hs)
  | vecStoreLaneOob hm h => exact .inl (.vecStoreLaneOob hm h)
  | vecStoreLaneVal hm hs => exact .inl (.vecStoreLaneVal hm hs)
  | size hm => exact .inl (.size hm)
  | growSucceed hm hg _ =>
    exact .inl (.growSucceed hm hg (by simp [Profile.growMaySucceed, profile,
      Profile.deterministic, neverFail]))
  | @growFail s f x a n ma mi hm hp =>
    rcases hg : mi.grow? n.toNat with _ | mi'
    · exact .inl (.growFail hm (.inr hg))
    · exact .inr ⟨a, n, x, rfl, rfl⟩
  | fillOob hm h => exact .inl (.fillOob hm h)
  | fillZero hm h => exact .inl (.fillZero hm h)
  | fillSucc hm h hn => exact .inl (.fillSucc hm h hn)
  | copyOob h₁ h₂ h => exact .inl (.copyOob h₁ h₂ h)
  | copyZero h₁ h₂ h => exact .inl (.copyZero h₁ h₂ h)
  | copyLe h₁ h₂ h hn hle => exact .inl (.copyLe h₁ h₂ h hn hle)
  | copyGt h₁ h₂ h hn hgt => exact .inl (.copyGt h₁ h₂ h hn hgt)
  | initOob hm hd h => exact .inl (.initOob hm hd h)
  | initZero hm hd h => exact .inl (.initZero hm hd h)
  | initSucc hm hd h hn hb => exact .inl (.initSucc hm hd h hn hb)
  | dataDrop hd => exact .inl (.dataDrop hd)


/-- A memory step: a step of `PD`, or a grow failure before its guard. -/
theorem transfer_memory {P : Profile} {c c' : Config Nat} (h : MemoryStep P c c')
    (K : List Admin) (hG : GrowSeq c.code K) : Step PD Det.noHost c c' ∨ Dm (c'.code ++ K) := by
  rcases MemoryStep.transfer h with h' | ⟨a, n, x, hc, hc'⟩
  · exact .inl (.memory h')
  · have hG' : GrowSeq [aconst a n, .plain (.memoryGrow x)] K := hc ▸ hG
    have hg : guardA K = true := by simpa [isGrow] using hG'
    rw [hc']
    exact .inr (dm_of_guard hg a)

/-- A step under a value prefix and a suffix. -/
theorem transfer_ctxtInstrs {s s' : Store Nat} {f f' : Frame} {vs : List Val}
    {is is' rest K : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : ∀ K, GAs G f.module.funcs is → GrowSeq is K →
      Step PD Det.noHost ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨ Dm (is' ++ K))
    (hA : GAs G f.module.funcs (vals vs ++ is ++ rest)) (hG : GrowSeq (vals vs ++ is ++ rest) K) :
    Step PD Det.noHost ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ ∨
      Dm (vals vs ++ is' ++ rest ++ K) := by
  have hA' : (GAs G f.module.funcs (vals vs) ∧ GAs G f.module.funcs is) ∧
      GAs G f.module.funcs rest := by simpa using hA
  have hG' : GrowSeq is (rest ++ K) := (growSeq_append.mp (growSeq_append.mp hG).1).2
  rcases ih (rest ++ K) hA'.1.2 hG' with h' | hD
  · exact .inl (.ctxtInstrs h' hne)
  · exact .inr (by simpa using hD.vals_append vs)

/-! ## Every step -/

/-- **Every host-free step at an arbitrary profile, on code of the subset, is a step of
`profile neverFail` or leads to a guarded grow failure** (`Dm`, followed by the continuation
`K`). -/
theorem step_transfer {P : Profile} {c c' : Config Nat} (h : Step P Det.noHost c c') :
    ∀ K, GAs G c.frame.module.funcs c.code → GrowSeq c.code K →
      Step PD Det.noHost c c' ∨ Dm (c'.code ++ K) := by
  induction h with
  | parametric h => exact fun _ _ _ => .inl (.parametric h)
  | numeric h => exact fun _ hA _ => .inl (.numeric (NumericStep.transfer h hA))
  | vector h =>
    exact fun _ hA _ => by exfalso; cases h <;> simp_all [GA, instrOk, flatOk, Val.toAdmin]
  | «variable» h => exact fun _ _ _ => .inl (.variable h)
  | table h =>
    exact fun _ hA _ => by exfalso; cases h <;> simp_all [GA, instrOk, flatOk, aconst]
  | memory h => exact fun K _ hG => transfer_memory h K hG
  | reference h => exact fun _ _ _ => .inl (.reference h)
  | aggregate h => exact fun _ _ _ => .inl (.aggregate h)
  | @ctxtInstrs s s' f f' vs is is' rest hs hne ih =>
    exact fun K hA hG => transfer_ctxtInstrs hne ih hA hG
  | @ctxtLabel s s' f f' n cont is is' hs ih =>
    intro K hA _
    have hl : GA G f.module.funcs (.label n cont is) := hA.1
    rcases ih [] hl.2.2.1 hl.2.2.2.1 with h' | hD
    · exact .inl (.ctxtLabel h')
    · exact .inr (by simpa using Dm.label [] n cont is' K (by simpa using hD))
  | ctxtHandler _ _ => exact fun _ hA _ => absurd hA.1 (by simp [GA])
  | @ctxtFrame s s' f fi fi' n is is' hs ih =>
    intro K hA _
    have hl : GA G f.module.funcs (.frame n fi is) := hA.1
    rcases ih [] hl.1 hl.2.1 with h' | hD
    · exact .inl (.ctxtFrame h')
    · exact .inr (by simpa using Dm.frame [] n fi' is' K (by simpa using hD))
  | block hbt hm => exact fun _ _ _ => .inl (.block hbt hm)
  | loop hbt hm => exact fun _ _ _ => .inl (.loop hbt hm)
  | ifTrue hc => exact fun _ _ _ => .inl (.ifTrue hc)
  | ifFalse => exact fun _ _ _ => .inl .ifFalse
  | labelVals => exact fun _ _ _ => .inl .labelVals
  | brLabelZero hl hn => exact fun _ _ _ => .inl (.brLabelZero hl hn)
  | brLabelSucc hl => exact fun _ _ _ => .inl (.brLabelSucc hl)
  | brHandler => exact fun _ _ _ => .inl .brHandler
  | brIfTrue hc => exact fun _ _ _ => .inl (.brIfTrue hc)
  | brIfFalse => exact fun _ _ _ => .inl .brIfFalse
  | brTableLt hi => exact fun _ _ _ => .inl (.brTableLt hi)
  | brTableGe hi => exact fun _ _ _ => .inl (.brTableGe hi)
  | brOnNullNull => exact fun _ _ _ => .inl .brOnNullNull
  | brOnNullAddr hv => exact fun _ _ _ => .inl (.brOnNullAddr hv)
  | brOnNonNullNull => exact fun _ _ _ => .inl .brOnNonNullNull
  | brOnNonNullAddr hv => exact fun _ _ _ => .inl (.brOnNonNullAddr hv)
  | brOnCastSucceed h => exact fun _ _ _ => .inl (.brOnCastSucceed h)
  | brOnCastFail h => exact fun _ _ _ => .inl (.brOnCastFail h)
  | brOnCastFailSucceed h => exact fun _ _ _ => .inl (.brOnCastFailSucceed h)
  | brOnCastFailFail h => exact fun _ _ _ => .inl (.brOnCastFailFail h)
  | call hx hf => exact fun _ _ _ => .inl (.call hx hf)
  | callRefNull hc => exact fun _ _ _ => .inl (.callRefNull hc)
  | callRefFunc hc hf he hn hcode => exact fun _ _ _ => .inl (.callRefFunc hc hf he hn hcode)
  | callRefHost _ _ _ _ _ hh => exact hh.elim
  | callRefHostDiv _ _ _ _ _ hh => exact hh.elim
  | returnCall hx hf => exact fun _ _ _ => .inl (.returnCall hx hf)
  | returnCallRefLabel hc => exact fun _ _ _ => .inl (.returnCallRefLabel hc)
  | returnCallRefHandler hc => exact fun _ _ _ => .inl (.returnCallRefHandler hc)
  | returnCallRefFrameNull hc => exact fun _ _ _ => .inl (.returnCallRefFrameNull hc)
  | returnCallRefFrameAddr hc hf he hn =>
    exact fun _ _ _ => .inl (.returnCallRefFrameAddr hc hf he hn)
  | callIndirect => exact fun _ _ _ => .inl .callIndirect
  | returnCallIndirect => exact fun _ _ _ => .inl .returnCallIndirect
  | frameVals hn => exact fun _ _ _ => .inl (.frameVals hn)
  | returnFrame hn => exact fun _ _ _ => .inl (.returnFrame hn)
  | returnLabel => exact fun _ _ _ => .inl .returnLabel
  | returnHandler => exact fun _ _ _ => .inl .returnHandler
  | throw ht he hn => exact fun _ _ _ => .inl (.throw ht he hn)
  | throwRefNull => exact fun _ _ _ => .inl .throwRefNull
  | throwRefInstrs hne => exact fun _ _ _ => .inl (.throwRefInstrs hne)
  | throwRefLabel => exact fun _ _ _ => .inl .throwRefLabel
  | throwRefFrame => exact fun _ _ _ => .inl .throwRefFrame
  | throwRefHandlerEmpty => exact fun _ _ _ => .inl .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact fun _ _ _ => .inl (.throwRefHandlerCatch he ht)
  | throwRefHandlerCatchRef he ht => exact fun _ _ _ => .inl (.throwRefHandlerCatchRef he ht)
  | throwRefHandlerCatchAll => exact fun _ _ _ => .inl .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact fun _ _ _ => .inl .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact fun _ _ _ => .inl (.throwRefHandlerNext h)
  | tryTable hbt hm => exact fun _ _ _ => .inl (.tryTable hbt hm)
  | handlerVals => exact fun _ _ _ => .inl .handlerVals
  | trapInstrs hne => exact fun _ _ _ => .inl (.trapInstrs hne)
  | trapLabel => exact fun _ _ _ => .inl .trapLabel
  | trapHandler => exact fun _ _ _ => .inl .trapHandler
  | trapFrame => exact fun _ _ _ => .inl .trapFrame

end Silmaril.Proofs.Wasm.Det.GrowTrap
