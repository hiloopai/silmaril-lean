module

public import Silmaril.Wasm.Binaryen.DirectizeBackFrame

@[expose] public section

/-! # Directize: matching an actual direct call by the original administrative steps -/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile}

theorem GA.crI_crT {cur : ModuleInst} (r : Bool) (y : TypeIdx) (d : DefType) :
    GA ok mi cur (.plain (crI r y)) (crT r d) := by
  cases r
  · exact .ann trivial trivial
  · exact .retAnn trivial trivial

/-- Both ordinary and tail-call sites take three positive, profile-independent steps. -/
theorem site_steps {s : Store H} {f : Frame} {r : Bool} {tt : TableIdx} {y : TypeIdx}
    {kk : BitVec 32} {ta a : Nat} {ti : TableInst}
    (ht : s.table? f tt = some (ta, ti)) (hk : ti.refs[kk.toNat]? = some (.func a))
    (hcast : RefOk s (.func a) (f.module.instRef ⟨true, .typeIdx y⟩)) :
    Relation.TransGen (Step P Det.noHost)
      ⟨s, f, [constI32 kk, .plain (ciI r tt y)]⟩
      ⟨s, f, [.ref (.func a), .plain (crI r y)]⟩ := by
  have h₁ : Relation.TransGen (Step P Det.noHost)
      ⟨s, f, [constI32 kk, .plain (ciI r tt y)]⟩
      ⟨s, f, [constI32 kk, .plain (.tableGet tt), .plain (castY y), .plain (crI r y)]⟩ := by
    have hhead : Det.Head P s f [] (.plain (ciI r tt y))
        ⟨s, f, [.plain (.tableGet tt), .plain (castY y), .plain (crI r y)]⟩ := by
      cases r
      · exact .callIndirect
      · exact .returnCallIndirect
    simpa [vals, constI32, Val.toAdmin] using tg_instrs (tg_head hhead) [.i32 kk] []
  have h₂ : Relation.TransGen (Step P Det.noHost)
      ⟨s, f, [constI32 kk, .plain (.tableGet tt), .plain (castY y), .plain (crI r y)]⟩
      ⟨s, f, [.ref (.func a), .plain (castY y), .plain (crI r y)]⟩ := by
    simpa [vals, constI32, Val.toAdmin] using
      tg_instrs (tg_head (Det.Head.table (P := P) (args := [.i32 kk]) (e := .plain (.tableGet tt)) (TableStep.getVal (a := .i32) ht hk)))
        [] [.plain (castY y), .plain (crI r y)]
  have h₃ : Relation.TransGen (Step P Det.noHost)
      ⟨s, f, [.ref (.func a), .plain (castY y), .plain (crI r y)]⟩
      ⟨s, f, [.ref (.func a), .plain (crI r y)]⟩ := by
    simpa [vals, castY, Val.toAdmin] using
      tg_instrs (tg_head (Det.Head.reference (P := P) (args := [.ref (.func a)]) (e := .plain (castY y)) (RefStep.castSucceed hcast)))
        [] [.plain (crI r y)]
  exact h₁.trans (h₂.trans h₃)

/-- Inverting a chosen direct-call step does not constrain numerical choices. -/
theorem direct_head_shape {s : Store H} {f : Frame} {r : Bool} {fx : FuncIdx}
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s f args (.plain (clI r fx)) c₀) :
    ∃ a fi, args = [] ∧ c₀ = ⟨s, f, [.ref (.func a), crT r fi.type]⟩ ∧
      f.module.funcs[fx.toNat]? = some a ∧ s.funcs[a]? = some fi := by
  cases r <;> simp only [clI] at hh <;> cases hh <;>
    first | exact ⟨_, _, rfl, rfl, by assumption, by assumption⟩ | fam_dismiss |
      simp_all [Admin.IsCallRef]

/-- Match the actual target direct-call head with all three original site steps. -/
theorem sim_site {s t : Store H} {f : Frame} {vs args : List Val} {r : Bool}
    {tt : TableIdx} {kk : BitVec 32} {y : TypeIdx} {fx : FuncIdx}
    {rest rest' : List Admin} {d₀ : Config H} (hinv : DInv ok mi s)
    (hh : Det.Head P t f args (.plain (clI r fx)) d₀) (hq : f.module = mi)
    (hok : ok tt kk y fx) (hr : GL ok mi f.module rest rest') (hSR : SR ok mi s t) :
    Res ok mi P ⟨s, f, vals (vs ++ args) ++ constI32 kk :: .plain (ciI r tt y) :: rest⟩
      ⟨d₀.store, d₀.frame, vals vs ++ d₀.code ++ rest'⟩ := by
  obtain ⟨a, fi, rfl, rfl, hfa', _⟩ := direct_head_shape hh
  obtain ⟨aL, ta, ti, hfa, hta, hti, hk, hcast, _⟩ := hinv tt kk y fx hok
  have ha : aL = a := by rw [hq, hfa] at hfa'; exact Option.some.inj hfa'
  subst aL
  have ht : s.table? f tt = some (ta, ti) := by simp [Store.table?, hq, hta, hti]
  have hc : RefOk s (.func a) (f.module.instRef ⟨true, .typeIdx y⟩) := by
    simpa only [hq] using hcast
  refine ⟨⟨s, f, vals vs ++ [.ref (.func a), .plain (crI r y)] ++ rest⟩,
    ?_, ⟨rfl, ?_⟩, hSR⟩
  · simpa using tg_instrs (site_steps (r := r) ht hk hc) vs rest
  · exact GL.append (GL.append (GL.of_vals vs)
      (.cons (.ref _ _) (.cons (GA.crI_crT r y fi.type) (.nil _)))) hr

end Silmaril.Wasm.Binaryen.DirSim.Back
