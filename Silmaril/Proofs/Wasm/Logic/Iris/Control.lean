module

public import Silmaril.Proofs.Wasm.Logic.Iris.Aggregate

/-!
# The Iris logic of Wasm Core 3.0: outcomes, arithmetic and exceptions

* exits, instances of `wp_exit`: `wp_vals` (falling through), `wp_trap`,
  `wp_throwing` (an exception), `wp_br`, `wp_return`, `wp_tail` (a tail call);
  their postconditions are the corresponding outcome of `Res`;
* `wp_intBinOp`, `wp_intBinOp_trap`: integer binary operators, both outcomes;
* `wp_throw`: `throw x` allocates an exception and exits with outcome `throw a`
  for its fresh address `a`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head)
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (Exits)
open _root_.Iris _root_.Iris.BI _root_.Iris.Std _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem cellOf_addExn {s : Store H} {f : Frame} {e : ExnInst} (l : ILoc) :
    cellOf (s.addExn e) f l = cellOf s f l := by
  cases l <;> rfl

theorem tag_of_cells {s : Store H} {f f' : Frame} {ta : Nat} {ti : TagInst}
    (h : Cells [(.frame, .frame f), (.tag ta, .tag ti)] s f') : s.tags[ta]? = some ti := by
  have h₁ : cellOf s f' (.tag ta) = some (.tag ti) := h (.tag ta, .tag ti) (by simp)
  rcases ht : s.tags[ta]? with _ | ti'
  · simp [cellOf, ht] at h₁
  · simpa [cellOf, ht] using h₁

theorem tag?_eq {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (hx : f.module.tags[x.toNat]? = some ta) (ht : s.tags[ta]? = some ti) :
    s.tag? f x = some (ta, ti) := by
  simp [Store.tag?, hx, ht]

theorem throw_inv {us vs : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} {f : Frame} {rest : List Admin}
    (hx : f.module.tags[x.toNat]? = some ta) (he : Expand ti.type (.func ts .nil))
    (hn : vs.length = ts.length) (s : Store H) (f' : Frame) (us' args : List Val) (c₀ : Config H)
    (hc : Cells [(.frame, .frame f), (.tag ta, .tag ti)] s f') (hW : us ++ vs = us' ++ args)
    (hh : Head P s f' args (.plain (.throw x)) c₀) :
    vals us' ++ c₀.code ++ rest = vals us ++ throwing s.exns.length ++ rest ∧
      Change s f' c₀.store c₀.frame [(.frame, .frame f), (.tag ta, .tag ti)]
        [(.frame, .frame f), (.tag ta, .tag ti)] [] := by
  have hf : f' = f := frame_of_cells hc
  have ht : s.tags[ta]? = some ti := tag_of_cells hc
  obtain ⟨ta', ti', ts', ht', he', hn', rfl⟩ := Hoare.head_throw hh
  have htt : (ta', ti') = (ta, ti) := Option.some.inj (ht'.symm.trans (hf ▸ tag?_eq hx ht))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj htt
  have hts : ts' = ts := by
    have h₂ := SingleThreaded.Det.Expand.det he' he
    injection h₂
  subst hts
  obtain ⟨rfl, rfl⟩ := Hoare.split_args hW (hn'.trans hn.symm)
  refine ⟨by simp [throwing], rfl, by simp, by simp, ?_, ?_⟩
  · intro p hp
    rw [cellOf_addExn]
    exact hc p (by simpa using hp)
  · intro l c _ hlc
    rw [cellOf_addExn]
    exact hlc

section Rules

variable {GF : BundledGFunctors} [WasmGS GF]

local bi (IProp GF)

/-! ## Exits -/

/-- An exit whose postcondition holds in every state. -/
theorem wp_exit' {E : CoPset} {c : List Admin} {o : Outcome} {Φ : Res H → IProp GF}
    (he : Exits o c) :
    (∀ s f, Φ ⟨s, f, o⟩) ⊢ WP (IExpr.run c : IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_exit he
  iintro %s %f Hσ
  imodintro
  iframe Hσ
  iapply H

/-- An exit whose postcondition reads owned cells of the final store. -/
theorem wp_exit_cells {E : CoPset} {c : List Admin} {o : Outcome} {ps : List (ILoc × ICell)}
    {Φ : Res H → IProp GF} (he : Exits o c) :
    ownCells ps ∗ (∀ s f, ⌜Cells ps s f⌝ -∗ ownCells ps -∗ Φ ⟨s, f, o⟩)
    ⊢ WP (IExpr.run c : IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hc, H⟩
  iapply wp_exit he
  iintro %s %f Hσ
  ihave %hc : ⌜Cells ps s f⌝ $$ [Hσ Hc]
  · icases interp_lookup_cells $$ [$Hσ $Hc] with >%h
    ipureintro
    exact h
  imodintro
  iframe Hσ
  iapply H $$ %s %f %hc Hc

/-- **Falling through** with the values `vs`. -/
theorem wp_vals {E : CoPset} {vs : List Val} {Φ : Res H → IProp GF} :
    (∀ s f, Φ ⟨s, f, .normal vs⟩) ⊢ WP (IExpr.run (vals vs) : IExpr P host) @ E {{ Φ }} :=
  wp_exit' rfl

/-- **A trap**, with values before it and dead code after it. -/
theorem wp_trap {E : CoPset} {vs : List Val} {rest : List Admin} {Φ : Res H → IProp GF} :
    (∀ s f, Φ ⟨s, f, .trap⟩) ⊢
      WP (IExpr.run (vals vs ++ .trap :: rest) : IExpr P host) @ E {{ Φ }} :=
  wp_exit' ⟨vs, rest, rfl⟩

/-- **An exception** at address `a`, with values before it and dead code after it. -/
theorem wp_throwing {E : CoPset} {vs : List Val} {a : Nat} {rest : List Admin}
    {Φ : Res H → IProp GF} :
    (∀ s f, Φ ⟨s, f, .throw a⟩) ⊢
      WP (IExpr.run (vals vs ++ throwing a ++ rest) : IExpr P host) @ E {{ Φ }} :=
  wp_exit' ⟨vs, rest, rfl⟩

/-- **A branch** to the enclosing label `x` with the values `vs`. -/
theorem wp_br {E : CoPset} {vs : List Val} {x : LabelIdx} {rest : List Admin}
    {Φ : Res H → IProp GF} :
    (∀ s f, Φ ⟨s, f, .br x.toNat vs⟩) ⊢
      WP (IExpr.run (vals vs ++ .plain (.br x) :: rest) : IExpr P host) @ E {{ Φ }} :=
  wp_exit' ⟨x, rest, rfl, rfl⟩

/-- **A return** with the values `vs`. -/
theorem wp_return {E : CoPset} {vs : List Val} {rest : List Admin} {Φ : Res H → IProp GF} :
    (∀ s f, Φ ⟨s, f, .ret vs⟩) ⊢
      WP (IExpr.run (vals vs ++ .plain .return_ :: rest) : IExpr P host) @ E {{ Φ }} :=
  wp_exit' ⟨rest, rfl⟩

/-- **A tail call** of the function at address `a` (a `RETURN_CALL_REF` form `r`). -/
theorem wp_tail {E : CoPset} {vs : List Val} {a : Nat} {r : Admin} {rest : List Admin}
    {Φ : Res H → IProp GF} (hr : r.IsReturnCallRef) :
    (∀ s f, Φ ⟨s, f, .tail vs a r⟩) ⊢
      WP (IExpr.run (vals vs ++ .ref (.func a) :: r :: rest) : IExpr P host) @ E {{ Φ }} :=
  wp_exit' ⟨hr, rest, rfl⟩

/-! ## Integer arithmetic -/

/-- **An integer binary operator** that succeeds. -/
theorem wp_intBinOp {E : CoPset} {vs : List Val} {t : IntType} {op : IntBinOp}
    {x y z : BitVec t.width} {rest : List Admin} {Φ : Res H → IProp GF}
    (hok : Numerics.intBinOp t op x y = .ok z) :
    ▷ WP (IExpr.run (vals (vs ++ [.num ⟨.int t, z⟩]) ++ rest) : IExpr P host) @ E {{ Φ }}
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
        .plain (.intBinOp t op) :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_head_read (P := P) (host := host) (E := E) (Φ := Φ)
    (code' := vals (vs ++ [.num ⟨.int t, z⟩]) ++ rest) [] ⟨rfl, by simp, rfl⟩
    (fun _ _ _ => ⟨vs, _, _, rfl, .numeric (.intBinOp hok)⟩)
    (fun s f vs' args c₀ _ hW hh => by
      obtain ⟨x', y', rfl, hr⟩ := Hoare.head_intBinOp hh
      obtain ⟨rfl, hx, hy⟩ := Hoare.split_two hW
      obtain rfl := Hoare.numVal_int_inj (Val.num.inj hx)
      obtain rfl := Hoare.numVal_int_inj (Val.num.inj hy)
      rcases hr with ⟨z', hz, rfl⟩ | ⟨e, he, rfl⟩
      · obtain rfl : z' = z := by rw [hok] at hz; injection hz with h; exact h.symm
        exact ⟨rfl, rfl, by simp [vals, Val.toAdmin]⟩
      · rw [hok] at he; cases he)
  simp only [ownCells_nil]
  isplitr
  · iempintro
  · iintro !> -
    iexact H

/-- **An integer binary operator** that traps (division by zero, overflow). -/
theorem wp_intBinOp_trap {E : CoPset} {vs : List Val} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width} {e : IntTrap} {rest : List Admin} {Φ : Res H → IProp GF}
    (herr : Numerics.intBinOp t op x y = .error e) :
    ▷ WP (IExpr.run (vals vs ++ .trap :: rest) : IExpr P host) @ E {{ Φ }}
    ⊢ WP (IExpr.run (vals (vs ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
        .plain (.intBinOp t op) :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro H
  iapply wp_head_read (P := P) (host := host) (E := E) (Φ := Φ)
    (code' := vals vs ++ .trap :: rest) [] ⟨rfl, by simp, rfl⟩
    (fun _ _ _ => ⟨vs, _, _, rfl, .numeric (.intBinOpTrap herr)⟩)
    (fun s f vs' args c₀ _ hW hh => by
      obtain ⟨x', y', rfl, hr⟩ := Hoare.head_intBinOp hh
      obtain ⟨rfl, hx, hy⟩ := Hoare.split_two hW
      obtain rfl := Hoare.numVal_int_inj (Val.num.inj hx)
      obtain rfl := Hoare.numVal_int_inj (Val.num.inj hy)
      rcases hr with ⟨z', hz, rfl⟩ | ⟨e', he, rfl⟩
      · rw [herr] at hz; cases hz
      · exact ⟨rfl, rfl, by simp⟩)
  simp only [ownCells_nil]
  isplitr
  · iempintro
  · iintro !> -
    iexact H

/-! ## Exceptions -/

/-- **`throw x`**: the exception is allocated at a fresh address `a` and the code
exits with outcome `throw a` (through `wp_throwing`) unless a handler catches it. -/
theorem wp_throw {E : CoPset} {us vs : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} {rest : List Admin} {f : Frame} {Φ : Res H → IProp GF}
    (hx : f.module.tags[x.toNat]? = some ta) (he : Expand ti.type (.func ts .nil))
    (hn : vs.length = ts.length) :
    ownFrame f ∗ pts (.tag ta) (.tag ti) ∗ ▷ (∀ a, ownFrame f ∗ pts (.tag ta) (.tag ti) -∗
      WP (IExpr.run (vals us ++ throwing a ++ rest) : IExpr P host) @ E {{ Φ }})
    ⊢ WP (IExpr.run (vals (us ++ vs) ++ .plain (.throw x) :: rest) : IExpr P host) @ E {{ Φ }} := by
  iintro ⟨Hf, Ht, H⟩
  iapply wp_head_change [(.frame, .frame f), (.tag ta, .tag ti)]
    [(.frame, .frame f), (.tag ta, .tag ti)] (fun _ => [])
    (fun s => vals us ++ throwing s.exns.length ++ rest) ⟨rfl, by simp, rfl⟩
    (fun s f' hc => ⟨us, vs, _, rfl,
      .throw (tag?_eq ((frame_of_cells hc) ▸ hx) (tag_of_cells hc)) he hn⟩)
    (throw_inv hx he hn)
  simp only [ownCells_two, ownCells_nil]
  iframe Hf Ht
  iintro !> %s Hc -
  iapply H $$ %s.exns.length Hc

end Rules

end Silmaril.Wasm.Logic.IrisWasm
