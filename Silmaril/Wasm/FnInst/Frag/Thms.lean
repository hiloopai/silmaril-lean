module

public import Silmaril.Wasm.FnInst.Frag.Defs
public import Silmaril.Wasm.FnInst.Peephole.Thms

/-!
# The fragment: congruence, a refutation, and peephole rules

* `Hole.congr` and `fragPlug`: plugging into a one-hole context is a congruence for equality of
  execution functions, so the generic peephole theorem applies to the fragment.
* `plug_not_reflect`: plugging does not reflect equivalence (`seq _ unreachable` identifies
  `const 1` and `const 2`), so it is not a signature morphism with an exact satisfaction
  condition; `plug_no_reduct` states this for every candidate model reduct.
* Rules proved once over the empty context at the free segment type `freeTy`
  (`constFold_valid`, `constDrop_valid`, `getSet_valid`) and their transfer into every
  function of every module (`constFold_everywhere`); a typed rule (`addZero_valid`) at the type
  `[i32] → [i32]`, valid at every hole of that type (`addZero_everywhere`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Frag

open CategoryTheory Silmaril.Inst

variable {C : Ctx} {W : Type}

/-- Congruence of plugging. -/
theorem Hole.congr (h : Ev C → W → Resp × W) (K : Hole C) (b b' : Instr C)
    (hb : exec h b = exec h b') : exec h (K.plug b) = exec h (K.plug b') := by
  induction K with
  | here => exact hb
  | seqL K c ih =>
    funext s l w
    simp only [Hole.plug, exec, ih]
  | seqR a K ih =>
    funext s l w
    simp only [Hole.plug, exec, ih]
  | block K ih =>
    funext s l w
    simp only [Hole.plug, exec, ih]
  | iteT K e ih =>
    funext s l w
    cases s <;> simp only [Hole.plug, exec, ih]
  | iteE t K ih =>
    funext s l w
    cases s <;> simp only [Hole.plug, exec, ih]

/-- The fragment's contexts, as a `Plug`. -/
def fragPlug : Plug frag where
  Hole := Hole
  plug K b := K.plug b
  congr h K b b' hb := funext fun c => funext fun w => by
    have hb' : exec h b = exec h b' :=
      funext fun s => funext fun l => funext fun w => congrFun (congrFun hb (s, l)) w
    show exec h (K.plug b) c.1 c.2 w = exec h (K.plug b') c.1 c.2 w
    rw [Hole.congr h K b b' hb']

/-- The free segment type: no operands, locals or labels required. -/
def freeTy : SegTy := ⟨[], [], [], []⟩

theorem freeTy_free : SegTy.Free frag freeTy := fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- Plugging does not reflect segment equivalence. -/
theorem plug_not_reflect [Inhabited W] :
    ∃ (K : Hole Ctx.empty) (b b' : Instr Ctx.empty),
      (∀ h : Handler frag W Ctx.empty, exec h (K.plug b) = exec h (K.plug b')) ∧
      ∀ h : Handler frag W Ctx.empty, ¬ SegEq h freeTy b b' := by
  refine ⟨.seqL .here .unreachable, .const 1, .const 2, fun _ => rfl, fun h hseg => ?_⟩
  have h12 : Out.normal [1] [] (default : W) = Out.normal [2] [] default :=
    hseg ([], []) default (freeTy_free _)
  have hv : (1 : Val) = 2 := by injection h12 with hs; injection hs
  exact absurd hv (by decide)

/-- No model reduct makes plugging into `seq _ unreachable` satisfy the satisfaction
condition: it is not the sentence map of a signature morphism. -/
theorem plug_no_reduct [Inhabited W] :
    ∃ (K : Hole Ctx.empty) (b b' : Instr Ctx.empty),
      ∀ r : Handler frag W Ctx.empty → Handler frag W Ctx.empty,
        ¬ ∀ h, SegEq h freeTy (K.plug b) (K.plug b') ↔ SegEq (r h) freeTy b b' := by
  obtain ⟨K, b, b', hK, hb⟩ := plug_not_reflect (W := W)
  refine ⟨K, b, b', fun r hr => hb (r fun _ w => (none, w)) ((hr _).1 ?_)⟩
  intro c w _
  exact congrFun (congrFun (congrFun (hK _) c.1) c.2) w

/-! ### Rules at the minimal signature -/

/-- The minimal hole signature of a free segment. -/
abbrev minSig : HoleSig := ⟨Ctx.empty, freeTy⟩

/-- Constant folding: `i32.const a; i32.const b; i32.add` is `i32.const (a + b)`. -/
theorem constFold_valid (a b : Val) :
    (holeInst frag W).Valid (S := minSig)
      (Formula.atom (.seq (.const a) (.seq (.const b) .add), .const (a + b))) :=
  fun _ _ _ _ => rfl

/-- A dropped constant is nothing. -/
theorem constDrop_valid (v : Val) :
    (holeInst frag W).Valid (S := minSig) (Formula.atom (.seq (.const v) .drop, .nop)) :=
  fun _ _ _ _ => rfl

theorem set_getD_self (l : List Val) (n : ℕ) : l.set n (l.getD n 0) = l := by
  by_cases hn : n < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.set_getElem_self hn
  · exact List.set_eq_of_length_le (Nat.le_of_not_lt hn)

/-- Writing back a local that was just read is nothing. -/
theorem getSet_valid (n : ℕ) :
    (holeInst frag W).Valid (S := minSig) (Formula.atom (.seq (.localGet n) (.localSet n), .nop)) :=
  fun _ c w _ => by
    show Out.normal c.1 (c.2.set n (c.2.getD n 0)) w = Out.normal c.1 c.2 w
    rw [set_getD_self]

/-- Constant folding inside any context of any function of any module, in every model. -/
theorem constFold_everywhere (a b : Val) (C : Ctx) (K : Hole C) (i : C.Idx .func) :
    (allInst frag W).Valid (S := C) (Formula.atom (FnAtom.fn i
      (K.plug (.seq (.const a) (.seq (.const b) .add))) (K.plug (.const (a + b))))) :=
  peephole_empty fragPlug freeTy_free (constFold_valid a b) C K i

/-- A typed segment: one operand. -/
def unaryTy : SegTy := ⟨[.i32], [.i32], [], []⟩

/-- `i32.const 0; i32.add` is nothing on a segment with one operand (it is not at the free
type: on an empty stack the left side traps). -/
theorem addZero_valid :
    (holeInst frag W).Valid (S := ⟨Ctx.empty, unaryTy⟩)
      (Formula.atom (.seq (.const 0) .add, .nop)) := by
  intro h c w hc
  obtain ⟨s, l⟩ := c
  cases s with
  | nil => exact (Nat.not_succ_le_zero 0 hc.1).elim
  | cons x s =>
    show Out.normal ((x + 0) :: s) l w = Out.normal (x :: s) l w
    rw [show x + 0 = x from BitVec.add_zero x]

theorem addZero_not_free :
    ¬ (holeInst frag Unit).Valid (S := minSig) (Formula.atom (.seq (.const 0) .add, .nop)) :=
  fun hv => by
    have h : Out.trap () = Out.normal [] [] () :=
      hv (fun _ w => (none, w)) ([], []) () (freeTy_free _)
    cases h

/-- The typed rule at every hole of type `[i32] → [i32]` of every module, in every model. -/
theorem addZero_everywhere (C : Ctx) (h : Handler frag W C) :
    SegEq h unaryTy (.seq (.const 0) .add) .nop :=
  hole_valid_transfer (L := frag) (Ctx.ofEmpty C) addZero_valid h

end Silmaril.Wasm.FnInst.Frag
