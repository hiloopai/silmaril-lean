module

public import Silmaril.Proofs.Wasm.FX.Asyncify.SelFull

/-!
# Selective asyncify: the simulation

`simRel_sel`: for a sound analysis (`Sound o.instr P`), `Rel o f args` is a stuttering
relational simulation of the handler kernel `sstep P` by the asyncify machine on the selectively
instrumented program `tstep (compPO o P)`. Steps of the top frame that leave the stack below
alone are one target step (`TopRes`); a call pushes the caller with the flag of its call site
(`sel_call`); a return is one target step at an unchecked frame and two at a checked one
(`sel_return`); `resume` and `suspend` run on the fully checked stack (`SelFull`). The initial
configurations take one step each into the main relation (`sel_init`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Proofs.Wasm.Models.FXAsync (runN_one)

variable {V : Type} (o : Opt) (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V))

/-- The main relation from its parts. -/
theorem rel_main {K : List (Option (List (SFrame V)))} {top : SFrame V}
    {A : List (SFrame V × Bool)} (htop : HasU A → Calm o.instr top.code) (hok : OkR o.instr A) :
    Rel o f args ⟨K, top :: A.map Prod.fst⟩
      ⟨trKO o K, .normal, ⟨compO o top.code, top.ops⟩ :: A.map (trF o)⟩ :=
  .inr (.inl ⟨top, A, rfl, htop, hok, rfl⟩)

/-- A step that only changes the top frame (to code `c`) and the store, or stops equally. -/
def TopRes (A : List (SFrame V × Bool)) (c : List (Ins V)) (r : Res (SCfg V) V)
    (r' : Res (TCfg V) V) : Prop :=
  (∃ out, r = .stop out ∧ r' = .stop out) ∨
    ∃ K' ops' w, r = .next ⟨K', ⟨c, ops', w⟩ :: A.map Prod.fst⟩ ∧
      r' = .next ⟨trKO o K', .normal, ⟨compO o c, ops'⟩ :: A.map (trF o)⟩

theorem resRel_topRes {A : List (SFrame V × Bool)} {i : Ins V} {c : List (Ins V)}
    {r : Res (SCfg V) V} {r' : Res (TCfg V) V} (h : TopRes o A c r r')
    (htop : HasU A → Calm o.instr (i :: c)) (hok : OkR o.instr A) :
    ResRel (Rel o f args) r r' := by
  rcases h with ⟨out, rfl, rfl⟩ | ⟨K', ops', w, rfl, rfl⟩
  · rfl
  · exact rel_main o f args (top := ⟨c, ops', w⟩) (fun hu => calm_tail (htop hu)) hok

/-- One target step matching a source step. -/
theorem of_one {x : SCfg V} {y : TCfg V} {r' : Res (TCfg V) V}
    (h : tstep (compPO o P) test y = r') (hr : ResRel (Rel o f args) (sstep P test x) r') :
    ∃ n, 0 < n ∧ ResRel (Rel o f args) (sstep P test x) (runN (tstep (compPO o P) test) n y) :=
  ⟨1, Nat.one_pos, by rw [runN_one, h]; exact hr⟩

/-! ## Simple instructions -/

theorem top_prim (K : List (Option (List (SFrame V)))) (n : Nat) (op : List V → List V)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause))
    (A : List (SFrame V × Bool)) :
    TopRes o A c (sstep P test ⟨K, ⟨.prim n op :: c, ops, w⟩ :: A.map Prod.fst⟩)
      (tstep (compPO o P) test
        ⟨trKO o K, .normal, ⟨compO o (.prim n op :: c), ops⟩ :: A.map (trF o)⟩) := by
  rcases hp : popN n ops with _ | ⟨a, o'⟩
  · exact .inl ⟨.trap, by simp only [sstep, sexec, hp], by simp only [tstep, compO, texec, hp]⟩
  rcases ha : allVals a with _ | vs
  · exact .inl ⟨.trap, by simp only [sstep, sexec, hp, ha],
      by simp only [tstep, compO, texec, hp, ha]⟩
  · exact .inr ⟨K, (op vs).map .val ++ o', w, by simp only [sstep, sexec, hp, ha],
      by simp only [tstep, compO, texec, hp, ha]⟩

theorem top_drop (K : List (Option (List (SFrame V)))) (c : List (Ins V)) (ops : List (SV V))
    (w : Option (List Clause)) (A : List (SFrame V × Bool)) :
    TopRes o A c (sstep P test ⟨K, ⟨.drop :: c, ops, w⟩ :: A.map Prod.fst⟩)
      (tstep (compPO o P) test
        ⟨trKO o K, .normal, ⟨compO o (.drop :: c), ops⟩ :: A.map (trF o)⟩) := by
  rcases ops with _ | ⟨v, o'⟩
  · exact .inl ⟨.trap, rfl, rfl⟩
  · exact .inr ⟨K, o', w, rfl, rfl⟩

theorem top_contNew (K : List (Option (List (SFrame V)))) (g : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (A : List (SFrame V × Bool)) :
    TopRes o A c (sstep P test ⟨K, ⟨.contNew g :: c, ops, w⟩ :: A.map Prod.fst⟩)
      (tstep (compPO o P) test
        ⟨trKO o K, .normal, ⟨compO o (.contNew g :: c), ops⟩ :: A.map (trF o)⟩) := by
  rcases hg : P g with _ | ⟨np, body⟩
  · exact .inl ⟨.trap, by simp only [sstep, sexec, hg],
      by simp only [tstep, compO, texec, compPO, hg, Option.map_none]⟩
  · refine .inr ⟨K ++ [some [⟨body, [], none⟩]], .cont K.length :: ops, w,
      by simp only [sstep, sexec, hg], ?_⟩
    simp only [tstep, compO, texec, compPO, hg, Option.map_some, trKO, List.map_append,
      List.map_cons, List.map_nil, List.length_map, trSO]

/-! ## Calls -/

/-- **A call**: the caller waits with the flag `b` of its call site. -/
theorem sel_call (hS : Sound o.instr P) (K : List (Option (List (SFrame V)))) (g : Nat)
    (b : Bool) (fr : SFrame V) (ops : List (SV V)) (c : List (Ins V))
    (A : List (SFrame V × Bool)) (hb : b = false → o.instr g = false)
    (hc : HasU A → Calm o.instr c ∧ o.instr g = false) (hok : OkR o.instr A) :
    ResRel (Rel o f args) (scall P K g fr ops c (A.map Prod.fst))
      (tcall (compPO o P) (trKO o K) g ops (chkIf b ++ compO o c) (A.map (trF o))) := by
  rcases hg : P g with _ | ⟨np, body⟩
  · show ResRel _ (scall P K g fr ops c _) (tcall (compPO o P) _ g ops _ _)
    simp only [scall, tcall, compPO, hg, Option.map_none]
    rfl
  rcases hp : popN np ops with _ | ⟨a, o'⟩
  · show ResRel _ (scall P K g fr ops c _) (tcall (compPO o P) _ g ops _ _)
    simp only [scall, tcall, compPO, hg, hp, Option.map_some]
    rfl
  have hcalm : o.instr g = false → Calm o.instr body := hS g np body hg
  have htop : HasU ((⟨c, o', none⟩, b) :: A) → Calm o.instr body := by
    rintro ⟨x, hx, hxf⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hcalm (hb hxf)
    · exact hcalm (hc ⟨x, hx, hxf⟩).2
  have hok' : OkR o.instr ((⟨c, o', none⟩, b) :: A) :=
    ⟨fun _ => rfl, fun hu => (hc hu).1, hok⟩
  have hrel := rel_main o f args (K := K) (top := ⟨body, a, none⟩) htop hok'
  have hsrc : scall P K g fr ops c (A.map Prod.fst) =
      .next ⟨K, ⟨body, a, none⟩ :: ⟨c, o', none⟩ :: A.map Prod.fst⟩ := by
    simp only [scall, hg, hp]
  have htgt : tcall (compPO o P) (trKO o K) g ops (chkIf b ++ compO o c) (A.map (trF o)) =
      .next ⟨trKO o K, .normal, ⟨compO o body, a⟩ ::
        trF o (⟨c, o', none⟩, b) :: A.map (trF o)⟩ := by
    simp only [tcall, compPO, hg, hp, Option.map_some, trF_call]
  rw [hsrc, htgt]
  exact hrel

/-! ## Returns -/

/-- **A return**: one target step at an unchecked frame, two at a checked one. -/
theorem sel_return (K : List (Option (List (SFrame V)))) (ops : List (SV V))
    (w : Option (List Clause)) (A : List (SFrame V × Bool)) (hok : OkR o.instr A) :
    ∃ n, 0 < n ∧ ResRel (Rel o f args) (sstep P test ⟨K, ⟨[], ops, w⟩ :: A.map Prod.fst⟩)
      (runN (tstep (compPO o P) test) n
        ⟨trKO o K, .normal, ⟨compO o [], ops⟩ :: A.map (trF o)⟩) := by
  rcases A with _ | ⟨⟨b, fl⟩, L⟩
  · exact ⟨1, Nat.one_pos, rfl⟩
  obtain ⟨hfl, hL, hokL⟩ := hok
  have hrel := rel_main o f args (K := K) (top := { b with ops := ops ++ b.ops }) hL hokL
  have hsrc : sstep P test ⟨K, ⟨[], ops, w⟩ :: List.map Prod.fst ((b, fl) :: L)⟩ =
      .next ⟨K, { b with ops := ops ++ b.ops } :: L.map Prod.fst⟩ := rfl
  rw [hsrc]
  cases fl with
  | false =>
    have hw : b.wait = none := hfl rfl
    refine ⟨1, Nat.one_pos, ?_⟩
    show ResRel _ _ (runN _ 1 (⟨_, _, ⟨[], ops⟩ :: trF o (b, false) :: L.map (trF o)⟩ : TCfg V))
    exact hrel
  | true =>
    refine ⟨2, by omega, ?_⟩
    show ResRel _ _ (runN _ 2 (⟨_, _, ⟨[], ops⟩ :: trBO o b :: L.map (trF o)⟩ : TCfg V))
    rcases b with ⟨code, bops, _ | hs⟩
    · exact hrel
    · exact hrel

/-- **A two-way call** (`cond`): instrumented iff either callee is. -/
theorem sel_cond (hS : Sound o.instr P) (K : List (Option (List (SFrame V)))) (g g' : Nat)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause))
    (A : List (SFrame V × Bool)) (htop : HasU A → Calm o.instr (.cond g g' :: c))
    (hok : OkR o.instr A) :
    ∃ n, 0 < n ∧ ResRel (Rel o f args)
      (sstep P test ⟨K, ⟨.cond g g' :: c, ops, w⟩ :: A.map Prod.fst⟩)
      (runN (tstep (compPO o P) test) n
        ⟨trKO o K, .normal, ⟨compO o (.cond g g' :: c), ops⟩ :: A.map (trF o)⟩) := by
  rcases ops with _ | ⟨v | k, o'⟩
  · exact of_one o P test f args rfl rfl
  · have hb : (o.instr g || o.instr g') = false →
        o.instr (if test v then g else g') = false := by
      intro h
      have h' : o.instr g = false ∧ o.instr g' = false := Bool.or_eq_false_iff.mp h
      split
      · exact h'.1
      · exact h'.2
    have hc : HasU A → Calm o.instr c ∧ o.instr (if test v then g else g') = false := by
      intro hu
      have h' : o.instr g = false ∧ o.instr g' = false := calm_cond (htop hu)
      refine ⟨calm_tail (htop hu), ?_⟩
      split
      · exact h'.1
      · exact h'.2
    exact of_one o P test f args rfl (sel_call o P f args hS K _ _ ⟨[], [], none⟩ o' c A hb hc hok)
  · exact of_one o P test f args rfl rfl

/-! ## Assembling the cases -/

/-- The fully checked case (`resume`, `suspend`) in the relation. -/
theorem resRel_full {x : SCfg V} {n : Nat}
    (h : runN (tstep (compPO o P) test) n (trCO o x) = (sstep P test x).map (trCO o)) :
    ResRel (Rel o f args) (sstep P test x) (runN (tstep (compPO o P) test) n (trCO o x)) := by
  rw [h]
  cases sstep P test x with
  | next x' => exact rel_trCO o f args x'
  | stop out => rfl

/-- A non-calm top frame sees a fully checked stack. -/
theorem full_of_not_calm {K : List (Option (List (SFrame V)))} {top : SFrame V}
    {A : List (SFrame V × Bool)} (htop : HasU A → Calm o.instr top.code)
    (hn : ¬ Calm o.instr top.code) :
    (⟨trKO o K, .normal, ⟨compO o top.code, top.ops⟩ :: A.map (trF o)⟩ : TCfg V) =
      trCO o ⟨K, top :: A.map Prod.fst⟩ := by
  have hA : ¬ HasU A := fun hu => hn (htop hu)
  simp only [trCO, trSO, map_trF_of_not hA]

/-- **The main relation is matched**, by instruction of the top frame. -/
theorem sel_main (hS : Sound o.instr P) (K : List (Option (List (SFrame V)))) (top : SFrame V)
    (A : List (SFrame V × Bool)) (htop : HasU A → Calm o.instr top.code)
    (hok : OkR o.instr A) :
    ∃ n, 0 < n ∧ ResRel (Rel o f args) (sstep P test ⟨K, top :: A.map Prod.fst⟩)
      (runN (tstep (compPO o P) test) n
        ⟨trKO o K, .normal, ⟨compO o top.code, top.ops⟩ :: A.map (trF o)⟩) := by
  rcases top with ⟨_ | ⟨i, c⟩, ops, w⟩
  · exact sel_return o P test f args K ops w A hok
  cases i with
  | push v =>
    exact of_one o P test f args rfl
      (resRel_topRes o f args (.inr ⟨K, .val v :: ops, w, rfl, rfl⟩) htop hok)
  | prim n op =>
    exact of_one o P test f args rfl (resRel_topRes o f args (top_prim o P test K n op c ops w A)
      htop hok)
  | drop =>
    exact of_one o P test f args rfl (resRel_topRes o f args (top_drop o P test K c ops w A)
      htop hok)
  | contNew g =>
    exact of_one o P test f args rfl
      (resRel_topRes o f args (top_contNew o P test K g c ops w A) htop hok)
  | call g =>
    exact of_one o P test f args rfl (sel_call o P f args hS K g (o.instr g) ⟨.call g :: c, ops, w⟩ ops c A id
      (fun hu => ⟨calm_tail (htop hu), calm_call (htop hu)⟩) hok)
  | cond g g' =>
    exact sel_cond o P test f args hS K g g' c ops w A htop hok
  | resume n hs =>
    rw [full_of_not_calm o htop calm_resume]
    obtain ⟨m, hm, hrun⟩ := simO_resume o P test K n hs c ops w (A.map Prod.fst)
    exact ⟨m, hm, resRel_full o P test f args hrun⟩
  | suspend t n =>
    rw [full_of_not_calm o htop calm_suspend]
    obtain ⟨m, hm, hrun⟩ := simO_suspend o P test K t n c ops w (A.map Prod.fst)
    exact ⟨m, hm, resRel_full o P test f args hrun⟩

/-- The initial configurations take one step each into the relation. -/
theorem sel_init (hS : Sound o.instr P) :
    ∃ n, 0 < n ∧ ResRel (Rel o f args) (sstep P test (sInit f args))
      (runN (tstep (compPO o P) test) n (tInit f args)) := by
  refine of_one o P test f args rfl ?_
  exact sel_call o P f args hS [] f true ⟨[.call f], args, none⟩ args [] [] (fun h => by cases h)
    (fun ⟨_, h, _⟩ => by cases h) trivial

/-- **Selective asyncify is a stuttering relational simulation** on a sound analysis. -/
theorem simRel_sel (hS : Sound o.instr P) :
    SimRel (sstep P test) (tstep (compPO o P) test) (Rel o f args) := by
  rintro x y (⟨hx, rfl⟩ | ⟨top, A, hx, htop, hok, rfl⟩ | ⟨rfl, rfl⟩)
  · rcases x with ⟨K, _ | _⟩
    · exact ⟨1, Nat.one_pos, rfl⟩
    · cases hx
  · rcases x with ⟨K, stk⟩
    have hstk : stk = top :: A.map Prod.fst := hx
    rw [hstk]
    exact sel_main o P test f args hS K top A htop hok
  · exact sel_init o P test f args hS

/-- **Selective asyncify preserves behaviours** on a sound analysis. -/
theorem beh_sel (hS : Sound o.instr P) :
    beh (sstep P test) (sInit f args) = beh (tstep (compPO o P) test) (tInit f args) :=
  beh_eq_of_simRel (simRel_sel o P test f args hS) (.inr (.inr ⟨rfl, rfl⟩))

end Silmaril.Proofs.Wasm.FX.Asyncify
