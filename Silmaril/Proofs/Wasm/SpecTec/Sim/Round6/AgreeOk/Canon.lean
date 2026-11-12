module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Check
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.TyBnd
public import Silmaril.Wasm.Validation.Check.TyOkComplete

/-!
# Round 6: Core-valid bounded types have canonical derivations

`tyOkB_of_tyOk`: a bounded type that is Core-valid in a context without `TYPES` has a canonical
derivation (`TyOkB`) in that context with any `RECS` appended. One mutual structural recursion
over `TyOk`/`SubOk2`/`GroupOk2`, as `RefOkV.tyOkS_of_tyOk`, except at `Subtype_ok2`'s subtyping
premise: Core's derivation of `Sub Δ ct ct'` may go through unbounded middle types, so it is
replaced by the one Silmaril's checker builds (`Sub.checkRWith_complete`, then
`subB_checkCompR`), whose middles are abstract heap types or declared supertypes of the group's
members, bounded because the group is.

`tyOkB_empty`: in `{}`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round4 (tyBnd)

/-! ## Bounds of the parts of a bounded type -/

theorem tyBnd_cons_iff {k : TKind} {a : Ty k} {l : Ty (.list k)} :
    tyBnd (.cons a l) = true ↔ tyBnd a = true ∧ tyBnd l = true := by
  simp [tyBnd]

theorem tyBnd_defn {subs : Ty (.list .sub)} {i : Nat}
    (h : tyBnd (Ty.defn (.group subs) i : DefType) = true) : tyBnd subs = true := by
  simp only [tyBnd, Bool.and_eq_true] at h
  exact h.2

theorem tyBnd_struct' {fs : Ty (.list .field)} (h : tyBnd (Ty.struct fs) = true) :
    tyBnd fs = true := by
  simp only [tyBnd, Bool.and_eq_true] at h
  exact h.2

theorem tyBnd_func' {ps rs : Ty (.list .val)} (h : tyBnd (Ty.func ps rs) = true) :
    tyBnd ps = true ∧ tyBnd rs = true :=
  Round5.Fwd.tyBnd_func h

theorem tyBnd_sub' {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (h : tyBnd (Ty.sub fin sups ct) = true) : tyBnd sups = true ∧ tyBnd ct = true := by
  simpa only [tyBnd, Bool.and_eq_true] using h

/-- A declared supertype of a member of a bounded group is bounded. -/
theorem tyBnd_super {subs : Ty (.list .sub)} (hb : tyBnd subs = true) {k : Nat} {st : CSubType}
    (hk : subs.toList[k]? = some st) {u : CTypeUse} (hu : u ∈ st.supers) : tyBnd u = true := by
  have hst : tyBnd st = true := Round5.Fwd.tyBnd_of_mem hb (List.mem_of_getElem? hk)
  cases st with
  | sub fin sups ct =>
    exact Round5.Fwd.tyBnd_of_mem (tyBnd_sub' hst).1 (by simpa [Ty.supers] using hu)

/-! ## Core subtyping, made canonical -/

/-- A context without `TYPES` is well formed. -/
theorem ok_of_types_nil {Δ : TypeCtx} (ht : Δ.types = []) : Δ.Ok := fun d hd => by
  simp [ht] at hd

/-- **Core subtyping between valid composite types, under a valid group, is canonical**, in every
extension of `RECS`: Silmaril's checker accepts it, and builds a canonical derivation. -/
theorem subB_of_sub {Δ : TypeCtx} (ht : Δ.types = []) (hG : RecsGoodB Δ) (hR : Δ.RecsOk)
    {a b : CCompType} (h : Sub Δ a b) (ha : TyOk Δ a) (hb : TyOk Δ b) (M : List CSubType) :
    SubB (ext Δ M) a b :=
  subB_checkCompR ht hG M (Sub.checkRWith_complete (okD := fun _ => true) (ok_of_types_nil ht)
    hR (fun _ _ _ _ _ => rfl) h ha hb)

/-- `GroupOk2` makes its own `RECS` good, given that the declared supertypes are bounded and
canonically valid in every extension. -/
theorem recsGoodB_withRecs {Δ : TypeCtx} {subs : Ty (.list .sub)}
    (hg : GroupOk2 (Δ.withRecs subs.toList) (.group subs) 0) (hb : tyBnd subs = true)
    (hok : ∀ (k : Nat) (st : CSubType), subs.toList[k]? = some st → ∀ M, ∀ u ∈ st.supers,
      TyOkB (ext (Δ.withRecs subs.toList) M) u) :
    RecsGoodB (Δ.withRecs subs.toList) := by
  intro i st hst u hu
  have hst' : subs.toList[i]? = some st := hst
  have hso := GroupOk2.get subs hg hst'
  rw [Nat.zero_add] at hso
  cases hso with
  | noSuper => simp [Ty.supers] at hu
  | oneSuper _ hb' hunroll _ hsub =>
    simp only [Ty.supers, Ty.toList_cons, Ty.toList_nil, List.mem_singleton] at hu
    subst hu
    exact ⟨hb', tyBnd_super hb hst' (by simp [Ty.supers]),
      fun M => hok i _ hst' M _ (by simp [Ty.supers]), _, _, hunroll,
      (Sub.compAbs_eq hsub).symm⟩

/-! ## The recursion -/

mutual

/-- **Core-valid bounded types have canonical derivations**, in a context without `TYPES`, with
any `RECS` appended. -/
theorem tyOkB_of_tyOk : ∀ {Δ : TypeCtx} {k : TKind} {t : Ty k}, TyOk Δ t → Δ.types = [] →
    tyBnd t = true → ∀ M, TyOkB (ext Δ M) t
  | _, _, _, .idx h, ht, _, _ => absurd h (by simp [ht])
  | _, _, _, .recv h, _, _, _ => .recv (recs_ext h)
  | _, _, _, .dt h, ht, hb, M => .dt (tyOkB_of_tyOk h ht hb M)
  | Δ, _, _, .defn hg hi, ht, hb, M =>
    .defn ((groupOk2B_of hg ht (tyBnd_defn hb)).2
      (recsGoodB_withRecs hg (tyBnd_defn hb) (groupOk2B_of hg ht (tyBnd_defn hb)).1)
      (TypeCtx.recsOk_withRecs hg) (Δ.recs ++ M)) hi
  | _, _, _, .abs a, _, _, _ => .abs a
  | _, _, _, .bot, _, _, _ => .bot
  | _, _, _, .use h, ht, hb, M => .use (tyOkB_of_tyOk h ht hb M)
  | _, _, _, .ref h, ht, hb, M => .ref (tyOkB_of_tyOk h ht hb M)
  | _, _, _, .num t, _, _, _ => .num t
  | _, _, _, .vec t, _, _, _ => .vec t
  | _, _, _, .refv h, ht, hb, M => .refv (tyOkB_of_tyOk h ht hb M)
  | _, _, _, .botv, _, _, _ => .botv
  | _, _, _, .val h, ht, hb, M => .val (tyOkB_of_tyOk h ht hb M)
  | _, _, _, .pack p, _, _, _ => .pack p
  | _, _, _, .field h, ht, hb, M => .field (tyOkB_of_tyOk h ht hb M)
  | _, _, _, .struct h, ht, hb, M => .struct (tyOkB_of_tyOk h ht (tyBnd_struct' hb) M)
  | _, _, _, .array h, ht, hb, M => .array (tyOkB_of_tyOk h ht hb M)
  | _, _, _, .func hp hr, ht, hb, M =>
    .func (tyOkB_of_tyOk hp ht (tyBnd_func' hb).1 M) (tyOkB_of_tyOk hr ht (tyBnd_func' hb).2 M)
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons ha hl, ht, hb, M =>
    .cons (tyOkB_of_tyOk ha ht (tyBnd_cons_iff.1 hb).1 M)
      (tyOkB_of_tyOk hl ht (tyBnd_cons_iff.1 hb).2 M)

/-- `SubOk2`: its supertypes are canonically valid, and over a valid group it is canonical. -/
theorem subOk2B_of : ∀ {Δ : TypeCtx} {st : CSubType} {i : Nat}, SubOk2 Δ st i →
    Δ.types = [] → tyBnd st = true →
    (∀ M, ∀ u ∈ st.supers, TyOkB (ext Δ M) u) ∧
      (RecsGoodB Δ → Δ.RecsOk → ∀ M, SubOk2B (ext Δ M) st i)
  | _, _, _, .noSuper hct, ht, hb =>
    ⟨fun _ _ hu => by simp [Ty.supers] at hu,
     fun _ _ M => .noSuper (tyOkB_of_tyOk hct ht (tyBnd_sub' hb).2 M)⟩
  | _, _, _, .oneSuper hu hbf hunroll hct hsub, ht, hb =>
    ⟨fun M u' hu' => (show _ = u' from (List.mem_singleton.1 hu').symm) ▸
      tyOkB_of_tyOk hu ht (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1 M,
     fun hG hR M => .oneSuper (tyOkB_of_tyOk hu ht (tyBnd_cons_iff.1 (tyBnd_sub' hb).1).1 M)
      hbf (unrollUse_ext hunroll) (tyOkB_of_tyOk hct ht (tyBnd_sub' hb).2 M)
      (subB_of_sub ht hG hR hsub hct
        (TyOk.unrollUse_body (ok_of_types_nil ht) hR hu hunroll) M)⟩

/-- `GroupOk2`: its members' supertypes are canonically valid, and over a valid group it is
canonical. -/
theorem groupOk2B_of : ∀ {Δ : TypeCtx} {g : CRecType} {i : Nat}, GroupOk2 Δ g i →
    Δ.types = [] → tyBnd g.subs = true →
    (∀ (k : Nat) (st : CSubType), g.subs.toList[k]? = some st → ∀ M, ∀ u ∈ st.supers,
      TyOkB (ext Δ M) u) ∧
      (RecsGoodB Δ → Δ.RecsOk → ∀ M, GroupOk2B (ext Δ M) g i)
  | _, _, _, .nil, _, _ => ⟨fun _ _ h => by simp [Ty.subs] at h, fun _ _ _ => .nil⟩
  | _, _, _, .cons h hs, ht, hb =>
    ⟨fun k st hk => by
      cases k with
      | zero =>
        simp only [Ty.subs, Ty.toList_cons, List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact (subOk2B_of h ht (tyBnd_cons_iff.1 hb).1).1
      | succ k =>
        simp only [Ty.subs, Ty.toList_cons, List.getElem?_cons_succ] at hk
        exact (groupOk2B_of hs ht (tyBnd_cons_iff.1 hb).2).1 k st hk,
     fun hG hR M => .cons ((subOk2B_of h ht (tyBnd_cons_iff.1 hb).1).2 hG hR M)
      ((groupOk2B_of hs ht (tyBnd_cons_iff.1 hb).2).2 hG hR M)⟩

end

/-- **Core-valid bounded types in `{}` have canonical derivations in `{}`.** -/
theorem tyOkB_empty {k : TKind} {t : Ty k} (h : TyOk {} t) (hb : tyBnd t = true) :
    TyOkB {} t :=
  tyOkB_of_tyOk h rfl hb []

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
