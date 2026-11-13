module

public import Silmaril.Wasi.Versions.WitImport.FwdNamed.Defs
public import Silmaril.Wasi.Versions.WitImport.Fwd.Thms

@[expose] public section

/-!
# Forwarding across named types: theorems

PROVED (standard axioms):

* **`tyOkR_tyEq`**: equivalent types (`tyEq`) have the same resolved typing, value by value, in
  their environments and at their fuels.
* `argsOkR_sigEqR`, `resOkR_sigEqR`: so do the arguments and answers of equivalent signatures.
* **`fwdN_model`**: for a forwarding map with equivalent signatures (`FwdOkN P Q M`), the
  forwarder `fwdBody M` is a model of the export package's typing `witRTh Q` over every host of
  the import package's typing `witRTh P`, as `fwd_model` for free signatures.

The pairs between the vendored versions are computed and checked in `FwdNamed.Pairs`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (WpInv ag_of_wpInv link_model ofSBody)
open Silmaril.Games (Sig)

/-! ## Lists and options -/

theorem listEq_zipOk {g : Binary.Ty → Binary.Ty → Bool} {f f' : Binary.Ty → Val → Bool}
    (h : ∀ t t', g t t' = true → ∀ v, f t v = f' t' v) :
    ∀ {ts ts' : List Binary.Ty}, listEq g ts ts' = true → ∀ vs, zipOk f ts vs = zipOk f' ts' vs
  | [], [], _, vs => by cases vs <;> rfl
  | t :: ts, t' :: ts', hl, vs => by
    have hl' : g t t' = true ∧ listEq g ts ts' = true := by simpa [listEq] using hl
    cases vs with
    | nil => rfl
    | cons v vs => simp only [zipOk, h t t' hl'.1 v, listEq_zipOk h hl'.2 vs]
  | [], _ :: _, hl, _ => absurd hl (by simp [listEq])
  | _ :: _, [], hl, _ => absurd hl (by simp [listEq])

theorem optEq_optOk {g : Binary.Ty → Binary.Ty → Bool} {f f' : Binary.Ty → Val → Bool}
    (h : ∀ t t', g t t' = true → ∀ v, f t v = f' t' v) :
    ∀ {a a' : Option Binary.Ty}, optEq g a a' = true → ∀ p, optOk f a p = optOk f' a' p
  | none, none, _, p => by cases p <;> rfl
  | some t, some t', hl, p => by
    cases p with
    | none => rfl
    | some v => exact h t t' hl v
  | none, some _, hl, _ => absurd hl (by simp [optEq])
  | some _, none, hl, _ => absurd hl (by simp [optEq])

theorem listEq_getElem? {α : Type} {G : α → α → Bool} :
    ∀ {as bs : List α}, listEq G as bs = true → ∀ i : Nat, optEq G as[i]? bs[i]? = true
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hl, i => by
    have hl' : G a b = true ∧ listEq G as bs = true := by simpa [listEq] using hl
    cases i with
    | zero => simpa [optEq] using hl'.1
    | succ i => simpa using listEq_getElem? hl'.2 i
  | [], _ :: _, hl, _ => absurd hl (by simp [listEq])
  | _ :: _, [], hl, _ => absurd hl (by simp [listEq])

/-! ## Kinds -/

theorem kindEq_variant {eq : Binary.IfaceName → Binary.IfaceName → Binary.Ty → Binary.Ty → Bool}
    {ok ok' : Binary.IfaceName → Binary.Ty → Val → Bool}
    (h : ∀ j j' u u', eq j j' u u' = true → ∀ v, ok j u v = ok' j' u' v)
    {j j' : Binary.IfaceName} {cs cs' : List (Binary.Labeled (Option Binary.Ty))}
    (hk : listEq (optEq (eq j j')) (cs.map (·.ty)) (cs'.map (·.ty)) = true) (i : Nat)
    (p : Option Val) :
    kindOk ok j (.variant cs) (.variant i p) = kindOk ok' j' (.variant cs') (.variant i p) := by
  have hi : optEq (optEq (eq j j')) (cs[i]?.map (·.ty)) (cs'[i]?.map (·.ty)) = true := by
    simpa [List.getElem?_map] using listEq_getElem? hk i
  simp only [kindOk]
  cases hc : cs[i]? with
  | none =>
    cases hc' : cs'[i]? with
    | none => rfl
    | some _ => simp [hc, hc', optEq] at hi
  | some x =>
    cases hc' : cs'[i]? with
    | none => simp [hc, hc', optEq] at hi
    | some y =>
      have hxy : optEq (eq j j') x.ty y.ty = true := by simpa [hc, hc', optEq] using hi
      exact optEq_optOk (h j j') hxy p

/-- **Equivalent kinds accept the same values**, for checks that agree on equivalent parts. -/
theorem kindEq_kindOk {eq : Binary.IfaceName → Binary.IfaceName → Binary.Ty → Binary.Ty → Bool}
    {ok ok' : Binary.IfaceName → Binary.Ty → Val → Bool}
    (h : ∀ j j' u u', eq j j' u u' = true → ∀ v, ok j u v = ok' j' u' v)
    {j j' : Binary.IfaceName} {k k' : Binary.TyDefKind} (hk : kindEq eq j j' k k' = true)
    (v : Val) : kindOk ok j k v = kindOk ok' j' k' v := by
  cases k <;> cases k' <;> simp only [kindEq, Bool.false_eq_true] at hk
  case record.record fs fs' =>
    cases v <;> first | rfl | exact listEq_zipOk (h j j') hk _
  case variant.variant cs cs' =>
    cases v <;> first | rfl | exact kindEq_variant h hk _ _
  case enum.enum cs cs' =>
    have hl : cs.length = cs'.length := by simpa using hk
    cases v <;> try rfl
    rename_i i p
    cases p <;> simp [kindOk, hl]
  case flags.flags fs fs' =>
    have hl : fs.length = fs'.length := by simpa using hk
    cases v <;> simp [kindOk, hl]
  case resource.resource => cases v <;> rfl
  case type.type t t' => exact h j j' t t' hk v

/-! ## Types -/

theorem pairOk_congrN {f f' : Binary.Ty → Val → Bool} {k w k' w' : Binary.Ty}
    (hk : ∀ v, f k v = f' k' v) (hw : ∀ v, f w v = f' w' v) (x : Val) :
    pairOk f k w x = pairOk f' k' w' x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | ⟨a, _ | ⟨b, _ | _⟩⟩⟩ | _
  all_goals first | rfl | simp [pairOk, hk, hw]

theorem resV_congr {f f' : Binary.Ty → Val → Bool} {g : Binary.Ty → Binary.Ty → Bool}
    (hg : ∀ t t', g t t' = true → ∀ v, f t v = f' t' v) {a b a' b' : Option Binary.Ty}
    (ha : optEq g a a' = true) (hb : optEq g b b' = true) (v : Val) :
    resV f a b v = resV f' a' b' v := by
  cases v with
  | variant i p =>
    rcases i with _ | _ | i
    · exact optEq_optOk hg ha p
    · exact optEq_optOk hg hb p
    · rfl
  | _ => rfl

theorem isHandle_tyOkR {E : TyEnv} {n : Nat} {c : Binary.IfaceName} {t : Binary.Ty}
    (ht : isHandleTy t = true) (v : Val) : tyOkR E (n + 1) c t v = isU32 v := by
  cases t <;> simp_all [isHandleTy, tyOkR]

/-- Named types resolved on both sides to equivalent kinds have the same typing. -/
theorem shapeEq_ref {E E' : TyEnv} {n n' : Nat}
    {eq : Binary.IfaceName → Binary.IfaceName → Binary.Ty → Binary.Ty → Bool}
    (h : ∀ j j' u u', eq j j' u u' = true → ∀ v, tyOkR E n j u v = tyOkR E' n' j' u' v)
    {c c' : Binary.IfaceName} {r r' : Binary.TyRef}
    (hs : shapeEq E E' eq c c' (.ref r) (.ref r') = true) (v : Val) :
    tyOkR E (n + 1) c (.ref r) v = tyOkR E' (n' + 1) c' (.ref r') v := by
  cases hr : findTy E c r with
  | none =>
    cases hr' : findTy E' c' r' with
    | none => simp [tyOkR, hr, hr']
    | some _ => simp [shapeEq, hr, hr'] at hs
  | some x =>
    cases hr' : findTy E' c' r' with
    | none => simp [shapeEq, hr, hr'] at hs
    | some y =>
      have hk : kindEq eq x.1 y.1 x.2 y.2 = true := by simpa [shapeEq, hr, hr'] using hs
      rw [tyOkR_ref hr, tyOkR_ref hr']
      exact kindEq_kindOk h hk v

/-- **The same shape, with parts on which the typings agree, gives the same typing.** -/
theorem shapeEq_ok {E E' : TyEnv} {n n' : Nat}
    {eq : Binary.IfaceName → Binary.IfaceName → Binary.Ty → Binary.Ty → Bool}
    (h : ∀ j j' u u', eq j j' u u' = true → ∀ v, tyOkR E n j u v = tyOkR E' n' j' u' v)
    {c c' : Binary.IfaceName} {t t' : Binary.Ty} (hs : shapeEq E E' eq c c' t t' = true)
    (v : Val) : tyOkR E (n + 1) c t v = tyOkR E' (n' + 1) c' t' v := by
  have hf : ∀ u u', eq c c' u u' = true → tyOkR E n c u = tyOkR E' n' c' u' :=
    fun u u' hu => funext (h c c' u u' hu)
  cases t <;> cases t' <;> simp only [shapeEq, isHandleTy, Bool.false_eq_true, Bool.and_self,
    Bool.and_false, Bool.false_and] at hs
  all_goals try rw [isHandle_tyOkR (by rfl), isHandle_tyOkR (by rfl)]
  case prim.prim p p' =>
    have hp : p = p' := by simpa using hs
    rw [hp]; rfl
  case ref.ref r r' => exact shapeEq_ref h hs v
  case list.list u u' => simp only [tyOkR, hf u u' hs]
  case fixedList.fixedList u k u' k' =>
    have hs' : k = k' ∧ eq c c' u u' = true := by simpa using hs
    simp only [tyOkR, hs'.1, hf u u' hs'.2]
  case map.map k w k' w' =>
    have hs' : eq c c' k k' = true ∧ eq c c' w w' = true := by simpa using hs
    have hp : pairOk (tyOkR E n c) k w = pairOk (tyOkR E' n' c') k' w' :=
      funext (pairOk_congrN (h c c' k k' hs'.1) (h c c' w w' hs'.2))
    simp only [tyOkR, hp]
  case option.option u u' => simp only [tyOkR, hf u u' hs]
  case result.result a b a' b' =>
    have hs' : optEq (eq c c') a a' = true ∧ optEq (eq c c') b b' = true := by simpa using hs
    rw [tyOkR_result, tyOkR_result]
    exact resV_congr (h c c') hs'.1 hs'.2 v
  case tuple.tuple ts ts' =>
    cases v <;> first | rfl | exact listEq_zipOk (h c c') hs _

/-- Unfolding an alias costs one unit of fuel. -/
theorem tyOkR_alias {E : TyEnv} {n : Nat} {c j : Binary.IfaceName} {t u : Binary.Ty}
    (ha : aliasOf E c t = some (j, u)) (v : Val) : tyOkR E (n + 1) c t v = tyOkR E n j u v := by
  cases t <;> simp only [aliasOf, reduceCtorEq] at ha
  case ref r =>
    cases hf : findTy E c r with
    | none => simp [hf] at ha
    | some x =>
      obtain ⟨j0, k0⟩ := x
      cases k0 <;> simp only [hf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      rw [tyOkR_ref hf]
      rfl

/-- **Equivalent types have the same resolved typing.** -/
theorem tyOkR_tyEq {E E' : TyEnv} :
    ∀ (k n n' : Nat) (c c' : Binary.IfaceName) (t t' : Binary.Ty),
      tyEq E E' k n n' c c' t t' = true → ∀ v, tyOkR E n c t v = tyOkR E' n' c' t' v
  | _, 0, 0, _, _, _, _, _, _ => rfl
  | 0, _ + 1, _ + 1, _, _, _, _, h, _ => absurd h (by simp [tyEq])
  | _, 0, _ + 1, _, _, _, _, h, _ => absurd h (by simp [tyEq])
  | _, _ + 1, 0, _, _, _, _, h, _ => absurd h (by simp [tyEq])
  | k + 1, n + 1, n' + 1, c, c', t, t', h, v => by
    cases ha : aliasOf E c t with
    | some x =>
      have h1 : tyEq E E' k n (n' + 1) x.1 c' x.2 t' = true := by simpa [tyEq, ha] using h
      rw [tyOkR_alias ha]
      exact tyOkR_tyEq k n (n' + 1) x.1 c' x.2 t' h1 v
    | none =>
      cases ha' : aliasOf E' c' t' with
      | some y =>
        have h2 : tyEq E E' k (n + 1) n' c y.1 t y.2 = true := by simpa [tyEq, ha, ha'] using h
        rw [tyOkR_alias ha']
        exact tyOkR_tyEq k (n + 1) n' c y.1 t y.2 h2 v
      | none =>
        have h3 : shapeEq E E' (tyEq E E' k n n') c c' t t' = true := by
          simpa [tyEq, ha, ha'] using h
        exact shapeEq_ok (fun j j' u u' hu => tyOkR_tyEq k n n' j j' u u' hu) h3 v

/-! ## Signatures -/

theorem argsOkR_sigEqR {E E' : TyEnv} {i i' : Binary.IfaceName} {s s' : Binary.Sig}
    (h : sigEqR E E' i i' s s' = true) (a : List Val) : argsOkR E i s a = argsOkR E' i' s' a := by
  have hp : listEq (tyEq E E' (2 * fuel) fuel fuel i i') (s.params.map Prod.snd)
      (s'.params.map Prod.snd) = true := by
    simp only [sigEqR, Bool.and_eq_true] at h; exact h.1
  exact listEq_zipOk (fun t t' ht => tyOkR_tyEq _ _ _ _ _ t t' ht) hp a

theorem resOkR_sigEqR {E E' : TyEnv} {i i' : Binary.IfaceName} {s s' : Binary.Sig}
    (h : sigEqR E E' i i' s s' = true) (r : Option (List Val)) :
    resOkR E i s r = resOkR E' i' s' r := by
  have hr : optEq (tyEq E E' (2 * fuel) fuel fuel i i') s.result s'.result = true := by
    simp only [sigEqR, Bool.and_eq_true] at h; exact h.2
  unfold resOkR
  rcases r with _ | vs
  · rfl
  cases hs : s.result with
  | none =>
    cases hs' : s'.result with
    | none => rfl
    | some _ => simp [hs, hs', optEq] at hr
  | some t =>
    cases hs' : s'.result with
    | none => simp [hs, hs', optEq] at hr
    | some t' =>
      have ht : tyEq E E' (2 * fuel) fuel fuel i i' t t' = true := by simpa [hs, hs', optEq] using hr
      rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
      · rfl
      · exact tyOkR_tyEq _ _ _ _ _ t t' ht v
      · rfl

/-! ## The forwarder -/

/-- An entry of a map with equivalent signatures. -/
theorem fwdN_entry {P Q : RPkg} {M : FwdMap} (hM : FwdOkN P Q M = true) {fg : FnName × FnName}
    (hm : fg ∈ M) : ∃ i s i' s', Q.1.lookup fg.1 = some (i, s) ∧ P.1.lookup fg.2 = some (i', s') ∧
      sigEqR Q.2 P.2 i i' s s' = true := by
  have he := List.all_eq_true.1 hM fg hm
  revert he
  cases hq : Q.1.lookup fg.1 with
  | none => simp
  | some x =>
    cases hp : P.1.lookup fg.2 with
    | none => simp
    | some y => exact fun he => ⟨x.1, x.2, y.1, y.2, rfl, rfl, he⟩

/-- **A typed answer of the imported function is a typed answer of the exported one.** -/
theorem fwdN_typed {P Q : RPkg} {M : FwdMap} (hM : FwdOkN P Q M = true) {f : FnName}
    (hf : f ∈ fwdX M) (a : List Val) (r : Option (List Val))
    (h : witROk P (.imp (fwdTo M f) a r) = true) : witROk Q (.imp f a r) = true := by
  obtain ⟨⟨f', g⟩, hm, rfl⟩ := List.mem_map.1 hf
  obtain ⟨g', hg'⟩ := lookup_some_of_mem hm
  have hto : fwdTo M f' = g' := by simp [fwdTo, hg']
  obtain ⟨i, s, i', s', hq, hp, hs⟩ := fwdN_entry hM (rlookup_mem hg')
  have hP : (!argsOkR P.2 i' s' a || resOkR P.2 i' s' r) = true := by
    simpa [witROk, hto, hp] using h
  have hQ : (!argsOkR Q.2 i s a || resOkR Q.2 i s r) = true := by
    rw [argsOkR_sigEqR hs, resOkR_sigEqR hs]
    exact hP
  simpa [witROk, hq] using hQ

/-- The invariant of the forwarder (none needed). -/
theorem fwdN_inv {P Q : RPkg} {M : FwdMap} (hM : FwdOkN P Q M = true) :
    WpInv (fwdBody M) () (witRTh P) (witRTh Q) (fun _ _ _ => True) where
  init := trivial
  call := fun _ _ _ q _ _ _ h => ⟨(), fwdP_step_of (fwdN_typed hM q.1.2 _ _ (fwdP_step h)), trivial⟩

/-- **The forwarder across named types is a model of the export package's typing over every
host of the import package's typing.** -/
theorem fwdN_model {Y : Sig.{0}} {P Q : RPkg} {M : FwdMap} (hM : FwdOkN P Q M = true)
    {η : Host Y (fwdI M)} (hη : (hostSat (witRTh P).Accepts).holds η) :
    (hostSat (witRTh Q).Accepts).holds (link η (ofSBody (fwdBody M) ())) :=
  link_model (ag_of_wpInv (fwdN_inv hM)) hη

end Silmaril.Wasi.Versions.WitImport
