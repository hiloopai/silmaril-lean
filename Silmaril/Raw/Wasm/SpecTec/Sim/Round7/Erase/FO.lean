module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Erase.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Roots.Thms

/-!
# Round 7, the export swap: the first-order evaluator fragment (unrefined)

`eraseFO`: at every fuel, on first-order syntax (`FO`) and a scope in the swap set, evaluating at
the erased scope gives the erased answer, and the answer is in the swap set. The case analysis
follows `Sem.evalExp` constructor by constructor and uses the value lemmas of `Round7/Swap`
(`Ops`, `Ops2`); it is kept unrefined, like the other evaluator inductions of round 7.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Erase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

variable {Q : Value → Prop}

/-! ## Scopes -/

theorem find?_eraseScope (ρ : VarEnv) (x : IL.Id) :
    (eraseScope ρ).findVal? x = (ρ.findVal? x).map eraseV := by
  simp only [eraseScope, VarEnv.findVal?]
  induction ρ.vals with
  | nil => rfl
  | cons p m ih =>
    obtain ⟨y, v⟩ := p
    simp only [List.map_cons, Map.find?]
    split <;> simp [ih]

theorem mapFind_allIn : ∀ (m : Map Value) {x : IL.Id} {v : Value}, (∀ p ∈ m, AllIn Q p.2) →
    m.find? x = some v → AllIn Q v
  | [], _, _, _, h => by simp [Map.find?] at h
  | (y, w) :: m, x, v, hm, h => by
    simp only [Map.find?] at h
    split at h
    · cases h
      exact hm (y, w) (List.mem_cons_self ..)
    · exact mapFind_allIn m (fun q hq => hm q (List.mem_cons_of_mem _ hq)) h

theorem ScopeIn.find? {ρ : VarEnv} (hρ : ScopeIn Q ρ) {x : IL.Id} {v : Value}
    (h : ρ.findVal? x = some v) : AllIn Q v :=
  mapFind_allIn ρ.vals hρ h

/-! ## `EOK` -/

theorem EOK.error (e : Stuck) : EOK Q (.error e) (.error e) := ⟨rfl, fun _ h => by cases h⟩

theorem EOK.ok {v : Value} (hv : AllIn Q v) : EOK Q (.ok v) (.ok (eraseV v)) :=
  ⟨rfl, fun _ h => by cases h; exact hv⟩

theorem EOK.bind {r r' : Res Value} {k k' : Value → Res Value} (hr : EOK Q r r')
    (hk : ∀ v, r = .ok v → AllIn Q v → EOK Q (k v) (k' (eraseV v))) :
    EOK Q (r >>= k) (r' >>= k') := by
  obtain ⟨rfl, hA⟩ := hr
  cases r with
  | error e => exact EOK.error e
  | ok v => exact hk v rfl (hA v rfl)

theorem EOK.ofOption {o o' : Option Value} (he : o' = o.map eraseV)
    (hA : ∀ v, o = some v → AllIn Q v) : EOK Q (Res.ofOption o) (Res.ofOption o') := by
  subst he
  cases o with
  | none => exact EOK.error _
  | some v => exact EOK.ok (hA v rfl)

/-- A result whose answers are booleans or numbers, the same on both sides. -/
theorem EOK.of_bool_num {r : Res Value}
    (h : ∀ v, r = .ok v → (∃ b, v = .bool b) ∨ ∃ n, v = .num n) : EOK Q r r := by
  refine ⟨(eraseV_res_bool_num h).symm, fun v hv => ?_⟩
  rcases h v hv with ⟨b, rfl⟩ | ⟨n, rfl⟩ <;> trivial

theorem unValue_bn (op : UnOp) (v u : Value) (h : unValue op v = .ok u) :
    (∃ b, u = .bool b) ∨ ∃ n, u = .num n := by
  unfold unValue at h
  split at h
  · cases h; exact .inl ⟨_, rfl⟩
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨n, -, rfl⟩ := h
    exact .inr ⟨n, rfl⟩
  · cases h

theorem binValues_bn (op : BinOp) (v w u : Value) (h : binValues op v w = .ok u) :
    (∃ b, u = .bool b) ∨ ∃ n, u = .num n := by
  unfold binValues at h
  split at h
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨b, -, rfl⟩ := h
    exact .inl ⟨b, rfl⟩
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨n, -, rfl⟩ := h
    exact .inr ⟨n, rfl⟩
  · cases h

theorem cmpValues_bn (op : CmpOp) (v w u : Value) (h : cmpValues op v w = .ok u) :
    ∃ b, u = .bool b := by
  unfold cmpValues at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨b, -, rfl⟩ := h
    exact ⟨b, rfl⟩
  · cases h

theorem memValue_bn (v w u : Value) (h : memValue v w = .ok u) : ∃ b, u = .bool b := by
  unfold memValue at h
  split at h <;> first | (cases h; exact ⟨_, rfl⟩) | cases h

theorem EOK.map (f : Value → Value) (hf : ∀ v, eraseV (f v) = f (eraseV v))
    (hA : ∀ v, AllIn Q v → AllIn Q (f v)) {r r' : Res Value} (h : EOK Q r r') :
    EOK Q (f <$> r) (f <$> r') := by
  obtain ⟨rfl, hr⟩ := h
  cases r with
  | error e => exact EOK.error e
  | ok v =>
    refine ⟨by simp [Functor.map, Except.map, hf], fun u hu => ?_⟩
    simp only [Functor.map, Except.map, Except.ok.injEq] at hu
    exact hu ▸ hA v (hr v rfl)

theorem boolShort_bool {op : BinOp} {v u : Value} (h : boolShort op v = some u) :
    ∃ b, u = .bool b := by
  unfold boolShort at h
  split at h <;> first | (cases h; exact ⟨_, rfl⟩) | cases h

theorem allIn_asTuple {v : Value} {vs : List Value} (hv : AllIn Q v) (h : v.asTuple? = some vs) :
    ∀ x ∈ vs, AllIn Q x := by
  cases v <;> simp [Value.asTuple?] at h
  subst h
  exact (allIns_iff Q _).1 hv

theorem allIn_asCase {v w : Value} {op : MixopS} (hv : AllIn Q v)
    (h : v.asCase? = some (op, w)) : AllIn Q w := by
  cases v <;> simp [Value.asCase?] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hv

theorem allIn_asOpt {v : Value} {o : Option Value} (hv : AllIn Q v) (h : v.asOpt? = some o) :
    ∀ w, o = some w → AllIn Q w := by
  cases v <;> simp [Value.asOpt?] at h
  subst h
  rintro w rfl
  exact hv

/-! ## Lists -/

theorem mapM_erase {f f' : Exp → Res Value} :
    ∀ es : List Exp, (∀ e ∈ es, EOK Q (f e) (f' e)) →
      es.mapM f' = List.map eraseV <$> es.mapM f ∧
        ∀ vs, es.mapM f = .ok vs → ∀ v ∈ vs, AllIn Q v
  | [], _ => ⟨rfl, fun vs h => by cases h; simp⟩
  | e :: es, h => by
    obtain ⟨he, hA⟩ := h e (List.mem_cons_self ..)
    obtain ⟨hes, hAs⟩ := mapM_erase es fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.mapM_cons, he, hes]
    cases hf : f e with
    | error err => exact ⟨rfl, fun vs h => by simp at h⟩
    | ok v =>
      cases hfs : es.mapM f with
      | error err => exact ⟨rfl, fun vs h => by simp at h⟩
      | ok vs =>
        refine ⟨rfl, fun ws h => ?_⟩
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hA w hf
        · exact hAs vs hfs w hw

theorem mapM_eraseF {f f' : ExpField → Res (AtomS × Value)} :
    ∀ fs : List ExpField,
      (∀ g ∈ fs, f' g = (fun p => (p.1, eraseV p.2)) <$> f g ∧
        ∀ p, f g = .ok p → AllIn Q p.2 ∧ p.1 ≠ "EXPORTS") →
      fs.mapM f' = List.map (fun p => (p.1, eraseV p.2)) <$> fs.mapM f ∧
        ∀ gs, fs.mapM f = .ok gs → ∀ p ∈ gs, AllIn Q p.2 ∧ p.1 ≠ "EXPORTS"
  | [], _ => ⟨rfl, fun gs h => by cases h; simp⟩
  | g :: fs, h => by
    obtain ⟨he, hA⟩ := h g (List.mem_cons_self ..)
    obtain ⟨hes, hAs⟩ := mapM_eraseF fs fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.mapM_cons, he, hes]
    cases hf : f g with
    | error err => exact ⟨rfl, fun vs h => by simp at h⟩
    | ok v =>
      cases hfs : fs.mapM f with
      | error err => exact ⟨rfl, fun vs h => by simp at h⟩
      | ok vs =>
        refine ⟨rfl, fun ws h => ?_⟩
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hA w hf
        · exact hAs vs hfs w hw

/-! ## The fragment -/

/-- **The first-order fragment at fuel `n`.** -/
def FOAt (env : Env) (Q : Value → Prop) (n : Nat) : Prop :=
  (∀ ρ e, ScopeIn Q ρ → FO e → EOK Q (evalExp n env ρ e) (evalExp n env (eraseScope ρ) e)) ∧
  (∀ ρ es, ScopeIn Q ρ → FOs es →
    evalExps n env (eraseScope ρ) es = List.map eraseV <$> evalExps n env ρ es ∧
      ∀ vs, evalExps n env ρ es = .ok vs → ∀ v ∈ vs, AllIn Q v) ∧
  (∀ ρ fs, ScopeIn Q ρ → FOf fs →
    evalExpFields n env (eraseScope ρ) fs =
        List.map (fun p => (p.1, eraseV p.2)) <$> evalExpFields n env ρ fs ∧
      ∀ gs, evalExpFields n env ρ fs = .ok gs → ∀ p ∈ gs, AllIn Q p.2 ∧ p.1 ≠ "EXPORTS")

theorem fos_mem : ∀ {es : List Exp}, FOs es → ∀ e ∈ es, FO e
  | _, .nil, _, h => by simp at h
  | _, .cons he hes, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact he
    · exact fos_mem hes e h

theorem fof_mem : ∀ {fs : List ExpField}, FOf fs → ∀ g ∈ fs,
    ∃ a e, g = .mk a e ∧ a ≠ "EXPORTS" ∧ FO e
  | _, .nil, _, h => by simp at h
  | _, .cons ha he hfs, g, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, _, rfl, ha, he⟩
    · exact fof_mem hfs g h

theorem allIns_of_mem {vs : List Value} (h : ∀ v ∈ vs, AllIn Q v) : AllIns Q vs :=
  (allIns_iff Q vs).2 h

/-- The map of a result by `List.map eraseV`, as an `EOK` of the tuple or list built from it. -/
theorem EOK.ofList (mk : List Value → Value) (hmk : ∀ vs, eraseV (mk vs) = mk (vs.map eraseV))
    (hA : ∀ vs, (∀ v ∈ vs, AllIn Q v) → AllIn Q (mk vs)) {r r' : Res (List Value)}
    (h : r' = List.map eraseV <$> r) (hr : ∀ vs, r = .ok vs → ∀ v ∈ vs, AllIn Q v) :
    EOK Q (mk <$> r) (mk <$> r') := by
  subst h
  cases r with
  | error e => exact EOK.error e
  | ok vs =>
    refine ⟨by simp [hmk], fun v hv => ?_⟩
    simp only [Functor.map, Except.map, Except.ok.injEq] at hv
    subst hv
    exact hA vs (hr vs rfl)

theorem foAt_zero (env : Env) : FOAt env Q 0 :=
  ⟨fun _ _ _ _ => by simp only [evalExp]; exact EOK.error _,
   fun _ _ _ _ => ⟨by simp [evalExps], fun _ h => by simp [evalExps] at h⟩,
   fun _ _ _ _ => ⟨by simp [evalExpFields], fun _ h => by simp [evalExpFields] at h⟩⟩

theorem foAt_succ (hQ : QInj Q) (env : Env) (n : Nat) (ih : FOAt env Q n) :
    FOAt env Q (n + 1) := by
  obtain ⟨ihE, ihEs, ihF⟩ := ih
  refine ⟨fun ρ e hρ he => ?_, fun ρ es hρ hes => ?_, fun ρ fs hρ hfs => ?_⟩
  · cases he with
    | varE x =>
      simp only [evalExp]
      exact EOK.ofOption (find?_eraseScope ρ x) fun v hv => hρ.find? hv
    | boolE b => simp only [evalExp]; exact EOK.ok (v := .bool b) trivial
    | numE m => simp only [evalExp]; exact EOK.ok (v := .num m) trivial
    | textE t => simp only [evalExp]; exact EOK.ok (v := .text t) trivial
    | unE h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ _ => ?_
      rw [unValue_eraseV]
      exact EOK.of_bool_num (unValue_bn _ v)
    | binE h₁ h₂ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ _ => ?_
      rw [boolShort_eraseV]
      cases hb : boolShort _ v with
      | some u =>
        obtain ⟨b, rfl⟩ := boolShort_bool hb
        exact EOK.ok (v := .bool b) trivial
      | none =>
        refine (ihE ρ _ hρ h₂).bind fun w _ _ => ?_
        rw [binValues_eraseV]
        exact EOK.of_bool_num (binValues_bn _ v w)
    | cmpE h₁ h₂ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => (ihE ρ _ hρ h₂).bind fun w _ hw => ?_
      rw [cmpValues_eraseV hQ hv hw]
      exact EOK.of_bool_num fun u hu => .inl (cmpValues_bn _ v w u hu)
    | tupE hs =>
      simp only [evalExp]
      obtain ⟨h₁, h₂⟩ := ihEs ρ _ hρ hs
      exact EOK.ofList Value.tuple (fun vs => eraseV_tuple' vs) (fun vs h => allIns_of_mem h) h₁ h₂
    | projE h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => ?_
      rw [asTuple?_eraseV]
      cases ht : v.asTuple? with
      | none => exact EOK.error _
      | some vs =>
        refine EOK.ofOption ?_ ?_
        · split <;> simp [List.getElem?_map]
        · intro u hu
          split at hu
          · exact allIn_asTuple hv ht u (List.mem_of_getElem? hu)
          · cases hu
    | @caseE op _ h₁ =>
      simp only [evalExp]
      exact EOK.map (Value.case op) (fun _ => rfl) (fun _ h => h) (ihE ρ _ hρ h₁)
    | @uncaseE _ op h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => ?_
      rw [asCase?_eraseV]
      cases ht : v.asCase? with
      | none => exact EOK.error _
      | some p =>
        obtain ⟨op', w⟩ := p
        simp only [Option.map_some, Res.ofOption_some]
        show EOK Q (Res.assert (op' = op) (.ok w)) (Res.assert (op' = op) (.ok (eraseV w)))
        by_cases he : op' = op
        · simp only [Res.assert_pos he]; exact EOK.ok (allIn_asCase hv ht)
        · simp only [Res.assert_neg he]; exact EOK.error _
    | optNone => simp only [evalExp]; exact EOK.ok (v := .opt none) trivial
    | optSome h₁ =>
      simp only [evalExp]
      exact EOK.map (fun v => Value.opt (some v)) (fun _ => rfl) (fun _ h => h) (ihE ρ _ hρ h₁)
    | theE h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => ?_
      rw [asOpt?_eraseV]
      cases ht : v.asOpt? with
      | none => exact EOK.error _
      | some o =>
        simp only [Option.map_some, Res.ofOption_some]
        show EOK Q (Res.ofOption o) (Res.ofOption (o.map eraseV))
        exact EOK.ofOption rfl (allIn_asOpt hv ht)
    | strE hs =>
      simp only [evalExp]
      obtain ⟨h₁, h₂⟩ := ihF ρ _ hρ hs
      rw [h₁]
      cases hr : evalExpFields n env ρ _ with
      | error e => exact EOK.error e
      | ok gs =>
        have hg := h₂ gs hr
        have hn : NoExpF gs := fun p hp => (hg p hp).2
        refine ⟨?_, fun v hv => ?_⟩
        · simp [eraseV_struct_of_noExp hn]
        · simp only [Functor.map, Except.map, Except.ok.injEq] at hv
          subst hv
          exact allIn_struct_of_noExp hn fun p hp => (hg p hp).1
    | dotE ha h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => ?_
      exact EOK.ofOption (field?_eraseV ha v) fun u hu => hv.field? hu
    | listE hs =>
      simp only [evalExp]
      obtain ⟨h₁, h₂⟩ := ihEs ρ _ hρ hs
      exact EOK.ofList Value.list (fun vs => eraseV_list' vs) (fun vs h => allIns_of_mem h) h₁ h₂
    | liftE h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => ?_
      rw [asOpt?_eraseV]
      cases ht : v.asOpt? with
      | none => exact EOK.error _
      | some o =>
        simp only [Option.map_some, Res.ofOption_some]
        show EOK Q (.ok (.list o.toList)) (.ok (.list (o.map eraseV).toList))
        have := EOK.ok (Q := Q) (v := .list o.toList) ((allIns_iff Q _).2 fun w hw =>
          allIn_asOpt hv ht w (Option.mem_toList.1 hw))
        cases o <;> simpa [eraseVs_eq_map] using this
    | memE h₁ h₂ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => (ihE ρ _ hρ h₂).bind fun w _ hw => ?_
      rw [memValue_eraseV hQ hv hw]
      exact EOK.of_bool_num fun u hu => .inl (memValue_bn v w u hu)
    | lenE h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => ?_
      rw [len?_eraseV]
      exact EOK.of_bool_num fun u hu => by
        simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at hu
        obtain ⟨k, -, rfl⟩ := hu
        exact .inr ⟨_, rfl⟩
    | catE h₁ h₂ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => (ihE ρ _ hρ h₂).bind fun w _ hw => ?_
      exact EOK.ofOption (cat?_eraseV v w) fun u hu => AllIn.cat? hv hw hu
    | idxE h₁ h₂ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => (ihE ρ _ hρ h₂).bind fun w _ _ => ?_
      rw [asNat?_eraseV]
      cases w.asNat? with
      | none => exact EOK.error _
      | some i =>
        simp only [Res.ofOption_some]
        show EOK Q (Res.ofOption (v.idx? i)) (Res.ofOption ((eraseV v).idx? i))
        exact EOK.ofOption (idx?_eraseV v i) fun u hu => hv.idx? hu
    | sliceE h₁ h₂ h₃ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ hv => (ihE ρ _ hρ h₂).bind fun w _ _ =>
        (ihE ρ _ hρ h₃).bind fun x _ _ => ?_
      rw [asNat?_eraseV, asNat?_eraseV]
      cases w.asNat? with
      | none => exact EOK.error _
      | some i =>
        cases x.asNat? with
        | none => exact EOK.error _
        | some k =>
          simp only [Res.ofOption_some]
          show EOK Q (Res.ofOption (v.slice? i k)) (Res.ofOption ((eraseV v).slice? i k))
          exact EOK.ofOption (slice?_eraseV v i k) fun u hu => hv.slice? hu
    | cvtE h₁ =>
      simp only [evalExp]
      refine (ihE ρ _ hρ h₁).bind fun v _ _ => ?_
      rw [asNum?_eraseV]
      cases v.asNum? with
      | none => exact EOK.error _
      | some m =>
        exact EOK.of_bool_num fun u hu => by
          simp only [Res.ofOption_some, bind, Except.bind, Res.ofOption_eq_ok,
            Option.map_eq_some_iff] at hu
          obtain ⟨k, -, rfl⟩ := hu
          exact .inr ⟨_, rfl⟩
    | subE h₁ =>
      simp only [evalExp]
      exact ihE ρ _ hρ h₁
  · simp only [evalExps]
    exact mapM_erase es fun e he => ihE ρ e hρ (fos_mem hes e he)
  · simp only [evalExpFields]
    refine mapM_eraseF fs fun g hg => ?_
    obtain ⟨a, e, rfl, ha, he⟩ := fof_mem hfs g hg
    obtain ⟨h₁, h₂⟩ := ihE ρ e hρ he
    simp only [h₁]
    cases hr : evalExp n env ρ e with
    | error err => exact ⟨rfl, fun p h => by simp at h⟩
    | ok v =>
      refine ⟨rfl, fun p h => ?_⟩
      simp only [Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact ⟨h₂ v hr, ha⟩

theorem foAt (hQ : QInj Q) (env : Env) : ∀ n, FOAt env Q n
  | 0 => foAt_zero env
  | n + 1 => foAt_succ hQ env n (foAt hQ env n)

/-- **The first-order evaluator fragment commutes with erasing export lists**: at every fuel, on a
scope in the swap set `AllIn Q` with `QInj Q`, a first-order expression evaluates at the erased
scope to the erased answer, and its answer is in the swap set. -/
theorem eraseFO (hQ : QInj Q) (env : Env) (n : Nat) {ρ : VarEnv} {e : Exp} (hρ : ScopeIn Q ρ)
    (he : FO e) : EOK Q (evalExp n env ρ e) (evalExp n env (eraseScope ρ) e) :=
  (foAt hQ env n).1 ρ e hρ he

end Silmaril.Wasm.SpecTec.Sim.Round7.Erase
