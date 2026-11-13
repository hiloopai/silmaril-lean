module

public import Silmaril.Proofs.Wasm.Wit.Text.Lists
public import Silmaril.Proofs.Wasm.Wit.Text.Ty

/-!
# WIT text: functions and type definitions read back

Parameters, signatures, function types, record fields, variant cases, labels,
resource functions and type definitions read back from their printing (resource
functions and type definitions up to `ResourceFunc.norm`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open _root_.Silmaril.Wasm.Wit.Text.Parse

/-! ## Item starts -/

/-- What may follow docs and gates: not a doc line, not `@`. -/
abbrev ItemStart (r : List Tok) : Prop := NoDoc r ∧ r.head? ≠ some (.sym '@')

theorem itemStart_kw (w : Kw) (r : List Tok) : ItemStart (.kw w :: r) :=
  ⟨fun s h => by simp at h, by simp⟩

theorem itemStart_id (s : String) (r : List Tok) : ItemStart (.id s :: r) :=
  ⟨fun s h => by simp at h, by simp⟩

theorem gateVOk_of_gateOk {g : Gate} (h : gateOk g = true) : gateVOk g = true := by
  cases g <;> simp_all [gateOk, gateVOk]

theorem noDoc_prGates (gs : List Gate) {r : List Tok} (h : NoDoc r) :
    NoDoc (toks (prGates gs) ++ r) := by
  cases gs with
  | nil => simpa [prGates] using h
  | cons g gs => intro s; cases g <;> simp [prGates, prGate]

/-- Docs and gates before an item read back. -/
theorem docs_gates (d : Docs) (gs : List Gate) (hg : gs.all gateOk = true) {r : List Tok}
    (hr : ItemStart r) :
    docs (toks (prDocs d) ++ (toks (prGates gs) ++ r)) = (d, toks (prGates gs) ++ r) ∧
      gates (toks (prGates gs) ++ r) = some (gs, r) :=
  ⟨docs_prDocs d (noDoc_prGates gs hr.1),
   gates_prGates gs (fun g hm => gateVOk_of_gateOk (List.all_eq_true.mp hg g hm)) hr.2⟩

@[simp] theorem docs_prDocs_id (d : Docs) (s : String) (r : List Tok) :
    docs (toks (prDocs d) ++ (.id s :: r)) = (d, .id s :: r) :=
  docs_prDocs d (fun _ h => by simp at h)

@[simp] theorem docs_prDocs_kw (d : Docs) (w : Kw) (r : List Tok) :
    docs (toks (prDocs d) ++ (.kw w :: r)) = (d, .kw w :: r) :=
  docs_prDocs d (fun _ h => by simp at h)

theorem docs_nil {r : List Tok} (h : NoDoc r) : docs r = ({}, r) := by
  simpa [prDocs] using docs_prDocs {} h

theorem head_docs_ne (d : Docs) (t : Tok) (r : List Tok) (ht : ∀ c, t ≠ .sym c) (c : Char) :
    (toks (prDocs d) ++ t :: r).head? ≠ some (.sym c) := by
  obtain ⟨c'⟩ := d
  cases c' with
  | none => simpa [prDocs] using ht c
  | some s =>
    cases hs : splitOn '\n' s.toList with
    | nil => exact absurd hs (splitOn_ne_nil _ _)
    | cons w ws => simp [prDocs, toks, hs]

theorem head_docs_gates_ne (d : Docs) (gs : List Gate) (t : Tok) (r : List Tok)
    (ht : ∀ c, t ≠ .sym c) :
    (toks (prDocs d) ++ (toks (prGates gs) ++ t :: r)).head? ≠ some (.sym '}') := by
  obtain ⟨c'⟩ := d
  cases c' with
  | none =>
    cases gs with
    | nil => simpa [prDocs, prGates] using ht '}'
    | cons g gs => cases g <;> simp [prDocs, prGates, prGate]
  | some s =>
    cases hs : splitOn '\n' s.toList with
    | nil => exact absurd hs (splitOn_ne_nil _ _)
    | cons w ws => simp [prDocs, toks, hs]

/-! ## Functions -/

theorem param_prParam (x : Name × Ty) : ∀ n r, (prParam x).length ≤ n → NotLt r →
    param n (toks (prParam x) ++ r) = some (x, r) := by
  intro n r h hr
  obtain ⟨s, t⟩ := x
  simp only [prParam] at h ⊢
  unfold_toks
  simp only [param]
  rw [ty_prTy t n r (by omega) hr]
  rfl

theorem readsSep_param (ps : List (Name × Ty)) : ReadsSep param prParam (.sym ')') ps := by
  intro x _
  refine ⟨by simp [prParam], fun r => by simp [prParam], fun n r h hr => ?_⟩
  exact param_prParam x n r h (by rcases hr with hr | hr <;> simp [hr])

theorem sig_none (ps : List (Name × Ty)) (n : Nat) (r : List Tok)
    (h : (prSig ps none).length ≤ n) :
    sig n (toks (prSig ps none) ++ .sym ';' :: r) = some ((ps, none), .sym ';' :: r) := by
  simp only [prSig] at h ⊢
  unfold_toks
  simp only [sig]
  rw [sepBy_prSep (by decide) ps (readsSep_param ps) n _ (by omega) rfl]
  rfl

theorem sig_some (ps : List (Name × Ty)) (t : Ty) (n : Nat) (r : List Tok)
    (h : (prSig ps (some t)).length ≤ n) :
    sig n (toks (prSig ps (some t)) ++ .sym ';' :: r) = some ((ps, some t), .sym ';' :: r) := by
  simp only [prSig] at h ⊢
  unfold_toks
  simp only [sig]
  rw [sepBy_prSep (by decide) ps (readsSep_param ps) n _ (by omega) rfl]
  simp only
  rw [ty_prTy t n _ (by omega) (by simp)]
  rfl

theorem sig_prSig (ps : List (Name × Ty)) (res : Option Ty) : ∀ n r,
    (prSig ps res).length ≤ n → r.head? = some (.sym ';') →
    sig n (toks (prSig ps res) ++ r) = some ((ps, res), r) := by
  intro n r h hr
  obtain ⟨r', rfl⟩ : ∃ r', r = .sym ';' :: r' := by
    cases r with
    | nil => simp at hr
    | cons t r' => simp at hr; exact ⟨r', by rw [hr]⟩
  cases res with
  | none => exact sig_none ps n r' h
  | some t => exact sig_some ps t n r' h

theorem func_prFunc (f : Func) : ∀ n r, (prFunc f).length ≤ n →
    r.head? = some (.sym ';') → func n (toks (prFunc f) ++ r) = some (f, r) := by
  intro n r h hr
  obtain ⟨ps, res, a⟩ := f
  cases a with
  | true =>
    simp only [prFunc, ite_true] at h ⊢
    unfold_toks
    simp only [func]
    rw [sig_prSig ps res n r (by omega) hr]
    rfl
  | false =>
    simp only [prFunc, Bool.false_eq_true, ite_false] at h ⊢
    unfold_toks
    simp only [func]
    rw [sig_prSig ps res n r (by omega) hr]
    rfl

theorem prFunc_head (f : Func) (r : List Tok) :
    ∃ r', toks (prFunc f) ++ r = .kw .async :: r' ∨ toks (prFunc f) ++ r = .kw .func :: r' := by
  obtain ⟨ps, res, a⟩ := f
  cases a <;> simp [prFunc]

/-! ## Record fields, variant cases, labels -/

theorem field_prField (f : Field) : ∀ n r, (prField f).length ≤ n → NotLt r →
    field n (toks (prField f) ++ r) = some (f, r) := by
  intro n r h hr
  obtain ⟨s, t, d⟩ := f
  simp only [prField] at h ⊢
  unfold_toks
  simp only [field, docs_prDocs_id]
  rw [ty_prTy t n r (by omega) hr]
  rfl

theorem readsSep_field (fs : List Field) : ReadsSep field prField (.sym '}') fs := by
  intro x _
  refine ⟨by simp [prField]; omega, fun r => ?_, fun n r h hr => ?_⟩
  · simpa [prField] using head_docs_ne x.docs (.id x.name)
      (.sym ':' :: (toks (prTy x.ty) ++ r)) (by simp) '}'
  · exact field_prField x n r h (by rcases hr with hr | hr <;> simp [hr])

theorem case_prCase (c : Case) : ∀ n r, (prCase c).length ≤ n → SepFollow (.sym '}') r →
    case n (toks (prCase c) ++ r) = some (c, r) := by
  intro n r h hr
  obtain ⟨s, t, d⟩ := c
  have h1 : r.head? ≠ some (.sym '(') := by rcases hr with hr | hr <;> simp [hr]
  cases t with
  | none =>
    simp only [prCase] at h ⊢
    unfold_toks
    simp [case, docs_prDocs_id, h1]
  | some t =>
    simp only [prCase] at h ⊢
    unfold_toks
    simp only [case, docs_prDocs_id, List.head?_cons, ite_true,
      List.tail_cons]
    rw [ty_prTy t n _ (by omega) (by simp)]
    simp [andThen, expect]

theorem readsSep_case (cs : List Case) : ReadsSep case prCase (.sym '}') cs := by
  intro x _
  refine ⟨by simp [prCase]; omega, fun r => ?_, fun n r h hr => case_prCase x n r h hr⟩
  obtain ⟨s, t, d⟩ := x
  cases t with
  | none =>
    have := head_docs_ne d (.id s) r (by simp) '}'
    simpa [prCase] using this
  | some t =>
    have := head_docs_ne d (.id s) (.sym '(' :: (toks (prTy t) ++ (.sym ')' :: r))) (by simp) '}'
    simpa [prCase] using this

theorem readsSep_label (ls : List Label) : ReadsSep label prLabel (.sym '}') ls := by
  intro x _
  refine ⟨by simp [prLabel], fun r => ?_, fun n r h hr => ?_⟩
  · simpa [prLabel] using head_docs_ne x.docs (.id x.name) r (by simp) '}'
  · obtain ⟨s, d⟩ := x
    simp only [prLabel]
    unfold_toks
    simp [label, docs_prDocs_id]

/-! ## Resource functions and type definitions -/

theorem resFunc_ctor (fn : Func) (d : Docs) (gs : List Gate) (hg : gs.all gateOk = true)
    (n : Nat) (r : List Tok) (h : (prResFunc ⟨.ctor, fn, d, gs⟩).length ≤ n) :
    resFunc n (toks (prResFunc ⟨.ctor, fn, d, gs⟩) ++ r) =
      some (ResourceFunc.norm ⟨.ctor, fn, d, gs⟩, r) := by
  simp only [prResFunc] at h ⊢
  unfold_toks
  obtain ⟨h1, h2⟩ := docs_gates d gs hg (itemStart_kw .ctor
    (toks (prSig fn.params fn.result) ++ (Tok.sym ';' :: r)))
  simp only [resFunc, h1, h2]
  rw [sig_prSig fn.params fn.result n _ (by omega) rfl]
  simp [andThen, expect, ResourceFunc.norm]

theorem resFunc_method (fn : Func) (d : Docs) (gs : List Gate) (hg : gs.all gateOk = true)
    (s : Name) (n : Nat) (r : List Tok) (h : (prResFunc ⟨.method s, fn, d, gs⟩).length ≤ n) :
    resFunc n (toks (prResFunc ⟨.method s, fn, d, gs⟩) ++ r) =
      some (ResourceFunc.norm ⟨.method s, fn, d, gs⟩, r) := by
  simp only [prResFunc] at h ⊢
  unfold_toks
  obtain ⟨h1, h2⟩ := docs_gates d gs hg (itemStart_id s
    (Tok.sym ':' :: (toks (prFunc fn) ++ (Tok.sym ';' :: r))))
  simp only [resFunc, h1, h2]
  obtain ⟨r', hr'⟩ := prFunc_head fn (Tok.sym ';' :: r)
  rcases hr' with hr' | hr' <;>
  · simp only [hr']
    rw [← hr', func_prFunc fn n _ (by omega) rfl]
    simp [andThen, expect, ResourceFunc.norm]

theorem resFunc_static (fn : Func) (d : Docs) (gs : List Gate) (hg : gs.all gateOk = true)
    (s : Name) (n : Nat) (r : List Tok) (h : (prResFunc ⟨.static s, fn, d, gs⟩).length ≤ n) :
    resFunc n (toks (prResFunc ⟨.static s, fn, d, gs⟩) ++ r) =
      some (ResourceFunc.norm ⟨.static s, fn, d, gs⟩, r) := by
  simp only [prResFunc] at h ⊢
  unfold_toks
  obtain ⟨h1, h2⟩ := docs_gates d gs hg (itemStart_id s
    (Tok.sym ':' :: Tok.kw .static :: (toks (prFunc fn) ++ (Tok.sym ';' :: r))))
  simp only [resFunc, h1, h2]
  rw [func_prFunc fn n _ (by omega) rfl]
  simp [andThen, expect, ResourceFunc.norm]

theorem resFunc_prResFunc (f : ResourceFunc) (hf : resFuncOk f = true) : ∀ n r,
    (prResFunc f).length ≤ n →
    resFunc n (toks (prResFunc f) ++ r) = some (ResourceFunc.norm f, r) := by
  intro n r h
  obtain ⟨kind, fn, d, gs⟩ := f
  have hg : gs.all gateOk = true := by
    simp only [resFuncOk, Bool.and_eq_true] at hf; exact hf.1.1
  cases kind with
  | ctor => exact resFunc_ctor fn d gs hg n r h
  | method s => exact resFunc_method fn d gs hg s n r h
  | static s => exact resFunc_static fn d gs hg s n r h

theorem readsMany_resFunc (fs : List ResourceFunc) (hf : fs.all resFuncOk = true) :
    ReadsMany resFunc prResFunc ResourceFunc.norm fs := by
  intro x hx
  refine ⟨?_, fun r => ?_, fun n r h => resFunc_prResFunc x (List.all_eq_true.mp hf x hx) n r h⟩
  · obtain ⟨kind, fn, d, gs⟩ := x
    cases kind <;> simp [prResFunc] <;> omega
  · obtain ⟨kind, fn, d, gs⟩ := x
    cases kind with
    | ctor =>
      simp only [prResFunc, toks_append, List.append_assoc]
      exact head_docs_gates_ne d gs _ _ (by simp)
    | method s =>
      simp only [prResFunc, toks_append, List.append_assoc, toks_cons, List.cons_append]
      exact head_docs_gates_ne d gs _ _ (by simp)
    | static s =>
      simp only [prResFunc, toks_append, List.append_assoc, toks_cons, List.cons_append]
      exact head_docs_gates_ne d gs _ _ (by simp)

theorem typeDefBody_alias (nm : Name) (t : Ty) (n : Nat) (r : List Tok)
    (h : (prTypeDefBody nm (.alias t)).length ≤ n) :
    typeDefBody n (toks (prTypeDefBody nm (.alias t)) ++ r) =
      some ((nm, TypeDefKind.norm (.alias t)), r) := by
  simp only [prTypeDefBody] at h ⊢
  unfold_toks
  simp only [typeDefBody]
  rw [ty_prTy t n _ (by omega) (by simp)]
  simp [andThen, expect, TypeDefKind.norm]

theorem typeDefBody_record (nm : Name) (fs : List Field) (n : Nat) (r : List Tok)
    (h : (prTypeDefBody nm (.record fs)).length ≤ n) :
    typeDefBody n (toks (prTypeDefBody nm (.record fs)) ++ r) =
      some ((nm, TypeDefKind.norm (.record fs)), r) := by
  simp only [prTypeDefBody] at h ⊢
  unfold_toks
  simp only [typeDefBody, braced]
  rw [sepBy_prTerm fs (readsSep_field fs) n _ (by omega) rfl]
  simp [andThen, expect, TypeDefKind.norm]

theorem typeDefBody_variant (nm : Name) (cs : List Case) (n : Nat) (r : List Tok)
    (h : (prTypeDefBody nm (.variant cs)).length ≤ n) :
    typeDefBody n (toks (prTypeDefBody nm (.variant cs)) ++ r) =
      some ((nm, TypeDefKind.norm (.variant cs)), r) := by
  simp only [prTypeDefBody] at h ⊢
  unfold_toks
  simp only [typeDefBody, braced]
  rw [sepBy_prTerm cs (readsSep_case cs) n _ (by omega) rfl]
  simp [andThen, expect, TypeDefKind.norm]

theorem typeDefBody_enum (nm : Name) (ls : List Label) (n : Nat) (r : List Tok)
    (h : (prTypeDefBody nm (.enum ls)).length ≤ n) :
    typeDefBody n (toks (prTypeDefBody nm (.enum ls)) ++ r) =
      some ((nm, TypeDefKind.norm (.enum ls)), r) := by
  simp only [prTypeDefBody] at h ⊢
  unfold_toks
  simp only [typeDefBody, braced]
  rw [sepBy_prTerm ls (readsSep_label ls) n _ (by omega) rfl]
  simp [andThen, expect, TypeDefKind.norm]

theorem typeDefBody_flags (nm : Name) (ls : List Label) (n : Nat) (r : List Tok)
    (h : (prTypeDefBody nm (.flags ls)).length ≤ n) :
    typeDefBody n (toks (prTypeDefBody nm (.flags ls)) ++ r) =
      some ((nm, TypeDefKind.norm (.flags ls)), r) := by
  simp only [prTypeDefBody] at h ⊢
  unfold_toks
  simp only [typeDefBody, braced]
  rw [sepBy_prTerm ls (readsSep_label ls) n _ (by omega) rfl]
  simp [andThen, expect, TypeDefKind.norm]

theorem typeDefBody_resource (nm : Name) (f : ResourceFunc) (fs : List ResourceFunc)
    (hk : (f :: fs).all resFuncOk = true) (n : Nat) (r : List Tok)
    (h : (prTypeDefBody nm (.resource (f :: fs))).length ≤ n) :
    typeDefBody n (toks (prTypeDefBody nm (.resource (f :: fs))) ++ r) =
      some ((nm, TypeDefKind.norm (.resource (f :: fs))), r) := by
  simp only [prTypeDefBody] at h ⊢
  unfold_toks
  simp only [typeDefBody, braced]
  rw [many_flatMap (f :: fs) (readsMany_resFunc _ hk) n _ (by omega) (by simp)]
  simp [andThen, expect, TypeDefKind.norm]

theorem typeDefBody_pr (nm : Name) (k : TypeDefKind) (hk : typeDefKindOk k = true) : ∀ n r,
    (prTypeDefBody nm k).length ≤ n →
    typeDefBody n (toks (prTypeDefBody nm k) ++ r) = some ((nm, TypeDefKind.norm k), r) := by
  intro n r h
  cases k with
  | «alias» t => exact typeDefBody_alias nm t n r h
  | record fs => exact typeDefBody_record nm fs n r h
  | variant cs => exact typeDefBody_variant nm cs n r h
  | enum ls => exact typeDefBody_enum nm ls n r h
  | flags ls => exact typeDefBody_flags nm ls n r h
  | resource fs =>
    cases fs with
    | nil => simp [prTypeDefBody, typeDefBody, TypeDefKind.norm]
    | cons f fs => exact typeDefBody_resource nm f fs (by simpa [typeDefKindOk] using hk) n r h

end Silmaril.Wasm.Wit.Text
