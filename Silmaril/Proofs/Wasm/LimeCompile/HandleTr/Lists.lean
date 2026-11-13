module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Pair

/-!
# List lemmas for the handle compiler's session simulation

* `getElem?_mapM`: an element of a successful `mapM`;
* `find?_mapM`: `find?` by name commutes with a name-preserving `mapM`;
* `fwd_body`: a forwarding body is `js.map local.get`;
* `args_src`, `args_tgt`: `ArgRelT`-related argument lists at 2.0 parameter types transfer
  well-typedness (`Forall₂ ValOk`) in both directions, and contain no function reference;
* `proj_src`, `proj_tgt`: projections of related arguments are pointwise `ResRel`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.HandleTr
open Silmaril.Wasm.LimeCompile.Handle (handleRef ResRel)

variable {H : Type}

theorem getElem?_mapM {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → ∀ i : Nat, l'[i]? = (l[i]?).bind g
  | [], l', h, i => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | a :: l, l', h, i => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l'', hl'', h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    cases i with
    | zero => simp [hb]
    | succ i => simpa using getElem?_mapM hl'' i

theorem length_mapM' {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l'', hl'', h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simp [length_mapM' hl'']

theorem find?_mapM {α β : Type} {g : α → Option β} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, g a = some b → q b = p a) :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → l'.find? q = (l.find? p).bind g
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l'', hl'', h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rw [List.find?_cons, List.find?_cons, hpq a b hb]
    cases p a
    · exact find?_mapM hpq hl''
    · simp [hb]

/-- The `local.get` indices of a forwarding body. -/
def getIdx : Instr → Option LocalIdx
  | .localGet j => some j
  | _ => none

theorem localGets_eq : ∀ l : List Instr,
    (∀ x ∈ l, (match x with | .localGet _ => true | _ => false) = true) →
      l = (l.filterMap getIdx).map .localGet
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i List.mem_cons_self
    have his := localGets_eq is fun x hx => h x (List.mem_cons_of_mem i hx)
    split at hi
    · rename_i j
      rw [List.filterMap_cons_some (by rfl), List.map_cons, ← his]
    · cases hi

theorem fwd_body {f : Func} (hf : fwdFunc f = true) :
    f.locals = [] ∧ ∃ js : List LocalIdx, f.body = js.map .localGet := by
  simp only [fwdFunc, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hf
  exact ⟨hf.1, _, localGets_eq f.body hf.2⟩

/-- Related arguments at 2.0 parameter types. -/
def ArgsAt (σ : List Val) (τs : List V2.ValType) (ws vs : List Val) : Prop :=
  List.Forall₂ (fun w tv => ArgRelT σ tv.1 w tv.2) ws ((τs.map V2.ValType.toCore).zip vs)

theorem args_src {σ : List Val} {s s' : Store H} :
    ∀ {τs : List V2.ValType} {ws vs : List Val}, ArgsAt σ τs ws vs → vs.length = τs.length →
      List.Forall₂ (ValOk s') ws (τs.map fun τ => (hV2val τ).toC) →
      List.Forall₂ (ValOk s) vs (τs.map V2.ValType.toC) ∧ NoFuncRef vs
  | [], ws, vs, h, hl, _ => by
    simp only [List.length_nil, List.length_eq_zero_iff] at hl
    subst hl
    exact ⟨.nil, by simp [NoFuncRef]⟩
  | τ :: τs, ws, v :: vs, h, hl, hw => by
    simp only [ArgsAt, List.map_cons, List.zip_cons_cons] at h
    obtain ⟨w, ws', hrel, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp h
    simp only [List.map_cons, List.forall₂_cons] at hw
    have hv := argOk_src (s := s) hrel hw.1
    obtain ⟨ih, ihn⟩ := args_src hrest (by simpa using hl) hw.2
    refine ⟨.cons hv ih, ?_⟩
    intro u hu b
    rcases List.mem_cons.mp hu with rfl | hu
    · exact argRel_src_not_func hrel hv b
    · exact ihn u hu b
  | τ :: τs, ws, [], _, hl, _ => by simp at hl

theorem args_tgt {σ : List Val} {s s' : Store H} :
    ∀ {τs : List V2.ValType} {ws vs : List Val}, ArgsAt σ τs ws vs →
      List.Forall₂ (ValOk s) vs (τs.map V2.ValType.toC) →
      List.Forall₂ (ValOk s') ws (τs.map fun τ => (hV2val τ).toC) ∧ NoFuncRef ws ∧ NoFuncRef vs
  | [], ws, vs, h, hv => by
    cases hv
    cases h
    exact ⟨.nil, by simp [NoFuncRef], by simp [NoFuncRef]⟩
  | τ :: τs, ws, vs, h, hv => by
    simp only [List.map_cons] at hv
    obtain ⟨v, vs', hv1, hv2, rfl⟩ := List.forall₂_cons_right_iff.mp hv
    simp only [ArgsAt, List.map_cons, List.zip_cons_cons] at h
    obtain ⟨w, ws', hrel, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp h
    obtain ⟨ih, ihw, ihv⟩ := args_tgt (s' := s') hrest hv2
    refine ⟨.cons (argOk_tgt hrel hv1) ih, ?_, ?_⟩
    · intro u hu b
      rcases List.mem_cons.mp hu with rfl | hu
      · exact argRel_tgt_not_func hrel hv1 b
      · exact ihw u hu b
    · intro u hu b
      rcases List.mem_cons.mp hu with rfl | hu
      · exact argRel_src_not_func hrel hv1 b
      · exact ihv u hu b

theorem args_get {σ : List Val} :
    ∀ {τs : List V2.ValType} {ws vs : List Val}, ArgsAt σ τs ws vs → vs.length = τs.length →
      ws.length = vs.length ∧ ∀ (j : Nat) w v, ws[j]? = some w → vs[j]? = some v → ResRel σ w v
  | [], ws, vs, h, hl => by
    simp only [List.length_nil, List.length_eq_zero_iff] at hl
    subst hl
    cases h
    exact ⟨rfl, by simp⟩
  | τ :: τs, ws, v :: vs, h, hl => by
    simp only [ArgsAt, List.map_cons, List.zip_cons_cons] at h
    obtain ⟨w, ws', hrel, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp h
    obtain ⟨ihl, ih⟩ := args_get hrest (by simpa using hl)
    refine ⟨by simp [ihl], ?_⟩
    intro j w' v' hw hv
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hv
      subst hw hv
      exact resRel_of_argRel hrel
    | succ j => exact ih j w' v' (by simpa using hw) (by simpa using hv)
  | τ :: τs, ws, [], _, hl => by simp at hl

theorem proj_rel {σ : List Val} {ws vs : List Val} (hl : ws.length = vs.length)
    (h : ∀ (j : Nat) w v, ws[j]? = some w → vs[j]? = some v → ResRel σ w v) :
    ∀ {js : List LocalIdx} {us' : List Val}, proj js ws = some us' →
      ∃ us, proj js vs = some us ∧ List.Forall₂ (ResRel σ) us' us
  | [], us', hp => by
    simp only [proj, List.mapM_nil, Option.pure_def, Option.some.injEq] at hp
    subst hp
    exact ⟨[], rfl, .nil⟩
  | j :: js, us', hp => by
    simp only [proj, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hp
    obtain ⟨w, hw, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨us'', hus'', hp⟩ := Option.bind_eq_some_iff.mp hp
    cases hp
    obtain ⟨us, hus, hrel⟩ := proj_rel hl h hus''
    have hj : j.toNat < vs.length := by
      rw [← hl]
      exact (List.getElem?_eq_some_iff.mp hw).1
    obtain ⟨v, hv⟩ : ∃ v, vs[j.toNat]? = some v := ⟨_, List.getElem?_eq_getElem hj⟩
    refine ⟨v :: us, ?_, .cons (h _ w v hw hv) hrel⟩
    simp only [proj] at hus
    simp [proj, hv, hus]

theorem proj_rel' {σ : List Val} {ws vs : List Val} (hl : ws.length = vs.length)
    (h : ∀ (j : Nat) w v, ws[j]? = some w → vs[j]? = some v → ResRel σ w v) :
    ∀ {js : List LocalIdx} {us : List Val}, proj js vs = some us →
      ∃ us', proj js ws = some us' ∧ List.Forall₂ (ResRel σ) us' us
  | [], us, hp => by
    simp only [proj, List.mapM_nil, Option.pure_def, Option.some.injEq] at hp
    subst hp
    exact ⟨[], rfl, .nil⟩
  | j :: js, us, hp => by
    simp only [proj, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hp
    obtain ⟨v, hv, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨us'', hus'', hp⟩ := Option.bind_eq_some_iff.mp hp
    cases hp
    obtain ⟨us', hus', hrel⟩ := proj_rel' hl h hus''
    have hj : j.toNat < ws.length := by
      rw [hl]
      exact (List.getElem?_eq_some_iff.mp hv).1
    obtain ⟨w, hw⟩ : ∃ w, ws[j.toNat]? = some w := ⟨_, List.getElem?_eq_getElem hj⟩
    refine ⟨w :: us', ?_, .cons (h _ w v hw hv) hrel⟩
    simp only [proj] at hus'
    simp [proj, hw, hus']

theorem proj_length {vs : List Val} : ∀ {js : List LocalIdx} {us : List Val},
    proj js vs = some us → us.length = js.length
  | [], us, hp => by
    simp only [proj, List.mapM_nil, Option.pure_def, Option.some.injEq] at hp
    subst hp
    rfl
  | j :: js, us, hp => by
    simp only [proj, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hp
    obtain ⟨v, hv, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨us'', hus'', hp⟩ := Option.bind_eq_some_iff.mp hp
    cases hp
    simp [proj_length hus'']

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
