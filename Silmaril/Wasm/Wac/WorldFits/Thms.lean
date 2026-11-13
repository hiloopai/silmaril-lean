module

public import Silmaril.Wasm.Wac.World.Thms
public import Silmaril.Wasm.Wac.Valid.Thms

/-!
# WAC: the target world's kinds have the target world's names and sorts

`World.fits_of_sat` derives the untyped targets check `Targets.Fits` from typed world
satisfaction `World.Sat`, under the hypothesis that the kinds of the target world
(`World.targetKinds env w`: `Wit.Binary.decWorld`, then `WitKind.ofWorld`) erase to the
names and sorts of the world `w` (`Targets.imports w`, `Targets.exports w`). This module
proves that hypothesis (`targetKinds_erase`) and so states the implication without it
(`fits_of_sat_target`).

The decoder keeps the names: an interface import `ns:pkg/iface@v` is parsed into an
`IfaceName` whose identifier is the name again (`parseIfaceName_id`), a plain name is
kept, and a function's binary name is demangled into a function whose mangled name is
the name again (`demangle_mangled_name`). `WitKind.ofWorldItem` names items by these
(`i.id`, the inline name, `f.mangled`, the type's name), with the sort of the
declaration (`ofWorldItem_erase`). Each declaration of the world's component type adds
at most one import or export, in order (`compStep_names`, `compSteps_names`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (IfaceName PackageName Func FuncKind Sig CSt DItem DecM
  dropPrefix? splitAt? parseIfaceName nameKey demangle demangleChars compStep compSteps
  instanceItem funcItem decWorld pConstructor pMethod pStatic pAsync pAsyncMethod pAsyncStatic)

namespace WorldFits

/-! ## The `Except` monad -/

theorem bind_ok {α β : Type} {m : Except String α} {f : α → Except String β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem pure_inj {α : Type} {a b : α} (h : (pure a : Except String α) = .ok b) : a = b :=
  Except.ok.inj h

/-! ## Names survive decoding -/

theorem toList_ofList (l : List Char) : (String.ofList l).toList = l := String.toList_ofList

/-- **A parsed interface name prints back**: its identifier is the parsed text. -/
theorem parseIfaceName_id {cs : List Char} {i : IfaceName} (h : parseIfaceName cs = some i) :
    i.idChars = cs := by
  cases h1 : splitAt? ':' cs with
  | none => exact absurd h (by simp [parseIfaceName, h1])
  | some q =>
    show i.idChars = cs
    cases h2 : splitAt? '/' q.2 with
    | none => exact absurd h (by simp [parseIfaceName, h1, h2])
    | some q2 =>
      show i.idChars = cs
      have e1 : cs = q.1 ++ ':' :: q.2 := Valid.splitAt?_eq (show splitAt? ':' cs = some (q.1, q.2) from h1)
      have e2 : q.2 = q2.1 ++ '/' :: q2.2 :=
        Valid.splitAt?_eq (show splitAt? '/' q.2 = some (q2.1, q2.2) from h2)
      cases h3 : splitAt? '@' q2.2 with
      | none =>
        have hi : some (⟨⟨String.ofList q.1, String.ofList q2.1, none⟩, String.ofList q2.2⟩ : IfaceName) =
            some i := by rw [← h]; simp [parseIfaceName, h1, h2, h3]
        rw [← Option.some.inj hi, e1, e2]; simp [IfaceName.idChars, PackageName.prefix, Wit.Binary.versionSuffix]
      | some q3 =>
        have e3 : q2.2 = q3.1 ++ '@' :: q3.2 :=
          Valid.splitAt?_eq (show splitAt? '@' q2.2 = some (q3.1, q3.2) from h3)
        have hi : some (⟨⟨String.ofList q.1, String.ofList q2.1, some (String.ofList q3.2)⟩,
            String.ofList q3.1⟩ : IfaceName) = some i := by rw [← h]; simp [parseIfaceName, h1, h2, h3]
        rw [← Option.some.inj hi, e1, e2, e3]; simp [IfaceName.idChars, PackageName.prefix, Wit.Binary.versionSuffix]

/-- The name of an interface key: the identifier, or the plain name. -/
def keyName : IfaceName ⊕ String → String
  | .inl i => i.id
  | .inr n => n

theorem nameKey_name {n : String} {key : IfaceName ⊕ String} (h : nameKey n = .ok key) :
    keyName key = n := by
  by_cases hc : ':' ∈ n.toList
  · cases hp : parseIfaceName n.toList with
    | none => simp [nameKey, hc, hp] at h
    | some i =>
      have h' : (pure (Sum.inl i) : DecM (IfaceName ⊕ String)) = .ok key := by simpa [nameKey, hc, hp] using h
      rw [← pure_inj h', keyName, IfaceName.id, parseIfaceName_id hp, String.ofList_toList]
  · have h' : (pure (Sum.inr n) : DecM (IfaceName ⊕ String)) = .ok key := by simpa [nameKey, hc] using h
    rw [← pure_inj h', keyName]

/-- The `res` step of `demangleChars`: `r` is `x.base`. -/
theorem res_some {kf : String → FuncKind} {a a' : Bool} {r base : List Char} {k : FuncKind}
    (h : (splitAt? '.' r).map (fun (q : List Char × List Char) => (kf (String.ofList q.1), q.2, a)) =
      some (k, base, a')) :
    ∃ x, r = x ++ '.' :: base ∧ k = kf (String.ofList x) ∧ a' = a := by
  cases hs : splitAt? '.' r with
  | none => simp [hs] at h
  | some q =>
    have e : kf (String.ofList q.1) = k ∧ q.2 = base ∧ a = a' := by simpa [hs] using h
    exact ⟨q.1, by rw [Valid.splitAt?_eq (show splitAt? '.' r = some (q.1, q.2) from hs), e.2.1],
      e.1.symm, e.2.2.symm⟩

/-- The mangled name of a decoded function. -/
def mangledOf (k : FuncKind) (base : List Char) (a : Bool) : List Char :=
  Func.mangledChars { name := String.ofList base, kind := k, async := a, params := [] }

theorem mangled_res {p : List Char} {kf : String → FuncKind} {a : Bool} {r base : List Char}
    {k : FuncKind} {a' : Bool} (hp : ∀ x, mangledOf (kf (String.ofList x)) base a = p ++ x ++ '.' :: base)
    (h : (splitAt? '.' r).map (fun (q : List Char × List Char) => (kf (String.ofList q.1), q.2, a)) =
      some (k, base, a')) : mangledOf k base a' = p ++ r := by
  obtain ⟨x, e, hk, ha⟩ := res_some h
  rw [hk, ha, hp x, e, List.append_assoc]

theorem mangled_method (a : Bool) (base x : List Char) :
    mangledOf (.method (String.ofList x)) base a =
      (if a then pAsyncMethod else pMethod) ++ x ++ '.' :: base := by
  simp [mangledOf, Func.mangledChars]

theorem mangled_static (a : Bool) (base x : List Char) :
    mangledOf (.static (String.ofList x)) base a =
      (if a then pAsyncStatic else pStatic) ++ x ++ '.' :: base := by
  simp [mangledOf, Func.mangledChars]

theorem tail_async {cs r base : List Char} {k : FuncKind} {a : Bool} (h5 : dropPrefix? pAsync cs = some r)
    (e : FuncKind.freestanding = k ∧ r = base ∧ a = true) : mangledOf k base a = cs := by
  rw [← e.1, ← e.2.1, e.2.2, Valid.dropPrefix?_eq h5]
  simp [mangledOf, Func.mangledChars]

theorem tail_plain {cs base : List Char} {k : FuncKind} {a : Bool}
    (e : FuncKind.freestanding = k ∧ cs = base ∧ a = false) : mangledOf k base a = cs := by
  rw [← e.1, ← e.2.1, e.2.2]
  simp [mangledOf, Func.mangledChars]

theorem tail_ctor {cs r base : List Char} {k : FuncKind} {a : Bool} (h0 : dropPrefix? pConstructor cs = some r)
    (e : FuncKind.constructor (String.ofList r) = k ∧ r = base ∧ a = false) : mangledOf k base a = cs := by
  rw [← e.1, e.2.2, Valid.dropPrefix?_eq h0]
  simp [mangledOf, Func.mangledChars]

/-- **Demangling inverts mangling**: the decoded function's mangled name is the name. -/
theorem demangleChars_mangled {cs base : List Char} {k : FuncKind} {a : Bool}
    (h : demangleChars cs = some (k, base, a)) : mangledOf k base a = cs := by
  cases h0 : dropPrefix? pConstructor cs with
  | some r => exact tail_ctor h0 (by simpa [demangleChars, h0] using h)
  | none =>
    show mangledOf k base a = cs
    cases h1 : dropPrefix? pMethod cs with
    | some r => rw [Valid.dropPrefix?_eq h1]; exact mangled_res (mangled_method false base) (by simpa [demangleChars, h0, h1] using h)
    | none =>
      show mangledOf k base a = cs
      cases h2 : dropPrefix? pStatic cs with
      | some r => rw [Valid.dropPrefix?_eq h2]; exact mangled_res (mangled_static false base) (by simpa [demangleChars, h0, h1, h2] using h)
      | none =>
        show mangledOf k base a = cs
        cases h3 : dropPrefix? pAsyncMethod cs with
        | some r =>
          rw [Valid.dropPrefix?_eq h3]; exact mangled_res (mangled_method true base) (by simpa [demangleChars, h0, h1, h2, h3] using h)
        | none =>
          show mangledOf k base a = cs
          cases h4 : dropPrefix? pAsyncStatic cs with
          | some r =>
            rw [Valid.dropPrefix?_eq h4]
            exact mangled_res (mangled_static true base) (by simpa [demangleChars, h0, h1, h2, h3, h4] using h)
          | none =>
            show mangledOf k base a = cs
            cases h5 : dropPrefix? pAsync cs with
            | some r => exact tail_async h5 (by simpa [demangleChars, h0, h1, h2, h3, h4, h5] using h)
            | none =>
              by_cases hb : cs.head? = some '['
              · exact absurd h (by simp [demangleChars, h0, h1, h2, h3, h4, h5, hb])
              · exact tail_plain (by simpa [demangleChars, h0, h1, h2, h3, h4, h5, hb] using h)

/-- **A demangled function's binary name is the name it was read from.** -/
theorem demangle_mangled_name {n : String} {s : Sig} {f : Silmaril.Wasm.Wit.Binary.Func} (h : demangle n s = .ok f) :
    f.mangled = n := by
  cases hd : demangleChars n.toList with
  | none => simp [demangle, hd] at h
  | some t =>
    obtain ⟨k, base, a⟩ := t
    by_cases ha : a = s.async
    · have hm : mangledOf k base a = n.toList := demangleChars_mangled hd
      have hf : f.mangledChars = mangledOf k base a := by
        simp [demangle, hd, ha] at h
        rw [← pure_inj h, ha]; simp [mangledOf, Func.mangledChars]
      rw [Func.mangled, hf, hm, String.ofList_toList]
    · simp [demangle, hd, ha] at h

/-! ## Each declaration adds its import or export -/

/-- The name and sort of a decoded item, as `Targets.imports` spells them. -/
def dns : DItem → String × String
  | .iface key _ => (keyName key, "instance")
  | .func f => (f.mangled, "func")
  | .type t => (t.name, "type")

theorem instanceItem_ok {s s2 : CSt} {n : String} {k : Nat} {it : DItem}
    (h : instanceItem s n k = .ok (it, s2)) :
    s2.imports = s.imports ∧ s2.exports = s.exports ∧ dns it = (n, "instance") := by
  obtain ⟨sl, -, h2⟩ := bind_ok h
  cases sl with
  | inst b =>
    obtain ⟨key, hk, h3⟩ := bind_ok h2
    have e : (DItem.iface key b, { s with insts := s.insts ++ [key.getLeft?] }) = (it, s2) := pure_inj h3
    rw [← (Prod.mk.inj e).1, ← (Prod.mk.inj e).2]
    exact ⟨rfl, rfl, by rw [dns, nameKey_name hk]⟩
  | ty _ | «def» _ | named _ | func _ | used => cases h2

theorem funcItem_ok {s : CSt} {n : String} {k : Nat} {it : DItem} (h : funcItem s n k = .ok it) :
    dns it = (n, "func") := by
  obtain ⟨sl, -, h2⟩ := bind_ok h
  cases sl with
  | func sig =>
    have h3 : (DItem.func <$> demangle n sig) = .ok it := h2
    cases hd : demangle n sig with
    | error e => rw [hd] at h3; cases h3
    | ok f =>
      rw [hd] at h3
      have e : DItem.func f = it := Except.ok.inj h3
      rw [← e, dns, demangle_mangled_name hd]
  | ty _ | «def» _ | named _ | inst _ | used => cases h2

/-- What a step leaves unchanged or adds, as a statement about names. -/
def StepNames (s s' : CSt) (d : ComponentDecl) : Prop :=
  s'.imports.map dns = s.imports.map dns ++ Targets.imports [d] ∧
    s'.exports.map dns = s.exports.map dns ++ Targets.exports [d]

theorem step_same {s s' : CSt} {d : ComponentDecl} (h1 : s'.imports = s.imports)
    (h2 : s'.exports = s.exports) (hi : Targets.imports [d] = []) (he : Targets.exports [d] = []) :
    StepNames s s' d := by
  rw [StepNames, h1, h2, hi, he, List.append_nil, List.append_nil]; exact ⟨rfl, rfl⟩

theorem step_import {s s' : CSt} {d : ComponentDecl} {it : DItem}
    (h1 : s'.imports = s.imports ++ [it]) (h2 : s'.exports = s.exports)
    (hi : Targets.imports [d] = [dns it]) (he : Targets.exports [d] = []) : StepNames s s' d := by
  rw [StepNames, h1, h2, hi, he, List.map_append, List.append_nil]; exact ⟨rfl, rfl⟩

theorem step_export {s s' : CSt} {d : ComponentDecl} {it : DItem}
    (h1 : s'.imports = s.imports) (h2 : s'.exports = s.exports ++ [it])
    (hi : Targets.imports [d] = []) (he : Targets.exports [d] = [dns it]) : StepNames s s' d := by
  rw [StepNames, h1, h2, hi, he, List.map_append, List.append_nil]; exact ⟨rfl, rfl⟩

/-- A step that only adds a type slot. -/
theorem step_slot {s s' : CSt} {d : ComponentDecl} {sl : List Wit.Binary.Slot}
    (h : (pure { s with slots := sl } : DecM CSt) = .ok s') (hi : Targets.imports [d] = [])
    (he : Targets.exports [d] = []) : StepNames s s' d := by
  rw [← pure_inj h]; exact step_same rfl rfl hi he

/-- **Each declaration of a world's component type adds its import or export.** -/
theorem compStep_names {s s' : CSt} {d : ComponentDecl} : compStep s d = .ok s' → StepNames s s' d := by
  fun_cases compStep s d
  next => intro h; obtain ⟨b, -, h2⟩ := bind_ok h; exact step_slot h2 rfl rfl
  next => intro h; obtain ⟨sl, -, h2⟩ := bind_ok h; exact step_slot h2 rfl rfl
  next => intro h; obtain ⟨sig, -, h2⟩ := bind_ok h; exact step_slot h2 rfl rfl
  next => intro h; exact step_slot h rfl rfl
  next => intro h; cases h
  next n k =>
    intro h
    obtain ⟨⟨it, s2⟩, h1, h2⟩ := bind_ok h
    have hs : s2.imports = s.imports ∧ s2.exports = s.exports ∧ dns it = (n, "instance") := instanceItem_ok h1
    rw [← pure_inj h2]
    exact step_import (by rw [hs.1]) hs.2.1 (by rw [hs.2.2]; rfl) rfl
  next n k =>
    intro h
    obtain ⟨⟨it, s2⟩, h1, h2⟩ := bind_ok h
    have hs : s2.imports = s.imports ∧ s2.exports = s.exports ∧ dns it = (n, "instance") := instanceItem_ok h1
    rw [← pure_inj h2]
    exact step_export hs.1 (by rw [hs.2.1]) rfl (by rw [hs.2.2]; rfl)
  next n k =>
    intro h
    obtain ⟨it, h1, h2⟩ := bind_ok h
    rw [← pure_inj h2]
    exact step_import rfl rfl (by rw [funcItem_ok h1]; rfl) rfl
  next n k =>
    intro h
    obtain ⟨it, h1, h2⟩ := bind_ok h
    rw [← pure_inj h2]
    exact step_export rfl rfl rfl (by rw [funcItem_ok h1]; rfl)
  next => intro h; rw [← pure_inj h]; exact step_import rfl rfl rfl rfl
  next =>
    intro h
    obtain ⟨⟨kind, sl⟩, -, h2⟩ := bind_ok h
    rw [← pure_inj h2]
    exact step_import rfl rfl rfl rfl
  next => intro h; cases h

theorem imports_cons (d : ComponentDecl) (ds : List ComponentDecl) :
    Targets.imports (d :: ds) = Targets.imports [d] ++ Targets.imports ds := by
  cases d with
  | «import» n e => rfl
  | inst i => rfl

theorem exports_cons (d : ComponentDecl) (ds : List ComponentDecl) :
    Targets.exports (d :: ds) = Targets.exports [d] ++ Targets.exports ds := by
  cases d with
  | «import» n e => rfl
  | inst i => cases i <;> rfl

/-- **The decoded imports and exports of a world's declarations, in order.** -/
theorem compSteps_names {s s' : CSt} {ds : List ComponentDecl} (h : compSteps s ds = .ok s') :
    s'.imports.map dns = s.imports.map dns ++ Targets.imports ds ∧
      s'.exports.map dns = s.exports.map dns ++ Targets.exports ds := by
  induction ds generalizing s with
  | nil =>
    have e : s = s' := pure_inj h
    rw [← e]; exact ⟨(List.append_nil _).symm, (List.append_nil _).symm⟩
  | cons d ds ih =>
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    have hs : StepNames s s1 d := compStep_names h1
    have hr := ih h2
    rw [hr.1, hr.2, hs.1, hs.2, imports_cons d ds, exports_cons d ds, List.append_assoc, List.append_assoc]
    exact ⟨rfl, rfl⟩

/-! ## The world's kinds -/

theorem ofWorldItem_erase (env : Wit.Binary.Env) (it : DItem) :
    ((WitKind.ofWorldItem env it.toWorldItem).1, World.sortName (WitKind.ofWorldItem env it.toWorldItem).2.promote) =
      dns it := by
  cases it with
  | iface key b => cases key <;> rfl
  | func f => rfl
  | type t =>
    show (t.name, World.sortName (WitKind.ofTypeDef t).promote) = (t.name, "type")
    unfold WitKind.ofTypeDef
    split <;> rfl

theorem erase_items (env : Wit.Binary.Env) (its : List DItem) :
    World.erase (World.promoteEx (its.map DItem.toWorldItem |>.map (WitKind.ofWorldItem env))) = its.map dns := by
  induction its with
  | nil => rfl
  | cons it its ih =>
    show _ :: _ = _ :: _
    rw [← ofWorldItem_erase env it]
    exact congrArg _ ih

/-- **The target world's kinds erase to its names and sorts**: the hypothesis of
`World.fits_of_sat` holds for every world `targetKinds` decodes. -/
theorem targetKinds_erase {env : Wit.Binary.Env} {w : Wit.Project.WorldType} {tw : World.WorldK}
    (h : World.targetKinds env w = .ok tw) :
    World.erase (World.promoteEx tw.1) = Targets.imports w ∧
      World.erase (World.promoteEx tw.2) = Targets.exports w := by
  cases hd : decWorld w with
  | error e => simp [World.targetKinds, hd, Except.map] at h
  | ok W =>
    have e : WitKind.ofWorld env W = tw := by simpa [World.targetKinds, hd, Except.map] using h
    obtain ⟨s, hs, hW⟩ := bind_ok hd
    have eW := pure_inj hW
    have hn := compSteps_names hs
    rw [← e, ← eW]
    exact ⟨(erase_items env s.imports).trans (by simpa using hn.1),
      (erase_items env s.exports).trans (by simpa using hn.2)⟩

/-- **Typed targets checking implies untyped targets checking**, for every target world
in binary form: `World.fits_of_sat` without its hypothesis on the target's kinds. -/
theorem fits_of_sat_target {K : Nat → Kind} {imps : Externs} {c : Ast} {cw tw : World.WorldK}
    {env : Wit.Binary.Env} {w : Wit.Project.WorldType} (hc : World.profileWorld K imps c = .ok cw)
    (ht : World.targetKinds env w = .ok tw) (hs : World.Sat cw tw) :
    Targets.Fits (Targets.surface c) w :=
  World.fits_of_sat hc (targetKinds_erase ht).1 (targetKinds_erase ht).2 hs

/-- `checkTyped` is sound for `Targets.Fits`. -/
theorem checkTyped_fits {K : Nat → Kind} {imps : Externs} {env : Wit.Binary.Env} {c : Ast}
    {w : Wit.Project.WorldType} (h : World.checkTyped K imps env c w = .ok true) :
    Targets.Fits (Targets.surface c) w := by
  obtain ⟨cw, hc, h2⟩ := bind_ok h
  obtain ⟨tw, ht, h3⟩ := bind_ok h2
  have hsat : World.sat cw tw = true := pure_inj h3
  exact fits_of_sat_target hc ht ((sub_iff _ _).1 hsat)

end WorldFits

end Silmaril.Wasm.Wac
