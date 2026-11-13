module

public import Silmaril.Wasm.Wit.Elab.Defs
public import Silmaril.Wasm.Wit.Valid.Thms
public import Silmaril.Wasm.Wit.Binary.Thms

/-!
# Elaboration: soundness

* the Boolean checks of `elaborate` decide the binary conditions
  (`Package.validB_sound`, `Package.namesUniqueB_sound`);
* `elaborate_sound`: a successful elaboration comes from a valid (gated)
  universe and gives a package with the hypotheses of
  `decodePackage_encodePackage_canon`;
* `elaborate_decode`: the bytes of an elaborated package decode to its
  canonical form, and encode ∘ decode is the identity on them when the package
  is canonical.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

theorem not_mem_of_not_contains {l : List Char} {c : Char} (h : (!l.contains c) = true) : c ∉ l := by
  intro hm
  rw [List.contains_iff_mem.mpr hm] at h
  exact absurd h (by decide)

theorem IfaceName.validB_sound {i : Binary.IfaceName} (h : IfaceName.validB i = true) : i.Valid := by
  simp only [IfaceName.validB, Bool.and_eq_true] at h
  exact ⟨not_mem_of_not_contains h.1.1, not_mem_of_not_contains h.1.2, not_mem_of_not_contains h.2⟩

theorem Func.validB_sound {f : Binary.Func} (h : Func.validB f = true) : f.Valid := by
  unfold Func.validB at h
  unfold Binary.Func.Valid
  cases hk : f.kind with
  | freestanding =>
    rw [hk] at h
    intro ha
    simp only [ha, Bool.false_or, bne_iff_ne, ne_eq] at h
    exact h
  | method r =>
    rw [hk] at h
    exact not_mem_of_not_contains h
  | static r =>
    rw [hk] at h
    exact not_mem_of_not_contains h
  | constructor r =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    exact h

theorem Interface.validB_sound {b : Binary.Interface} (h : Interface.validB b = true) : b.Valid := by
  intro f hf
  exact Func.validB_sound (List.all_eq_true.mp h f hf)

theorem WorldItem.validB_sound {it : Binary.WorldItem} (h : WorldItem.validB it = true) : it.Valid := by
  cases it with
  | ifaceRef i _ _ => exact IfaceName.validB_sound h
  | ifaceInline n b =>
    simp only [WorldItem.validB, Bool.and_eq_true] at h
    exact ⟨not_mem_of_not_contains h.1, Interface.validB_sound h.2⟩
  | func f => exact Func.validB_sound h
  | type _ => trivial

theorem Package.validB_sound {p : Binary.Package} {deps : Binary.Env} (h : Package.validB p deps = true) :
    p.Valid deps := by
  simp only [Package.validB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hne, hi⟩, hw⟩, he⟩, hws⟩ := h
  refine ⟨hne, fun nb m => IfaceName.validB_sound (hi nb m), fun nw m => IfaceName.validB_sound (hw nw m),
    fun ib m => ?_, fun nw m => ?_⟩
  · have := he ib m
    exact ⟨IfaceName.validB_sound this.1, Interface.validB_sound this.2⟩
  · have := hws nw m
    exact ⟨fun it hm => WorldItem.validB_sound (this.1 it hm), fun it hm => WorldItem.validB_sound (this.2 it hm)⟩

theorem labelsUniqueB_sound {k : Binary.TyDefKind} (h : labelsUniqueB k = true) : k.LabelsUnique := by
  cases k <;> simp_all [labelsUniqueB, Binary.TyDefKind.LabelsUnique]

theorem Interface.namesUniqueB_sound {b : Binary.Interface} (h : Interface.namesUniqueB b = true) :
    b.NamesUnique := by
  simp only [Interface.namesUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun td m => labelsUniqueB_sound (h.2 td m)⟩

theorem World.namesUniqueB_sound {w : Binary.World} (h : World.namesUniqueB w = true) :
    w.NamesUnique := by
  simp only [World.namesUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun it m => ?_⟩
  have := h4 it m
  cases it with
  | ifaceInline _ b => exact Interface.namesUniqueB_sound this
  | type td => exact labelsUniqueB_sound this
  | ifaceRef _ _ _ => trivial
  | func _ => trivial

theorem Package.namesUniqueB_sound {p : Binary.Package} (h : Package.namesUniqueB p = true) : p.NamesUnique := by
  simp only [Package.namesUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun nb m => Interface.namesUniqueB_sound (h3 nb m),
    fun nw m => World.namesUniqueB_sound (h4 nw m)⟩

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem elabPackage_name {c : Ctx} {env : Binary.Env} {Q : Wit.Package} {out : Binary.Package}
    (h : elabPackage c env Q = .ok out) : out.name = pkgName Q.name := by
  unfold elabPackage at h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  cases h; rfl

theorem require_ok {b : Bool} {msg : String} {u : Unit} (h : require b msg = .ok u) : b = true := by
  cases b with
  | false => cases h
  | true => rfl

theorem lookupPkg_ok {U : Universe} {p : PackageName} {Q : Wit.Package} (h : lookupPkg U p = .ok Q) :
    Q.name = p := by
  unfold lookupPkg at h
  cases hP : U.pkg? p with
  | none => rw [hP] at h; cases h
  | some Q' =>
    rw [hP] at h
    cases h
    simpa using List.find?_some hP

/-- The checks a successful `elaborate` has passed. -/
theorem elaborate_parts {U : Universe} {p : PackageName} {fs : List Name} {P : Binary.Package}
    {deps : Binary.Env} (h : elaborate U p fs = .ok (P, deps)) :
    check (Universe.gate fs U) = true ∧ P.name = pkgName p ∧
      Package.validB P deps = true ∧ Package.namesUniqueB P = true := by
  unfold elaborate at h
  obtain ⟨_, hc, h⟩ := except_bind_ok h
  obtain ⟨Q, hQ, h⟩ := except_bind_ok h
  obtain ⟨env, _, h⟩ := except_bind_ok h
  obtain ⟨out, ho, h⟩ := except_bind_ok h
  obtain ⟨_, hv, h⟩ := except_bind_ok h
  obtain ⟨_, hn, h⟩ := except_bind_ok h
  cases h
  exact ⟨require_ok hc, by rw [elabPackage_name ho, lookupPkg_ok hQ], require_ok hv, require_ok hn⟩

/-- What a successful `elaborate` guarantees, read off its checks. -/
theorem elaborate_sound {U : Universe} {p : PackageName} {fs : List Name} {P : Binary.Package}
    {deps : Binary.Env} (h : elaborate U p fs = .ok (P, deps)) :
    Valid (Universe.gate fs U) ∧ P.Valid deps ∧ P.NamesUnique ∧ P.name = pkgName p :=
  have hp := elaborate_parts h
  ⟨check_sound hp.1, Package.validB_sound hp.2.2.1, Package.namesUniqueB_sound hp.2.2.2, hp.2.1⟩

/-- **Surface packages round-trip through bytes**: the bytes of an elaborated
package decode to its canonical form (`decodePackage_encodePackage_canon`). -/
theorem elaborate_decode {U : Universe} {p : PackageName} {fs : List Name} {P : Binary.Package}
    {deps : Binary.Env} (h : elaborate U p fs = .ok (P, deps)) {b : ByteArray}
    (hb : Binary.encodePackage deps P = .ok b) : Binary.decodePackage b = .ok P.canon :=
  have hs := elaborate_sound h
  Binary.decodePackage_encodePackage_canon hs.2.1 hs.2.2.1 hb

/-- encode ∘ decode is the identity on the bytes of an elaborated package in
canonical function order. -/
theorem elaborate_reencode {U : Universe} {p : PackageName} {fs : List Name} {P : Binary.Package}
    {deps : Binary.Env} (h : elaborate U p fs = .ok (P, deps)) (hc : P.canon = P) {b : ByteArray}
    (hb : Binary.encodePackage deps P = .ok b) {q : Binary.Package} (hq : Binary.decodePackage b = .ok q) :
    Binary.encodePackage deps q = .ok b :=
  have hs := elaborate_sound h
  Binary.encodePackage_decodePackage hs.2.1 hs.2.2.1 hc hb hq

end Silmaril.Wasm.Wit.Elab
