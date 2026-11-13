module

public import Silmaril.Wasm.Models.Game.Defs
public import Silmaril.Wasm.Category.Institution.Defs

/-!
# Embeddings as realisers and their composition

* `WasmModel.lang A`: a model as a language of the compiler category
  (`Silmaril.Compile.Category.Language`): programs are the calls at points of the domain, one
  interface, behaviours are the observations;
* `Emb.realiser e t hinj hd`: an embedding of direction `eq` with a total (`Emb.Total`) and
  injective read-back is a `Silmaril.Wasm.Category.Realiser` of `A.lang` in `B.lang`, hence a Hets
  comorphism of behavioural institutions (`Emb.coHom`) that borrows entailment when the
  read-back is also surjective (`Emb.entails_iff`, in `Thms`);
* `EmbDir.comp`: composition of directions (`eq` is neutral, `sub ∘ sub = sub`,
  `sup ∘ sup = sup`, mixed `sub`/`sup` do not compose); `pullback rb S`: the read-back of a set
  of observations;
* `Emb.comp e f h`: **composition of embeddings** when their directions compose; the read-back
  is the Kleisli composite (`Option.bind`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Compile.Category Silmaril.Wasm.Category

/-- The read-back of a set of observations. -/
def pullback {α β : Type} (rb : β → Option α) (S : Set β) : Set α :=
  {o | ∃ b ∈ S, rb b = some o}

/-- Composition of embedding directions. -/
def EmbDir.comp : EmbDir → EmbDir → Option EmbDir
  | .eq, d => some d
  | .sub, .eq => some .sub
  | .sup, .eq => some .sup
  | .sub, .sub => some .sub
  | .sup, .sup => some .sup
  | _, _ => none

namespace WasmModel

variable {A B D : WasmModel}

/-- **A model as a language**: programs are calls at points of the domain, behaviours are the
observations. -/
def lang (A : WasmModel) : Language.{0} where
  Iface := Unit
  Prog := {x : A.Pt × A.Call // A.dom x.1}
  iface _ := ()
  Obs := A.Obs
  beh x := A.obs x.1.1 x.1.2

/-- The view of a model is the read-back of its observations. -/
theorem view_eq_pullback (B : WasmModel) {O : Type} (rb : B.Obs → Option O) (p : B.Pt)
    (c : B.Call) : B.view rb p c = pullback rb (B.obs p c) :=
  rfl

/-- The read-back view of a total read-back is the image of the observations. -/
theorem Emb.view_eq_image (e : A.Emb B) (t : e.Total) (x : B.Pt) (c : B.Call) :
    B.view e.readback x c = t.g '' B.obs x c := by
  ext o
  constructor
  · rintro ⟨b, hb, he⟩
    rw [t.readback_eq] at he
    exact ⟨b, hb, Option.some.inj he⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, t.readback_eq b⟩

/-- **An equality embedding with a total injective read-back is a realiser.** -/
def Emb.realiser (e : A.Emb B) (t : e.Total) (hinj : Function.Injective t.g) (hd : e.dir = .eq) :
    Realiser A.lang B.lang where
  Φ := id
  prog x := ⟨(e.pt x.1.1, e.call x.1.2), e.dom _ x.2⟩
  g := t.g
  g_injective := hinj
  iface _ := rfl
  beh x := by
    have h := e.sat x.1.1 x.2 x.1.2
    rw [hd] at h
    change B.view e.readback (e.pt x.1.1) (e.call x.1.2) = A.obs x.1.1 x.1.2 at h
    rw [e.view_eq_image t] at h
    exact h

/-- **The Hets comorphism of an equality embedding** with a total injective read-back: the
comorphism of behavioural institutions of its realiser. -/
def Emb.coHom (e : A.Emb B) (t : e.Total) (hinj : Function.Injective t.g) (hd : e.dir = .eq) :
    Silmaril.Logic.Institution.Inst.CoHom (behInst A.lang) (behInst B.lang) :=
  (e.realiser t hinj hd).coHom

/-- Read-back along a Kleisli composite is iterated read-back. -/
theorem pullback_bind {α β γ : Type} (rb₁ : β → Option α) (rb₂ : γ → Option β) (S : Set γ) :
    pullback (fun c => (rb₂ c).bind rb₁) S = pullback rb₁ (pullback rb₂ S) := by
  ext o
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨b, hb, hbo⟩ := Option.bind_eq_some_iff.mp he
    exact ⟨b, ⟨c, hc, hb⟩, hbo⟩
  · rintro ⟨b, ⟨c, hc, hb⟩, hbo⟩
    exact ⟨c, hc, Option.bind_eq_some_iff.mpr ⟨b, hb, hbo⟩⟩

theorem pullback_mono {α β : Type} (rb : β → Option α) {S T : Set β} (h : S ⊆ T) :
    pullback rb S ⊆ pullback rb T :=
  fun _ ⟨b, hb, he⟩ => ⟨b, h hb, he⟩

/-- Directions compose: if `d₁` holds between `a` and the read-back of `b`, and `d₂` between
`b` and `c`, the composite holds between `a` and the read-back of `c`. -/
theorem EmbDir.holds_comp {α β : Type} {d₁ d₂ d : EmbDir} (hd : d₁.comp d₂ = some d)
    (rb : β → Option α) {a : Set α} {b c : Set β} (h₁ : d₁.Holds a (pullback rb b))
    (h₂ : d₂.Holds b c) : d.Holds a (pullback rb c) := by
  cases d₁ <;> cases d₂ <;> simp only [EmbDir.comp, Option.some.injEq, reduceCtorEq] at hd <;>
    subst hd
  · exact (show c = b from h₂) ▸ h₁
  · exact (show pullback rb b = a from h₁) ▸ pullback_mono rb h₂
  · exact (show pullback rb b = a from h₁) ▸ pullback_mono rb h₂
  · exact (show c = b from h₂) ▸ h₁
  · exact fun o ho => pullback_mono rb h₂ (h₁ ho)
  · exact (show c = b from h₂) ▸ h₁
  · exact fun o ho => h₁ (pullback_mono rb h₂ ho)

/-- **Composition of embeddings** whose directions compose. -/
def Emb.comp (e : A.Emb B) (f : B.Emb D) {d : EmbDir} (hd : e.dir.comp f.dir = some d) :
    A.Emb D where
  mod m := f.mod (e.mod m)
  valid m hm := f.valid _ (e.valid m hm)
  pt p := f.pt (e.pt p)
  call c := f.call (e.call c)
  readback x := (f.readback x).bind e.readback
  dom p hp := f.dom _ (e.dom p hp)
  dir := d
  sat p hp c := by
    change d.Holds (A.obs p c) (pullback _ (D.obs (f.pt (e.pt p)) (f.call (e.call c))))
    rw [pullback_bind]
    exact EmbDir.holds_comp hd e.readback (e.sat p hp c) (f.sat _ (e.dom p hp) (e.call c))

end WasmModel

end Silmaril.Wasm.Models
