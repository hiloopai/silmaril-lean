module

public import Silmaril.Encoding.Encoded
public import Silmaril.Formats.Bytes

/-!
# Carriers and carrier functors

The carriers used by encodings:

* `List UInt8` — the proof-friendly byte carrier (grammar productions compose
  by concatenation); `Silmaril.Formats.Bytes` and `ByteArray` are bridged by
  equivalences, so encodings over them are pullbacks along the bridges;
* `String` — sequences of Unicode scalar values (`Unicode.lean` relates it to
  bytes through UTF-8, UTF-16 and Latin-1);
* `Nat` — an injective coding of byte strings (`natCode`), a stub for later
  Gödel-style arguments.

Carrier maps act on encodings by pushforward/pullback (`EncRel.push`,
`EncRel.pull`, `Relation.lean`), on `EncCat` by functors (`Category.lean`), and
partial carrier maps (decoders) act Kleisli-style by `pushPartial` /
`pullPartial`.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace Carrier

/-! ## Bytes -/

/-- `Formats.Bytes` as a byte list. -/
def ofBytes (b : Formats.Bytes) : List UInt8 := b.toList

/-- The two byte carriers are equivalent. -/
def bytesEquiv : Formats.Bytes ≃ List UInt8 where
  toFun := Formats.Bytes.toList
  invFun := Formats.Bytes.ofList
  left_inv := Formats.Bytes.ofList_toList
  right_inv := Formats.Bytes.toList_ofList

/-- `ByteArray` as a byte list. -/
def ofByteArray (b : ByteArray) : List UInt8 := b.data.toList

/-- `ByteArray` and byte lists are equivalent. -/
def byteArrayEquiv : ByteArray ≃ List UInt8 where
  toFun := ofByteArray
  invFun := List.toByteArray
  left_inv b := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    exact List.toList_data_toByteArray
  right_inv l := List.toList_data_toByteArray

theorem ofByteArray_injective : Function.Injective ofByteArray :=
  byteArrayEquiv.injective

/-! ## Natural numbers -/

/-- Bijective base-257 numeration with digits `1..256`: an injective coding of
byte strings as natural numbers. -/
def natCode : List UInt8 → Nat
  | [] => 0
  | b :: bs => (b.toNat + 1) + 257 * natCode bs

theorem natCode_injective : Function.Injective natCode := by
  intro l
  induction l with
  | nil =>
    rintro (_ | ⟨b, bs⟩) h
    · rfl
    · simp [natCode] at h
      omega
  | cons b bs ih =>
    rintro (_ | ⟨c, cs⟩) h
    · simp [natCode] at h
    · simp only [natCode] at h
      have hb := b.toNat_lt
      have hc := c.toNat_lt
      have h1 : b.toNat = c.toNat := by omega
      have h2 : natCode bs = natCode cs := by omega
      rw [UInt8.toNat_inj.mp h1, ih h2]

/-- Partial inverse of `natCode`. -/
def natDecode (n : Nat) : Option (List UInt8) :=
  if h : n = 0 then some []
  else if n % 257 = 0 then none
  else (natDecode (n / 257)).map (UInt8.ofNat (n % 257 - 1) :: ·)
termination_by n
decreasing_by omega

@[simp]
theorem natDecode_natCode (l : List UInt8) : natDecode (natCode l) = some l := by
  induction l with
  | nil => rw [natCode, natDecode]; simp
  | cons b bs ih =>
    have hb := b.toNat_lt
    have h1 : natCode (b :: bs) ≠ 0 := by simp only [natCode]; omega
    have h2 : natCode (b :: bs) % 257 = b.toNat + 1 := by simp only [natCode]; omega
    have h3 : natCode (b :: bs) / 257 = natCode bs := by simp only [natCode]; omega
    rw [natDecode]
    simp only [h1, h3, ih, h2, dite_false]
    simp

theorem natDecode_eq_some_iff {n : Nat} {l : List UInt8} :
    natDecode n = some l ↔ natCode l = n := by
  refine ⟨fun h => ?_, fun h => h ▸ natDecode_natCode l⟩
  induction n using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rw [natDecode] at h
    split_ifs at h with h0 h1
    · cases h
      simp [natCode, h0]
    · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      have ht' := ih (n / 257) (by omega) ht
      have hd : (UInt8.ofNat (n % 257 - 1)).toNat = n % 257 - 1 := by
        have : n % 257 < 257 := Nat.mod_lt _ (by omega)
        rw [UInt8.toNat_ofNat']
        omega
      simp only [natCode, ht', hd]
      omega

end Carrier

/-! ## Partial carrier maps on categories of encodings -/

namespace EncCat

variable {σ σ' σ'' : Type}

/-- Pushforward along a partial carrier map. -/
@[simps]
def pushPartialFunctor (g : σ → Option σ') : EncCat σ ⥤ EncCat σ' where
  obj X := ⟨X.ast, X.rel.pushPartial g⟩
  map f := ⟨f.fn, by
    rintro s' a ⟨s, hs, h⟩
    exact ⟨s, hs, f.preserves _ _ h⟩⟩

/-- Strong pullback along a partial carrier map. -/
@[simps]
def pullPartialFunctor (g : σ → Option σ') : EncCat σ' ⥤ EncCat σ where
  obj X := ⟨X.ast, X.rel.pullPartial g⟩
  map f := ⟨f.fn, by
    rintro s a ⟨s', hs, h⟩
    exact ⟨s', hs, f.preserves _ _ h⟩⟩

/-- Weak pullback along a partial carrier map. -/
@[simps]
def pullPartialAllFunctor (g : σ → Option σ') : EncCat σ' ⥤ EncCat σ where
  obj X := ⟨X.ast, X.rel.pullPartialAll g⟩
  map f := ⟨f.fn, fun _ _ h s' hs => f.preserves _ _ (h s' hs)⟩

/-- `pushPartial g ⊣ pullPartialAll g` on categories of encodings. -/
def pushPartialAdjunction (g : σ → Option σ') :
    pushPartialFunctor g ⊣ pullPartialAllFunctor g :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ⟨f.fn, fun s a h s' hs => f.preserves s' a ⟨s, hs, h⟩⟩
          invFun := fun f => ⟨f.fn, by
            rintro s' a ⟨s, hs, h⟩
            exact f.preserves s a h s' hs⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } }

/-- Pushforward along composable carrier maps, on objects. -/
theorem pushFunctor_obj_comp (g : σ → σ') (h : σ' → σ'') (X : EncCat σ) :
    (pushFunctor h).obj ((pushFunctor g).obj X) = (pushFunctor (h ∘ g)).obj X := by
  change (⟨X.ast, (X.rel.push g).push h⟩ : EncCat σ'') = ⟨X.ast, X.rel.push (h ∘ g)⟩
  rw [EncRel.push_push]

/-- Kleisli composition of partial carrier maps. -/
def kleisli (g : σ → Option σ') (h : σ' → Option σ'') : σ → Option σ'' :=
  fun s => (g s).bind h

theorem pushPartial_kleisli (g : σ → Option σ') (h : σ' → Option σ'') {α : Type}
    (E : EncRel σ α) :
    E.pushPartial (kleisli g h) = (E.pushPartial g).pushPartial h := by
  ext s'' a
  constructor
  · rintro ⟨s, hs, hE⟩
    simp only [kleisli, Option.bind_eq_some_iff] at hs
    obtain ⟨s', hs', hs''⟩ := hs
    exact ⟨s', hs'', s, hs', hE⟩
  · rintro ⟨s', hs'', s, hs', hE⟩
    exact ⟨s, by simp [kleisli, hs', hs''], hE⟩

/-- Partial pushforward along a left inverse undoes pushforward (on objects):
e.g. decoding UTF-8 after encoding UTF-8. -/
theorem pushPartialFunctor_obj_pushFunctor_obj {g : σ → σ'} {g? : σ' → Option σ}
    (hg : ∀ s, g? (g s) = some s) (X : EncCat σ) :
    (pushPartialFunctor g?).obj ((pushFunctor g).obj X) = X := by
  change (⟨X.ast, (X.rel.push g).pushPartial g?⟩ : EncCat σ) = X
  rw [EncRel.pushPartial_push_of_leftInverse hg]

/-- A partial carrier map defined on every valid spelling of `X` yields an
`EncCat₂` morphism `(g.getD d, id) : ι X ⟶ ι (g_! X)`. -/
def pushPartialUnit (g : σ → Option σ') (d : σ') (X : EncCat σ)
    (hdef : ∀ s, X.rel.Encodable s → (g s).isSome) :
    (incl σ).obj X ⟶ (incl σ').obj ((pushPartialFunctor g).obj X) where
  onCarrier s := (g s).getD d
  fn := id
  preserves s a h := by
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (hdef s ⟨a, h⟩)
    refine ⟨s, ?_, h⟩
    simp [hs']

end EncCat

end Silmaril
