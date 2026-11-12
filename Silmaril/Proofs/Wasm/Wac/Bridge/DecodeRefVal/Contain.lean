module

public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeRefVal.Lists

/-!
# WAC bridge: `EsOkR` contains `DecodeNamed.EsOk`

On the named fragment the read-back is the identity: `esOkR_of_esOk` gives, for items of
`DecodeNamed.EsOk N Γ`, that they are items of `EsOkR N Γ`, that `rdEs Γ es = es` and
that `extendR Γ es = extend Γ es`. So `decode_encode_refVal` contains
`DecodeNamed.decode_encode_named`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeNamed (Ctx EsOk TyOk SigOk extend sortOf sortOf_plain)

namespace DecodeRefVal

theorem rdTo_id {Γ : Ctx} {a : Option Silmaril.Wasm.Wit.Binary.Ty} (h : ∀ t ∈ a, rdT Γ t = t) : rdTo Γ a = a := by
  cases a with
  | none => rfl
  | some t => simp [rdTo, h t rfl]

theorem rdTs_id {Γ : Ctx} : ∀ {ts : List Silmaril.Wasm.Wit.Binary.Ty}, (∀ t ∈ ts, rdT Γ t = t) → rdTs Γ ts = ts
  | [], _ => rfl
  | t :: _, h => by
    simp [rdTs, h t List.mem_cons_self, rdTs_id (fun t' ht => h t' (List.mem_cons_of_mem _ ht))]

theorem rdPs_id {Γ : Ctx} : ∀ {ps : List (String × Silmaril.Wasm.Wit.Binary.Ty)}, (∀ p ∈ ps, rdT Γ p.2 = p.2) → rdPs Γ ps = ps
  | [], _ => rfl
  | (n, t) :: _, h => by
    simp [rdPs, h (n, t) List.mem_cons_self, rdPs_id (fun p hp => h p (List.mem_cons_of_mem _ hp))]

/-- On `TyOk`, the read-back is the identity. -/
theorem rdT_of_tyOk {Γ : Ctx} {t : Silmaril.Wasm.Wit.Binary.Ty} (h : TyOk Γ t) : rdT Γ t = t := by
  induction h with
  | prim _ => rfl
  | refVal h | refAlias h | own h => simp [rdT, h]
  | borrowRes _ | borrowAlias _ => rfl
  | list _ ih | option _ ih | fixedList _ _ ih => simp [rdT, ih]
  | map _ _ ihk ihv => simp [rdT, ihk, ihv]
  | result _ _ iha ihb => simp [rdT, rdTo_id iha, rdTo_id ihb]
  | tuple _ ih => simp [rdT, rdTs_id ih]
  | future _ ih | stream _ ih => simp [rdT, rdTo_id ih]

theorem rdS_of_sigOk {Γ : Ctx} {s : Sig} (h : SigOk Γ s) : rdS Γ s = s := by
  simp [rdS, rdPs_id (fun p hp => rdT_of_tyOk (h.1 p hp)), rdTo_id (fun t ht => rdT_of_tyOk (h.2 t ht))]

theorem sigOkR_of_sigOk {Γ : Ctx} {s : Sig} (h : SigOk Γ s) : SigOkR Γ s :=
  ⟨fun p hp => tyOkR_of_tyOk (h.1 p hp), fun t ht => tyOkR_of_tyOk (h.2 t ht)⟩

/-- What `esOkR_of_esOk` proves of a list of items. -/
def Contained (N : NomTable) (Γ : Ctx) (es : Externs) : Prop :=
  EsOkR N Γ es ∧ rdEs Γ es = es ∧ extendR Γ es = extend Γ es

/-- **The named fragment is contained in `EsOkR`**, with the identity as read-back. -/
theorem esOkR_of_esOk {N : NomTable} {Γ : Ctx} {es : Externs} (h : EsOk N Γ es) : Contained N Γ es := by
  induction h with
  | nil => exact ⟨.nil, rfl, rfl⟩
  | func hs _ ih =>
    exact ⟨.func (sigOkR_of_sigOk hs) ih.1, by simp [rdEs, rdKd, rdS_of_sigOk hs, stepR, ih.2.1],
      by simp [extendR, extend, stepR, ih.2.2]⟩
  | inst _ _ ihf ih =>
    exact ⟨.inst ihf.1 ih.1, by simp [rdEs, rdKd, ihf.2.1, stepR, ih.2.1], by simp [extendR, extend, stepR, ih.2.2]⟩
  | comp _ _ _ ih1 ih2 ih =>
    exact ⟨.comp ih1.1 (ih1.2.2 ▸ ih2.1) ih.1, by simp [rdEs, rdKd, ih1.2.1, ih1.2.2, ih2.2.1, stepR, ih.2.1],
      by simp [extendR, extend, stepR, ih.2.2]⟩
  | res _ ih =>
    exact ⟨.res ih.1, by simp [rdEs, rdKd, rdTB, stepR, sortR, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, ih.2.2]⟩
  | tyOwn ha _ ih =>
    exact ⟨.tyRes (Or.inl rfl) ha ih.1, by simp [rdEs, rdKd_res (Or.inl rfl) ha, stepR, sortR, ha, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, ha, ih.2.2]⟩
  | tyRef ha _ ih =>
    exact ⟨.tyRef ha ih.1, by simp [rdEs, rdKd, rdTB, rdTV, rdAli, stepR, sortR, ha, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, ha, ih.2.2]⟩
  | tyNom hn hN hd _ ih =>
    exact ⟨.tyNom hn hN hd ih.1, by simp [rdEs, rdKd, rdTB, rdTV, rdAli, stepR, sortR, hn, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, hn, ih.2.2]⟩
  | tyVal hp ht _ ih =>
    exact ⟨.tyVal hp (tyOkR_of_tyOk ht) ih.1,
      by simp [rdEs, rdKd, rdTB, rdTV_plain _ hp, rdT_of_tyOk ht, stepR, sortR_plain _ hp, ih.2.1],
      by simp [extendR, extend, stepR, sortR_plain _ hp, sortOf_plain hp, ih.2.2]⟩
  | tyFunc hs _ ih =>
    exact ⟨.tyFunc (sigOkR_of_sigOk hs) ih.1, by simp [rdEs, rdKd, rdTB, rdS_of_sigOk hs, stepR, sortR, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, ih.2.2]⟩
  | tyInst _ _ ihf ih =>
    exact ⟨.tyInst ihf.1 ih.1, by simp [rdEs, rdKd, rdTB, ihf.2.1, stepR, sortR, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, ih.2.2]⟩
  | tyComp _ _ _ ih1 ih2 ih =>
    exact ⟨.tyComp ih1.1 (ih1.2.2 ▸ ih2.1) ih.1,
      by simp [rdEs, rdKd, rdTB, ih1.2.1, ih1.2.2, ih2.2.1, stepR, sortR, ih.2.1],
      by simp [extendR, extend, stepR, sortR, sortOf, ih.2.2]⟩

end DecodeRefVal

end Silmaril.Wasm.Wac.Bridge
