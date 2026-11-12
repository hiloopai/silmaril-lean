module

public import Silmaril.Wasm.Models.V2CoreSpec.Defs
public import Silmaril.Wasm.Game.SpecGlobals.Thms

/-!
# The Core host induced by a 2.0 host commutes with global embeddings on image targets

`liftHost src` (`Silmaril.Wasm.Models.V2Core`) answers a Core call only on a store whose erasure is
the image of a 2.0 store. A global-address embedding's target may hold globals outside the image
of the source, so `liftHost src` does not satisfy `HostEmb` once it answers at all. It does
satisfy the relativised `HostEmbR GImg` (`Silmaril.Proofs.Wasm.Game.SpecGlobals.StepHostOut`): the
targets whose globals outside the image are images of 2.0 globals.

* `exists_pre`: a list whose entries are all images has a preimage that agrees with a given list
  on the embedded positions (the preimage of a Core global is not unique, because a Core null
  forgets its type);
* `pre_store`: the target of an embedding of an image store, with image globals outside the
  embedding, is the image of the renamed 2.0 store (`EmbV`);
* `post_store`: the store the 2.0 host returns on the renamed store gives a Core target that is
  again an image and again embeds the source's result;
* **`hostEmbR_liftHost`**: `HostEmbV src → HostEmbR GImg (liftHost src)`;
* **`hostEmbV_blind`**: a 2.0 host blind to globals and functions commutes with the 2.0
  embeddings; `pureHostV_blind`: so does every 2.0 host that leaves the store unchanged.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Proofs.Wasm.Game.SpecGlobals (Emb OutG HostEmbR ImgD moduleView function external ModDom)

variable {H : Type}

/-! ## Lists of images -/

/-- Each entry of a list of images has a preimage, which is the entry of `sg` at an embedded
position. -/
theorem exists_pre_entry {α β : Type} (f : α → β) {ρ : Nat → Nat} {D : Nat → Prop}
    (hinj : ∀ a b, D a → D b → ρ a = ρ b → a = b) (sg : List α) (Tg : List β)
    (hT : ∀ a, D a → Tg[ρ a]? = (sg[a]?).map f)
    (hout : ∀ b g, ¬ ImgD ρ D b → Tg[b]? = some g → ∃ x, f x = g) (i : Nat)
    (hi : i < Tg.length) :
    ∃ x, f x = Tg[i] ∧ ∀ a (ha : a < sg.length), D a → ρ a = i → x = sg[a] := by
  by_cases hin : ∃ a, D a ∧ ρ a = i ∧ a < sg.length
  · show ∃ x, f x = Tg[i] ∧ ∀ a (ha : a < sg.length), D a → ρ a = i → x = sg[a]
    obtain ⟨a, hDa, hρa, hal⟩ := hin
    have h : Tg[ρ a]? = (sg[a]?).map f := hT a hDa
    have h' : some Tg[i] = some (f sg[a]) := by
      rw [← List.getElem?_eq_getElem hi, ← hρa, h, List.getElem?_eq_getElem hal, Option.map_some]
    have hfa : f sg[a] = Tg[i] := (Option.some.inj h').symm
    have huniq : ∀ a' (ha' : a' < sg.length), D a' → ρ a' = i → sg[a] = sg[a'] :=
      fun a' _ hDa' hρa' => by
        have hea : a' = a := hinj a' a hDa' hDa (hρa'.trans hρa.symm)
        simp only [hea]
    exact ⟨sg[a], hfa, huniq⟩
  · show ∃ x, f x = Tg[i] ∧ ∀ a (ha : a < sg.length), D a → ρ a = i → x = sg[a]
    have himg : ¬ ImgD ρ D i := by
      rintro ⟨a, hDa, hρa⟩
      have hal : ¬ a < sg.length := fun hal => hin ⟨a, hDa, hρa, hal⟩
      have h : Tg[ρ a]? = (sg[a]?).map f := hT a hDa
      have hnone : Tg[i]? = none := by
        rw [← hρa, h, List.getElem?_eq_none (Nat.le_of_not_lt hal), Option.map_none]
      have hsome : Tg[i]? = some Tg[i] := List.getElem?_eq_getElem hi
      exact absurd (hnone.symm.trans hsome) (by simp)
    obtain ⟨x, hx⟩ : ∃ x, f x = Tg[i] := hout i Tg[i] himg (List.getElem?_eq_getElem hi)
    exact ⟨x, hx, fun a ha hDa hρa => absurd ⟨a, hDa, hρa, ha⟩ hin⟩

/-- An embedded position past the end of `sg` is past the end of `Tg`. -/
theorem pre_none {α β : Type} {f : α → β} {sg : List α} {Tg : List β} {a b : Nat}
    (h : Tg[b]? = (sg[a]?).map f) (hal : ¬ a < sg.length) : Tg.length ≤ b := by
  have hnone : Tg[b]? = none := by
    rw [h, List.getElem?_eq_none (Nat.le_of_not_lt hal), Option.map_none]
  exact List.getElem?_eq_none_iff.mp hnone

/-- An embedded position inside `sg` is inside `Tg`. -/
theorem pre_some {α β : Type} {f : α → β} {sg : List α} {Tg : List β} {a b : Nat}
    (h : Tg[b]? = (sg[a]?).map f) (hal : a < sg.length) : b < Tg.length := by
  have hsome : Tg[b]? = some (f sg[a]) := by
    rw [h, List.getElem?_eq_getElem hal, Option.map_some]
  exact (List.getElem?_eq_some_iff.mp hsome).1

/-- A list of images has a preimage agreeing with `sg` on the embedded positions. -/
theorem exists_pre {α β : Type} (f : α → β) {ρ : Nat → Nat} {D : Nat → Prop}
    (hinj : ∀ a b, D a → D b → ρ a = ρ b → a = b) (sg : List α) (Tg : List β)
    (hT : ∀ a, D a → Tg[ρ a]? = (sg[a]?).map f)
    (hout : ∀ b g, ¬ ImgD ρ D b → Tg[b]? = some g → ∃ x, f x = g) :
    ∃ tg : List α, tg.map f = Tg ∧ ∀ a, D a → tg[ρ a]? = sg[a]? := by
  have hex := exists_pre_entry f hinj sg Tg hT hout
  let tg : List α := List.ofFn fun (i : Fin Tg.length) => (hex i.1 i.2).choose
  have hlen : tg.length = Tg.length := List.length_ofFn
  have hmap : tg.map f = Tg := by
    apply List.ext_getElem (by simp [hlen])
    intro i h₁ h₂
    show (tg.map f)[i] = Tg[i]
    simp only [tg, List.getElem_map, List.getElem_ofFn]
    exact (hex i h₂).choose_spec.1
  refine ⟨tg, hmap, fun a hDa => ?_⟩
  show tg[ρ a]? = sg[a]?
  by_cases hal : a < sg.length
  · have hi : ρ a < Tg.length := pre_some (hT a hDa) hal
    have hget : tg[ρ a]'(hlen ▸ hi) = sg[a] := by
      simp only [tg, List.getElem_ofFn]
      exact (hex (ρ a) hi).choose_spec.2 a hal hDa rfl
    rw [List.getElem?_eq_getElem hal, List.getElem?_eq_getElem (hlen ▸ hi), hget]
  · have hge : Tg.length ≤ ρ a := pre_none (hT a hDa) hal
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hal), List.getElem?_eq_none (hlen ▸ hge)]

theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y ∈ l', f x = some y
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl'', rfl⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_mem hl'' x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-! ## Renaming commutes with the translation -/

theorem toCore_externalV (ρ : Nat → Nat) (x : Silmaril.Wasm.V2.Execution.ExternAddr) :
    (externalV ρ x).toCore = external ρ x.toCore := by
  cases x <;> rfl

theorem toCore_moduleViewV (ρ : Nat → Nat) (m : Silmaril.Wasm.V2.Execution.ModuleInst) :
    (moduleViewV ρ m).toCore = moduleView ρ m.toCore := by
  simp only [Silmaril.Wasm.V2.Execution.ModuleInst.toCore, moduleViewV, moduleView,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp [Silmaril.Wasm.V2.Execution.ExportInst.toCore, toCore_externalV]

theorem toCore_functionV (ρ : Nat → Nat) (fi : Silmaril.Wasm.V2.Execution.FuncInst H) :
    (functionV ρ fi).toCore = (fi.toCore).map (function ρ) := by
  obtain ⟨ty, m, code⟩ := fi
  cases code with
  | wasm fn =>
    simp only [Silmaril.Wasm.V2.Execution.FuncInst.toCore, functionV, Option.map_map]
    congr 1
    funext c
    simp [function, toCore_moduleViewV]
  | host h =>
    simp [Silmaril.Wasm.V2.Execution.FuncInst.toCore, functionV, function, toCore_moduleViewV]

theorem mapM_functionV (ρ : Nat → Nat) :
    ∀ l : List (Silmaril.Wasm.V2.Execution.FuncInst H),
      (l.map (functionV ρ)).mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore =
        (l.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore).map (List.map (function ρ))
  | [] => rfl
  | fi :: l => by
    simp only [List.map_cons, List.mapM_cons, toCore_functionV, mapM_functionV ρ l]
    cases fi.toCore <;> cases l.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore <;> rfl

/-- The erasure of a function instance's module. -/
abbrev eraseF (fi : FuncInst H) : FuncInst H :=
  { fi with module := Silmaril.Wasm.V2.Execution.ToCore.ModuleInst.erase fi.module }

theorem eraseF_function (ρ : Nat → Nat) (fi : FuncInst H) :
    eraseF (function ρ fi) = function ρ (eraseF fi) := rfl

theorem toCore_module {fi : Silmaril.Wasm.V2.Execution.FuncInst H} {fc : FuncInst H}
    (h : fi.toCore = some fc) : fc.module = fi.module.toCore := by
  obtain ⟨ty, m, code⟩ := fi
  cases code with
  | wasm fn =>
    simp only [Silmaril.Wasm.V2.Execution.FuncInst.toCore, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | host h' =>
    simp only [Silmaril.Wasm.V2.Execution.FuncInst.toCore, Option.some.injEq] at h
    subst h
    rfl

/-! ## Image stores -/

/-- The fields of an image store. -/
theorem toCore_fields {s : VStore H} {X : CStore H}
    (h : Silmaril.Wasm.V2.Execution.Store.toCore s = some X) :
    s.funcs.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore = some X.funcs ∧
      X.globals = s.globals.map Silmaril.Wasm.V2.Execution.GlobalInst.toCore ∧
      X.mems = s.mems.map Silmaril.Wasm.V2.Execution.MemInst.toCore ∧
      X.tables = s.tables.map Silmaril.Wasm.V2.Execution.TableInst.toCore ∧
      X.datas = s.datas.map Silmaril.Wasm.V2.Execution.DataInst.toCore ∧
      X.elems = s.elems.map Silmaril.Wasm.V2.Execution.ElemInst.toCore ∧
      X.tags = [] ∧ X.structs = [] ∧ X.arrays = [] ∧ X.exns = [] := by
  simp only [Silmaril.Wasm.V2.Execution.Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  exact ⟨hfs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A Core store with the fields of an image is that image. -/
theorem toCore_of_fields {s : VStore H} {X : CStore H}
    (hf : s.funcs.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore = some X.funcs)
    (hg : X.globals = s.globals.map Silmaril.Wasm.V2.Execution.GlobalInst.toCore)
    (hm : X.mems = s.mems.map Silmaril.Wasm.V2.Execution.MemInst.toCore)
    (ht : X.tables = s.tables.map Silmaril.Wasm.V2.Execution.TableInst.toCore)
    (hd : X.datas = s.datas.map Silmaril.Wasm.V2.Execution.DataInst.toCore)
    (he : X.elems = s.elems.map Silmaril.Wasm.V2.Execution.ElemInst.toCore)
    (h1 : X.tags = []) (h2 : X.structs = []) (h3 : X.arrays = []) (h4 : X.exns = []) :
    Silmaril.Wasm.V2.Execution.Store.toCore s = some X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := X
  simp only at hg hm ht hd he h1 h2 h3 h4 hf
  subst hg hm ht hd he h1 h2 h3 h4
  simp only [Silmaril.Wasm.V2.Execution.Store.toCore, hf, Option.map_some]

theorem erase_funcs (S : CStore H) :
    (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S).funcs = S.funcs.map eraseF := rfl

theorem modDomV_of_toCore {D : Nat → Prop} {m : Silmaril.Wasm.V2.Execution.ModuleInst}
    (h : ModDom D m.toCore) : ModDomV D m := by
  refine ⟨h.1, fun e he a ha => h.2 e.toCore ?_ a ?_⟩
  · exact List.mem_map_of_mem he
  · simp [Silmaril.Wasm.V2.Execution.ExportInst.toCore, ha,
      Silmaril.Wasm.V2.Execution.ExternAddr.toCore]

/-- The 2.0 functions of an embedded image store name only globals in the domain. -/
theorem fdomV_of_emb {ρ : Nat → Nat} {D : Nat → Prop} {S T : CStore H} {s : VStore H}
    (e : Emb ρ D S T)
    (hf : s.funcs.mapM Silmaril.Wasm.V2.Execution.FuncInst.toCore =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S).funcs) :
    ∀ fi ∈ s.funcs, ModDomV D fi.module := by
  intro fi hfi
  obtain ⟨fc, hfc, hfi'⟩ : ∃ fc ∈ (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S).funcs,
      fi.toCore = some fc := mapM_mem hf fi hfi
  obtain ⟨fS, hfS, hfc'⟩ : ∃ fS ∈ S.funcs, eraseF fS = fc := List.mem_map.1 hfc
  have hmod : fc.module = fi.module.toCore := toCore_module hfi'
  have hdom : ModDom D fS.module := e.fdom fS hfS
  have hdom' : ModDom D fi.module.toCore := by
    rw [← hmod, ← hfc']
    exact hdom
  exact modDomV_of_toCore hdom'

/-- **The target of an embedding of an image store is an image**, when its globals outside the
embedding are images: the image of the renamed 2.0 store. -/
theorem pre_store {ρ : Nat → Nat} {D : Nat → Prop} {S T : CStore H} {s : VStore H}
    (e : Emb ρ D S T) (out : OutG GImg ρ D T)
    (hs : Silmaril.Wasm.V2.Execution.Store.toCore s =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S)) :
    ∃ sT : VStore H, Silmaril.Wasm.V2.Execution.Store.toCore sT =
        some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase T) ∧ EmbV ρ D s sT := by
  obtain ⟨hf, hg, hm, ht, hd, hel, -⟩ := toCore_fields hs
  have hT : ∀ a, D a → T.globals[ρ a]? =
      (s.globals[a]?).map Silmaril.Wasm.V2.Execution.GlobalInst.toCore := by
    intro a hDa
    rw [e.globals a hDa, ← List.getElem?_map]
    exact congrArg (·[a]?) hg
  obtain ⟨gs, hgs, hgsD⟩ := exists_pre Silmaril.Wasm.V2.Execution.GlobalInst.toCore e.inj
    s.globals T.globals hT (fun b g hb hgb => out b g hb hgb)
  refine ⟨{ s with globals := gs, funcs := s.funcs.map (functionV ρ) }, ?_, ?_⟩
  · show Silmaril.Wasm.V2.Execution.Store.toCore _ =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase T)
    refine toCore_of_fields ?_ hgs.symm ?_ ?_ ?_ ?_ rfl rfl rfl rfl
    · rw [mapM_functionV, hf, Option.map_some, erase_funcs, erase_funcs, e.funcs]
      simp only [List.map_map]
      rfl
    · exact (congrArg Store.mems e.swap_eq).trans hm
    · exact (congrArg Store.tables e.swap_eq).trans ht
    · exact (congrArg Store.datas e.swap_eq).trans hd
    · exact (congrArg Store.elems e.swap_eq).trans hel
  · exact ⟨hgsD, e.inj, rfl, fdomV_of_emb e hf, rfl, rfl, rfl, rfl⟩

/-- The Core target after a host call: the source's result with the 2.0 answer's globals and
the target's functions. -/
def postT (S' T : CStore H) (sT' : VStore H) : CStore H :=
  { S' with globals := sT'.globals.map Silmaril.Wasm.V2.Execution.GlobalInst.toCore,
            funcs := T.funcs }

/-- **The 2.0 host's answer on the renamed store is an image target embedding the source's
answer.** -/
theorem post_store {ρ : Nat → Nat} {D : Nat → Prop} {S T S' : CStore H} {s' sT' : VStore H}
    (e : Emb ρ D S T)
    (hs' : Silmaril.Wasm.V2.Execution.Store.toCore s' =
      some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S'))
    (hfun : S'.funcs = S.funcs) (e' : EmbV ρ D s' sT') :
    Silmaril.Wasm.V2.Execution.Store.toCore sT' =
        some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase (postT S' T sT')) ∧
      Emb ρ D S' (postT S' T sT') ∧ OutG GImg ρ D (postT S' T sT') := by
  unfold postT
  obtain ⟨hf, hg, hm, ht, hd, hel, -⟩ := toCore_fields hs'
  refine ⟨toCore_of_fields ?_ rfl ?_ ?_ ?_ ?_ rfl rfl rfl rfl, ?_, ?_⟩
  · rw [e'.funcs, mapM_functionV, hf, Option.map_some, erase_funcs, erase_funcs, e.funcs, hfun]
    simp only [List.map_map]
    rfl
  · rw [← e'.mems]; exact hm
  · rw [← e'.tables]; exact ht
  · rw [← e'.datas]; exact hd
  · rw [← e'.elems]; exact hel
  · refine ⟨fun a hDa => ?_, e.inj, ?_, fun fi hfi => e.fdom fi (hfun ▸ hfi),
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show (sT'.globals.map _)[ρ a]? = S'.globals[a]?
      rw [List.getElem?_map, e'.globals a hDa, ← List.getElem?_map]
      exact (congrArg (·[a]?) hg).symm
    · show T.funcs = S'.funcs.map (function ρ)
      rw [hfun]; exact e.funcs
  · intro b g _ hgb
    show GImg g
    have hgb' : (sT'.globals[b]?).map Silmaril.Wasm.V2.Execution.GlobalInst.toCore = some g := by
      rw [← List.getElem?_map]
      exact hgb
    obtain ⟨gv, -, hgv⟩ : ∃ gv, sT'.globals[b]? = some gv ∧
        Silmaril.Wasm.V2.Execution.GlobalInst.toCore gv = g := Option.map_eq_some_iff.mp hgb'
    exact ⟨gv, hgv⟩

/-- **The Core host induced by a 2.0 host commuting with the 2.0 embeddings commutes with the
Core embeddings whose targets hold image globals outside the image.** -/
theorem hostEmbR_liftHost {src : VHost H} (hv : HostEmbV src) : HostEmbR GImg (liftHost src) where
  ret {ρ D S T S'} {h vs r} e out hl := by
    obtain ⟨s, ws, hs, rfl, hcase⟩ := hl
    rcases hcase with ⟨-, hout⟩ | ⟨s', r', S'', hsrc, hout, hs', hfun⟩
    · cases hout
    · simp only [Silmaril.Wasm.Execution.Host.Outcome.returned.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      obtain ⟨sT, hsT, eV⟩ := pre_store e out hs
      obtain ⟨sT', hsrcT, eV'⟩ := hv.ret eV hsrc
      obtain ⟨hcT, e', out'⟩ := post_store (T := T) e hs' hfun eV'
      exact ⟨_, ⟨sT, ws, hsT, rfl, Or.inr ⟨sT', r', _, hsrcT, rfl, hcT, rfl⟩⟩, e', out'⟩
  div {ρ D S T} {h vs} e out hl := by
    obtain ⟨s, ws, hs, rfl, hcase⟩ := hl
    rcases hcase with ⟨hd, -⟩ | ⟨s', r', S'', -, hout, -, -⟩
    · obtain ⟨sT, hsT, eV⟩ := pre_store e out hs
      exact ⟨sT, ws, hsT, rfl, Or.inl ⟨hv.div eV hd, rfl⟩⟩
    · cases hout

/-! ## Hosts blind to globals -/

theorem embV_swap_eq {ρ : Nat → Nat} {D : Nat → Prop} {s t : VStore H} (e : EmbV ρ D s t) :
    t = { s with globals := t.globals, funcs := t.funcs } := by
  obtain ⟨_, _, _, _, _, _⟩ := s
  obtain ⟨_, _, _, _, _, _⟩ := t
  simp only [Silmaril.Wasm.V2.Execution.Store.mk.injEq]
  exact ⟨trivial, trivial, e.tables.symm, e.mems.symm, e.elems.symm, e.datas.symm⟩

/-- **A 2.0 host blind to globals and functions commutes with the 2.0 embeddings.** -/
theorem hostEmbV_blind {src : VHost H} (hb : GlobalsBlindV src) : HostEmbV src where
  ret {ρ D s t s' h vs r} e hh := by
    have hk := hb.keeps _ _ _ _ _ hh
    refine ⟨{ s' with globals := t.globals, funcs := t.funcs }, ?_, ?_⟩
    · rw [embV_swap_eq e]
      exact hb.ret _ _ _ _ _ _ _ hh
    · refine ⟨fun a hDa => ?_, e.inj, ?_, fun fi hfi => e.fdom fi (hk.2 ▸ hfi), rfl, rfl, rfl, rfl⟩
      · show t.globals[ρ a]? = s'.globals[a]?
        rw [hk.1]; exact e.globals a hDa
      · show t.funcs = s'.funcs.map (functionV ρ)
        rw [hk.2]; exact e.funcs
  div {ρ D s t h vs} e hh := by
    rw [embV_swap_eq e]
    exact hb.div _ _ _ _ _ hh

/-- Pure 2.0 hosts are blind to globals and functions. -/
theorem pureHostV_blind
    (F : H → List Silmaril.Wasm.V2.Execution.Val → Silmaril.Wasm.V2.Execution.Result → Prop)
    (G : H → List Silmaril.Wasm.V2.Execution.Val → Prop) : GlobalsBlindV (pureHostV F G) where
  keeps _ _ _ _ _ hh := by
    rcases hh with ⟨_, _, he⟩ | ⟨_, he⟩
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  ret _ _ _ _ _ _ _ hh := by
    rcases hh with ⟨r', hr, he⟩ | ⟨_, he⟩
    · cases he
      exact Or.inl ⟨_, hr, rfl⟩
    · cases he
  div _ _ _ _ _ hh := by
    rcases hh with ⟨_, _, he⟩ | ⟨hg, -⟩
    · cases he
    · exact Or.inr ⟨hg, rfl⟩

end Silmaril.Proofs.Wasm.Models.V2CoreSpec
