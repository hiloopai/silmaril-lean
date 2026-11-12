module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SelCore

/-!
# `StoreOk10` from V1 module validation

`GoodV1`'s second field, `StoreOk10`, says that the store's functions have at most one result
and that every table entry names a function of the store. Round 4 noted that Core's `StoreOk`
does not give the arity half (Core function types may have several results). Here both halves
come from V1 itself, with no Core detour:

* `storeOk10_prepare`: V1's executable allocation and segment initialisation (`prepare?`) of a
  module that V1 validates (`ModuleValid`, whose `FuncTypeValid` is the 1.0 arity bound), with
  imports that match (`ImportsMatch`), keeps `StoreOk10` and `NoHost10`. New functions take their
  types from the module's type section; new tables are empty; element segments write the
  module's function addresses, which are imported (so allocated) or fresh.
* `storeOk10_step`, `storeOk10_steps`: a V1 step from a store with no host function changes
  neither the functions nor the tables.
* **`storeOk10_instantiation`**: so a V1 instantiation (`Instantiation`, which includes the run
  of the start function) of a valid module into a store with `StoreOk10` and no host function
  ends in a store with both; `storeOk10_empty` starts the chain at the empty store.

This replaces Core's `StoreOk` for `StoreOk10` by V1 module validation. `ResOkL10` (named
resources exist) is not derived here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Runtime (ExternVal FuncAddr ModuleInst FuncInst TableInst AddrKind)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps allocate? prepare?
  Prepared ImportsMatch ExternMatches applyElem applyData resolveElem? ElemWrite DataWrite
  importedInstance addresses Instantiation)
open Silmaril.Wasm.SpecTec.Sim10.Whole (NoHost10)
open Silmaril.Wasm.SpecTec.Sim10 (StoreOk10)

variable {H : Type}

/-! ## Lists -/

theorem mapM_some_mem {α β : Type _} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → ∀ y ∈ r, ∃ x ∈ l, g x = some y
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self .., hb⟩
    · obtain ⟨x, hx, hgx⟩ := mapM_some_mem hbs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hgx⟩

theorem mapM_some_length {α β : Type _} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    simp [mapM_some_length hbs]

theorem mem_modify {α : Type _} {f : α → α} :
    ∀ {l : List α} {i : Nat} {x : α}, x ∈ l.modify i f → x ∈ l ∨ ∃ y ∈ l, x = f y
  | [], _, _, h => by simp at h
  | a :: l, 0, x, h => by
    simp only [List.modify_zero_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inr ⟨a, List.mem_cons_self .., rfl⟩
    · exact .inl (List.mem_cons_of_mem _ h)
  | a :: l, i + 1, x, h => by
    simp only [List.modify_succ_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl (List.mem_cons_self ..)
    · rcases mem_modify h with h | ⟨y, hy, rfl⟩
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

/-! ## Steps -/

/-- **A V1 step from a store with no host function keeps `StoreOk10`**: it changes neither the
functions nor the tables. -/
theorem storeOk10_step {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hnh : NoHost10 c.store) (hs : StoreOk10 c.store) : StoreOk10 c'.store := by
  induction h with
  | context _ vs tail ih => exact ih hnh hs
  | label _ n cont ih => exact ih hnh hs
  | frame _ n outer ih => exact ih hnh hs
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact absurd h₁ (hnh _ _ _)
  | _ => exact hs

/-- **`StoreOk10` along every V1 run** from a store with no host function. -/
theorem storeOk10_steps {host : HostSemantics H} {c c' : Config H} (h : Steps host c c')
    (hnh : NoHost10 c.store) (hs : StoreOk10 c.store) : NoHost10 c'.store ∧ StoreOk10 c'.store := by
  induction h with
  | refl => exact ⟨hnh, hs⟩
  | tail _ hst ih => exact ⟨Whole.noHost10_step hst ih.1, storeOk10_step hst ih.1 ih.2⟩

/-! ## Segment writes -/

/-- Data writes keep functions and tables. -/
theorem foldl_applyData (s : Store H) : ∀ (ds : List DataWrite),
    (ds.foldl applyData s).funcs = s.funcs ∧ (ds.foldl applyData s).tables = s.tables
  | [] => ⟨rfl, rfl⟩
  | d :: ds => foldl_applyData (applyData s d) ds

/-- An element write of addresses of the store keeps the table half. -/
theorem tabOk_applyElem {s : Store H} {w : ElemWrite}
    (hw : ∀ a ∈ w.values, a.value < s.funcs.length) (hs : StoreOk10 s) :
    StoreOk10 (applyElem s w) := by
  refine ⟨hs.1, fun t ht a ha => ?_⟩
  rcases mem_modify ht with ht | ⟨t₀, ht₀, rfl⟩
  · exact hs.2 t ht a ha
  · simp only [List.mem_append, List.mem_map] at ha
    rcases ha with (ha | ha) | ha
    · exact hs.2 t₀ ht₀ a (List.mem_of_mem_take ha)
    · obtain ⟨b, hb, e⟩ := ha
      exact Option.some.inj e ▸ hw b hb
    · exact hs.2 t₀ ht₀ a (List.mem_of_mem_drop ha)

/-- Element writes of addresses of the store keep `StoreOk10` and the functions. -/
theorem foldl_applyElem : ∀ (ws : List ElemWrite) (s : Store H),
    (∀ w ∈ ws, ∀ a ∈ w.values, a.value < s.funcs.length) → StoreOk10 s →
    StoreOk10 (ws.foldl applyElem s) ∧ (ws.foldl applyElem s).funcs = s.funcs
  | [], _, _, hs => ⟨hs, rfl⟩
  | w :: ws, s, hw, hs => by
    have h₁ := tabOk_applyElem (hw w (List.mem_cons_self ..)) hs
    have e : (applyElem s w).funcs = s.funcs := rfl
    obtain ⟨h₂, e₂⟩ := foldl_applyElem ws (applyElem s w)
      (fun w' hw' a ha => e ▸ hw w' (List.mem_cons_of_mem _ hw') a ha) h₁
    exact ⟨h₂, e₂.trans e⟩

/-- A resolved element segment writes addresses of the module's functions. -/
theorem resolveElem_values {s : Store H} {mi : ModuleInst} {e : V1.Elem} {w : ElemWrite}
    (h : resolveElem? s mi e = some w) : ∀ a ∈ w.values, a ∈ mi.funcs := by
  unfold resolveElem? at h
  simp only [bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨off, -, a, -, table, -, refs, hrefs, hif⟩ := h
  split at hif
  · simp only [Option.some.injEq] at hif
    subst hif
    intro b hb
    obtain ⟨i, -, hi⟩ := mapM_some_mem hrefs b hb
    exact List.mem_of_getElem? hi
  · cases hif

/-! ## Allocation -/

/-- What allocation does to functions and tables. -/
theorem allocate_spec {s : Store H} {m : V1.Module} {imports : List ExternVal} {s₁ : Store H}
    {mi : ModuleInst} (h : allocate? s m imports = some (s₁, mi)) :
    ∃ (fs : List (FuncInst V1.Func H)) (ts : List TableInst),
      s₁.funcs = s.funcs ++ fs ∧ s₁.tables = s.tables ++ ts ∧ fs.length = m.funcs.length ∧
      (∀ fi ∈ fs, (∃ ft mo f, fi = .wasm ft mo f) ∧ fi.type ∈ m.types) ∧
      (∀ t ∈ ts, ∀ x ∈ t.refs, x = none) ∧
      mi.funcs = (importedInstance imports).funcs ++ addresses .func s.funcs.length m.funcs.length := by
  unfold allocate? at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨inits, -, exps, -, fs, hfs, rfl, rfl⟩ := h
  refine ⟨fs, _, rfl, rfl, mapM_some_length hfs, fun fi hfi => ?_, fun t ht x hx => ?_, rfl⟩
  · obtain ⟨f, -, hf⟩ := mapM_some_mem hfs fi hfi
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hf
    obtain ⟨ft, hft, rfl⟩ := hf
    exact ⟨⟨_, _, _, rfl⟩, List.mem_of_getElem? hft⟩
  · simp only [List.mem_map] at ht
    obtain ⟨tt, -, rfl⟩ := ht
    exact List.eq_of_mem_replicate hx

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil => by simp
  | _, _, .cons hab h => by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right h b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Every import satisfies its extern type. -/
theorem importsMatch_mem {s : Store H} {m : V1.Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) : ∀ e ∈ imports, ∃ et, ExternMatches s e et := by
  intro e he
  obtain ⟨i, -, et, -, hm⟩ := forall₂_mem_right h e he
  exact ⟨et, hm⟩

/-- An imported function is allocated. -/
theorem imported_funcs_lt {s : Store H} {m : V1.Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) {a : FuncAddr} (ha : a ∈ (importedInstance imports).funcs) :
    a.value < s.funcs.length := by
  simp only [importedInstance, List.mem_filterMap] at ha
  obtain ⟨e, he, hea⟩ := ha
  obtain ⟨et, hm⟩ := importsMatch_mem h e he
  cases e with
  | func b =>
    simp only [Option.some.injEq] at hea
    subst hea
    cases hm with
    | func _ fn _ found _ => exact (List.getElem?_eq_some_iff.1 found).1
  | _ => simp at hea

/-- A fresh address is below the new length. -/
theorem addresses_lt {n k : Nat} {a : FuncAddr} (h : a ∈ addresses .func n k) : a.value < n + k := by
  simp only [addresses, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only
  omega

/-- No host function among the allocated ones. -/
theorem noHost10_append {s : Store H} {fs : List (FuncInst V1.Func H)} (hnh : NoHost10 s)
    (hfs : ∀ fi ∈ fs, ∃ ft mo f, fi = .wasm ft mo f) (s' : Store H)
    (he : s'.funcs = s.funcs ++ fs) : NoHost10 s' := by
  intro i ft h hi
  rw [he, List.getElem?_append] at hi
  split at hi
  · exact hnh i ft h hi
  · obtain ⟨ft', mo, f, e⟩ := hfs _ (List.mem_of_getElem? hi)
    cases e

/-- Allocation of a V1-valid module keeps `StoreOk10`. -/
theorem storeOk10_allocate {s s₁ : Store H} {m : V1.Module} {fs : List (FuncInst V1.Func H)}
    {ts : List TableInst} (hv : V1.Validation.ModuleValid m) (hs : StoreOk10 s)
    (hf : s₁.funcs = s.funcs ++ fs) (ht : s₁.tables = s.tables ++ ts)
    (hfs : ∀ fi ∈ fs, fi.type ∈ m.types) (hts : ∀ t ∈ ts, ∀ x ∈ t.refs, x = none) :
    StoreOk10 s₁ := by
  refine ⟨fun fi hfi => ?_, fun t ht' a ha' => ?_⟩
  · rcases List.mem_append.1 (hf ▸ hfi) with hfi | hfi
    · exact hs.1 fi hfi
    · exact hv.types _ (hfs fi hfi)
  · rcases List.mem_append.1 (ht ▸ ht') with ht' | ht'
    · have hle : s.funcs.length ≤ s₁.funcs.length := by
        rw [hf, List.length_append]; exact Nat.le_add_right _ _
      exact Nat.lt_of_lt_of_le (hs.2 t ht' a ha') hle
    · cases hts t ht' _ ha'

/-- The element segments of an allocated module write allocated functions. -/
theorem elems_lt10 {s s₁ : Store H} {m : V1.Module} {imports : List ExternVal}
    {mi : ModuleInst} {fs : List (FuncInst V1.Func H)} {elems : List ElemWrite}
    (hi : ImportsMatch s m imports) (hf : s₁.funcs = s.funcs ++ fs)
    (hlen : fs.length = m.funcs.length)
    (hmi : mi.funcs = (importedInstance imports).funcs ++
      addresses .func s.funcs.length m.funcs.length)
    (he : m.elems.mapM (resolveElem? s₁ mi) = some elems) :
    ∀ w ∈ elems, ∀ a ∈ w.values, a.value < s₁.funcs.length := by
  intro w hw a ha'
  obtain ⟨e, -, hre⟩ := mapM_some_mem he w hw
  have hm : a ∈ mi.funcs := resolveElem_values hre a ha'
  have hl : s₁.funcs.length = s.funcs.length + m.funcs.length := by
    rw [hf, List.length_append, hlen]
  rw [hmi, List.mem_append] at hm
  rw [hl]
  rcases hm with hm | hm
  · exact Nat.lt_of_lt_of_le (imported_funcs_lt hi hm) (Nat.le_add_right _ _)
  · exact addresses_lt hm

/-- The store `prepare?` returns: allocation, then element and data writes. -/
theorem prepare_store {s : Store H} {m : V1.Module} {imports : List ExternVal} {p : Prepared H}
    (h : prepare? s m imports = some p) :
    ∃ s₁ mi elems data, allocate? s m imports = some (s₁, mi) ∧
      m.elems.mapM (resolveElem? s₁ mi) = some elems ∧
      p.store = List.foldl applyData (List.foldl applyElem s₁ elems) data := by
  unfold prepare? at h
  simp only [bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨⟨s₁, mi⟩, ha, elems, he, data, -, hrest⟩ := h
  refine ⟨s₁, mi, elems, data, ha, he, ?_⟩
  cases hm : m.start <;> simp only [hm, Option.bind_eq_some_iff, Option.some.injEq] at hrest
  · obtain ⟨_, -, rfl⟩ := hrest; rfl
  · obtain ⟨_, -, rfl⟩ := hrest; rfl

/-- **Allocation and segment initialisation of a V1-valid module keep `StoreOk10` and
`NoHost10`.** -/
theorem storeOk10_prepare {s : Store H} {m : V1.Module} {imports : List ExternVal}
    {p : Prepared H} (hv : V1.Validation.ModuleValid m) (hi : ImportsMatch s m imports)
    (hnh : NoHost10 s) (hs : StoreOk10 s) (h : prepare? s m imports = some p) :
    NoHost10 p.store ∧ StoreOk10 p.store := by
  obtain ⟨s₁, mi, elems, data, ha, he, hp⟩ := prepare_store h
  obtain ⟨fs, ts, hf, ht, hlen, hfs, hts, hmi⟩ := allocate_spec ha
  have hs₁ : StoreOk10 s₁ := storeOk10_allocate hv hs hf ht (fun fi hfi => (hfs fi hfi).2) hts
  obtain ⟨hE, eE⟩ := foldl_applyElem elems s₁ (elems_lt10 hi hf hlen hmi he) hs₁
  obtain ⟨eDf, eDt⟩ := foldl_applyData (List.foldl applyElem s₁ elems) data
  rw [hp]
  refine ⟨noHost10_append hnh (fun fi hfi => (hfs fi hfi).1) _ (by rw [eDf, eE, hf]), ?_⟩
  exact ⟨fun fi hfi => hE.1 fi (by rw [eDf] at hfi; exact hfi),
    fun t ht' a ha' => by rw [eDf]; exact hE.2 t (by rw [eDt] at ht'; exact ht') a ha'⟩

/-! ## Instantiation -/

/-- The empty store satisfies `StoreOk10` and has no host function. -/
theorem storeOk10_empty : NoHost10 ({} : Store H) ∧ StoreOk10 ({} : Store H) :=
  ⟨fun _ _ _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- **A V1 instantiation of a valid module keeps `StoreOk10` and `NoHost10`**, including the run
of its start function. -/
theorem storeOk10_instantiation {host : HostSemantics H} {before after : Store H}
    {m : V1.Module} {imports : List ExternVal} {module : ModuleInst}
    {outcome : Execution.Runtime.Result}
    (hI : Instantiation host before m imports after module outcome) (hnh : NoHost10 before)
    (hs : StoreOk10 before) : NoHost10 after ∧ StoreOk10 after := by
  obtain ⟨p, hp, -, hst⟩ := hI.prepared
  obtain ⟨hnh', hs'⟩ := storeOk10_prepare hI.valid hI.importsMatch hnh hs hp
  exact storeOk10_steps hst hnh' hs'

/-! ## `GoodV1` from validation -/

/-- **`GoodV1` from validation**: `SelOk` and `GSetOk` from Core typing, `StoreOk10` from V1
(for instance `storeOk10_instantiation`); only `ResOkL10` is assumed. -/
theorem goodV1_of_valid {c : Config H} (hr : Silmaril.Wasm.SpecTec.Sim10.ResOkL10 c.store c.frame c.code)
    (hs : StoreOk10 c.store) (hc : CoreTyped10 c) : Silmaril.Wasm.SpecTec.Sim10.GoodV1 c :=
  ⟨hr, hs, selOk_of_coreTyped10 hc, gsetOk_of_coreTyped10 hc⟩

/-- **`GoodV1` along a V1 run**, from a `CoreTyped10` configuration whose store has no host
function and satisfies `StoreOk10`, wherever `ResOkL10` holds. -/
theorem goodV1_steps {host : HostSemantics H} {c d : Config H} (h : Steps host c d)
    (hnh : NoHost10 c.store) (hs : StoreOk10 c.store) (hc : CoreTyped10 c)
    (hr : Silmaril.Wasm.SpecTec.Sim10.ResOkL10 d.store d.frame d.code) :
    Silmaril.Wasm.SpecTec.Sim10.GoodV1 d :=
  goodV1_of_valid hr (storeOk10_steps h hnh hs).2 (coreTyped10_steps h hnh hc).2

end Silmaril.Wasm.SpecTec.Sim10.Valid
