module

public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

/-!
# `Engine.Core3.Typed.Store`: the laws that definitions cite

The theorems of the component reference copy `Engine.Core3.Typed.Store` that definition parts cite
(engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Store`, which imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
variable {H : Type}

theorem tyOk_ofList_num (Δ : TypeCtx) : ∀ ts : List NumType, TyOk Δ (Silmaril.Wasm.Validation.Ty.ofList (ts.map Silmaril.Wasm.Validation.Ty.num))
  | [] => .nil
  | t :: ts => .cons (.num t) (tyOk_ofList_num Δ ts)

/-- The defined type of a flat function type is valid in the empty context. -/
theorem tyOk_ofFlatType (ft : V1.FuncType) :
    TyOk ({} : TypeCtx) (SingleThreaded.ofFlatType ft) := by
  unfold SingleThreaded.ofFlatType V1.FuncType.toDefType
  simp only [liftRec, V1.FuncType.toCoreRec, List.map_cons, List.map_nil, liftSub, liftComp,
    V1.FuncType.toCore, V1.liftResult_toCore]
  exact TyOk.defn (GroupOk2.cons (SubOk2.noSuper (TyOk.func (tyOk_ofList_num _ _)
    (tyOk_ofList_num _ _))) GroupOk2.nil) (by simp [Silmaril.Wasm.Validation.Ty.length])

/-- The defined type of a flat function type expands to its numeric signature. -/
theorem expand_ofFlatType (ft : V1.FuncType) :
    Expand (SingleThreaded.ofFlatType ft)
      (.func (Silmaril.Wasm.Validation.Ty.ofList (ft.params.map Silmaril.Wasm.Validation.Ty.num)) (Silmaril.Wasm.Validation.Ty.ofList (ft.results.map Silmaril.Wasm.Validation.Ty.num))) :=
  Expand.iff.mpr (V1.FuncType.toDefType_expand ft)

/-- Appending a function instance that is typed in the extended store keeps the store typed and
extends it. -/
theorem StoreOk.appendFunc {s : Store H} {fi : FuncInst H} (hs : StoreOk s)
    (hfi : FuncInstOk { s with funcs := s.funcs ++ [fi] } fi) :
    StoreOk { s with funcs := s.funcs ++ [fi] } ∧ Extend s { s with funcs := s.funcs ++ [fi] } := by
  have he : Extend s { s with funcs := s.funcs ++ [fi] } :=
    { Extend.refl hs with
      funcs := ExtendsList.of_prefix (List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩ }
  have htr : ∀ {x y : FieldVal}, ImmutReachable { s with funcs := s.funcs ++ [fi] } x y →
      ImmutReachable s x y :=
    fun hr => TM.immutReachable_transfer (s := s) (s' := { s with funcs := s.funcs ++ [fi] })
      rfl rfl rfl hr
  refine ⟨{ tags := hs.tags, globals := ?_, mems := hs.mems, tables := ?_, funcs := ?_,
             elems := ?_, structs := ?_, arrays := ?_, exns := ?_, acyclicStructs := ?_,
             acyclicArrays := ?_, acyclicExns := ?_, structsClosed := hs.structsClosed,
             arraysClosed := hs.arraysClosed }, he⟩
  · intro gi h
    obtain ⟨h₁, h₂⟩ := hs.globals gi h
    exact ⟨h₁, TM.valOk_extend he h₂⟩
  · intro ti h
    exact TM.tableInstOk_extend he (hs.tables ti h)
  · intro fi' h
    rcases List.mem_append.mp h with h | h
    · cases hs.funcs fi' h with
      | wasm hdt hm hcode hf hsub => exact .wasm hdt (TM.moduleInstOk_extend hs he hm) hcode hf hsub
      | host hdt he' hcode => exact .host hdt he' hcode
    · rw [List.mem_singleton] at h
      subst h
      exact hfi
  · intro ei h
    exact TM.elemInstOk_extend he ⟨rfl, .inl rfl⟩ (hs.elems ei h)
  · intro si h
    obtain ⟨fs, hx, hf⟩ := hs.structs si h
    exact ⟨fs, hx, hf.imp fun _ _ h => TM.fieldValOk_extend he h⟩
  · intro ai h
    obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
    exact ⟨ft, hx, fun fv hfv => TM.fieldValOk_extend he (hf fv hfv)⟩
  · intro e h
    obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e h
    exact ⟨ti, ts, ht, hx, hf.imp fun _ _ h => TM.valOk_extend he h⟩
  · intro a ha hr
    exact hs.acyclicStructs a ha (htr hr)
  · intro a ha hr
    exact hs.acyclicArrays a ha (htr hr)
  · intro a ha hr
    exact hs.acyclicExns a ha (htr hr)

/-- `allocHost` appends the host function instance `⟨ofFlatType ft, {}, host h⟩`. -/
theorem allocHost_funcs {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat}
    (e : SingleThreaded.allocHost s ft h = (s', a)) :
    s' = { s with funcs := s.funcs ++ [⟨SingleThreaded.ofFlatType ft, {}, .host h⟩] } := by
  simp only [SingleThreaded.allocHost, allocFunc, Prod.mk.injEq] at e
  exact e.1.symm

/-- Host allocation keeps the store typed and extends it. -/
theorem allocHost_storeOk {s s' : Store H} {ft : V1.FuncType} {h : H} {a : Nat} (hs : StoreOk s)
    (e : SingleThreaded.allocHost s ft h = (s', a)) :
    StoreOk s' ∧ Extend s s' ∧
      s'.funcs = s.funcs ++ [⟨SingleThreaded.ofFlatType ft, {}, .host h⟩] := by
  rw [allocHost_funcs e]
  exact ⟨(StoreOk.appendFunc hs (.host (tyOk_ofFlatType ft) (expand_ofFlatType ft) rfl)).1,
    (StoreOk.appendFunc hs (.host (tyOk_ofFlatType ft) (expand_ofFlatType ft) rfl)).2, rfl⟩

/-- A byte write keeps the store typed, extends it and leaves the functions unchanged. -/
theorem memWrite?_storeOk {s s' : Store H} {m st : Nat} {bs : ByteArray} (hs : StoreOk s)
    (h : SingleThreaded.memWrite? s m st bs = some s') :
    StoreOk s' ∧ Extend s s' ∧ s'.funcs = s.funcs := by
  unfold SingleThreaded.memWrite? at h
  cases hm : s.mems[m]? with
  | none => simp [hm] at h
  | some mi =>
    cases hw : Silmaril.Wasm.Execution.Memory.writeBytes mi.bytes st bs with
    | none => simp [hm, hw] at h
    | some b =>
      simp only [hm, hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      have hsz := Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hw
      have hok := hs.mems mi (List.mem_of_getElem? hm)
      obtain ⟨h₁, h₂⟩ := StoreOk.setMem hs hm (mi' := { mi with bytes := b })
        ⟨rfl, rfl, Nat.le_refl _, Nat.le_of_eq hsz.symm⟩ ⟨hok.1, hsz.trans hok.2⟩
      exact ⟨h₁, h₂, rfl⟩

/-- Typing of a configuration survives store extension. -/
theorem configOk_extend {s s' : Store H} {f : Frame} {code : List Admin} {ts : List CValType}
    (hs : StoreOk s) (he : Extend s s') (hs' : StoreOk s') (h : ConfigOk ⟨s, f, code⟩ ts) :
    ConfigOk ⟨s', f, code⟩ ts := by
  obtain ⟨C, ⟨-, hf⟩, hc⟩ := h
  exact ⟨C, ⟨hs', FrameOk.extend_of_storeOk hs he hf⟩, AdminsOk.extend hs he hc⟩

/-- Every instruction of a typed sequence is typed (in some context, at some type). -/
theorem AdminsOk.mem_adminOk {s : Store H} {C : Context} {L : List Admin} {it : InstrType}
    (h : AdminsOk s C L it) : ∀ x ∈ L, ∃ C' it', AdminOk s C' x it' := by
  refine AdminsOk.rec' (motive := fun _ L _ => ∀ x ∈ L, ∃ C' it', AdminOk s C' x it')
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C x hx
    cases hx
  · intro C a it ha x hx
    have hxa : x = a := List.mem_singleton.mp hx
    exact ⟨_, _, hxa ▸ ha⟩
  · intro C as₁ as₂ _ _ _ _ _ _ _ _ ih₁ ih₂ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih₁ x hx
    · exact ih₂ x hx
  · intro C a as _ _ _ _ _ ha _ _ ih x hx
    rcases List.mem_cons.mp hx with hxa | hx
    · exact ⟨_, _, hxa ▸ ha⟩
    · exact ih x hx
  · intro C as it it' _ _ _ ih
    exact ih
  · intro C as ts t₁ t₂ xs _ _ ih
    exact ih

/-- A typed function reference names an allocated function. -/
theorem RefOk.func_exists {s : Store H} {a : Nat} {rt : CRefType} (h : RefOk s (.func a) rt) :
    ∃ fi, s.funcs[a]? = some fi := by
  generalize hr : Ref.func a = r at h
  induction h with
  | func h => cases hr; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih hr
  | _ => cases hr

/-- The callee of a typed invocation exists. -/
theorem invoke_func_exists {s : Store H} {a : Nat} {vs : List Val} {ts : List CValType}
    (h : ConfigOk (invoke s a vs) ts) : ∃ fi, s.funcs[a]? = some fi := by
  obtain ⟨C, -, hc⟩ := h
  have hmem : Admin.ref (.func a) ∈ (invoke s a vs).code := by simp [invoke]
  obtain ⟨C', it', ha⟩ := AdminsOk.mem_adminOk hc _ hmem
  cases ha with
  | ref hr => exact RefOk.func_exists hr

/-- A typed thread stays typed in an extended typed store. -/
theorem threadOk_extend {s s' : Store H} {t : SingleThreaded.Thread} {ts : List CValType}
    (hs : StoreOk s) (he : Extend s s') (hs' : StoreOk s') (h : SingleThreaded.ThreadOk s t ts) :
    SingleThreaded.ThreadOk s' t ts := by
  cases t with
  | active f code => exact configOk_extend hs he hs' h
  | pending a args =>
    obtain ⟨fi, hfi⟩ := invoke_func_exists h
    obtain ⟨fi', hfi', hx⟩ := he.funcs.get hfi
    have e : (SingleThreaded.Thread.pending a args).config s' =
        ⟨s', {}, (invoke s a args).code⟩ := by
      simp [SingleThreaded.Thread.config, invoke, hfi, hfi', hx.1]
    unfold SingleThreaded.ThreadOk
    rw [e]
    exact configOk_extend hs he hs' h

end Silmaril.Wasm.Component.Engine.Core3.Typed
