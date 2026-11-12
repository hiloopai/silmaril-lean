module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Inv

/-!
# Round 7: Core typing survives removing exports

Core's store and configuration typing read a module's exports only to check them
(`ModuleInstOk`: typed, distinct, among the module's addresses), and read a function instance
only through its type, module and code. So removing every export keeps a configuration typed:
`configOk_strip`. The pieces: invariance of the value judgments under function instances with
the same types (`valOk_withFuncs`, …), and the store, module, frame and code judgments at the
stripped store (`storeOk_strip`, `moduleInstOk_strip`, `adminOk_strip`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Value judgments only read the types of function instances -/

section WithFuncs

variable {s : Store H} {F : List (FuncInst H)} (hF : F.map stripFI = s.funcs.map stripFI)
include hF

theorem valOk_withFuncs {v : Val} {t : CValType} (h : ValOk s v t) :
    ValOk { s with funcs := F } v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (refOk_withFuncs hF h)

theorem fieldValOk_withFuncs {v : FieldVal} {t : CStorageType} (h : FieldValOk s v t) :
    FieldValOk { s with funcs := F } v t := by
  cases h with
  | val h => exact .val (valOk_withFuncs hF h)
  | pack p b => exact .pack p b

theorem externAddrOk_withFuncs {a : ExternAddr} {t : CExternType} (h : ExternAddrOk s a t) :
    ExternAddrOk { s with funcs := F } a t := by
  induction h with
  | tag h => exact .tag h
  | global h => exact .global h
  | mem h => exact .mem h
  | table h => exact .table h
  | func h =>
      rename_i a fi
      obtain ⟨fi', hfi', hty, -, -⟩ := stripFI_get hF h
      exact hty ▸ .func hfi'
  | sub _ hok hs ih => exact .sub ih hok hs

end WithFuncs

theorem immutReachable_withFuncs {s : Store H} {F : List (FuncInst H)} {a b : FieldVal}
    (h : ImmutReachable { s with funcs := F } a b) : ImmutReachable s a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | refExn hs hv => exact .refExn hs hv
  | refExtern r => exact .refExtern r

/-! ## The stripped store -/

theorem stripFI_stripFI (fi : FuncInst H) : stripFI (stripFI fi) = stripFI fi := rfl

theorem funcs_stripStore (s : Store H) :
    (stripStore s).funcs.map stripFI = s.funcs.map stripFI := by
  simp only [stripStore_eq, List.map_map]
  rfl

theorem moduleInstOk_strip {s : Store H} {m : ModuleInst} {C : Context}
    (h : ModuleInstOk s m C) : ModuleInstOk (stripStore s) (stripModule m) C := by
  have hF := funcs_stripStore s
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems _ _ _ hk =>
      exact .mk htypes
        (htags.imp fun _ _ h => externAddrOk_withFuncs hF h)
        (hglobals.imp fun _ _ h => externAddrOk_withFuncs hF h)
        (hfuncs.imp fun _ _ h => externAddrOk_withFuncs hF h)
        (hmems.imp fun _ _ h => externAddrOk_withFuncs hF h)
        (htables.imp fun _ _ h => externAddrOk_withFuncs hF h)
        hdatas
        (helems.imp fun _ _ ⟨ei, hei, hok, hty⟩ =>
          ⟨ei, hei, ⟨hok.1, fun r hr => refOk_withFuncs hF (hok.2 r hr)⟩, hty⟩)
        (fun _ h => absurd h List.not_mem_nil) List.nodup_nil
        (fun _ h => absurd h List.not_mem_nil) hk

theorem funcInstOk_strip {s : Store H} {fi : FuncInst H} (h : FuncInstOk s fi) :
    FuncInstOk (stripStore s) (stripFI fi) := by
  cases h with
  | wasm hdt hm hcode hf hs => exact .wasm hdt (moduleInstOk_strip hm) hcode hf hs
  | host hdt he hcode => exact .host hdt he hcode

theorem storeOk_strip {s : Store H} (h : StoreOk s) : StoreOk (stripStore s) := by
  have hF : (stripStore s).funcs.map stripFI = s.funcs.map stripFI := funcs_stripStore s
  refine ⟨h.tags, ?_, h.mems, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.structsClosed,
    h.arraysClosed⟩
  · exact fun gi hgi => ⟨(h.globals gi hgi).1, valOk_withFuncs hF (h.globals gi hgi).2⟩
  · exact fun ti hti => ⟨(h.tables ti hti).1, (h.tables ti hti).2.1,
      fun r hr => refOk_withFuncs hF ((h.tables ti hti).2.2 r hr)⟩
  · intro fi hfi
    obtain ⟨fi₀, hfi₀, hfe⟩ : ∃ fi₀ ∈ s.funcs, stripFI fi₀ = fi := List.mem_map.mp hfi
    exact hfe ▸ funcInstOk_strip (h.funcs fi₀ hfi₀)
  · exact fun ei hei => ⟨(h.elems ei hei).1, fun r hr => refOk_withFuncs hF ((h.elems ei hei).2 r hr)⟩
  · intro si hsi
    obtain ⟨fs, he, hfs⟩ := h.structs si hsi
    exact ⟨fs, he, hfs.imp fun _ _ h => fieldValOk_withFuncs hF h⟩
  · intro ai hai
    obtain ⟨ft, he, hfs⟩ := h.arrays ai hai
    exact ⟨ft, he, fun fv hfv => fieldValOk_withFuncs hF (hfs fv hfv)⟩
  · intro e he
    obtain ⟨ti, ts, ht, hx, hvs⟩ := h.exns e he
    exact ⟨ti, ts, ht, hx, hvs.imp fun _ _ h => valOk_withFuncs hF h⟩
  · exact fun a ha hr => h.acyclicStructs a ha (immutReachable_withFuncs hr)
  · exact fun a ha hr => h.acyclicArrays a ha (immutReachable_withFuncs hr)
  · exact fun a ha hr => h.acyclicExns a ha (immutReachable_withFuncs hr)

theorem localValOk_strip {s : Store H} {v : Option Val} {lt : LocalType}
    (h : LocalValOk s v lt) : LocalValOk (stripStore s) v lt := by
  cases h with
  | set h => exact .set (valOk_withFuncs (funcs_stripStore s) h)
  | unset h => exact .unset h

theorem frameOk_strip {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    FrameOk (stripStore s) (stripFrame f) C := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := h
  exact ⟨C₀, lts, moduleInstOk_strip hm, hl.imp fun _ _ h => localValOk_strip h, rfl⟩

theorem stripAdmins_expression (cont : List Instr) :
    stripAdmins (expression cont) = expression cont :=
  stripAdmins_atomic fun a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact True.intro

mutual
theorem adminOk_strip {s : Store H} :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it →
      AdminOk (stripStore s) C (stripAdmin a) it
  | _, _, _, .plain h => .plain h
  | _, _, _, .callRefType hok hex => .callRefType hok hex
  | _, _, _, .returnCallRefType hok hex hr hsub hit => .returnCallRefType hok hex hr hsub hit
  | _, _, _, .ref h => .ref (refOk_withFuncs (funcs_stripStore s) h)
  | _, _, _, .label hn hc hb =>
      .label hn (stripAdmins_expression _ ▸ adminsOk_strip hc) (adminsOk_strip hb)
  | _, _, _, .frame hf hn hb hok => .frame (frameOk_strip hf) hn (adminsOk_strip hb) hok
  | _, _, _, .handler hc hb => .handler hc (adminsOk_strip hb)
  | _, _, _, .trap hok => .trap hok
  | _, _, _, .throwRefInits hok => .throwRefInits hok

theorem adminsOk_strip {s : Store H} :
    ∀ {C : Context} {l : List Admin} {it : InstrType}, AdminsOk s C l it →
      AdminsOk (stripStore s) C (stripAdmins l) it
  | _, _, _, .nil => .nil
  | _, _, _, .single h => .single (adminOk_strip h)
  | _, _, _, .seq h₁ hx h₂ => by
      rw [stripAdmins_append]
      exact .seq (adminsOk_strip h₁) hx (adminsOk_strip h₂)
  | _, _, _, .cons ha hx hs => .cons (adminOk_strip ha) hx (adminsOk_strip hs)
  | _, _, _, .sub h hsub hok => .sub (adminsOk_strip h) hsub hok
  | _, _, _, .frame h hok => .frame (adminsOk_strip h) hok

end

/-- **Removing every export keeps a configuration typed.** -/
theorem configOk_strip {c : Config H} {ts : List CValType} (h : ConfigOk c ts) :
    ConfigOk (stripConfig c) ts := by
  obtain ⟨C, ⟨hs, hf⟩, hc⟩ := h
  exact ⟨C, ⟨storeOk_strip hs, frameOk_strip hf⟩, adminsOk_strip hc⟩

end Silmaril.Wasm.SpecTec.Sim.Round7
