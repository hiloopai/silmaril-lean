module

public import Silmaril.Wasm.Binary.Extensions.SharedMemory.Modules
public import Silmaril.Wasm.Binary.Core.CompactImports

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.SharedMemory

open Core

private theorem seq_map {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    (f : α → β) (hf : ∀ b x, G b x → H b (f x)) {bs : Bytes} {xs : List α}
    (h : Seq G bs xs) : Seq H bs (xs.map f) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hf _ _ hx) ih

private theorem vec_map {α β : Type} {G : Bytes → α → Prop} {H : Bytes → β → Prop}
    (f : α → β) (hf : ∀ b x, G b x → H b (f x)) {bs : Bytes} {xs : List α}
    (h : Vec G bs xs) : Vec H bs (xs.map f) := by
  cases h with
  | mk hn hs => exact .mk (by simpa using hn) (seq_map f hf hs)

theorem ExternType.of_core {F : Forms} {b : Bytes} {t : Wasm.ExternType}
    (h : Core.ExternType F b t) : ExternType F b (Wasm.Extensions.SharedMemory.ExternType.ofCore t) := by
  cases h with
  | func hx => exact .func hx
  | table hx => exact .table hx
  | memory hx => exact .memory (.unshared hx)
  | global hx => exact .global hx
  | tag hx => exact .tag hx

theorem Item.of_core {F : Forms} {b : Bytes} {item : String × Wasm.ExternType}
    (h : Core.CompactImports.Item F b item) :
    Item F b (item.1, Wasm.Extensions.SharedMemory.ExternType.ofCore item.2) := by
  cases h with | mk hn ht => exact .mk hn (ExternType.of_core ht)

theorem Group.of_core {F : Forms} {b : Bytes} {is : List Wasm.Import}
    (h : Core.CompactImports.Group F b is) :
    Group F b (is.map Wasm.Extensions.SharedMemory.Import.ofCore) := by
  cases h with
  | mk hm hn ht =>
    cases ht with
    | single ht => exact .mk hm hn (.single (ExternType.of_core ht))
    | sharedModule hx =>
      have hg := vec_map (fun i : String × Wasm.ExternType =>
        (i.1, Wasm.Extensions.SharedMemory.ExternType.ofCore i.2)) (fun _ _ h => Item.of_core h) hx
      simpa [expandItems, Core.CompactImports.expandItems,
        Wasm.Extensions.SharedMemory.Import.ofCore, List.map_map, Function.comp_def]
        using (Group.mk hm hn (Tail.sharedModule hg))
    | sharedAll ht hx =>
      simpa [expandNames, Core.CompactImports.expandNames,
        Wasm.Extensions.SharedMemory.Import.ofCore, List.map_map, Function.comp_def]
        using (Group.mk hm hn (Tail.sharedAll (ExternType.of_core ht) hx))

theorem ImportBody.of_core {F : Forms} {b : Bytes} {is : List Wasm.Import}
    (h : Core.CompactImports.ImportBody F b is) :
    ImportBody F b (is.map Wasm.Extensions.SharedMemory.Import.ofCore) := by
  cases h with
  | mk hg =>
    have h := vec_map (List.map Wasm.Extensions.SharedMemory.Import.ofCore) (fun _ _ h => Group.of_core h) hg
    simpa using (ImportBody.mk h)

theorem ImportSec.of_core {F : Forms} {b : Bytes} {is : List Wasm.Import}
    (h : Core.CompactImports.ImportSec F b is) :
    ImportSec F b (is.map Wasm.Extensions.SharedMemory.Import.ofCore) := by
  cases h with
  | empty => exact .empty
  | mk hl he hb => exact .mk hl he (ImportBody.of_core hb)

theorem MemSec.of_core {F : Forms} {b : Bytes} {ms : List Wasm.MemoryType}
    (h : Core.MemSec F b ms) :
    Section 5 (Vec (MemType F)) b (ms.map fun m => ⟨m, false⟩) := by
  cases h with
  | empty => exact .empty
  | mk hl he hb => exact .mk hl he (vec_map (fun m : Wasm.MemoryType => (⟨m, false⟩ : MemoryType)) (fun _ _ h => MemType.unshared h) hb)

/-- Every original compact-import Core encoding embeds without changing bytes
or adding shared flags. Together with `Module.toCore?_ofCore`, this provides a
checked, conservative boundary for existing Core syntax. -/
theorem of_compact_core {F : Forms} {b : Bytes} {m : Wasm.Module}
    (h : Core.CompactImports.Module F b m) :
    Module F b (Wasm.Extensions.SharedMemory.Module.ofCore m) := by
  cases h with
  | mk h₀ hty h₁ him h₂ hfn h₃ htb h₄ hme h₅ htg h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco
      h₁₂ hda h₁₃ hcount hdataidx hfuncs =>
    exact .mk h₀ hty h₁ (ImportSec.of_core him) h₂ hfn h₃ htb h₄ (MemSec.of_core hme) h₅ htg
      h₆ hgl h₇ hex h₈ hst h₉ hel h₁₀ hdc h₁₁ hco h₁₂ hda h₁₃ hcount hdataidx hfuncs

theorem of_standard_core {F : Forms} {b : Bytes} {m : Wasm.Module}
    (h : Core.Module F b m) : Module F b (Wasm.Extensions.SharedMemory.Module.ofCore m) :=
  of_compact_core (Core.CompactImports.of_standard h)

end Silmaril.Wasm.Binary.Extensions.SharedMemory
