module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes.Read

/-!
# A record reads back from the byte layout

`readRec_layout`: in the layout of `pre ++ enc q ++ post`, the record read backwards from the end
address of `enc q` is `q`, starting at the end address of `pre`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC Silmaril.Wasm.FX.Asyncify.Shadow

variable {V : Type} (C : Codec V)

/-- The layout of a record: its operand slots, then the trailer words. -/
theorem layout_enc {q : Rec V} {bq : List UInt8} (h : layout C (enc q) = some bq) :
    ∃ ob, layout C (q.ops.map .sv) = some ob ∧ q.fn < 2 ^ 32 ∧ q.r < 2 ^ 32 ∧
      q.ops.length < 2 ^ 32 ∧ bq = ob ++ (le32 q.fn ++ le32 q.r ++ le32 q.ops.length) := by
  obtain ⟨ob, tb, ho, ht, rfl⟩ := layout_append C (a := q.ops.map .sv) h
  obtain ⟨b1, t1, h1, ht1, rfl⟩ := layout_cons C ht
  obtain ⟨b2, t2, h2, ht2, rfl⟩ := layout_cons C ht1
  obtain ⟨b3, t3, h3, ht3, rfl⟩ := layout_cons C ht2
  have e3 : t3 = [] := by cases ht3; rfl
  obtain ⟨n1, rfl⟩ := cellBytes_num C h1
  obtain ⟨n2, rfl⟩ := cellBytes_num C h2
  obtain ⟨n3, rfl⟩ := cellBytes_num C h3
  exact ⟨ob, ho, n1, n2, n3, by simp [e3]⟩

theorem addrOf_append (a b : List (Cell V)) : addrOf C (a ++ b) = addrOf C a + addrOf C b := by
  simp [addrOf]

/-- The bytes of a record with its operand slots `ob`, between `bp` and `bpost`. -/
abbrev recBytes (bp ob bpost : List UInt8) (fn r n : Nat) : List UInt8 :=
  bp ++ (ob ++ (le32 fn ++ le32 r ++ le32 n)) ++ bpost

theorem rd_count (bp ob bpost : List UInt8) (fn r : Nat) {n : Nat} (hn : n < 2 ^ 32) :
    rd32 (recBytes bp ob bpost fn r n) (bp.length + ob.length + 12 - 4) = n := by
  have h : rd32 (bp ++ ob ++ le32 fn ++ le32 r ++ le32 n ++ bpost)
      (bp ++ ob ++ le32 fn ++ le32 r).length = n := rd32_at hn
  have hl : (bp ++ ob ++ le32 fn ++ le32 r).length = bp.length + ob.length + 12 - 4 := by
    simp only [List.length_append, le32_len]
    omega
  rw [hl] at h
  simpa only [recBytes, List.append_assoc] using h

theorem rd_resume (bp ob bpost : List UInt8) (fn n : Nat) {r : Nat} (hr : r < 2 ^ 32) :
    rd32 (recBytes bp ob bpost fn r n) (bp.length + ob.length + 12 - 8) = r := by
  have h : rd32 (bp ++ ob ++ le32 fn ++ le32 r ++ (le32 n ++ bpost))
      (bp ++ ob ++ le32 fn).length = r := rd32_at hr
  have hl : (bp ++ ob ++ le32 fn).length = bp.length + ob.length + 12 - 8 := by
    simp only [List.length_append, le32_len]
    omega
  rw [hl] at h
  simpa only [recBytes, List.append_assoc] using h

theorem rd_fn (bp ob bpost : List UInt8) (r n : Nat) {fn : Nat} (hfn : fn < 2 ^ 32) :
    rd32 (recBytes bp ob bpost fn r n) (bp.length + ob.length + 12 - 12) = fn := by
  have h : rd32 (bp ++ ob ++ le32 fn ++ (le32 r ++ le32 n ++ bpost)) (bp ++ ob).length = fn :=
    rd32_at hfn
  have hl : (bp ++ ob).length = bp.length + ob.length + 12 - 12 := by
    simp only [List.length_append]
    omega
  rw [hl] at h
  simpa only [recBytes, List.append_assoc] using h

/-- The record in its bytes reads back. -/
theorem readRec_bytes (bp bpost : List UInt8) {q : Rec V} {ob : List UInt8}
    (ho : layout C (q.ops.map .sv) = some ob) (hfn : q.fn < 2 ^ 32) (hr : q.r < 2 ^ 32)
    (hn : q.ops.length < 2 ^ 32) :
    readRec C (recBytes bp ob bpost q.fn q.r q.ops.length) (bp.length + ob.length + 12) =
      some (q, bp.length) := by
  have hL : ob.length = C.sw * q.ops.length := layout_sv C ho
  have rv : rdVals C (recBytes bp ob bpost q.fn q.r q.ops.length)
      (bp.length + ob.length + 12 - 12 - C.sw * q.ops.length) q.ops.length = some q.ops := by
    have h := rdVals_at C bp ((le32 q.fn ++ le32 q.r ++ le32 q.ops.length) ++ bpost) ho
    rw [show bp.length + ob.length + 12 - 12 - C.sw * q.ops.length = bp.length by omega]
    simpa only [recBytes, List.append_assoc] using h
  have hle : 12 + C.sw * q.ops.length ≤ bp.length + ob.length + 12 := by omega
  have hst : bp.length + ob.length + 12 - 12 - C.sw * q.ops.length = bp.length := by omega
  unfold readRec
  rw [rd_count _ _ _ _ _ hn]
  simp only [hle, ↓reduceIte]
  rw [rv, rd_resume _ _ _ _ _ hr, rd_fn _ _ _ _ _ hfn, hst]
  rfl

/-- **A record reads back from the byte layout.** -/
theorem readRec_layout {pre post : List (Cell V)} {q : Rec V} {bs : List UInt8}
    (h : layout C (pre ++ enc q ++ post) = some bs) :
    readRec C bs (addrOf C (pre ++ enc q)) = some (q, addrOf C pre) := by
  obtain ⟨b1, bpost, h1, -, hbs⟩ := layout_append C h
  obtain ⟨bp, bq, hp, hq, hb1⟩ := layout_append C h1
  obtain ⟨ob, ho, hfn, hr, hn, hbq⟩ := layout_enc C hq
  have hA : addrOf C pre = bp.length := (layout_len C hp).symm
  have he : addrOf C (pre ++ enc q) = bp.length + ob.length + 12 := by
    rw [← layout_len C h1, hb1, hbq]
    simp only [List.length_append, le32_len]
    omega
  have hbs' : bs = recBytes bp ob bpost q.fn q.r q.ops.length := by rw [hbs, hb1, hbq]
  rw [he, hA, hbs']
  exact readRec_bytes C bp bpost ho hfn hr hn

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes
