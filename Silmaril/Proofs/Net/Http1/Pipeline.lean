module

public import Silmaril.Net.Http1.Pipeline.Defs
public import Silmaril.Net.Http1.Profile.Thms
public import Silmaril.Net.Http1.Framing.Thms

/-! Proofs for `Silmaril.Net.Http1.Pipeline.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Pipeline

open Silmaril.Net.Http1
open Silmaril.Parse.ByteParse

theorem encRequest_length_pos (h : RequestHead) (b : Body) : 0 < (encRequest h b).length := by
  simp [encRequest, encRequestHead, encRequestLine]

theorem serve_pipeline (cfg : ServerConfig) (H : Handler) :
    ∀ (xs : List (RequestHead × Body)) (pre : Bytes) (n : Nat),
      (∀ x ∈ xs, x.1.Valid ∧ x.2.Fits (cfg.profile.frame x.1.line.version x.1.fields)) →
      (∀ x ∈ xs, KeptOpen cfg H x.1 x.2) → xs.length < n →
      (serve cfg H n ⟨(pre ++ (xs.map fun x => encRequest x.1 x.2).flatten).toArray⟩
          pre.length).1.map (fun e => (e.request, e.body)) = xs ∧
        (serve cfg H n ⟨(pre ++ (xs.map fun x => encRequest x.1 x.2).flatten).toArray⟩
          pre.length).2 = .eof := by
  intro xs
  induction xs with
  | nil =>
    intro pre n _ _ hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hs : ¬ (pre.length < (⟨pre.toArray⟩ : ByteArray).size) := by
      rw [size_ofList]; omega
    simp only [List.map_nil, List.flatten_nil, List.append_nil]
    rw [serve]
    simp [show (⟨pre.toArray⟩ : ByteArray).size ≤ pre.length by rw [size_ofList]]
  | cons x xs ih =>
    intro pre n hv hp hn
    obtain ⟨h, b⟩ := x
    simp only [List.length_cons] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨c, hc, hk⟩ := hp (h, b) (by simp)
    have e : pre ++ (((h, b) :: xs).map fun x => encRequest x.1 x.2).flatten =
        pre ++ encRequest h b ++ (xs.map fun x => encRequest x.1 x.2).flatten := by simp
    have hparse := parseRequestWith_encode cfg.profile (hv (h, b) (by simp)).1
      (hv (h, b) (by simp)).2 pre (xs.map fun x => encRequest x.1 x.2).flatten
    have hsize : ¬ (⟨(pre ++ encRequest h b ++
        (xs.map fun x => encRequest x.1 x.2).flatten).toArray⟩ : ByteArray).size ≤ pre.length := by
      rw [size_ofList]; have := encRequest_length_pos h b; simp only [List.length_append]; omega
    have ih' := ih (pre ++ encRequest h b) m (fun y hy => hv y (by simp [hy]))
      (fun y hy => hp y (by simp [hy])) (by omega)
    rw [List.length_append] at ih'
    rw [e, serve]
    simp only [hsize, ↓reduceIte]
    rw [hparse]
    simp only [hc, hk, ite_true, List.map_cons]
    exact ⟨by rw [ih'.1], ih'.2⟩

theorem serve_closes (cfg : ServerConfig) (H : Handler) {h : RequestHead} {b : Body}
    (hv : h.Valid) (hb : b.Fits (cfg.profile.frame h.line.version h.fields)) {c : Context}
    (hc : checkRequest cfg h = .ok c)
    (hk : (c.persistent && keepOpen cfg.keepAlive h (H h b c).1) = false)
    (pre rest : Bytes) (n : Nat) :
    serve cfg H (n + 1) ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
      ([⟨h, b, c, (H h b c).1, (H h b c).2⟩], .closed) := by
  have hparse := parseRequestWith_encode cfg.profile hv hb pre rest
  have hsize : ¬ (⟨(pre ++ encRequest h b ++ rest).toArray⟩ : ByteArray).size ≤ pre.length := by
    rw [size_ofList]; have := encRequest_length_pos h b; simp only [List.length_append]; omega
  rw [serve]
  simp only [hsize, ↓reduceIte]
  rw [hparse]
  simp only [hc, hk, Bool.false_eq_true, ite_false]

theorem encResponses_cons (i : ResponseHead) (is : List ResponseHead) (f : ResponseHead)
    (fb : Body) : encResponses (i :: is) f fb = encResponse i .none ++ encResponses is f fb := by
  simp [encResponses, encResponse, encBody]

theorem readResponse_encode (method : Bytes) :
    ∀ (is : List ResponseHead) {f : ResponseHead} {fb : Body} (pre rest : Bytes) (n : Nat),
      ResponsesFit method is f fb → is.length < n →
      readResponse method ⟨(pre ++ encResponses is f fb ++ rest).toArray⟩ n pre.length =
        .ok (is, f, fb) (pre.length + (encResponses is f fb).length) := by
  intro is
  induction is with
  | nil =>
    intro f fb pre rest n hr hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨-, hf, hfi, hfb⟩ := hr
    have hp := parseResponseAt_encode hf hfb pre rest
    simp only [encResponses, List.map_nil, List.flatten_nil, List.nil_append] at hp ⊢
    rw [readResponse, hp]
    simp only [hfi, Bool.false_eq_true, ite_false]
  | cons i is ih =>
    intro f fb pre rest n hr hn
    simp only [List.length_cons] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨his, hf, hfi, hfb⟩ := hr
    obtain ⟨hiv, hii⟩ := his i (by simp)
    have hcode : i.line.code / 100 = 1 := by
      simp only [isInterim, Bool.and_eq_true, beq_iff_eq] at hii; exact hii.1
    have hfit : Body.Fits (responseBodyLength method i.line.code i.fields) Body.none := by
      rw [responseBodyLength_noContent _ (Or.inl hcode)]; trivial
    have hp := parseResponseAt_encode hiv hfit pre (encResponses is f fb ++ rest)
    have ih' := ih (pre ++ encResponse i .none) rest m
      ⟨fun j hj => his j (by simp [hj]), hf, hfi, hfb⟩ (by omega)
    rw [List.length_append] at ih'
    have e : pre ++ encResponses (i :: is) f fb ++ rest =
        pre ++ encResponse i .none ++ (encResponses is f fb ++ rest) := by
      simp [encResponses_cons]
    have e' : pre ++ encResponse i .none ++ (encResponses is f fb ++ rest) =
        pre ++ encResponse i .none ++ encResponses is f fb ++ rest := by simp
    rw [e, readResponse, hp]
    simp only [hii, ite_true]
    rw [e'] 
    rw [ih']
    simp [encResponses_cons, Nat.add_assoc]

theorem readResponses_encode (n : Nat) :
    ∀ (rs : List (Bytes × List ResponseHead × ResponseHead × Body)) (pre rest : Bytes),
      (∀ r ∈ rs, ResponsesFit r.1 r.2.1 r.2.2.1 r.2.2.2 ∧ r.2.1.length ≤ n) →
      readResponses
          ⟨(pre ++ (rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten ++ rest).toArray⟩ n
          (rs.map (·.1)) pre.length =
        .ok (rs.map (·.2))
          (pre.length + (rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten.length) := by
  intro rs
  induction rs with
  | nil => intro pre rest _; simp [readResponses]
  | cons r rs ih =>
    intro pre rest hr
    obtain ⟨m, is, f, fb⟩ := r
    obtain ⟨hfit, hlen⟩ := hr (m, is, f, fb) (by simp)
    simp only at hfit hlen
    have h₁ := readResponse_encode m is pre
      ((rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten ++ rest) (n + 1) hfit (by omega)
    have ih' := ih (pre ++ encResponses is f fb) rest (fun y hy => hr y (by simp [hy]))
    rw [List.length_append] at ih'
    have e : pre ++ (((m, is, f, fb) :: rs).map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten
        ++ rest = pre ++ encResponses is f fb ++
          ((rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten ++ rest) := by simp
    have e' : pre ++ encResponses is f fb ++
          ((rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten ++ rest) =
        pre ++ encResponses is f fb ++ (rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten
          ++ rest := by simp
    rw [e]
    simp only [List.map_cons]
    rw [readResponses, h₁]
    simp only
    rw [e', ih']
    simp [Nat.add_assoc]

end Silmaril.Net.Http1.Proofs.Pipeline
