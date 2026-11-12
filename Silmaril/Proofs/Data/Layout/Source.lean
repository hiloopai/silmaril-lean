module

public import Silmaril.Data.Layout.Source.Defs

/-!
# Proofs: the record-source parser is sound for its grammar

Each parser function is sound for the grammar relation of the same name, by induction on the
token list or on the fuel; `parse_sound` combines them with the lexer and `checkScope`.
-/

@[expose] public section

namespace Silmaril.Proofs.Data.Layout.Source

open Silmaril.Data.Layout Silmaril.Data.Layout.Source

theorem stripWords_sound : ∀ {ws : List String} {ts r : List Token},
    stripWords ws ts = some r → ts = ws.map .ident ++ r
  | [], ts, r, h => by simp only [stripWords, Option.some.injEq] at h; simp [h]
  | w :: ws, .ident v :: ts, r, h => by
    simp only [stripWords] at h
    split at h
    · subst w; simp [stripWords_sound h]
    · cases h
  | _ :: _, [], _, h => by simp [stripWords] at h
  | _ :: _, .num _ :: _, _, h => by simp [stripWords] at h
  | _ :: _, .punct _ :: _, _, h => by simp [stripWords] at h

theorem matchScalar_sound : ∀ {tbl : List (List String × CTy)} {ts : List Token} {t : CTy}
    {r : List Token}, matchScalar tbl ts = some (t, r) →
    ∃ ws, (ws, t) ∈ tbl ∧ ts = ws.map .ident ++ r
  | [], _, _, _, h => by simp [matchScalar] at h
  | (ws, t') :: rest, ts, t, r, h => by
    simp only [matchScalar] at h
    split at h
    · rename_i r' hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ws, List.mem_cons_self .., stripWords_sound hr⟩
    · obtain ⟨ws', hm, he⟩ := matchScalar_sound h
      exact ⟨ws', List.mem_cons_of_mem _ hm, he⟩

theorem spec_of_matchScalar {ts : List Token} {t : CTy} {r : List Token}
    (h : matchScalar scalarSpellings ts = some (t, r)) : Spec ts t r := by
  obtain ⟨ws, hm, rfl⟩ := matchScalar_sound h
  exact .scalar hm

theorem parseSpec_sound {ts : List Token} {t : CTy} {r : List Token}
    (h : parseSpec ts = .ok (t, r)) : Spec ts t r := by
  fun_cases parseSpec ts
  all_goals simp only [parseSpec, *, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
    ite_true, ite_false, Bool.false_eq_true] at h
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h; exact .record (by assumption) (by assumption))
    | (exact spec_of_matchScalar (by simp_all))

theorem parseSuffix_sound {t : CTy} {ts : List Token} {t' : CTy} {r : List Token}
    (h : parseSuffix t ts = .ok (t', r)) : Suffix t ts t' r := by
  fun_induction parseSuffix t ts generalizing t' r
  all_goals try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact .array (by assumption) (by apply_assumption; assumption)
  · obtain ⟨rfl, rfl⟩ := h; exact .done

theorem parseDeclarator_sound {t : CTy} {ts : List Token} {f : Field} {r : List Token}
    (h : parseDeclarator t ts = .ok (f, r)) : Declarator t ts f r := by
  fun_induction parseDeclarator t ts generalizing f r
  all_goals try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · exact .ptr (by apply_assumption; assumption)
  · obtain ⟨rfl, rfl⟩ := h; exact .name (by assumption) (parseSuffix_sound (by assumption))

theorem parseDeclList_sound {t : CTy} {fuel : Nat} {ts : List Token} {fs : List Field}
    {r : List Token} (h : parseDeclList t fuel ts = .ok (fs, r)) : DeclList t ts fs r := by
  fun_induction parseDeclList t fuel ts generalizing fs r
  all_goals try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact .last (parseDeclarator_sound (by assumption))
  · obtain ⟨rfl, rfl⟩ := h
    exact .more (parseDeclarator_sound (by assumption)) (by apply_assumption; assumption)

theorem parseMembers_sound {fuel : Nat} {ts : List Token} {fs : List Field} {r : List Token}
    (h : parseMembers fuel ts = .ok (fs, r)) : Members ts fs r := by
  fun_induction parseMembers fuel ts generalizing fs r
  all_goals try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact .close
  · obtain ⟨rfl, rfl⟩ := h
    exact .decl (parseSpec_sound (by assumption)) (parseDeclList_sound (by assumption))
      (by apply_assumption; assumption)

theorem parseRecord_sound {fuel : Nat} {ts : List Token} {d : Decl} {r : List Token}
    (h : parseRecord fuel ts = .ok (d, r)) : RecordDef ts d r := by
  fun_cases parseRecord fuel ts
  all_goals simp only [parseRecord, *, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
    ite_true, ite_false, Bool.false_eq_true] at h
  obtain ⟨rfl, rfl⟩ := h
  exact .mk (by assumption) (by simp_all) (parseMembers_sound (by assumption)) (by simp)

theorem parseUnit_sound {fuel : Nat} {ts : List Token} {env : Env}
    (h : parseUnit fuel ts = .ok env) : TransUnit ts env := by
  fun_induction parseUnit fuel ts generalizing env
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  · subst h; exact .nil
  · subst h; exact .cons (parseRecord_sound (by assumption)) (by apply_assumption; assumption)

theorem parse_sound {src : String} {env : Env} (h : parse src = .ok env) : Parses src env := by
  fun_cases parse src
  all_goals simp only [parse, *, Except.ok.injEq, reduceCtorEq] at h
  subst h
  exact ⟨_, by assumption, parseUnit_sound (by assumption), by assumption⟩

end Silmaril.Proofs.Data.Layout.Source
