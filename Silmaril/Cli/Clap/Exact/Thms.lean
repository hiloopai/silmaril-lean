module

public import Silmaril.Cli.Clap.Exact.Defs

/-!
# clap's texts: channels and the shape of an error

* **`Tool.text_channel`**: for every tool and every presentation (`Tool.present`, e.g. clap's
  exact texts), the front end prints help and the version on **stdout** and a missing subcommand
  and usage errors on **stderr**, and nothing when the program runs (`Outcome.channel`);
  `Tool.text_help`, `Tool.text_error`, … one outcome each.
* `Tool.text_present`: with a presentation, the text of an outcome that does not run is the
  presentation's.
* **`Exact.errorText_prefix`**: clap's text of a usage error starts with `error: `.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Clap

open Silmaril.Cli

/-- The channel the front end prints an outcome on (`none`: the program runs). -/
def Outcome.channel : Outcome → Option Channel
  | .run _ _ | .undecided _ _ _ => none
  | .help _ | .version => some .stdout
  | .needCommand _ | .error _ => some .stderr

/-- **Help and the version on stdout, a missing subcommand and errors on stderr**, whatever the
presentation. -/
theorem Tool.text_channel (t : Tool) (argv : List String) (o : Outcome) :
    (t.text argv o).map Prod.fst = o.channel := by
  cases o <;> rfl

theorem Tool.text_help (t : Tool) (argv path : List String) :
    ∃ s, t.text argv (.help path) = some (.stdout, s) := ⟨_, rfl⟩

theorem Tool.text_version (t : Tool) (argv : List String) :
    ∃ s, t.text argv .version = some (.stdout, s) := ⟨_, rfl⟩

theorem Tool.text_needCommand (t : Tool) (argv path : List String) :
    ∃ s, t.text argv (.needCommand path) = some (.stderr, s) := ⟨_, rfl⟩

theorem Tool.text_error (t : Tool) (argv : List String) (msg : String) :
    ∃ s, t.text argv (.error msg) = some (.stderr, s) := ⟨_, rfl⟩

/-- Nothing is printed by the front end when the program runs. -/
theorem Tool.text_runs (t : Tool) (argv : List String) (o : Outcome) (h : o.runs = true) :
    t.text argv o = none := by
  cases o <;> first | rfl | cases h

/-- With a presentation `f`, the text of an outcome that does not run is `f`'s. -/
theorem Tool.text_present (t : Tool) (f : List String → Outcome → String) (argv : List String)
    (o : Outcome) (h : o.runs = false) :
    (({ t with present := some f } : Tool).text argv o).map Prod.snd = some (f argv o) := by
  cases o <;> first | rfl | cases h

/-- Dropping the trailing newlines of `p ++ q` keeps `p` when `p` ends in another character. -/
theorem chomp_keeps (p0 q : List Char) (c : Char) (hc : (c == '\n') = false) :
    ∃ q', (((p0 ++ [c]) ++ q).reverse.dropWhile (· == '\n')).reverse = p0 ++ [c] ++ q' := by
  have hp : ((p0 ++ [c]).reverse.dropWhile (· == '\n')) = (p0 ++ [c]).reverse := by
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.dropWhile_cons_of_neg (by simpa using hc)]
  rw [List.reverse_append, List.dropWhile_append]
  split
  · exact ⟨[], by rw [hp, List.reverse_reverse, List.append_nil]⟩
  · exact ⟨(q.reverse.dropWhile (· == '\n')).reverse, by
      rw [List.reverse_append, List.reverse_reverse]⟩

/-- `chompS` keeps a leading `error: `. -/
theorem chompS_error (r : String) :
    "error: ".toList <+: (Exact.chompS ("error: " ++ r)).toList := by
  obtain ⟨q', hq⟩ := chomp_keeps "error:".toList r.toList ' ' rfl
  have e : ("error: " ++ r).toList = ("error:".toList ++ [' ']) ++ r.toList := by
    rw [String.toList_append]; rfl
  have e2 : "error: ".toList = "error:".toList ++ [' '] := rfl
  refine ⟨q', ?_⟩
  simp only [Exact.chompS, String.toList_ofList, e, hq, e2]

/-- **clap's text of a usage error starts with `error: `**. -/
theorem Exact.errorText_prefix (msg : String) (tl : Exact.Tail) :
    "error: ".toList <+: (Exact.errorText msg tl).toList := by
  unfold Exact.errorText
  simp only [String.append_assoc]
  exact chompS_error _

end Silmaril.Cli.Clap
