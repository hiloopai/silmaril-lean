module

public import Silmaril.Games.Play.Defs

/-!
# Plays: basic facts

The basic facts about plays (determinism of the legality automaton, paths
along concatenation, prefix closure of legal plays, alternation, and the
unfolding of copycat plays) are stated in `Silmaril.Games.Play.Defs`, with the
definitions, because the proof fields of `Silmaril.Games.Strategy.Defs` need
them and a definitions module may not import a theorem header. This header
re-exports them for the modules that import it.
-/
