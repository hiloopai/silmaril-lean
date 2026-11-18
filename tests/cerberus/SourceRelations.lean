module
public meta import Silmaril.Project.CompilesTo.Probe.Defs
open Silmaril.Project.CompilesTo.Probe in
#guard ((docText "int less(int x, int y) { return x < y; }").splitOn "(OpLt)").length > 1
open Silmaril.Project.CompilesTo.Probe in
#guard ((docText "int less_equal(int x, int y) { return x <= y; }").splitOn "(OpLe)").length > 1
open Silmaril.Project.CompilesTo.Probe in
#guard ((docText "int greater_equal(int x, int y) { return x >= y; }").splitOn "(OpGe)").length > 1
