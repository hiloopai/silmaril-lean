// Run from the pinned starlark-go checkout. The fixtures arrive from Lean.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"slices"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

type fixture struct {
	Name          string
	Source        string
	Accepts       bool
	Module        *moduleControl
	Loader        *loaderControl
	BranchTests   [][4]int32
	ListDisplays  [][4]int32
	TupleDisplays [][4]int32
	HeaderFormals [][4]int32
}

type moduleControl struct {
	Phase  string
	Want   string
	Events string
}

type loaderControl struct {
	Phase    string
	Want     string
	Sources  map[string]string
	Requests []string
	Marker   string
	Wrapper  string
}

func isInteger(value starlark.Value, want string) bool {
	integer, ok := value.(starlark.Int)
	return ok && integer.String() == want
}

func checkNodeSpans(file *syntax.File, want [][4]int32, locate func(syntax.Node) []syntax.Node) error {
	var got [][4]int32
	syntax.Walk(file, func(node syntax.Node) bool {
		for _, located := range locate(node) {
			start, end := located.Span()
			// Go's empty tuple reports the closing token, not the half-open end.
			if tuple, ok := located.(*syntax.TupleExpr); ok && tuple.Lparen.IsValid() {
				end.Col++
			}
			got = append(got, [4]int32{start.Line, start.Col, end.Line, end.Col})
		}
		return true
	})
	if !slices.Equal(got, want) {
		return fmt.Errorf("want spans %v, got %v", want, got)
	}
	return nil
}

func branchTestNodes(node syntax.Node) []syntax.Node {
	if branch, ok := node.(*syntax.IfStmt); ok {
		return []syntax.Node{branch.Cond}
	}
	return nil
}

func formalNodes(node syntax.Node) []syntax.Node {
	if function, ok := node.(*syntax.DefStmt); ok {
		nodes := make([]syntax.Node, 0, len(function.Params))
		for _, parameter := range function.Params {
			nodes = append(nodes, parameter)
		}
		return nodes
	}
	return nil
}

func listDisplayNodes(node syntax.Node) []syntax.Node {
	if display, ok := node.(*syntax.ListExpr); ok {
		return displayNodes(display, display.List)
	}
	return nil
}

func tupleDisplayNodes(node syntax.Node) []syntax.Node {
	// A nonempty parenthesized tuple is a ParenExpr over a bare TupleExpr.
	switch display := node.(type) {
	case *syntax.ParenExpr:
		if tuple, ok := display.X.(*syntax.TupleExpr); ok && !tuple.Lparen.IsValid() {
			return displayNodes(display, tuple.List)
		}
	case *syntax.TupleExpr:
		if display.Lparen.IsValid() {
			return displayNodes(display, display.List)
		}
	}
	return nil
}

func displayNodes(display syntax.Node, elements []syntax.Expr) []syntax.Node {
	nodes := make([]syntax.Node, 1, len(elements)+1)
	nodes[0] = display
	for _, element := range elements {
		nodes = append(nodes, element)
	}
	return nodes
}

func checkModule(file *syntax.File, control moduleControl) error {
	program, err := starlark.FileProgram(file, func(string) bool { return false })
	if control.Phase == "validation" {
		if err != nil && strings.Contains(err.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want validation error containing %q, got %v", control.Want, err)
	}
	if err != nil {
		return fmt.Errorf("unexpected validation error: %w", err)
	}

	globals, err := program.Init(new(starlark.Thread), nil)
	if control.Events != "" {
		events, ok := globals["events"].(*starlark.List)
		if !ok || events.String() != control.Events {
			return fmt.Errorf("want events %s, got %v", control.Events, globals["events"])
		}
	}
	if control.Phase == "runtime" {
		if err != nil && strings.Contains(err.Error(), control.Want) && globals["out"] == nil {
			return nil
		}
		return fmt.Errorf("want runtime error containing %q with out unbound, got error %v and out %v",
			control.Want, err, globals["out"])
	}
	if control.Phase != "publication" {
		return fmt.Errorf("unknown module phase %q", control.Phase)
	}
	if err != nil {
		return fmt.Errorf("unexpected runtime error: %w", err)
	}
	globals.Freeze()
	if !isInteger(globals["out"], control.Want) {
		return fmt.Errorf("want out to be integer %s, got %v", control.Want, globals["out"])
	}
	return nil
}

func checkLoader(file *syntax.File, parseError error, control loaderControl) error {
	if control.Phase == "parse" {
		if parseError != nil && strings.Contains(parseError.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want parse error containing %q, got %v", control.Want, parseError)
	}
	if parseError != nil {
		return fmt.Errorf("unexpected parse error: %w", parseError)
	}

	program, err := starlark.FileProgram(file, func(string) bool { return false })
	if control.Phase == "validation" {
		if err != nil && strings.Contains(err.Error(), control.Want) {
			return nil
		}
		return fmt.Errorf("want validation error containing %q, got %v", control.Want, err)
	}
	if err != nil {
		return fmt.Errorf("unexpected validation error: %w", err)
	}

	var requested []string
	var load func(*starlark.Thread, string) (starlark.StringDict, error)
	load = func(_ *starlark.Thread, label string) (starlark.StringDict, error) {
		requested = append(requested, label)
		source, ok := control.Sources[label]
		if !ok {
			return nil, fmt.Errorf("unexpected label %q", label)
		}
		return starlark.ExecFileOptions(&syntax.FileOptions{}, &starlark.Thread{Load: load},
			label+".star", []byte(source), nil)
	}
	globals, err := program.Init(&starlark.Thread{Load: load}, nil)
	if !slices.Equal(requested, control.Requests) {
		return fmt.Errorf("want load order %v, got %v", control.Requests, requested)
	}
	if control.Phase == "runtime" {
		marker := globals["marker"]
		markerMatches := marker == nil && control.Marker == "" || isInteger(marker, control.Marker)
		if err != nil && strings.Contains(err.Error(), control.Want) && globals["out"] == nil && markerMatches {
			return nil
		}
		return fmt.Errorf("want error containing %q with out unbound and marker %q, got %v and %v",
			control.Want, control.Marker, err, globals)
	}
	if control.Phase != "publication" {
		return fmt.Errorf("unknown loader phase %q", control.Phase)
	}
	if err != nil {
		return fmt.Errorf("unexpected runtime error: %w", err)
	}
	globals.Freeze()
	wantCount := 1
	if control.Wrapper != "" {
		wantCount++
		if _, ok := globals[control.Wrapper].(*starlark.Function); !ok {
			return fmt.Errorf("want wrapper function %s, got %v", control.Wrapper, globals)
		}
	}
	if len(globals) != wantCount || !isInteger(globals["out"], control.Want) {
		return fmt.Errorf("want out = %s among %d globals, got %v", control.Want, wantCount, globals)
	}
	return nil
}

func main() {
	var fixtures []fixture
	if err := json.NewDecoder(os.Stdin).Decode(&fixtures); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if len(fixtures) == 0 {
		fmt.Fprintln(os.Stderr, "no Starlark frontend fixtures")
		os.Exit(1)
	}
	failed := false
	modules := 0
	loaders := 0
	for _, f := range fixtures {
		file, err := (&syntax.FileOptions{}).Parse(f.Name+".star", []byte(f.Source), 0)
		if (err == nil) != f.Accepts {
			fmt.Fprintf(os.Stderr, "%s: want Go acceptance %t, got %v\n", f.Name, f.Accepts, err)
			failed = true
			continue
		}
		if f.Module != nil {
			modules++
			if err != nil {
				fmt.Fprintf(os.Stderr, "%s: module control needs a Go syntax tree: %v\n", f.Name, err)
				failed = true
				continue
			}
			if err := checkModule(file, *f.Module); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
		if f.Loader != nil {
			loaders++
			if err := checkLoader(file, err, *f.Loader); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
		if f.BranchTests != nil {
			if err := checkNodeSpans(file, f.BranchTests, branchTestNodes); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
		if f.ListDisplays != nil {
			if err := checkNodeSpans(file, f.ListDisplays, listDisplayNodes); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
		if f.TupleDisplays != nil {
			if err := checkNodeSpans(file, f.TupleDisplays, tupleDisplayNodes); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
		if f.HeaderFormals != nil {
			if err := checkNodeSpans(file, f.HeaderFormals, formalNodes); err != nil {
				fmt.Fprintf(os.Stderr, "%s: %v\n", f.Name, err)
				failed = true
			}
		}
	}
	spreads, err := checkGoSpreadControls()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		failed = true
	}
	if failed {
		os.Exit(1)
	}
	fmt.Printf("Pinned Go matched %d parse expectations, %d module observations, %d loader controls, and %d Go-only controls\n",
		len(fixtures), modules, loaders, spreads)
}
