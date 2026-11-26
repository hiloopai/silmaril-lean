// Run from the pinned Starlark-Go checkout with go run and this file's path.
package main

import (
	"fmt"
	"strings"

	"go.starlark.net/starlark"
	"go.starlark.net/syntax"
)

const producer = `data = [31]
def factory(value):
    def child(first, *rest, key=value, **extras):
        marked = [44]
        print(marked[0])
        probe = key[0]
        seen = value[0]
        print(probe, seen)
        return late
    copy = child
    value = [52]
    return copy
escaped = factory(data)
late = [83]
alias = escaped
result = alias(another=[61], *[data, data], **{"extra": late})
after = [99]
`

func require(ok bool, detail any) {
	if !ok {
		panic(detail)
	}
}

func checkConsumer(warm bool, consumer string) (partial, cached starlark.StringDict, events []string, err error) {
	opts := &syntax.FileOptions{}
	thread := &starlark.Thread{}
	thread.Print = func(_ *starlark.Thread, msg string) {
		events = append(events, msg)
	}
	var initializations, hits int
	thread.Load = func(_ *starlark.Thread, module string) (starlark.StringDict, error) {
		require(module == "prodé.star", module)
		if cached != nil {
			hits++
			return cached, nil
		}
		initializations++
		globals, err := starlark.ExecFileOptions(opts, thread, module, producer, nil)
		if err == nil {
			cached = globals
		}
		return globals, err
	}
	if warm {
		_, err := thread.Load(thread, "prodé.star")
		require(err == nil, err)
	}
	_, program, err := starlark.SourceProgramOptions(opts, "consumer.star", consumer, func(string) bool { return false })
	require(err == nil, err)
	partial, err = program.Init(thread, nil)
	require(initializations == 1 && (hits == 1) == warm, []int{initializations, hits})
	return partial, cached, events, err
}

func check(warm bool, name, mapping string) {
	consumer := fmt.Sprintf(`load("prodé.star", loaded=%q)
starter = loaded
made = starter([41])
held = made
marker = [88]
result = held(another=[71], *[17, 18], **%s)
late = [199]
`, name, mapping)
	partial, cached, events, err := checkConsumer(warm, consumer)
	if name == "absent" {
		require(err != nil && strings.Contains(err.Error(), "absent") && strings.Join(events, ",") == "44,31 52", err)
		require(partial["starter"] == nil && partial["made"] == nil &&
			partial["result"] == nil && partial["late"] == nil, partial)
	} else if mapping == `{"key": 8}` {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(strings.Join(events, ",") == "44,31 52,44" && partial["result"] == nil && partial["late"] == nil, partial)
		require(partial["starter"] == cached["factory"] && partial["made"] != nil && partial["made"] == partial["held"] &&
			partial["marker"].String() == "[88]", partial)
	} else {
		require(err == nil, err)
		partial.Freeze()
		require(partial["result"] == cached["late"] && partial["late"].String() == "[199]" &&
			partial["loaded"] == nil && strings.Join(events, ",") == "44,31 52,44,41 52", partial)
		require(partial["starter"] == cached["factory"] && partial["made"] == partial["held"] &&
			partial["made"] != cached["escaped"] && partial["marker"].String() == "[88]", partial)
		require(partial["late"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
	require(cached["data"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, cached)
	require(cached["late"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, cached)
}

func checkWrapper(warm bool, name, mapping string) {
	consumer := fmt.Sprintf(`load("prodé.star", loaded=%q)
def relay():
    return loaded(another=[71], *[17, 18], **%s)
result = relay()
`, name, mapping)
	partial, cached, events, err := checkConsumer(warm, consumer)
	switch {
	case name == "absent":
		require(err != nil && strings.Contains(err.Error(), "absent"), err)
		require(partial["relay"] == nil && partial["result"] == nil && strings.Join(events, ",") == "44,31 52", partial)
	case mapping == `{"key": 8}`:
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["relay"] != nil && partial["result"] == nil && strings.Join(events, ",") == "44,31 52,44", partial)
	default:
		require(err == nil, err)
		partial.Freeze()
		require(partial["relay"] != nil && partial["loaded"] == nil && partial["result"] == cached["late"] &&
			strings.Join(events, ",") == "44,31 52,44,31 52", partial)
		require(partial["result"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
}

func checkDeclarationSuite(warm, bad bool) {
	mapping := `{"key": [72]}`
	if bad {
		mapping = `{"key": 8}`
	}
	consumer := fmt.Sprintf(`load("prodé.star", loaded="escaped")
def first():
    return loaded(another=[71], *[17, 18], **{"extra": 9})
copied = first
marker = [88]
def second():
    return loaded(another=[71], *[17, 18], **%s)
firstOut = copied()
secondOut = second()
after = [199]
`, mapping)
	partial, cached, events, err := checkConsumer(warm, consumer)
	require(partial["first"] != nil && partial["copied"] == partial["first"] &&
		partial["second"] != nil && partial["second"] != partial["first"], partial)
	require(partial["firstOut"] == cached["late"] && partial["marker"].String() == "[88]", partial)
	if bad {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["secondOut"] == nil && partial["after"] == nil &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44", partial)
	} else {
		require(err == nil, err)
		partial.Freeze()
		require(partial["secondOut"] == cached["late"] && partial["after"].String() == "[199]" &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,72 52", partial)
		require(partial["firstOut"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
}

func checkReturnedClosure(warm bool) {
	consumer := `load("prodé.star", loaded="factory")
def make():
    return loaded([41])
held = make()
result = held(17)
`
	partial, cached, events, err := checkConsumer(warm, consumer)
	require(err == nil, err)
	require(partial["held"] != nil && partial["held"] != cached["escaped"] &&
		partial["result"] == cached["late"] && strings.Join(events, ",") == "44,31 52,44,41 52", partial)
}

func initChain(preload, middle, source string) (starlark.StringDict, map[string]starlark.StringDict, []string, error) {
	opts := &syntax.FileOptions{}
	thread := &starlark.Thread{}
	var events []string
	thread.Print = func(_ *starlark.Thread, message string) {
		events = append(events, message)
	}
	files := map[string]string{"prodé.star": producer, "middle.star": middle}
	cache := map[string]starlark.StringDict{}
	initializations := map[string]int{}
	hits := map[string]int{}
	thread.Load = func(_ *starlark.Thread, name string) (starlark.StringDict, error) {
		if value, found := cache[name]; found {
			hits[name]++
			return value, nil
		}
		source, exists := files[name]
		require(exists, name)
		initializations[name]++
		value, err := starlark.ExecFileOptions(opts, thread, name, source, nil)
		if err == nil {
			cache[name] = value
		}
		return value, err
	}
	if preload != "" {
		_, err := thread.Load(thread, preload)
		require(err == nil, err)
	}
	_, program, err := starlark.SourceProgramOptions(opts, "final.star", source, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(thread, nil)
	require(initializations["prodé.star"] == 1 && initializations["middle.star"] == 1, initializations)
	require((hits["prodé.star"] == 1) == (preload == "prodé.star") &&
		(hits["middle.star"] == 1) == (preload == "middle.star"), hits)
	return partial, cache, events, err
}

func checkChain(preload string, bad bool) {
	const middle = `load("prodé.star", loaded="escaped")
def relay():
    return loaded(17)
before = relay()
reexport = loaded
`
	mapping := `{"key": [72]}`
	if bad {
		mapping = `{"key": 8}`
	}
	source := fmt.Sprintf(`load("middle.star", transferred="reexport")
held = transferred
first = held(another=[71], *[17, 18])
marker = [88]
answer = held(another=[71], *[17, 18], **%s)
after = [199]
`, mapping)
	partial, cache, events, err := initChain(preload, middle, source)
	prod, mid := cache["prodé.star"], cache["middle.star"]
	require(mid["relay"] != nil && mid["reexport"] == prod["escaped"] &&
		partial["held"] == prod["escaped"] && mid["before"] == prod["late"] &&
		partial["first"] == prod["late"] && partial["marker"].String() == "[88]", partial)
	if bad {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["answer"] == nil && partial["after"] == nil &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,31 52,44", partial)
	} else {
		require(err == nil, err)
		require(partial["answer"] == prod["late"] && partial["after"].String() == "[199]" &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,31 52,44,72 52", partial)
		require(partial["answer"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
}

func checkWrapperChain(preload string, nested, bad bool) {
	override := ""
	if bad {
		override = ", **{\"key\": 8}"
	}
	middle := fmt.Sprintf(`load("prodé.star", loaded="escaped")
def relay():
    return loaded(17%s)
before = loaded(17)
reexport = loaded
`, override)
	callee := "held"
	if nested {
		callee = "outer"
	}
	source := fmt.Sprintf(`load("middle.star", wrapped="relay")
held = wrapped
marker = [88]
def outer():
    return wrapped()
answer = %s()
after = [199]
`, callee)
	partial, cache, events, err := initChain(preload, middle, source)
	prod, mid := cache["prodé.star"], cache["middle.star"]
	require(mid["reexport"] == prod["escaped"] && mid["before"] == prod["late"] &&
		partial["held"] == mid["relay"] && partial["outer"] != nil && partial["marker"].String() == "[88]", partial)
	if bad {
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(partial["answer"] == nil && partial["after"] == nil &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44", partial)
	} else {
		require(err == nil, err)
		require(partial["answer"] == prod["late"] && partial["after"].String() == "[199]" &&
			strings.Join(events, ",") == "44,31 52,44,31 52,44,31 52", partial)
		require(partial["answer"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
	}
}

func checkDiamond(preload bool, failure string) {
	const left = `load("prodé.star", loaded="escaped")
def relay():
    return loaded(17)
before = relay()
reexport = loaded
`
	right := left
	if failure == "dependency" {
		right = `load("prodé.star", loaded="escaped")
before = loaded(17, key=8)
`
	}
	first, last := "reexport", "relay"
	if failure == "first" || failure == "both" {
		first = "absentFirst"
	}
	if failure == "last" || failure == "both" {
		last = "absentLast"
	}
	skip := ""
	if failure != "" {
		skip = "load(\"skip.star\", skipped=\"relay\")\n"
	}
	source := fmt.Sprintf(`load("left.star", left="relay")
load("right.star", rightExtra=%q, right=%q)
%sdef wrapRight():
    return right()
leftResult = left()
rightResult = wrapRight()
rightCopy = rightExtra
after = [199]
`, first, last, skip)

	sources := map[string]string{"prodé.star": producer, "left.star": left, "right.star": right, "skip.star": left}
	cache := make(map[string]starlark.StringDict)
	var initialized, cacheHits, prints []string
	thread := &starlark.Thread{}
	thread.Print = func(_ *starlark.Thread, msg string) { prints = append(prints, msg) }
	opts := &syntax.FileOptions{}
	thread.Load = func(_ *starlark.Thread, path string) (starlark.StringDict, error) {
		if cached, ok := cache[path]; ok {
			cacheHits = append(cacheHits, path)
			return cached, nil
		}
		initialized = append(initialized, path)
		body, exists := sources[path]
		require(exists, path)
		result, err := starlark.ExecFileOptions(opts, thread, path, body, nil)
		if err == nil {
			cache[path] = result
		}
		return result, err
	}
	if preload {
		_, err := thread.Load(thread, "left.star")
		require(err == nil, err)
	}
	_, program, err := starlark.SourceProgramOptions(opts, "diamond.star", source, func(string) bool { return false })
	require(err == nil, err)
	partial, err := program.Init(thread, nil)
	require(strings.Join(initialized, ",") == "left.star,prodé.star,right.star", initialized)
	expectedHits := "prodé.star"
	if preload {
		expectedHits = "left.star,prodé.star"
	}
	require(strings.Join(cacheHits, ",") == expectedHits, cacheHits)
	prod, leftPub, rightPub := cache["prodé.star"], cache["left.star"], cache["right.star"]
	require(leftPub["reexport"] == prod["escaped"] && leftPub["before"] == prod["late"], leftPub)
	switch failure {
	case "":
		require(err == nil, err)
		require(leftPub["relay"] != rightPub["relay"] && rightPub["reexport"] == prod["escaped"], rightPub)
		require(partial["leftResult"] == prod["late"] && partial["rightResult"] == prod["late"] &&
			partial["left"] == nil && partial["right"] == nil && partial["rightExtra"] == nil &&
			partial["rightCopy"] == prod["escaped"] && partial["after"].String() == "[199]", partial)
		require(partial["rightResult"].(*starlark.List).SetIndex(0, starlark.MakeInt(2)) != nil, partial)
		require(strings.Join(prints, ",") == "44,31 52,44,31 52,44,31 52,44,31 52,44,31 52", prints)
	case "first", "last", "both":
		missing := "absentLast"
		if failure == "first" {
			missing = "absentFirst"
		}
		require(err != nil && strings.Contains(err.Error(), "load: name "+missing+" not found in module right.star"), err)
		require(rightPub != nil && rightPub["reexport"] == prod["escaped"] && len(partial) == 0, partial)
		require(strings.Join(prints, ",") == "44,31 52,44,31 52,44,31 52", prints)
	case "dependency":
		require(err != nil && strings.Contains(err.Error(), "unhandled index operation"), err)
		require(rightPub == nil && len(partial) == 0, partial)
		require(strings.Join(prints, ",") == "44,31 52,44,31 52,44", prints)
	}
}

const positionalProducer = `def spare():
    return 999
def pick(first, second):
    probe = [first]
    print(first, second)
    return probe[second]
`

type positionalWrapperRun struct {
	consumer, forwarder starlark.StringDict
	cache               map[string]starlark.StringDict
	savedDefaults       []starlark.Value
	events              []string
	err                 error
}

func initPositionalWrapper(preload, forwarding, source string) positionalWrapperRun {
	run := positionalWrapperRun{cache: make(map[string]starlark.StringDict)}
	var visits, hits []string
	opts := &syntax.FileOptions{}
	thread := &starlark.Thread{}
	thread.Print = func(_ *starlark.Thread, msg string) { run.events = append(run.events, msg) }
	thread.Load = func(_ *starlark.Thread, path string) (starlark.StringDict, error) {
		if cached, ok := run.cache[path]; ok {
			hits = append(hits, path)
			return cached, nil
		}
		visits = append(visits, path)
		body := positionalProducer
		if path == "forwarder.star" {
			body = forwarding
		} else {
			require(path == "positional.star", path)
		}
		_, program, err := starlark.SourceProgramOptions(opts, path, body, func(string) bool { return false })
		require(err == nil, err)
		values, err := program.Init(thread, nil)
		if path == "forwarder.star" {
			run.forwarder = values
		}
		if err == nil {
			values.Freeze()
			run.cache[path] = values
			if relay, ok := values["relay"].(*starlark.Function); ok {
				for i := 0; i < relay.NumParams(); i++ {
					run.savedDefaults = append(run.savedDefaults, relay.ParamDefault(i))
				}
			}
		}
		return values, err
	}
	if preload != "" {
		_, err := thread.Load(thread, preload)
		require(err == nil, err)
	}
	_, program, err := starlark.SourceProgramOptions(opts, "consumer.star", source, func(string) bool { return false })
	require(err == nil, err)
	run.consumer, run.err = program.Init(thread, nil)
	expectedVisits := "forwarder.star,positional.star"
	if preload == "positional.star" {
		expectedVisits = "positional.star,forwarder.star"
	}
	require(strings.Join(visits, ",") == expectedVisits && strings.Join(hits, ",") == preload, []any{visits, hits})
	require(thread.CallStackDepth() == 0, thread.CallStack())
	return run
}

func checkPositionalWrapper(preload bool, failure string) {
	const forwarding = `load("positional.star", ignored="spare", loaded="pick")
def relay(x, y):
    return loaded(y, x)
`
	call := "bound(0, 53)"
	switch failure {
	case "arity":
		call = "bound(0, 39, 55)"
	case "body":
		call = "bound(1, 39)"
	}
	source := fmt.Sprintf(`load("forwarder.star", bound="relay")
firstResult = bound(0, 27)
marker = [88]
out = %s
after = [199]
`, call)
	preloaded := ""
	if preload {
		preloaded = "forwarder.star"
	}
	run := initPositionalWrapper(preloaded, forwarding, source)
	partial, events, err := run.consumer, run.events, run.err
	require(run.cache["forwarder.star"]["relay"] != nil && partial["firstResult"] == starlark.MakeInt(27) &&
		partial["marker"].String() == "[88]" && partial["bound"] == nil, partial)
	switch failure {
	case "":
		require(err == nil, err)
		require(partial["out"] == starlark.MakeInt(53) && partial["after"].String() == "[199]" &&
			strings.Join(events, ",") == "27 0,53 0", partial)
	case "arity":
		require(err != nil && strings.Contains(err.Error(), "function relay accepts 2 positional arguments (3 given)"), err)
		require(partial["out"] == nil && partial["after"] == nil && strings.Join(events, ",") == "27 0", events)
	case "body":
		require(err != nil && strings.Contains(err.Error(), "index 1 out of range"), err)
		require(partial["out"] == nil && partial["after"] == nil && strings.Join(events, ",") == "27 0,39 1", events)
	}
}

func checkSavedWrapper(warm bool, failure string) {
	indices := []int{0, 0}
	if failure == "default" {
		indices = []int{1, 2}
	}
	forwarding := fmt.Sprintf(`load("positional.star", ignored="spare", loaded="pick")
seed = 27
before = [76]
def relay(x, y=[seed], z=[51][%d], t=[72][%d]):
    return loaded(y[0], x)
later = [199]
`, indices[0], indices[1])
	call := "bound(0, [53])"
	switch failure {
	case "missing":
		call = "bound()"
	case "surplus":
		call = "bound(0, [53], 1, 2, 3)"
	}
	source := fmt.Sprintf(`load("forwarder.star", bound="relay")
firstResult = bound(0)
marker = [88]
out = %s
again = bound(0)
after = [198]
`, call)
	preload := ""
	if warm {
		preload = "forwarder.star"
		if failure == "default" {
			preload = "positional.star"
		}
	}
	run := initPositionalWrapper(preload, forwarding, source)
	require(run.cache["positional.star"]["pick"] != nil && run.forwarder["seed"] == starlark.MakeInt(27) &&
		run.forwarder["before"].String() == "[76]", run.forwarder)
	if failure == "default" {
		require(run.err != nil && strings.Contains(run.err.Error(), "index 1 out of range"), run.err)
		require(run.cache["forwarder.star"] == nil && run.forwarder["relay"] == nil &&
			run.forwarder["later"] == nil && len(run.consumer) == 0 && len(run.events) == 0, run.forwarder)
		return
	}
	relay := run.cache["forwarder.star"]["relay"].(*starlark.Function)
	saved := relay.ParamDefault(1).(*starlark.List)
	require(saved == run.savedDefaults[1] && saved.String() == "[27]" &&
		relay.ParamDefault(2) == starlark.MakeInt(51) && relay.ParamDefault(3) == starlark.MakeInt(72), relay)
	require(saved.SetIndex(0, starlark.MakeInt(7)) != nil, saved)
	partial := run.consumer
	require(partial["firstResult"] == starlark.MakeInt(27) && partial["marker"].String() == "[88]" && partial["bound"] == nil, partial)
	if failure == "" {
		require(run.err == nil && partial["out"] == starlark.MakeInt(53) && partial["again"] == starlark.MakeInt(27) &&
			partial["after"].String() == "[198]" && strings.Join(run.events, ",") == "27 0,53 0,27 0", run.err)
		return
	}
	message := "missing 1 argument (x)"
	if failure == "surplus" {
		message = "accepts at most 4 positional arguments (5 given)"
	}
	require(run.err != nil && strings.Contains(run.err.Error(), message), run.err)
	require(partial["out"] == nil && partial["again"] == nil && partial["after"] == nil &&
		strings.Join(run.events, ",") == "27 0", partial)
}

func checkKeywordWrapper(warm bool, failure string) {
	const forwarding = `load("positional.star", ignored="spare", loaded="pick")
seed = 27
before = [76]
def relay(x, *, at, key=[seed]):
    return loaded(key[0], at)
later = [199]
`
	call := "bound(0, key=[53], at=0)"
	message := ""
	operandEvents := ""
	switch failure {
	case "missing":
		call = "bound(0, key=mark([63]))"
		message = "missing 1 argument (at)"
		operandEvents = ",63"
	case "surplus":
		call = "bound(0, mark([64]), at=mark([65])[0])"
		message = "accepts 1 positional argument (2 given)"
		operandEvents = ",64,65"
	case "unknown":
		call = "bound(0, extra=mark([64]), at=mark([65])[0])"
		message = `unexpected keyword argument "extra"`
		operandEvents = ",64,65"
	case "duplicate":
		call = "bound(0, at=mark([70])[0], x=mark([71]))"
		message = `multiple values for parameter "x"`
		operandEvents = ",70,71"
	case "operand":
		call = "bound(0, extra=mark([64]), at=mark([65])[1], key=mark([66]))"
		message = "index 1 out of range"
		operandEvents = ",64,65"
	}
	// mark makes reached operand order visible through Go's public API.
	source := fmt.Sprintf(`load("forwarder.star", bound="relay")
def mark(xs):
    print(xs[0])
    return xs
firstResult = bound(0, at=0)
marker = [88]
out = %s
again = bound(0, at=0)
after = [198]
`, call)
	preload := ""
	if warm {
		preload = "forwarder.star"
	}
	run := initPositionalWrapper(preload, forwarding, source)
	relay := run.cache["forwarder.star"]["relay"].(*starlark.Function)
	require(relay.NumKwonlyParams() == 2 && relay.ParamDefault(1) == nil, relay)
	saved := relay.ParamDefault(2).(*starlark.List)
	require(saved == run.savedDefaults[2] && saved.String() == "[27]" &&
		saved.SetIndex(0, starlark.MakeInt(7)) != nil, saved)
	partial := run.consumer
	require(partial["firstResult"] == starlark.MakeInt(27) && partial["marker"].String() == "[88]" &&
		partial["bound"] == nil, partial)
	if failure == "" {
		require(run.err == nil && partial["out"] == starlark.MakeInt(53) && partial["again"] == starlark.MakeInt(27) &&
			partial["after"].String() == "[198]" && strings.Join(run.events, ",") == "27 0,53 0,27 0", run.err)
		return
	}
	require(run.err != nil && strings.Contains(run.err.Error(), message), run.err)
	require(partial["out"] == nil && partial["again"] == nil && partial["after"] == nil &&
		strings.Join(run.events, ",") == "27 0"+operandEvents, run.events)
}

func checkRepeatedKeyword() {
	const source = `load("forwarder.star", bound="relay")
out = bound(0, at=0, at=[64][1])
`
	_, _, err := starlark.SourceProgramOptions(&syntax.FileOptions{}, "duplicate.star", source, func(string) bool { return false })
	require(err != nil && strings.Contains(err.Error(), "keyword argument \"at\" is repeated"), err)
}

func checkCollectorWrapper(warm bool, failure string) {
	const forwarding = `load("positional.star", ignored="spare", loaded="pick")
seed = 27
before = [76]
def relay(x, *rest, at, key=[0]):
    return loaded(rest, key[at])
later = [199]
`
	call := "bound(91, 17, marker, 18, key=[-1], at=0)"
	message := ""
	operandEvents := ""
	switch failure {
	case "missing":
		call = "bound(91, mark([63]))"
		message = "missing 1 argument (at)"
		operandEvents = ",63"
	case "unknown":
		call = "bound(91, 17, extra=mark([64]), at=mark([65])[0])"
		message = `unexpected keyword argument "extra"`
		operandEvents = ",64,65"
	case "operand":
		call = "bound(91, 17, extra=mark([64]), at=mark([65])[1], key=mark([66]))"
		message = "index 1 out of range"
		operandEvents = ",64,65"
	}
	source := fmt.Sprintf(`load("forwarder.star", bound="relay")
def mark(xs):
    print(xs[0])
    return xs
firstResult = bound(91, at=0)
marker = [88]
out = %s
again = bound(91, at=0)
after = [198]
`, call)
	preload := ""
	if warm {
		preload = "forwarder.star"
	}
	run := initPositionalWrapper(preload, forwarding, source)
	relay := run.cache["forwarder.star"]["relay"].(*starlark.Function)
	require(relay.HasVarargs() && !relay.HasKwargs() && relay.NumKwonlyParams() == 2 &&
		relay.ParamDefault(1) == nil && relay.ParamDefault(3) == nil, relay)
	saved := relay.ParamDefault(2).(*starlark.List)
	require(saved == run.savedDefaults[2] && saved.String() == "[0]" &&
		saved.SetIndex(0, starlark.MakeInt(7)) != nil, saved)
	partial := run.consumer
	first, firstOK := partial["firstResult"].(starlark.Tuple)
	require(firstOK && len(first) == 0 && partial["marker"].String() == "[88]" && partial["bound"] == nil, partial)
	if failure == "" {
		require(run.err == nil, run.err)
		ordered, orderedOK := partial["out"].(starlark.Tuple)
		again, againOK := partial["again"].(starlark.Tuple)
		require(orderedOK && len(ordered) == 3 && ordered[0] == starlark.MakeInt(17) &&
			ordered[1] == partial["marker"] && ordered[2] == starlark.MakeInt(18) &&
			againOK && len(again) == 0 && partial["after"].String() == "[198]", partial)
		require(strings.Join(run.events, ",") == "() 0,(17, [88], 18) -1,() 0", run.events)
		return
	}
	require(run.err != nil && strings.Contains(run.err.Error(), message), run.err)
	require(partial["out"] == nil && partial["again"] == nil && partial["after"] == nil &&
		strings.Join(run.events, ",") == "() 0"+operandEvents, run.events)
}

func main() {
	checkRepeatedKeyword()
	for _, warm := range []bool{false, true} {
		check(warm, "factory", `{"extra": 9}`)
		check(warm, "factory", `{"key": 8}`)
		check(warm, "absent", `{"extra": 9}`)
		checkWrapper(warm, "escaped", `{"extra": 9}`)
		checkWrapper(warm, "escaped", `{"key": 8}`)
		checkWrapper(warm, "absent", `{"extra": 9}`)
		checkDeclarationSuite(warm, false)
		checkDeclarationSuite(warm, true)
		checkReturnedClosure(warm)
		for _, failure := range []string{"", "arity", "body"} {
			checkPositionalWrapper(warm, failure)
		}
		for _, failure := range []string{"", "missing", "surplus", "default"} {
			checkSavedWrapper(warm, failure)
		}
		for _, failure := range []string{"", "missing", "surplus", "unknown", "duplicate", "operand"} {
			checkKeywordWrapper(warm, failure)
		}
		for _, failure := range []string{"", "missing", "unknown", "operand"} {
			checkCollectorWrapper(warm, failure)
		}
		for _, failure := range []string{"", "first", "last", "both", "dependency"} {
			checkDiamond(warm, failure)
		}
	}
	for _, preload := range []string{"", "prodé.star", "middle.star"} {
		checkChain(preload, false)
		checkChain(preload, true)
		for _, nested := range []bool{false, true} {
			checkWrapperChain(preload, nested, false)
			checkWrapperChain(preload, nested, true)
		}
	}
	fmt.Println("PASS cold and cached importer suites retain callable returns, saved values and producer globals")
	fmt.Println("PASS missing export stops the suite and a second-call error retains the factory and marker")
	fmt.Println("PASS consumer-owned wrapper calls the imported closure on cold and cached loads; reached errors preserve prior effects")
	fmt.Println("PASS interleaved importer declarations, alias calls, saved defaults, and skipped effects after the first error")
	fmt.Println("PASS a consumer wrapper returns a fresh imported closure that remains callable")
	fmt.Println("PASS three-module re-export with cold, root-preloaded and middle-preloaded histories")
	fmt.Println("PASS direct and nested calls through the published middle wrapper, including reached failures")
	fmt.Println("PASS grouped diamond loads reuse one dependency per command, choose the rightmost missing export, and skip later commands")
	fmt.Println("PASS published positional wrappers call the second alias in operand order and stop at arity or reached body errors")
	fmt.Println("PASS wrapper defaults are saved through cache hits and overrides, and a reached default error prevents publication")
	fmt.Println("PASS keyword-only wrappers preserve saved defaults and operand order across binding errors and cache hits")
	fmt.Println("PASS positional wrapper collectors preserve empty and ordered tuple payloads, defaults, and reached errors")
}
