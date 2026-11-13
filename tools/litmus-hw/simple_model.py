#!/usr/bin/env python3
"""Exhaustive explorer for the simple pthread model.

An executable transcription of `Silmaril.Process.Mt.Pthread.Simple` (`tisa`, `start`,
`Csl.Step`, `Csl.Fault`, `Csl.Race`) and of the primitive specifications of
`Silmaril.Process.Mt.Pthread` (`Op.spec`), with the programs `p1`..`p8` of
`scripts/pthread-hw/src` transcribed into the model's instruction set (`Ins`), with their loop
bounds as parameters.

It explores every reachable configuration (breadth-first, with configurations deduplicated)
and reports:

* the outcome set: the outputs of the configurations in which `main` has finished
  (`Simple.Outcome`);
* undefined behaviour: reachable configurations with a faulting thread (`Csl.Fault`);
* data races: reachable configurations where two threads' next plain steps access a common
  cell (`Csl.Race`, which counts read/read pairs), and the subset with a store (a write race);
* stuck configurations: no step possible, `main` not finished (deadlock).

Two reductions, both sound for the outputs these programs print:
* `pthread_create` picks the least unused thread id (thread ids are names; no program prints
  one);
* `pthread_key_create` picks the least free key (keys are names; no program prints one).

This file is a transcription, not extracted from Lean: agreement is by review, checked by the
expected outcome sets (the `Deterministic` statements) and the hardware runs.

Usage:  python3 -I simple_model.py [PROGRAM[:PARAM] ...]      (default: the small set)
        python3 -I simple_model.py --json ...                  (machine-readable)
"""
import json
import sys
from collections import deque

# ---- errors and limits (Pthread/Defs) ----
EPERM, EAGAIN, EBUSY, EINVAL, EDEADLK, EOVERFLOW = 1, 11, 16, 22, 35, 75
SERIAL = 2**32 - 1
KEYS_MAX = 1024
SEM_MAX = 2**31 - 1
DEPTH_MAX = 2**32 - 1


# ---- immutable maps as sorted tuples ----
def fz(d):
    return tuple(sorted(d.items()))


def th(d):
    return dict(d)


# ---- the pthread state PSt: a dict of frozen maps; defaults are omitted ----
# thr: tid -> (life, val, detached)   life: 'run' | 'exit'
# jret: tid -> v;  mtx: a -> (kind, owner, depth);  cnd: a -> sorted tuple of waiters
# rw: a -> (writer, sorted readers);  once: a -> ('init',) | ('running', t) | ('done',)
# keys: k -> True;  dtor: k -> d;  tls: (t, k) -> v;  spin: a -> 'free' | ('held', t)
# bar: a -> (count, sorted waiting);  sem: a -> n
FIELDS = ("thr", "jret", "mtx", "cnd", "rw", "once", "keys", "dtor", "tls", "spin", "bar", "sem")
MTX0 = ("normal", None, 0)
RW0 = (None, ())
BAR0 = (0, ())


def ps_init(t0):
    p = {f: () for f in FIELDS}
    p["thr"] = ((t0, ("run", 0, False)),)
    return p


def get(p, f, a, default=None):
    for k, v in p[f]:
        if k == a:
            return v
    return default


def put(p, f, a, v, default=None):
    d = dict(p[f])
    if v == default:
        d.pop(a, None)
    else:
        d[a] = v
    q = dict(p)
    q[f] = fz(d)
    return q


def ms_add(ms, x):
    return tuple(sorted(ms + (x,)))


def ms_erase(ms, x):
    l = list(ms)
    if x in l:
        l.remove(x)
    return tuple(l)


def arg(args, i):
    return args[i] if i < len(args) else 0


# ---- primitive specs: fault(t, args, p) -> bool; steps(t, args, p) -> [(r, p')] ----
def mutex_init(kind):
    def fault(t, a, p):
        return get(p, "mtx", arg(a, 0), MTX0)[1] is not None

    def steps(t, a, p):
        return [(0, put(p, "mtx", arg(a, 0), (kind, None, 0), MTX0))]

    return fault, steps


def take(s, t):
    return (s[0], t, 1)


def drop(s):
    return (s[0], None, 0) if s[2] <= 1 else (s[0], s[1], s[2] - 1)


def mutex_lock(t, a, p, trylock=False):
    m = arg(a, 0)
    s = get(p, "mtx", m, MTX0)
    out = []
    if s[1] is None:
        out.append((0, put(p, "mtx", m, take(s, t), MTX0)))
    if s[1] == t and s[0] == "recursive" and s[2] < DEPTH_MAX:
        out.append((0, put(p, "mtx", m, (s[0], s[1], s[2] + 1), MTX0)))
    if s[1] == t and s[0] == "recursive" and DEPTH_MAX <= s[2]:
        out.append((EAGAIN, p))
    if not trylock and s[1] == t and s[0] == "errorcheck":
        out.append((EDEADLK, p))
    if trylock and s[1] is not None and not (s[1] == t and s[0] == "recursive"):
        out.append((EBUSY, p))
    return out


def mutex_unlock_fault(t, a, p):
    s = get(p, "mtx", arg(a, 0), MTX0)
    return s[0] == "normal" and s[1] != t


def mutex_unlock(t, a, p):
    m = arg(a, 0)
    s = get(p, "mtx", m, MTX0)
    out = []
    if s[1] == t:
        out.append((0, put(p, "mtx", m, drop(s), MTX0)))
    if s[1] != t and s[0] != "normal":
        out.append((EPERM, p))
    return out


def cond_wait_fault(t, a, p):
    s = get(p, "mtx", arg(a, 1), MTX0)
    return (s[1] != t and s[0] == "normal") or (s[1] == t and s[2] != 1)


def cond_wait(t, a, p):
    c, m = arg(a, 0), arg(a, 1)
    s = get(p, "mtx", m, MTX0)
    out = []
    if s[1] == t and s[2] == 1:
        q = put(p, "mtx", m, drop(s), MTX0)
        q = put(q, "cnd", c, ms_add(get(p, "cnd", c, ()), t), ())
        out.append((0, q))
    if s[1] != t and s[0] != "normal":
        out.append((EPERM, p))
    return out


def cond_resume(t, a, p):
    c, m = arg(a, 0), arg(a, 1)
    s = get(p, "mtx", m, MTX0)
    if s[1] is not None:
        return []
    q = put(p, "mtx", m, take(s, t), MTX0)
    q = put(q, "cnd", c, ms_erase(get(p, "cnd", c, ()), t), ())
    return [(0, q)]


def cond_signal(t, a, p):
    c = arg(a, 0)
    ws = get(p, "cnd", c, ())
    if not ws:
        return [(0, p)]
    return [(0, put(p, "cnd", c, ms_erase(ws, w), ())) for w in sorted(set(ws))]


def cond_broadcast(t, a, p):
    return [(0, put(p, "cnd", arg(a, 0), (), ()))]


def rw_rd(t, a, p, try_=False):
    l = arg(a, 0)
    s = get(p, "rw", l, RW0)
    out = []
    if s[0] is None:
        out.append((0, put(p, "rw", l, (s[0], ms_add(s[1], t)), RW0)))
    if not try_ and s[0] == t:
        out.append((EDEADLK, p))
    if try_ and s[0] is not None:
        out.append((EBUSY, p))
    return out


def rw_wr(t, a, p, try_=False):
    l = arg(a, 0)
    s = get(p, "rw", l, RW0)
    out = []
    if s[0] is None and not s[1]:
        out.append((0, put(p, "rw", l, (t, s[1]), RW0)))
    if not try_ and s[0] == t:
        out.append((EDEADLK, p))
    if try_ and (s[0] is not None or s[1]):
        out.append((EBUSY, p))
    return out


def rw_unlock_fault(t, a, p):
    s = get(p, "rw", arg(a, 0), RW0)
    return s[0] != t and t not in s[1]


def rw_unlock(t, a, p):
    l = arg(a, 0)
    s = get(p, "rw", l, RW0)
    if s[0] == t:
        return [(0, put(p, "rw", l, (None, s[1]), RW0))]
    if t in s[1]:
        return [(0, put(p, "rw", l, (s[0], ms_erase(s[1], t)), RW0))]
    return []


def once_begin(t, a, p):
    o = arg(a, 0)
    s = get(p, "once", o, ("init",))
    if s == ("done",):
        return [(0, p)]
    if s == ("init",):
        return [(1, put(p, "once", o, ("running", t), ("init",)))]
    return []


def once_end_fault(t, a, p):
    return get(p, "once", arg(a, 0), ("init",)) != ("running", t)


def once_end(t, a, p):
    return [(0, put(p, "once", arg(a, 0), ("done",), ("init",)))]


def key_create(t, a, p):
    used = {k for k, _ in p["keys"]}
    free = [k for k in range(KEYS_MAX) if k not in used]
    if not free:
        return [(KEYS_MAX, p)]
    k = free[0]  # reduction: the least free key
    q = put(p, "keys", k, True, None)
    q = put(q, "dtor", k, arg(a, 0), 0)
    q = dict(q)
    q["tls"] = fz({uk: v for uk, v in p["tls"] if uk[1] != k})
    return [(k, q)]


def key_fault(t, a, p):
    return get(p, "keys", arg(a, 0), None) is None


def key_delete(t, a, p):
    return [(0, put(p, "keys", arg(a, 0), None, None))]


def getspecific(t, a, p):
    return [(get(p, "tls", (t, arg(a, 0)), 0), p)]


def setspecific(t, a, p):
    return [(0, put(p, "tls", (t, arg(a, 0)), arg(a, 1), 0))]


def spin_held(p, s):
    v = get(p, "spin", s, "uninit")
    return isinstance(v, tuple)


def spin_init(t, a, p):
    return [(0, put(p, "spin", arg(a, 0), "free", "uninit"))]


def spin_destroy(t, a, p):
    return [(0, put(p, "spin", arg(a, 0), "uninit", "uninit"))]


def spin_lock_fault(t, a, p):
    v = get(p, "spin", arg(a, 0), "uninit")
    return v == "uninit" or v == ("held", t)


def spin_lock(t, a, p):
    s = arg(a, 0)
    if get(p, "spin", s, "uninit") == "free":
        return [(0, put(p, "spin", s, ("held", t), "uninit"))]
    return []


def spin_trylock(t, a, p):
    s = arg(a, 0)
    v = get(p, "spin", s, "uninit")
    if v == "free":
        return [(0, put(p, "spin", s, ("held", t), "uninit"))]
    if isinstance(v, tuple):
        return [(EBUSY, p)]
    return []


def spin_unlock(t, a, p):
    return [(0, put(p, "spin", arg(a, 0), "free", "uninit"))]


def bar_init(t, a, p):
    b, n = arg(a, 0), arg(a, 1)
    if n == 0:
        return [(EINVAL, p)]
    return [(0, put(p, "bar", b, (n, ()), BAR0))]


def bar_destroy(t, a, p):
    return [(0, put(p, "bar", arg(a, 0), BAR0, BAR0))]


def bar_arrive_fault(t, a, p):
    s = get(p, "bar", arg(a, 0), BAR0)
    return s[0] == 0 or t in s[1]


def bar_arrive(t, a, p):
    b = arg(a, 0)
    s = get(p, "bar", b, BAR0)
    if len(s[1]) + 1 == s[0]:
        return [(SERIAL, put(p, "bar", b, (s[0], ()), BAR0))]
    if len(s[1]) + 1 < s[0]:
        return [(0, put(p, "bar", b, (s[0], ms_add(s[1], t)), BAR0))]
    return []


def bar_depart(t, a, p):
    return [] if t in get(p, "bar", arg(a, 0), BAR0)[1] else [(0, p)]


def sem_init(t, a, p):
    s, v = arg(a, 0), arg(a, 1)
    if v <= SEM_MAX:
        return [(0, put(p, "sem", s, v, None))]
    return [(EINVAL, p)]


def sem_fault(t, a, p):
    return get(p, "sem", arg(a, 0), None) is None


def sem_wait(t, a, p, try_=False):
    s = arg(a, 0)
    v = get(p, "sem", s, None)
    if v is not None and v > 0:
        return [(0, put(p, "sem", s, v - 1, None))]
    if try_ and v == 0:
        return [(EAGAIN, p)]
    return []


def sem_post(t, a, p):
    s = arg(a, 0)
    v = get(p, "sem", s, None)
    if v is not None and v < SEM_MAX:
        return [(0, put(p, "sem", s, v + 1, None))]
    if v == SEM_MAX:
        return [(EOVERFLOW, p)]
    return []


def sem_getvalue(t, a, p):
    return [(get(p, "sem", arg(a, 0), None), p)]


def self_(t, a, p):
    return [(t, p)]


def join_fault(t, a, p):
    u = arg(a, 0)
    e = get(p, "thr", u, None)
    return u != t and (e is None or e[2])


def join(t, a, p):
    u = arg(a, 0)
    if u == t:
        return [(EDEADLK, p)]
    e = get(p, "thr", u, None)
    if e is not None and e[0] == "exit" and not e[2]:
        q = put(p, "thr", u, None, None)
        return [(0, put(q, "jret", t, e[1], 0))]
    return []


def joined(t, a, p):
    return [(get(p, "jret", t, 0), p)]


def exit_fault(t, a, p):
    e = get(p, "thr", t, None)
    return e is None or e[0] != "run"


def exit_(t, a, p):
    e = get(p, "thr", t, None)
    if e is None or e[0] != "run":
        return []
    return [(0, put(p, "thr", t, None if e[2] else ("exit", arg(a, 0), e[2]), None))]


NEVER = lambda t, a, p: False  # noqa: E731

SPECS = {
    "self": (NEVER, self_),
    "join": (join_fault, join),
    "joined": (NEVER, joined),
    "exit": (exit_fault, exit_),
    "mutexInit.normal": mutex_init("normal"),
    "mutexInit.recursive": mutex_init("recursive"),
    "mutexInit.errorcheck": mutex_init("errorcheck"),
    "mutexLock": (NEVER, lambda t, a, p: mutex_lock(t, a, p)),
    "mutexTrylock": (NEVER, lambda t, a, p: mutex_lock(t, a, p, trylock=True)),
    "mutexUnlock": (mutex_unlock_fault, mutex_unlock),
    "condWait": (cond_wait_fault, cond_wait),
    "condResume": (NEVER, cond_resume),
    "condSignal": (NEVER, cond_signal),
    "condBroadcast": (NEVER, cond_broadcast),
    "rwRdlock": (NEVER, lambda t, a, p: rw_rd(t, a, p)),
    "rwTryRdlock": (NEVER, lambda t, a, p: rw_rd(t, a, p, True)),
    "rwWrlock": (NEVER, lambda t, a, p: rw_wr(t, a, p)),
    "rwTryWrlock": (NEVER, lambda t, a, p: rw_wr(t, a, p, True)),
    "rwUnlock": (rw_unlock_fault, rw_unlock),
    "onceBegin": (NEVER, once_begin),
    "onceEnd": (once_end_fault, once_end),
    "keyCreate": (NEVER, key_create),
    "keyDelete": (key_fault, key_delete),
    "getspecific": (key_fault, getspecific),
    "setspecific": (key_fault, setspecific),
    "spinInit": (lambda t, a, p: spin_held(p, arg(a, 0)), spin_init),
    "spinDestroy": (lambda t, a, p: spin_held(p, arg(a, 0)), spin_destroy),
    "spinLock": (spin_lock_fault, spin_lock),
    "spinTrylock": (lambda t, a, p: get(p, "spin", arg(a, 0), "uninit") == "uninit", spin_trylock),
    "spinUnlock": (lambda t, a, p: get(p, "spin", arg(a, 0), "uninit") != ("held", t), spin_unlock),
    "barInit": (lambda t, a, p: get(p, "bar", arg(a, 0), BAR0)[1] != (), bar_init),
    "barDestroy": (lambda t, a, p: get(p, "bar", arg(a, 0), BAR0)[1] != (), bar_destroy),
    "barArrive": (bar_arrive_fault, bar_arrive),
    "barDepart": (NEVER, bar_depart),
    "semInit": (NEVER, sem_init),
    "semWait": (sem_fault, lambda t, a, p: sem_wait(t, a, p)),
    "semTrywait": (sem_fault, lambda t, a, p: sem_wait(t, a, p, True)),
    "semPost": (sem_fault, sem_post),
    "semGetvalue": (sem_fault, sem_getvalue),
}


# ---- instructions (Simple.Ins) ----
# ('movi', d, v) ('add', d, a, b) ('addi', d, a, v) ('ld', d, base, idx) ('st', base, idx, s)
# ('beq', r, v, l) ('bne', r, v, l) ('beqr', a, b, l) ('bner', a, b, l) ('jmp', l)
# ('call', op, [args], d)  args: ('imm', v) | ('reg', r)
# ('create', f, arg, d) ('out', r) ('ret', r) ('halt',)
def I(v):
    return ("imm", v)


def R(r):
    return ("reg", r)


def aval(regs, a):
    return a[1] if a[0] == "imm" else regs.get(a[1], 0)


def addr(regs, base, idx):
    return base if idx is None else base + regs.get(idx, 0)


# A thread: (fn, pc, regs (frozen), fin).  A configuration: (threads (frozen), cells (frozen),
# pthread state (tuple of fields), out (tuple)).
def fetch(code, s):
    fn, pc, _, fin = s
    if fin:
        return None
    body = code.get(fn, [])
    return body[pc] if pc < len(body) else None


def footprint(code, s):
    ins = fetch(code, s)
    if ins is None:
        return None
    regs = dict(s[2])
    if ins[0] == "ld":
        return (addr(regs, ins[2], ins[3]), False)
    if ins[0] == "st":
        return (addr(regs, ins[1], ins[2]), True)
    return None


def setreg(regs, d, v):
    r = dict(regs)
    if v == 0:
        r.pop(d, None)
    else:
        r[d] = v
    return fz(r)


def nxt(s, regs):
    return (s[0], s[1] + 1, regs, s[3])


def thread_steps(code, t, s, cells, p, out, ths):
    """Successors of thread t: list of (threads-update dict, cells, p, out).  Faults: returns
    'fault' as the second component of the result."""
    ins = fetch(code, s)
    fn, pc, regs_f, fin = s
    if fin:
        return [], False
    if ins is None:
        return [], True  # ran off its function
    regs = dict(regs_f)
    op = ins[0]
    res = []
    if op == "movi":
        res.append(({t: nxt(s, setreg(regs, ins[1], ins[2]))}, cells, p, out))
    elif op == "add":
        res.append(({t: nxt(s, setreg(regs, ins[1], regs.get(ins[2], 0) + regs.get(ins[3], 0)))}, cells, p, out))
    elif op == "addi":
        res.append(({t: nxt(s, setreg(regs, ins[1], regs.get(ins[2], 0) + ins[3]))}, cells, p, out))
    elif op == "ld":
        v = dict(cells).get(addr(regs, ins[2], ins[3]), 0)
        res.append(({t: nxt(s, setreg(regs, ins[1], v))}, cells, p, out))
    elif op == "st":
        c = dict(cells)
        a = addr(regs, ins[1], ins[2])
        v = regs.get(ins[3], 0)
        if v == 0:
            c.pop(a, None)
        else:
            c[a] = v
        res.append(({t: nxt(s, regs_f)}, fz(c), p, out))
    elif op in ("beq", "bne"):
        eq = regs.get(ins[1], 0) == ins[2]
        jump = eq if op == "beq" else not eq
        res.append(({t: (fn, ins[3], regs_f, fin) if jump else nxt(s, regs_f)}, cells, p, out))
    elif op in ("beqr", "bner"):
        eq = regs.get(ins[1], 0) == regs.get(ins[2], 0)
        jump = eq if op == "beqr" else not eq
        res.append(({t: (fn, ins[3], regs_f, fin) if jump else nxt(s, regs_f)}, cells, p, out))
    elif op == "jmp":
        res.append(({t: (fn, ins[1], regs_f, fin)}, cells, p, out))
    elif op == "halt":
        res.append(({t: (fn, pc, regs_f, True)}, cells, p, out))
    elif op == "out":
        res.append(({t: nxt(s, regs_f)}, cells, p, out + (regs.get(ins[1], 0),)))
    elif op == "ret":
        v = regs.get(ins[1], 0)
        if exit_fault(t, [v], p):
            return [], True
        for _, q in exit_(t, [v], p):
            res.append(({t: (fn, pc, regs_f, True)}, cells, q, out))
    elif op == "call":
        name, args, d = ins[1], [aval(regs, a) for a in ins[2]], ins[3]
        fault, steps = SPECS[name]
        if fault(t, args, p):
            return [], True
        for r, q in steps(t, args, p):
            res.append(({t: nxt(s, setreg(regs, d, r))}, cells, q, out))
    elif op == "create":
        f, a, d = ins[1], ins[2], ins[3]
        u = 1
        while u in ths or get(p, "thr", u, None) is not None:
            u += 1  # reduction: the least unused thread id
        q = put(p, "thr", u, ("run", 0, False), None)
        q = dict(q)
        q["tls"] = fz({uk: v for uk, v in p["tls"] if uk[0] != u})
        child = (f, 0, setreg({}, 0, aval(regs, a)), False)
        res.append(({t: nxt(s, setreg(regs, d, u)), u: child}, cells, q, out))
    else:
        raise ValueError(ins)
    return res, False


def freeze_p(p):
    return tuple(p[f] for f in FIELDS)


def thaw_p(pt):
    return dict(zip(FIELDS, pt))


LOCAL = {"movi", "add", "addi", "beq", "bne", "beqr", "bner", "jmp"}


def explore(code, limit=20_000_000, reduce=True):
    start = (fz({0: (0, 0, (), False)}), (), freeze_p(ps_init(0)), ())
    seen = {start}
    queue = deque([start])
    outcomes, faults, races, wraces, stuck = {}, 0, 0, 0, 0
    race_ex = wrace_ex = fault_ex = stuck_ex = None
    while queue:
        C = queue.popleft()
        ths_f, cells, pt, out = C
        ths = dict(ths_f)
        p = thaw_p(pt)
        main = ths.get(0)
        if main is not None and main[3]:
            outcomes[out] = outcomes.get(out, 0) + 1
        # races (Csl.Race: common footprint of two threads' next plain steps)
        fps = [(t, footprint(code, s)) for t, s in ths.items()]
        fps = [(t, f) for t, f in fps if f is not None]
        rr = wr = False
        for i in range(len(fps)):
            for j in range(i + 1, len(fps)):
                if fps[i][1][0] == fps[j][1][0]:
                    rr = True
                    if fps[i][1][1] or fps[j][1][1]:
                        wr = True
        if rr:
            races += 1
            race_ex = race_ex or C
        if wr:
            wraces += 1
            wrace_ex = wrace_ex or C
        moved = False
        faulted = False
        # Reduction: a thread at a local instruction (register arithmetic, branches) takes
        # that step alone. Local steps touch no cell and no pthread state, so they commute with
        # every other thread's steps, and a thread at a local step has no footprint, so races,
        # faults and outcomes of the full exploration are reached (with the other threads'
        # local steps already taken). None of the programs has a loop of local steps only.
        order = sorted(ths.items())
        if reduce:
            loc = [(t, s) for t, s in order if (fetch(code, s) or ("halt",))[0] in LOCAL]
            if loc:
                order = loc[:1]
        for t, s in order:
            succ, fault = thread_steps(code, t, s, cells, p, out, ths)
            if fault:
                faulted = True
            for upd, c2, q, o2 in succ:
                moved = True
                nt = dict(ths)
                nt.update(upd)
                D = (fz(nt), c2, freeze_p(q), o2)
                if D not in seen:
                    seen.add(D)
                    queue.append(D)
                    if len(seen) > limit:
                        raise RuntimeError(f"more than {limit} configurations")
        if faulted:
            faults += 1
            fault_ex = fault_ex or C
        if not moved and not (main is not None and main[3]):
            stuck += 1
            stuck_ex = stuck_ex or C
    return {
        "configs": len(seen),
        "outcomes": {" ".join(map(str, o)): n for o, n in sorted(outcomes.items())},
        "faults": faults,
        "races": races,
        "write_races": wraces,
        "stuck": stuck,
        "examples": {"race": race_ex, "write_race": wrace_ex, "fault": fault_ex, "stuck": stuck_ex},
    }


# ---- the programs (transcriptions of scripts/pthread-hw/src/p*.c) ----
CTR, MTX = 0, 1


def p1(n):
    """p1_mutex_counter.c: two workers, n increments each under a normal mutex."""
    return {
        0: [("create", 1, I(0), 1), ("create", 1, I(0), 2), ("call", "join", [R(1)], 3),
            ("call", "join", [R(2)], 3), ("ld", 4, CTR, None), ("out", 4), ("halt",)],
        1: [("beq", 5, n, 8), ("call", "mutexLock", [I(MTX)], 6), ("ld", 7, CTR, None), ("addi", 7, 7, 1),
            ("st", CTR, None, 7), ("call", "mutexUnlock", [I(MTX)], 6), ("addi", 5, 5, 1), ("jmp", 0),
            ("ret", 0)],
    }


def p6(n):
    """p6_spin_counter.c: p1 with a spin lock initialised by main."""
    return {
        0: [("call", "spinInit", [I(MTX)], 3), ("create", 1, I(0), 1), ("create", 1, I(0), 2),
            ("call", "join", [R(1)], 3), ("call", "join", [R(2)], 3), ("ld", 4, CTR, None), ("out", 4),
            ("halt",)],
        1: [("beq", 5, n, 8), ("call", "spinLock", [I(MTX)], 6), ("ld", 7, CTR, None), ("addi", 7, 7, 1),
            ("st", CTR, None, 7), ("call", "spinUnlock", [I(MTX)], 6), ("addi", 5, 5, 1), ("jmp", 0),
            ("ret", 0)],
    }


def p5(n):
    """p5_racy_counter.c: p1 without the lock (mov/add/mov)."""
    return {
        0: [("create", 1, I(0), 1), ("create", 1, I(0), 2), ("call", "join", [R(1)], 3),
            ("call", "join", [R(2)], 3), ("ld", 4, CTR, None), ("out", 4), ("halt",)],
        1: [("beq", 5, n, 6), ("ld", 7, CTR, None), ("addi", 7, 7, 1), ("st", CTR, None, 7),
            ("addi", 5, 5, 1), ("jmp", 0), ("ret", 0)],
    }


FULL, SLOT, SUM, NOT_FULL, NOT_EMPTY = 10, 11, 12, 20, 21


def p2(n):
    """p2_prodcons_cond.c: producer sends 1..n through one slot; consumer sums."""
    prod = [("movi", 5, 1),
            ("beq", 5, n + 1, 15),
            ("call", "mutexLock", [I(MTX)], 6),
            ("ld", 7, FULL, None),
            ("beq", 7, 0, 8),
            ("call", "condWait", [I(NOT_FULL), I(MTX)], 6),
            ("call", "condResume", [I(NOT_FULL), I(MTX)], 6),
            ("jmp", 3),
            ("st", SLOT, None, 5),
            ("movi", 7, 1),
            ("st", FULL, None, 7),
            ("call", "condSignal", [I(NOT_EMPTY)], 6),
            ("call", "mutexUnlock", [I(MTX)], 6),
            ("addi", 5, 5, 1),
            ("jmp", 1),
            ("movi", 0, 0),
            ("ret", 0)]
    cons = [("movi", 5, 1),
            ("beq", 5, n + 1, 18),
            ("call", "mutexLock", [I(MTX)], 6),
            ("ld", 7, FULL, None),
            ("bne", 7, 0, 8),
            ("call", "condWait", [I(NOT_EMPTY), I(MTX)], 6),
            ("call", "condResume", [I(NOT_EMPTY), I(MTX)], 6),
            ("jmp", 3),
            ("ld", 8, SUM, None),
            ("ld", 9, SLOT, None),
            ("add", 8, 8, 9),
            ("st", SUM, None, 8),
            ("movi", 7, 0),
            ("st", FULL, None, 7),
            ("call", "condSignal", [I(NOT_FULL)], 6),
            ("call", "mutexUnlock", [I(MTX)], 6),
            ("addi", 5, 5, 1), ("jmp", 1),
            ("ret", 0)]
    return {
        0: [("create", 2, I(0), 1), ("create", 1, I(0), 2), ("call", "join", [R(2)], 3),
            ("call", "join", [R(1)], 3), ("ld", 4, SUM, None), ("out", 4), ("halt",)],
        1: prod,
        2: cons,
    }


TH_IDS, SEEN, INITS, VALUE, ONCE = 100, 110, 120, 121, 30


def p3(nthreads=4):
    """p3_once.c: nthreads threads call pthread_once; prints inits and how many saw 42."""
    return {
        0: [("movi", 1, 0),
            ("beq", 1, nthreads, 6),
            ("create", 1, R(1), 2),
            ("st", TH_IDS, 1, 2),
            ("addi", 1, 1, 1),
            ("jmp", 1),
            ("movi", 1, 0),
            ("movi", 3, 0),
            ("beq", 1, nthreads, 15),
            ("ld", 2, TH_IDS, 1),
            ("call", "join", [R(2)], 4),
            ("ld", 4, SEEN, 1),
            ("add", 3, 3, 4),
            ("addi", 1, 1, 1),
            ("jmp", 8),
            ("ld", 5, INITS, None),
            ("out", 5),
            ("out", 3),
            ("halt",)],
        1: [("call", "onceBegin", [I(ONCE)], 1),
            ("beq", 1, 0, 8),
            ("ld", 2, INITS, None),
            ("addi", 2, 2, 1),
            ("st", INITS, None, 2),
            ("movi", 2, 42),
            ("st", VALUE, None, 2),
            ("call", "onceEnd", [I(ONCE)], 1),
            ("ld", 3, VALUE, None),
            ("movi", 4, 0),
            ("bne", 3, 42, 12),
            ("movi", 4, 1),
            ("st", SEEN, 0, 4),
            ("movi", 5, 0),
            ("ret", 5)],
    }


KEY_CELL, DTORS, OWN = 130, 131, 140


def p4(k=1000, nthreads=4):
    """p4_tls_keys.c: one key with a destructor; each thread stores i + 1 and reads it back k
    times; the destructor (counting under a mutex) runs at thread exit for a non-null value."""
    return {
        0: [("call", "keyCreate", [I(1)], 1),
            ("st", KEY_CELL, None, 1),
            ("movi", 1, 0),
            ("beq", 1, nthreads, 8),
            ("create", 1, R(1), 2),
            ("st", TH_IDS, 1, 2),
            ("addi", 1, 1, 1),
            ("jmp", 3),
            ("movi", 1, 0),
            ("movi", 3, 0),
            ("beq", 1, nthreads, 17),
            ("ld", 2, TH_IDS, 1),
            ("call", "join", [R(2)], 4),
            ("ld", 4, OWN, 1),
            ("add", 3, 3, 4),
            ("addi", 1, 1, 1),
            ("jmp", 10),
            ("ld", 5, DTORS, None),
            ("ld", 6, KEY_CELL, None),
            ("call", "getspecific", [R(6)], 7),
            ("out", 3),
            ("out", 5),
            ("out", 7),
            ("halt",)],
        1: [("ld", 1, KEY_CELL, None),
            ("addi", 2, 0, 1),
            ("call", "setspecific", [R(1), R(2)], 3),
            ("movi", 4, 0),
            ("beq", 4, k, 10),
            ("call", "getspecific", [R(1)], 5),
            ("bner", 5, 2, 12),
            ("addi", 4, 4, 1),
            ("jmp", 4),
            ("jmp", 12),
            ("movi", 6, 1),
            ("st", OWN, 0, 6),
            ("call", "getspecific", [R(1)], 5),
            ("beq", 5, 0, 21),
            ("call", "setspecific", [R(1), I(0)], 3),
            ("call", "mutexLock", [I(MTX)], 3),
            ("ld", 7, DTORS, None),
            ("addi", 7, 7, 1),
            ("st", DTORS, None, 7),
            ("call", "mutexUnlock", [I(MTX)], 3),
            ("movi", 0, 0),
            ("movi", 0, 0),
            ("ret", 0)],
    }


PING, PONG, BAR, LOG, POS, SLOTS, ALL, SERIALC = 40, 41, 42, 200, 199, 150, 160, 170


def ping_pong(mine, other, c, rounds):
    return [("movi", 5, 0),
            ("beq", 5, rounds, 12),
            ("call", "semWait", [I(mine)], 6),
            ("ld", 7, POS, None),
            ("movi", 8, c),
            ("st", LOG, 7, 8),
            ("addi", 7, 7, 1),
            ("st", POS, None, 7),
            ("call", "semPost", [I(other)], 6),
            ("addi", 5, 5, 1),
            ("jmp", 1),
            ("jmp", 12),
            ("movi", 0, 0),
            ("ret", 0)]


def p7(rounds=10, nthreads=4):
    """p7_sem_barrier.c: semaphore ping-pong (rounds), then nthreads meet at a barrier."""
    return {
        0: [("call", "semInit", [I(PING), I(1)], 9),
            ("call", "semInit", [I(PONG), I(0)], 9),
            ("create", 1, I(0), 1),
            ("create", 2, I(0), 2),
            ("call", "join", [R(1)], 9),
            ("call", "join", [R(2)], 9),
            ("call", "barInit", [I(BAR), I(nthreads)], 9),
            ("movi", 1, 0),
            ("beq", 1, nthreads, 13),
            ("create", 3, R(1), 2),
            ("st", TH_IDS, 1, 2),
            ("addi", 1, 1, 1),
            ("jmp", 8),
            ("movi", 1, 0),
            ("movi", 3, 0),
            ("movi", 4, 0),
            ("beq", 1, nthreads, 25),
            ("ld", 2, TH_IDS, 1),
            ("call", "join", [R(2)], 9),
            ("ld", 5, ALL, 1),
            ("add", 3, 3, 5),
            ("ld", 5, SERIALC, 1),
            ("add", 4, 4, 5),
            ("addi", 1, 1, 1),
            ("jmp", 16),
            ("movi", 1, 0),
            ("beq", 1, 2 * rounds, 31),
            ("ld", 5, LOG, 1),
            ("out", 5),
            ("addi", 1, 1, 1),
            ("jmp", 26),
            ("out", 3),
            ("out", 4),
            ("halt",)],
        1: ping_pong(PING, PONG, 97, rounds),
        2: ping_pong(PONG, PING, 98, rounds),
        3: [("movi", 1, 1),
            ("st", SLOTS, 0, 1),
            ("call", "barArrive", [I(BAR)], 2),
            ("bne", 2, 0, 5),
            ("call", "barDepart", [I(BAR)], 2),
            ("movi", 3, 0),
            ("bne", 2, SERIAL, 8),
            ("movi", 3, 1),
            ("st", SERIALC, 0, 3),
            ("movi", 4, 0),
            ("movi", 5, 0),
            ("beq", 5, nthreads, 16),
            ("ld", 6, SLOTS, 5),
            ("add", 4, 4, 6),
            ("addi", 5, 5, 1),
            ("jmp", 11),
            ("movi", 3, 0),
            ("bne", 4, nthreads, 19),
            ("movi", 3, 1),
            ("st", ALL, 0, 3),
            ("movi", 0, 0),
            ("ret", 0)],
    }


EC, RC, NM, SPIN_L, SEM_S, RW_L, R_OTHER, R_TRY = 50, 51, 52, 53, 54, 55, 180, 181
MINUS_ONE = 2**32 - 1


def p8():
    """p8_mutex_errors.c: POSIX error returns."""
    main = [("call", "mutexInit.errorcheck", [I(EC)], 0),
            ("call", "mutexInit.recursive", [I(RC)], 0),
            ("call", "mutexLock", [I(EC)], 1),
            ("call", "mutexLock", [I(EC)], 2),
            ("create", 1, I(0), 20),
            ("call", "join", [R(20)], 0),
            ("ld", 3, R_OTHER, None),
            ("call", "mutexUnlock", [I(EC)], 4),
            ("call", "mutexLock", [I(RC)], 5),
            ("call", "mutexLock", [I(RC)], 6),
            ("call", "mutexUnlock", [I(RC)], 7),
            ("call", "mutexUnlock", [I(RC)], 8),
            ("call", "mutexUnlock", [I(RC)], 9),
            ("call", "mutexLock", [I(NM)], 0),
            ("create", 2, I(0), 20),
            ("call", "join", [R(20)], 0),
            ("call", "mutexUnlock", [I(NM)], 0),
            ("ld", 10, R_TRY, None),
            ("call", "spinInit", [I(SPIN_L)], 0),
            ("call", "spinTrylock", [I(SPIN_L)], 11),
            ("call", "spinTrylock", [I(SPIN_L)], 12),
            ("call", "spinUnlock", [I(SPIN_L)], 0),
            ("call", "semInit", [I(SEM_S), I(0)], 0),
            ("call", "semTrywait", [I(SEM_S)], 14),
            ("movi", 13, 0),
            ("beq", 14, 0, 27),
            ("movi", 13, MINUS_ONE),
            ("call", "rwRdlock", [I(RW_L)], 15),
            ("call", "rwRdlock", [I(RW_L)], 16),
            ("call", "rwTryWrlock", [I(RW_L)], 17),
            ("call", "rwUnlock", [I(RW_L)], 0),
            ("call", "rwUnlock", [I(RW_L)], 0),
            ("call", "rwWrlock", [I(RW_L)], 18),
            ("call", "rwRdlock", [I(RW_L)], 19),
            ("call", "rwUnlock", [I(RW_L)], 0),
            ("call", "self", [], 21),
            ("call", "join", [R(21)], 22)]
    main += [("out", r) for r in range(1, 20)] + [("out", 22), ("halt",)]
    return {
        0: main,
        1: [("call", "mutexUnlock", [I(EC)], 1), ("st", R_OTHER, None, 1), ("movi", 0, 0), ("ret", 0)],
        2: [("call", "mutexTrylock", [I(NM)], 1), ("st", R_TRY, None, 1), ("movi", 0, 0), ("ret", 0)],
    }


PROGRAMS = {
    "p1": (p1, 100000), "p2": (p2, 20000), "p3": (lambda _: p3(), None), "p4": (p4, 1000),
    "p5": (p5, 100000), "p6": (p6, 100000), "p7": (p7, 10), "p8": (lambda _: p8(), None),
}

# The small parameters explored by default (the hardware runs build the binaries with the
# same values: see pthread_diff.py).
SMALL = ["p1:2", "p1:3", "p2:2", "p2:3", "p3", "p4:2", "p5:1", "p5:2", "p5:3", "p6:2", "p6:3",
         "p7:2", "p7:3", "p8"]


def run(spec):
    name, _, param = spec.partition(":")
    mk, _default = PROGRAMS[name]
    code = mk(int(param) if param else None)
    return explore(code)


def main(argv):
    as_json = "--json" in argv
    specs = [a for a in argv if not a.startswith("--")] or SMALL
    report = {}
    for spec in specs:
        r = run(spec)
        r.pop("examples")
        report[spec] = r
        if not as_json:
            print(f"{spec}: {r['configs']} configurations; outcomes {r['outcomes']}; "
                  f"faults {r['faults']}; races {r['races']} (write races {r['write_races']}); "
                  f"stuck {r['stuck']}", flush=True)
    if as_json:
        json.dump(report, sys.stdout, indent=1)
        print()


if __name__ == "__main__":
    main(sys.argv[1:])
