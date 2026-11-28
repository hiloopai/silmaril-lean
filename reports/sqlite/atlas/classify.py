"""Reviewable classification rules for the pinned SQLite amalgamation."""
from collections import defaultdict, deque


# Section labels are from SQLite's amalgamation generator. Match whole labels
# so new or renamed sections remain visible as unclassified.
REGIONS = {
    "Tokenizer": "tokenize.c keywordhash.h complete.c",
    "Parser": "parse.c parse.h",
    "Name resolution and expressions": "walker.c resolve.c expr.c",
    "Planner and SQL code generation": (
        "alter.c analyze.c attach.c build.c delete.c fkey.c insert.c pragma.c "
        "pragma.h select.c trigger.c update.c upsert.c vacuum.c where.c "
        "wherecode.c whereexpr.c whereInt.h window.c"
    ),
    "Virtual machine": (
        "vdbe.c vdbe.h vdbeInt.h vdbeapi.c vdbeaux.c vdbeblob.c vdbemem.c "
        "vdbesort.c vdbetrace.c vdbevtab.c opcodes.c opcodes.h"
    ),
    "SQL builtins": "func.c date.c json.c",
    "B-tree": "btree.c btree.h btreeInt.h btmutex.c",
    "Pager and journal": "pager.c pager.h memjournal.c wal.c wal.h",
    "Page cache": "pcache.c pcache.h pcache1.c",
    "VFS": "os.c os.h os_common.h os_setup.h os_unix.c os_win.c os_win.h os_kv.c memdb.c",
    "Allocator": "malloc.c mem0.c mem1.c mem2.c mem3.c mem5.c",
    "Concurrency": "mutex.c mutex.h mutex_noop.c mutex_unix.c mutex_w32.c notify.c threads.c",
    "Virtual tables and extensions": (
        "fts3.c fts3.h fts3Int.h fts3_aux.c fts3_expr.c fts3_hash.c fts3_hash.h "
        "fts3_icu.c fts3_porter.c fts3_snippet.c fts3_tokenize_vtab.c fts3_tokenizer.c "
        "fts3_tokenizer.h fts3_tokenizer1.c fts3_unicode.c fts3_unicode2.c fts3_write.c "
        "fts5.c fts5.h rtree.c rtree.h sqlite3rtree.h sqliteicu.h geopoly.c icu.c "
        "sqlite3rbu.c sqlite3rbu.h sqlite3session.c sqlite3session.h dbstat.c dbpage.c "
        "carray.c stmt.c vtab.c"
    ),
    "Connection and public API": (
        "main.c prepare.c legacy.c callback.c auth.c table.c backup.c status.c "
        "global.c ctime.c loadext.c sqlite3ext.h sqlite3.h"
    ),
    "Utilities and portability": (
        "util.c utf.c printf.c random.c bitvec.c rowset.c hash.c hash.h fault.c "
        "treeview.c hwtime.h sqliteInt.h sqliteLimit.h msvc.h vxworks.h"
    ),
}
REGION_BY_SECTION = {
    section: region for region, sections in REGIONS.items() for section in sections.split()
}
assert len(REGION_BY_SECTION) == sum(len(sections.split()) for sections in REGIONS.values())

# These links identify generator inputs, not the originating line of a function.
GENERATED = {
    "sqlite3.c": ("tool/mksqlite3c.tcl",),
    "sqlite3.h": ("src/sqlite.h.in", "tool/mksqlite3h.tcl"),
    "ctime.c": ("tool/mkctimec.tcl",),
    "parse.c": ("src/parse.y", "tool/lemon.c", "tool/lempar.c"),
    "parse.h": ("src/parse.y", "tool/lemon.c", "tool/lempar.c"),
    "keywordhash.h": ("tool/mkkeywordhash.c",),
    "opcodes.c": ("src/vdbe.c", "tool/mkopcodeh.tcl", "tool/mkopcodec.tcl"),
    "opcodes.h": ("src/parse.y", "src/vdbe.c", "tool/mkopcodeh.tcl"),
    "pragma.h": ("tool/mkpragmatab.tcl",),
    "fts5.c": (
        "ext/fts5/tool/mkfts5c.tcl", "ext/fts5/fts5parse.y",
        "ext/fts5/fts5_main.c", "tool/lemon.c", "tool/lempar.c",
    ),
}

# Exact external roles. Every external call still has unknown closure.
EXTERNAL_ROLES = {
    "allocator": set("malloc calloc realloc free aligned_alloc".split()),
    "buffer": set(
        "memcpy memmove memset memcmp memchr strlen strnlen strcmp strncmp strcpy "
        "strncpy __builtin_memcpy __builtin_memmove __builtin_memset".split()
    ),
    "vfs": set(
        "open open64 close read write pread pread64 pwrite pwrite64 lseek lseek64 "
        "stat stat64 fstat fstat64 lstat lstat64 fsync fdatasync ftruncate "
        "ftruncate64 unlink getcwd access mmap munmap readlink chmod fchmod "
        "getenv getpid geteuid".split()
    ),
    "locks": set(
        "pthread_mutex_init pthread_mutex_destroy pthread_mutex_lock "
        "pthread_mutex_trylock pthread_mutex_unlock flock fcntl fcntl64".split()
    ),
}

# Classify internal boundary references by narrowly scoped entry points.
INTERNAL_ROLES = {
    "allocator": set(
        "sqlite3Malloc sqlite3MallocZero sqlite3Realloc sqlite3ReallocOrFree "
        "sqlite3DbMallocRaw sqlite3DbMallocRawNN sqlite3DbMallocZero "
        "sqlite3DbRealloc sqlite3DbReallocOrFree sqlite3DbFree sqlite3DbFreeNN "
        "sqlite3_malloc sqlite3_malloc64 sqlite3_realloc sqlite3_realloc64 "
        "sqlite3_free sqlite3MemMalloc sqlite3MemRealloc sqlite3MemFree".split()
    ),
    "vfs": set(
        "sqlite3OsOpen sqlite3OsOpenMalloc sqlite3OsClose sqlite3OsCloseFree "
        "sqlite3OsRead sqlite3OsWrite sqlite3OsFileSize sqlite3OsTruncate "
        "sqlite3OsSync sqlite3OsLock sqlite3OsUnlock sqlite3OsCheckReservedLock "
        "sqlite3OsFileControl sqlite3OsDelete sqlite3OsAccess sqlite3OsFullPathname "
        "sqlite3OsShmMap sqlite3OsShmLock sqlite3OsShmBarrier sqlite3OsShmUnmap".split()
    ),
    "locks": set(
        "sqlite3_mutex_alloc sqlite3_mutex_free sqlite3_mutex_enter "
        "sqlite3_mutex_try sqlite3_mutex_leave sqlite3BtreeEnter sqlite3BtreeLeave "
        "sqlite3OsLock sqlite3OsUnlock sqlite3OsShmLock".split()
    ),
}

PRIORITIES = [
    ("1", "Scalar and bounded-buffer utilities", "sqlite3VarintLen, sqlite3Get4byte, sqlite3Put4byte",
     "Start with explicit byte widths, shift ranges and input/output bounds."),
    ("2", "Tokenizer and row decoding", "sqlite3GetToken, sqlite3VdbeSerialGet",
     "Model token lookahead, buffer extent and Mem ownership before following VM dispatch."),
    ("3", "B-tree and page cache", "sqlite3BtreePayload, sqlite3PagerGet",
     "Track cursor state, page pinning, sharing and error paths."),
    ("4", "VFS, locking and callbacks", "sqlite3OsRead, sqlite3_mutex_enter",
     "Give method tables and externally supplied behavior explicit contracts."),
]


def local_classification(function, by_id):
    evidence = defaultdict(set)
    shapes = set(function["type_shapes"])
    features = set(function["features"])
    if "byte_element" in shapes:
        evidence["buffer"].add("byte-element pointer or array type")
    if {"member_access", "write_member"} & features or "record" in shapes:
        evidence["object"].add("record type or member access")
    if "volatile" in shapes or "atomic" in shapes:
        evidence["unknown"].add("volatile or atomic type")
    if function["nonlocal_objects"]:
        evidence["globals"].add("static-duration or extern object reference")
    if "inline_asm" in features:
        evidence["unknown"].add("inline assembly")
    if "function_pointer" in shapes:
        evidence["callback"].add("function-pointer type")
    for tag, names in INTERNAL_ROLES.items():
        if function["name"] in names:
            evidence[tag].add("named SQLite boundary: " + function["name"])
    for call in function["calls"]:
        if call["kind"] == "indirect":
            evidence["callback"].add("indirect call")
            evidence["unknown"].add("unresolved indirect call")
        elif call["kind"] != "sqlite_definition":
            evidence["unknown"].add("direct call outside the SQLite body graph")
            for tag, names in EXTERNAL_ROLES.items():
                if call["callee"]["name"] in names:
                    evidence[tag].add("external call: " + call["callee"]["name"])
        else:
            target = by_id[call["target_id"]]["name"]
            for tag, names in INTERNAL_ROLES.items():
                if target in names:
                    evidence[tag].add("direct boundary call: " + target)

    # Independent of reachability. E.g. a pointer-dense body can be in an
    # ordinary C fragment while a separately modeled callee touches the VFS.
    if {"inline_asm", "statement_expression"} & features:
        fragment = "compiler_extension"
    elif "unknown" in evidence:
        fragment = "opaque_boundary"
    elif {"object", "globals", "callback"} & evidence.keys():
        fragment = "object_or_state"
    elif {"pointer", "array_or_vector"} & shapes:
        fragment = "pointer_or_array"
    else:
        fragment = "scalar"
    if (
        fragment == "scalar" and not evidence and not function["calls"]
        and function["body"] and not ({"variadic_function", "explicit_address_of"} & features)
    ):
        evidence["pure_candidate"].add("scalar leaf by the recorded syntax")
    return fragment, {tag: sorted(notes) for tag, notes in sorted(evidence.items())}


def propagate(functions):
    """Compute a least fixed point on SQLite direct edges, including cycles."""
    by_id = {function["id"]: function for function in functions}
    predecessors = defaultdict(set)
    callees = {}
    for function in functions:
        identity = function["id"]
        fragment, evidence = local_classification(function, by_id)
        function["fragment"] = fragment
        function["local_tag_evidence"] = evidence
        callees[identity] = {
            call["target_id"] for call in function["calls"]
            if call["kind"] == "sqlite_definition"
        }
        for callee in callees[identity]:
            predecessors[callee].add(identity)
    local_effects = {
        identity: set(function["local_tag_evidence"]) - {"pure_candidate"}
        for identity, function in by_id.items()
    }
    closure = {identity: tags.copy() for identity, tags in local_effects.items()}
    queue = deque(by_id)
    queued = set(by_id)
    while queue:
        callee = queue.popleft()
        queued.remove(callee)
        for caller in predecessors[callee]:
            if closure[callee] - closure[caller]:
                closure[caller].update(closure[callee])
                if caller not in queued:
                    queued.add(caller)
                    queue.append(caller)
    for identity, function in by_id.items():
        from_callees = set().union(*(closure[edge] for edge in callees[identity]))
        function["reachable_callee_effect_tags"] = sorted(from_callees)
        function["propagated_only_effect_tags"] = sorted(from_callees - local_effects[identity])
