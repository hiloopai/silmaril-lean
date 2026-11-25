import { createHash } from 'node:crypto';
import { readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { prettySexp } from './ui/view.js';

const kinds = {
  'typed-ail': (tag) => /^Ail[ES]/.test(tag),
  core: (tag) => ['Pexpr', 'Expr', 'Action'].includes(tag),
  compact: (tag) => ['lit', 'slot', 'add', 'gt', 'return', 'let', 'if'].includes(tag),
  'compact-origins': () => false,
};

function measure(bytes, kind) {
  const text = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
  const pretty = prettySexp(text, kind === 'compact' ? 64 : 88);
  if (pretty === null) throw new Error(`malformed ${kind} S-expression`);
  const tokens = text.matchAll(/"(?:\\[\s\S]|[^"\\])*"|\(([^\s()]+)|\)/g);
  const stack = [];
  let lists = 0, semantic = 0, procedure = 0, inProcedure = 0;
  const metadata = {};
  for (const [token, tag] of tokens) {
    if (token === ')') {
      if (stack.pop() === 'Proc') inProcedure--;
    } else if (tag) {
      stack.push(tag);
      lists++;
      if (tag === 'Proc') inProcedure++;
      if (kinds[kind](tag)) {
        semantic++;
        if (inProcedure) procedure++;
      }
      if (['Symbol', 'Ctype', 'Aloc', 'Astd', 'GenRValueType', 'GenLValueType',
        '$loc_region', '$loc_point', '$loc_unknown', 'origin'].includes(tag)) {
        metadata[tag] = (metadata[tag] ?? 0) + 1;
      }
    }
  }
  return { sha256: createHash('sha256').update(bytes).digest('hex'),
    bytes: bytes.length, prettyBytes: Buffer.byteLength(pretty), expandedTaggedLists: lists,
    semanticOccurrences: semantic, ...(kind === 'core' && { inProcedures: procedure }), metadata };
}

const results = (process.argv.slice(2).length ? process.argv.slice(2) :
  ['straight', 'branch', 'loop'].map((directory) => `examples/compiles-to/${directory}`)).map((directory) => {
  const counts = { directory };
  for (const kind of Object.keys(kinds)) {
    const path = join(directory, `${kind}.sexp`);
    counts[kind] = existsSync(path) ? measure(readFileSync(path), kind) : null;
  }
  return counts;
});
console.log(JSON.stringify(results, null, 2));
