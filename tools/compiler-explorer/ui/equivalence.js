// Actual binary-to-binary obligations, kept separate from source/Core and fixtures.
const $ = id => document.getElementById(id);
function el(tag, value) { const e=document.createElement(tag); if(value!==undefined)e.textContent=String(value);return e; }
function link(label,href) { const a=el('a',label);a.href=href;return a; }
async function json(path) { const r=await fetch(path);if(!r.ok)throw new Error('missing binary evidence: '+r.status);return r.json(); }
async function text(r) {
  const response=await fetch(r.static_path);if(!response.ok)throw new Error('missing binary context');
  const data=await response.arrayBuffer();const digest=[...new Uint8Array(await crypto.subtle.digest('SHA-256',data))].map(b=>b.toString(16).padStart(2,'0')).join('');
  if(digest!==r.sha256||data.byteLength!==r.size)throw new Error('binary context identity mismatch');
  return new TextDecoder('utf-8',{fatal:true}).decode(data);
}
export async function initEquivalence() {
  const wanted=new URLSearchParams(location.search).get('equivalence');
  const response=await fetch('api/equivalences/index.json');
  if(!response.ok){if(wanted)throw new Error('no binary problem export');return false;}
  const listing=await response.json();
  const picker=$('binary-statement');
  for(const p of listing)picker.append(new Option(`${p.function_symbol} · ${p.declaration.split('.').at(-1)} · UNPROVED`,p.declaration));
  picker.onchange=()=>{if(picker.value)location.search='?equivalence='+encodeURIComponent(picker.value);};
  if(!wanted)return false;
  const entry=listing.find(p=>p.declaration===wanted);if(!entry)throw new Error('unregistered binary problem');
  const p=await json(entry.static_path);
  if(p.status!=='UNPROVED'||p.kind!=='functional_equivalence'||p.declaration!==wanted||p.proof_evidence!==null||p.source_refinement_assumed!==false||p.interactive_compilation!==false)throw new Error('unexpected binary problem status');
  picker.value=wanted;document.querySelector('.pickers').hidden=true;
  document.querySelector('h1 .sub').textContent='actual ELF ↔ ELF · contextual equivalence obligation · UNPROVED';
  const git=path=>`https://github.com/hiloopai/silmaril-lean/blob/${p.revision}/${path.split('/').map(encodeURIComponent).join('/')}`;
  const mutation=p.pair.profile==='cjson-interior-detach-v1';
  const render=a=>`${a.role.toUpperCase()} · ${a.path}\nELF sha256 ${a.sha256}\n${p.function_symbol} @ 0x${a.address.toString(16)} · ${a.size} bytes · file offset ${a.file_offset}\n${a.bytes_hex}\nFunction bytes sha256 ${a.code_sha256}\nPrivate writable stack: ${a.frame} bytes below entry RSP; ${mutation ? "exact four pointer words may change; all unrelated memory preserved" : "all other memory preserved"}\n${a.identity_check}`;
  $('src-title').textContent='Left actual ELF function';$('tgt-title').textContent='Right actual ELF function';
  $('src').textContent=render(p.artifacts[0]);$('tgt').textContent=render(p.artifacts[1]);
  const traversal=p.pair.profile==='cjson-finite-list-v1';
  const bytePredicate=p.pair.profile==='darkhttpd-byte-predicate-v1';
  const identifier=p.pair.profile==='legacy-tinycc-isid-v1';
  const selection=$('selection');selection.replaceChildren(el('h2','Contextual binary-equivalence problem'),el('strong','UNPROVED'),el('pre',p.declaration),
    el('p',bytePredicate ? 'Both actual byte predicates must admit joint entries for every unsigned byte and return equal actual EAX low32 values at their first System V returns. Arbitrary upper56 RDI bits, caller registers, flags and memory are admitted. Both ABI returns and caller memory/mappings outside exact12/0 private frames are obligations. No expected result, equality, refinement, safety or termination is an entry assumption.' : mutation ? 'Both actual interior-node detachments must admit joint entries for every declared five-object address/payload input and return equal actual pointer values at their first System V returns. Exact four final pointer words, unrelated caller bytes and complete mapping metadata must be preserved outside24/0 private frames. No equality, desired heap, source refinement or termination is assumed.' : traversal ? 'Both actual traversals must admit joint entries for every declared finite-list address/payload input and return the same actual low32 value at their first System V returns. Caller heap and complete mapping metadata must be preserved outside the exact private stack frames. No expected count, equality, source refinement or termination is an entry assumption.' : identifier ? 'Both actual functions must independently admit every signed32 input and return the explicit ASCII identifier predicate (a-z, A-Z or underscore), including for negative inputs. Both first-return ABI and original16-byte frame contracts are obligations. No source refinement or desired equality is assumed.' : `Both functions must independently be enterable and return signed int32 ${p.pair.value} at their first System V return, preserving callee-saved state and observable memory. No source refinement or desired equality is assumed.`));
  selection.append(link('Corpus catalog','../#/corpus'),document.createTextNode(' · '),link('Compiler integration','../#/compiler'),document.createTextNode(' · '),link('Exact Lean statement',git(p.root.replaceAll('.','/')+'.lean')));
  for(const a of p.artifacts){const row=el('p');row.append(el('strong',a.role+' · '),link('Corpus artifact','../#/corpus-artifact/'+encodeURIComponent(a.id)),document.createTextNode(' · '),link('Corpus function','../#/corpus-functions/'+encodeURIComponent(a.id)+'?symbol='+encodeURIComponent(p.function_symbol)),document.createTextNode(' · '),link('ELF in Git',git(a.path)));selection.append(row);}
  $('questions').replaceChildren(el('h2','Nonvacuous obligations'),el('p',bytePredicate ? 'All256 byte inputs, with DIL low8 argument and EAX low32 result. Shared initial memory includes both disjoint actual code excerpts. O0 branches/spills; Og uses actual LEA/byte comparisons/SETA/SETE/OR/MOVZX. Joint entry existence, both first returns, callee-saved ABI and preservation of unrelated caller bytes and complete region metadata are obligations. No globals, heap, callees or I/O effects.' : mutation ? 'Five aligned/disjoint64-byte objects; arbitrary admissible addresses and320 payload bytes with actual interior-list links. Shared initial memory includes both code excerpts. Joint entries, both first returns, ABI, exact final predecessor.next/successor.prev/item.next/item.prev bytes and preservation of all unrelated memory are obligations. Sse9 executes the actual128-bit zeroing/store; XMM is SysV caller-clobbered. No arbitrary hidden heap effects or C provenance interpretation.' : traversal ? 'Null or finite acyclic lists0..64; arbitrary admissible aligned heap base and arbitrary unrelated payload bytes. Only real child/next pointer fields are constrained. Shared initial memory includes both disjoint actual code excerpts. Joint entry existence, both first returns, ABI preservation, exact32/0 private frames and complete caller memory/region preservation are obligations. No callee or caller-heap write is permitted.' : 'Both System V entry sets must exist. Both total first-return contracts, ABI preservation and exact memory frames must hold. CodeAt facts bind the actual images; identity is separate from semantic equivalence. No callee, heap, global or I/O effects are permitted.'));
  const provenance=$('provenance');provenance.replaceChildren(el('h2','Build compatibility and exclusions'),el('pre',JSON.stringify(p.excluded,null,2)),link('Pinned pair manifest',git(p.manifest.path)),el('p','Manifest sha256 '+p.manifest.sha256),link('Measured Lean check',git(p.run_receipt)),el('p','Public revision '+p.revision));
  for(const a of p.artifacts){
    const span=a.source.definitions[p.function_symbol];
    provenance.append(el('h3',a.role+' observed build'),el('pre',span.text),el('pre',JSON.stringify({build:a.build,receipt:a.receipt,source:a.source.path,source_sha256:a.source.sha256,definition:span},null,2)),link(p.pair.profile?.startsWith('legacy-')?'Included upstream source (provenance only)':'Actual source',git(a.source.path)),document.createTextNode(' · '),link('Build receipt',git(a.receipt.path)));
  }
  $('assumptions').replaceChildren(el('h2','Limits'));for(const limit of p.limits)$('assumptions').append(el('p',limit));
  const evidence=$('corpus-evidence');evidence.hidden=false;evidence.replaceChildren(el('h2','Actual byte bindings, ABI and memory contracts'));
  for(const r of p.modules){const d=el('details');d.dataset.contextModule=r.path;d.append(el('summary',r.path+' · sha256 '+r.sha256),el('pre',await text(r)));evidence.append(d);}
  $('status').textContent=`${listing.length} binary-equivalence viewer problems · UNPROVED · no semantic proof · no interactive compilation`;
  document.body.dataset.equivalenceDeclaration=p.declaration;
  return true;
}
