// Exercise the same static compiler payloads Pages deploys, through its project navigation.
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {get} from 'node:http';
import path from 'node:path';
import fs from 'node:fs';
const pw=await import(process.env.PLAYWRIGHT_CORE||'/usr/local/lib/node_modules/playwright-core/index.mjs');
const site=path.resolve(process.argv[2]), shots=path.resolve(process.argv[3]);
fs.mkdirSync(shots,{recursive:true});
const server=spawn('python3',['-I',new URL('./pages_server.py',import.meta.url).pathname,'--root',site,'--port','8791','--log',path.join(shots,'compiler-requests.jsonl')],{stdio:'ignore'});
const chrome='/opt/ms-playwright/chromium-1248/chrome-linux64/chrome';
const browser=await pw.chromium.launch({executablePath:process.env.CHROME||(fs.existsSync(chrome)?chrome:undefined),args:['--no-sandbox']});
try {
  const page=await browser.newPage();
  const base='http://127.0.0.1:8791';
  // The local Python HTTP/1.0 server closes each response. Node24 fetch/Undici
  // can assert in Parser.finish on this readiness request, even with a drained
  // body. Use the standard HTTP client and wait for the complete response.
  for(let i=0;i<40;i++){
    try{
      const ready=await new Promise((resolve,reject)=>{
        get(base+'/index.html',response=>{
          response.resume();
          response.on('end',()=>resolve(response.statusCode===200));
          response.on('error',reject);
        }).on('error',reject);
      });
      if(ready)break;
    }catch{}
    await new Promise(resolve=>setTimeout(resolve,100));
  }
  await page.goto(base+'/index.html#/compiler');
  const link=page.getByRole('link',{name:'Open the source ↔ target viewer',exact:true});
  await link.waitFor({timeout:60000}); await link.click();
  await page.waitForFunction(()=>document.querySelectorAll('#program option').length>0);
  const listing=JSON.parse(fs.readFileSync(path.join(site,'compiler/api/problems.json'),'utf8'));
  assert.ok(listing.length>0,'actual compiler fixtures exported');
  await page.selectOption('#program','compiles-to/straight');
  await page.waitForFunction(()=>document.querySelector('#src-title').textContent.includes('straight'));
  assert.ok(await page.locator('#src .line').count()>1,'actual source text');
  assert.ok(await page.locator('#tgt .line').count()>1,'actual target listing');
  await page.selectOption('#mode','semantic');
  await page.waitForFunction(()=>document.querySelector('#status').textContent.includes('semantic link'));
  assert.match(await page.locator('body').innerText(),/not every corpus function/);
  await page.screenshot({path:path.join(shots,'compiler.png'),fullPage:true});
  await page.getByRole('link',{name:'Corpus catalog',exact:true}).click();
  await page.waitForFunction(()=>document.querySelector('#corpus-count')?.textContent.includes('matching artifacts'),{timeout:60000});
  assert.match(await page.locator('#main').innerText(),/16 registered function-equivalence statements · 16 connected binary viewer entries/);
  console.log('PASS published-shape compiler viewer: project navigation, static payloads, source/target/semantic modes and corpus return');
  // Real corpus statements use their own registry-backed, uniformly UNPROVED view.
  const corpusIndex=JSON.parse(fs.readFileSync(path.join(site,'compiler/api/corpus/index.json'),'utf8'));
  assert.equal(corpusIndex.length,32);
  assert.ok(corpusIndex.every(p=>p.status==='UNPROVED'));
  const cases=[
    {"symbol": "cJSON_InsertItemInArray", "declaration": "Silmaril.Elf.Corpus.CjsonInsert.Context.Task.compilesTo", "address": "0x5eca", "bytes": "55 48 89 e5 48 83 ec 28 48 89 7d e8 89 75 e4 48 89 55 d8 48 c7 45 f8 00 00 00 00 83 7d e4 00 78 07 48 83 7d d8 00 75 0a b8 00 00 00 00 e9 ae 00 00 00 8b 45 e4 48 63 d0 48 8b 45 e8 48 89 d6 48 89 c7 e8 c2 f4 ff ff 48 89 45 f8 48 83 7d f8 00 75 15 48 8b 55 d8 48 8b 45 e8 48 89 d6 48 89 c7 e8 40 f7 ff ff eb 79 48 8b 45 e8 48 8b 40 10 48 39 45 f8 74 14 48 8b 45 f8 48 8b 40 08 48 85 c0 75 07 b8 00 00 00 00 eb 57 48 8b 45 d8 48 8b 55 f8 48 89 10 48 8b 45 f8 48 8b 50 08 48 8b 45 d8 48 89 50 08 48 8b 45 f8 48 8b 55 d8 48 89 50 08 48 8b 45 e8 48 8b 40 10 48 39 45 f8 75 0e 48 8b 45 e8 48 8b 55 d8 48 89 50 10 eb 0f 48 8b 45 d8 48 8b 40 08 48 8b 55 d8 48 89 10 b8 01 00 00 00 c9 c3", "source": "02ab0ecd20b076cab3def2fc07074476993b79ee38532e1903507c44891086a0", "core": "eb22ccb1326729d07ff9f384a9f3241f2ab44299911d06466a4a6e4904316854", "offset": 140177, "length": 1571, "tu": "3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf", "context": "callerUpdate i before.memory after.memory", "insertion": true, "helpers": [{"symbol": "get_array_item", "address": 21459, "size": 84, "file_offset": 21459, "bytes_hex": "55 48 89 e5 48 89 7d e8 48 89 75 e0 48 c7 45 f8 00 00 00 00 48 83 7d e8 00 75 07 b8 00 00 00 00 eb 30 48 8b 45 e8 48 8b 40 10 48 89 45 f8 eb 10 48 83 6d e0 01 48 8b 45 f8 48 8b 00 48 89 45 f8 48 83 7d f8 00 74 07 48 83 7d e0 00 75 e2 48 8b 45 f8 5d c3", "code_sha256": "83a93716e5f22ed741d2bc1db8042b5550173564c8cfe257cf156eba339a4330", "identity_check": "ELF symbol + executable PT_LOAD bytes checked by Python; kernel CodeAt lives in the linked Lean modules"}, {"symbol": "suffix_object", "address": 21933, "size": 38, "file_offset": 21933, "bytes_hex": "55 48 89 e5 48 89 7d f8 48 89 75 f0 48 8b 45 f8 48 8b 55 f0 48 89 10 48 8b 45 f0 48 8b 55 f8 48 89 50 08 90 5d c3", "code_sha256": "7bb9605318ee7e45e38154c9acbc3a70cf2ed8516bc8bdb560a7ed7815e9b5d0", "identity_check": "ELF symbol + executable PT_LOAD bytes checked by Python; kernel CodeAt lives in the linked Lean modules"}, {"symbol": "add_item_to_array", "address": 22127, "size": 170, "file_offset": 22127, "bytes_hex": "55 48 89 e5 48 83 ec 20 48 89 7d e8 48 89 75 e0 48 c7 45 f8 00 00 00 00 48 83 7d e0 00 74 11 48 83 7d e8 00 74 0a 48 8b 45 e8 48 3b 45 e0 75 07 b8 00 00 00 00 eb 71 48 8b 45 e8 48 8b 40 10 48 89 45 f8 48 83 7d f8 00 75 25 48 8b 45 e8 48 8b 55 e0 48 89 50 10 48 8b 45 e0 48 8b 55 e0 48 89 50 08 48 8b 45 e0 48 c7 00 00 00 00 00 eb 34 48 8b 45 f8 48 8b 40 08 48 85 c0 74 27 48 8b 45 f8 48 8b 40 08 48 8b 55 e0 48 89 d6 48 89 c7 e8 ab fe ff ff 48 8b 45 e8 48 8b 40 10 48 8b 55 e0 48 89 50 08 b8 01 00 00 00 c9 c3", "code_sha256": "847da6a0f670a132bebd6214cf309ec9a92c511d27d267fc9f67189309409f07", "identity_check": "ELF symbol + executable PT_LOAD bytes checked by Python; kernel CodeAt lives in the linked Lean modules"}]},
    {"symbol": "cJSON_GetArrayItem", "declaration": "Silmaril.Elf.Corpus.CjsonArrayItem.Context.Task.compilesTo", "address": "0x5427", "bytes": "55 48 89 e5 48 83 ec 10 48 89 7d f8 89 75 f4 83 7d f4 00 79 07 b8 00 00 00 00 eb 15 8b 45 f4 48 63 d0 48 8b 45 f8 48 89 d6 48 89 c7 e8 7b ff ff ff c9 c3", "source": "c2de1199e9c8b0b2bc57d49490a269be893b34893e99f8c0a9d564032801a353", "core": "12735aa82853ce768a8b02641594fc70ee57ac18545a338ba621f43cd19314cf", "offset": 120649, "length": 1348, "tu": "3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf", "context": "callerPreserved", "caller": true, "helperBytes": "55 48 89 e5 48 89 7d e8 48 89 75 e0 48 c7 45 f8 00 00 00 00 48 83 7d e8 00 75 07 b8 00 00 00 00 eb 30 48 8b 45 e8 48 8b 40 10 48 89 45 f8 eb 10 48 83 6d e0 01 48 8b 45 f8 48 8b 00 48 89 45 f8 48 83 7d f8 00 74 07 48 83 7d e0 00 75 e2 48 8b 45 f8 5d c3", "helperHash": "83a93716e5f22ed741d2bc1db8042b5550173564c8cfe257cf156eba339a4330"},
    {"symbol": "cJSON_DetachItemViaPointer", "declaration": "Silmaril.Elf.Corpus.CjsonDetach.Context.Task.compilesTo", "address": "0x5cac", "bytes": "55 48 89 e5 48 89 7d f8 48 89 75 f0 48 83 7d f8 00 74 22 48 83 7d f0 00 74 1b 48 8b 45 f8 48 8b 40 10 48 39 45 f0 74 17 48 8b 45 f0 48 8b 40 08 48 85 c0 75 0a b8 00 00 00 00 e9 99 00 00 00 48 8b 45 f8 48 8b 40 10 48 39 45 f0 74 12 48 8b 45 f0 48 8b 40 08 48 8b 55 f0 48 8b 12 48 89 10 48 8b 45 f0 48 8b 00 48 85 c0 74 13 48 8b 45 f0 48 8b 00 48 8b 55 f0 48 8b 52 08 48 89 50 08 48 8b 45 f8 48 8b 40 10 48 39 45 f0 75 11 48 8b 45 f0 48 8b 10 48 8b 45 f8 48 89 50 10 eb 20 48 8b 45 f0 48 8b 00 48 85 c0 75 14 48 8b 45 f8 48 8b 40 10 48 8b 55 f0 48 8b 52 08 48 89 50 08 48 8b 45 f0 48 c7 40 08 00 00 00 00 48 8b 45 f0 48 c7 00 00 00 00 00 48 8b 45 f0 5d c3", "source": "dc3e68189a20294a404f896ac3611eae6a77c44c23bc89991c459bc590dab8a8", "core": "1e54f1805c02475ea193763bade7a524928b62e87cd99685ac0e6b28696b3e7d", "offset": 136693, "length": 2069, "tu": "3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf", "context": "returnMatches", "detachment": true},
    {"symbol": "suffix_object", "declaration": "Silmaril.Elf.Corpus.CjsonSuffix.Context.Task.compilesTo", "address": "0x55ad", "bytes": "55 48 89 e5 48 89 7d f8 48 89 75 f0 48 8b 45 f8 48 8b 55 f0 48 89 10 48 8b 45 f0 48 8b 55 f8 48 89 50 08 90 5d c3", "source": "43b84fd08dec2b8a7c056cc15e6203de0789e6b1bb7d2eb41eaca7c30fecd729", "core": "30c94a6ba01e474846d0d8f84b787e008844d8271054c58ef66af0070f3032ca", "offset": 125337, "length": 101, "tu": "3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf", "context": "expectedMemory", "mutation": true},
    {"symbol": "cJSON_GetArraySize", "declaration": "Silmaril.Elf.Corpus.CjsonArraySize.Context.Task.compilesTo", "address": "0x4090", "bytes": "48 85 ff 74 1b 48 8b 57 10 48 85 d2 74 12 31 c0 48 8b 12 48 83 c0 01 48 85 d2 75 f4 c3 0f 1f 00 31 c0 c3", "source": "e04af85a502ef41b93c99b3622720e0b9a82c47f2514efe85e9f32c89aeabf4d", "core": "b6f3ff0c2e350da276e6b4843368347f1ed5abf4b3a8ac36b8b9cbce5f26aa03", "offset": 119860, "length": 787, "tu": "3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf", "context": "Fin 65", "traversal": true},
    {"symbol": "needs_logencoding", "declaration": "Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Context.Task.compilesTo", "address": "0x503e", "bytes": "55 48 89 e5 89 f8 88 45 fc 80 7d fc 1f 76 0c 80 7d fc 7e 77 06 80 7d fc 22 75 07 b8 01 00 00 00 eb 05 b8 00 00 00 00 5d c3", "source": "ce9cbac8610df904f38a98b3db86d3b36cf1c22c286eaafdf2f6f85cf85ad749", "core": "8afeef037d7c66a599f4630f3fadceb726bf862ed47d4dd727a02d57b9a45bb7", "offset": 175434, "length": 110, "tu": "8b90d8bdc55576387362eef17ecc31fc1c0fde495ef73b2950bf10e1ad19ea82", "context": "layout.size == 1", "bytePredicate": true},
    {symbol:'cJSON_IsNull',declaration:'Silmaril.Elf.Corpus.CjsonTypePredicates.Context.Task.isNull',address:'0x5460',bytes:'48 85 ff 74 0b 31 c0 80 7f 18 04 0f 94 c0 c3 90 31 c0 c3',source:'c09e52545b71dcc83e603c21a65821a692bffbc4cb7fd3913a6660fc0fc942ab',core:'5567495bd982a19d43237278e2ce8455609fbf87d10f8c863c92b0f13243593a',offset:37470,length:211,tu:'3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf',context:'layout.size == 64'},
    {symbol:'_mi_os_large_page_size',declaration:'Silmaril.Elf.Corpus.MimallocOsGlobals.Context.Task.largePageSize',address:'0xf240',bytes:'48 8b 05 a1 38 01 00 48 85 c0 48 0f 44 05 8e 38 01 00 c3',source:'fd758ed6f378c0485f4a5b4cd7f4f177d1480ab5dca77ebe25ec9e16781d9364',core:'7cd269ca50b04f09cae919d75e379a97a491c07d6cd5f9a208b1c843edba492f',offset:277639,length:258,tu:'4e33d7c4e78fd242acba9caef4964217e3df3ef5f8138bd15a8af33bf40805e7',context:'layout.size == 48'},
    {symbol:'_mi_os_has_overcommit',declaration:'Silmaril.Elf.Corpus.MimallocOsFlags.Context.Task.overcommit',address:'0xf210',bytes:'0f b6 05 f1 38 01 00 c3',source:'2e3f89c48db58c79a63cee47c143bdd05a6ef81fbae56ca41760e70292890885',core:'66bf5e95d82ee9cbd83fde17d4c0ed92571df1f4f4ecd868f96ff47a66d94434',offset:277900,length:120,tu:'4e33d7c4e78fd242acba9caef4964217e3df3ef5f8138bd15a8af33bf40805e7',context:'layout.size == 48'},
    {symbol:'sqlite3_libversion_number',declaration:'Silmaril.Elf.Corpus.SqliteBuildQueries.Context.Task.versionNumber',address:'0x13820',bytes:'b8 b1 99 2e 00 c3',source:'fa8672b63affea57a936d76b3cd7adb67b19ef336c005cf4ed5213ee1355d028',core:'a319bf961d26528a99b34a78d1074964053a36240ac652f9bbc9dce017614a0e',offset:3240508,length:54,tu:'31992f073781a1cdbd06ee2a00b2de14b62d87b5e81199dbb6a0fb7dfb7b6f1d',context:'some .int32',pureQuery:true},
    {symbol:'sqlite3_threadsafe',declaration:'Silmaril.Elf.Corpus.SqliteBuildQueries.Context.Task.threadsafe',address:'0x13830',bytes:'b8 01 00 00 00 c3',source:'fa8672b63affea57a936d76b3cd7adb67b19ef336c005cf4ed5213ee1355d028',core:'a319bf961d26528a99b34a78d1074964053a36240ac652f9bbc9dce017614a0e',offset:3240569,length:41,tu:'31992f073781a1cdbd06ee2a00b2de14b62d87b5e81199dbb6a0fb7dfb7b6f1d',context:'some .int32',pureQuery:true}
  ];
  const pageErrors=[];page.on('pageerror',e=>pageErrors.push(e.message));
  {
    const declaration='Silmaril.Elf.Corpus.SqliteGlobalVersion.Context.Task.compilesTo';
    await page.goto(base+'/compiler/?corpus='+encodeURIComponent(declaration));
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,declaration);
    assert.match(await page.locator('#selection').innerText(),/UNPROVED/);
    assert.ok((await page.locator('[data-evidence-role="Source"]').innerText()).includes('d28acc15b04eb9fe7377e76026b006d36214ad39159ee797f795bacfb0974d38'));
    assert.ok((await page.locator('[data-evidence-role="Core"]').innerText()).includes('4e0bd85c2d333bb68b1f9d3b55772375eb2a02dcbb0d1b58fa1d8a683ed4c7d4'));
    const spans=JSON.parse(await page.locator('#corpus-source-spans').innerText());
    assert.equal(spans.tu_sha256,'31992f073781a1cdbd06ee2a00b2de14b62d87b5e81199dbb6a0fb7dfb7b6f1d');
    assert.deepEqual(spans.spans.map(s=>[s.offset,s.length]),[[529,50],[3240421,64]]);
    const target=await page.locator('#tgt').innerText();
    for(const expected of ['0x13810','48 8b 05 b1 b7 0f 00 c3','Actual ELF data object','sqlite3_version @ 0xed572','33 2e 35 34 2e 31 00','Actual raw RELA @ file offset 53296','R_X86_64_GLOB_DAT','symbol index 233','GOT slot 0x10efc8','Raw GOT slot bytes 00 00 00 00 00 00 00 00 (before loader resolution)','No dynamic-loader'])assert.ok(target.includes(expected),expected);
    const context=await page.locator('#corpus-evidence').textContent();
    for(const expected of ['Initialization.prepare input','memoryUnchanged before.memory after.memory','SysV.StackBelow machine 0','returnedAddress value'])assert.ok(context.includes(expected),expected);
    assert.match(await page.locator('#assumptions').innerText(),/post-loader/);
    assert.match(await page.locator('#assumptions').innerText(),/ONLY diagnostic currentLocation/);
    await page.getByRole('link',{name:'Corpus function',exact:true}).click();
    await page.waitForFunction(()=>document.querySelector('#corpus-function-search')?.value==='sqlite3_libversion');
    await page.waitForFunction(()=>document.querySelector('#corpus-functions details'));
    await page.locator('#corpus-functions details').filter({hasText:'0x13810'}).first().locator('summary').click();
    await page.locator('#corpus-functions a[href*="'+encodeURIComponent(declaration)+'"]').click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,declaration);
    await page.getByRole('link',{name:'Corpus artifact',exact:true}).click();
    await page.waitForFunction(()=>window.explore.view==='corpus-artifact'&&!window.explore.busy);
    await page.locator('a[href*="'+encodeURIComponent(declaration)+'"]').click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,declaration);
  }
  for(const c of cases){
    await page.goto(base+'/index.html#/compiler');
    await page.getByRole('link',{name:c.symbol+' (UNPROVED)',exact:true}).click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    assert.match(await page.locator('#selection').innerText(),/UNPROVED/);
    assert.ok((await page.locator('#src').innerText()).includes(c.symbol));
    const target=await page.locator('#tgt').innerText();
    assert.ok(target.includes(c.address));assert.ok(target.includes(c.bytes));
    assert.ok((await page.locator('[data-evidence-role="Source"]').innerText()).includes(c.source));
    assert.ok((await page.locator('[data-evidence-role="Core"]').innerText()).includes(c.core));
    const spans=JSON.parse(await page.locator('#corpus-source-spans').innerText());
    assert.equal(spans.tu_sha256,c.tu);
    assert.ok(spans.spans.some(s=>s.offset===c.offset&&s.length===c.length));
    const core=await page.locator('#corpus-core').innerText();
    assert.ok(core.includes(c.symbol),'actual named Core procedure');
    const context=await page.locator('#corpus-evidence').textContent();
    assert.ok(context.includes(c.context));assert.ok(context.includes('callees := []'));
    if(c.insertion){
      assert.equal(spans.spans.length,7);
      for(const required of ['payload : Nat → BitVec 8','before.nextId ≤ id','SysV.StackBelow m 128','expectedMemory i before','heapWrite i a','Contextual','All input instances']){
        assert.ok(context.includes(required),required);
      }
      for(const helper of c.helpers){
        for(const required of [helper.symbol+' @ 0x'+helper.address.toString(16),helper.bytes_hex,helper.code_sha256])assert.ok(target.includes(required),required);
        assert.ok((await page.locator('#src').innerText()).includes(helper.symbol));
        assert.ok(core.includes(helper.symbol));
        await page.getByRole('link',{name:'Actual callee '+helper.symbol,exact:true}).click();
        await page.waitForFunction(name=>document.querySelector('#corpus-function-search')?.value===name,helper.symbol);
        await page.goto(base+'/compiler/?corpus='+encodeURIComponent(c.declaration));
        await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
      }
      const assumptions=await page.locator('#assumptions').innerText();
      for(const required of ['ConstantNull','BTy_unit','128-byte','not full-record','observation','UNPROVED'])assert.ok(assumptions.includes(required),required);
    }else if(c.caller){
      assert.equal(spans.spans.length,3);
      for(const required of ['pointerWord', 'callerPreserved', 'SysV.StackBelow m 72', 'Source.signature', 'entryOffset']){
        assert.ok(context.includes(required),required);
      }
      for(const required of ['get_array_item @ 0x53d3', '84 bytes', c.helperBytes, c.helperHash, 'not a substituted contract']){
        assert.ok(target.includes(required),required);
      }
      assert.ok((await page.locator('#src').innerText()).includes('get_array_item'));
      assert.ok(core.includes('get_array_item'));
      const assumptions=await page.locator('#assumptions').innerText();
      for(const required of ['signed32','unsigned64','72 bytes','not full-record','not proofs','arbitrary payload'])assert.ok(assumptions.includes(required),required);
      await page.getByRole('link',{name:'Actual callee get_array_item',exact:true}).click();
      await page.waitForFunction(()=>document.querySelector('#corpus-function-search')?.value==='get_array_item');
      await page.goto(base+'/compiler/?corpus='+encodeURIComponent(c.declaration));
      await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    }else if(c.detachment){
      assert.equal(spans.spans.length,2);
      for(const required of ['address : Fin 5 → Nat','payload : Fin 5 → Fin 64 → BitVec 8',
        'exactUpdate input before.memory after.memory','returnMatches input value',
        'nextExcluded := before.nextExcluded + 4','lastUsed := some 1',
        'SysV.StackBelow machine 24','some .pointer','after.core.read .rax',
        'distinct provenance pointer equality choices','after.regions = before.regions']){
        assert.ok(context.includes(required),required);
      }
      assert.match(await page.locator('#assumptions').innerText(),/arbitrary admissible addresses/);
      assert.match(await page.locator('#assumptions').innerText(),/ONLY diagnostic currentLocation/);
      assert.match(await page.locator('#assumptions').innerText(),/equal-address\/different-provenance/i);
    }else if(c.mutation){
      assert.equal(spans.spans.length,2);
      for(const required of ['exactUpdate before.memory after.memory','nextExcluded := before.nextExcluded + 2','SysV.StackBelow machine 24','heapWrite','after.regions = before.regions','[.pointer, .pointer], none']){
        assert.ok(context.includes(required),required);
      }
      assert.match(await page.locator('#assumptions').innerText(),/ONLY diagnostic currentLocation/);
      assert.match(await page.locator('#assumptions').innerText(),/Null\/alias\/dead/);
    }else if(c.traversal){
      assert.equal(spans.spans.length,3);
      for(const required of ["callerPreserved", "heapAddress 0 + 16", "nextWord", "SysV.StackBelow machine 0", "setWidth 32"]){
        assert.ok(context.includes(required),required);
      }
      assert.match(await page.locator("#assumptions").innerText(),/64/);
      assert.match(await page.locator("#assumptions").innerText(),/divergence/);
    }else if(c.bytePredicate){
      assert.ok(context.includes("[.uint8]"));assert.ok(context.includes("readonly := some .UB064_modifying_const"));
      assert.ok(context.includes("{t.memory with currentLocation := s.memory.currentLocation} = s.memory"));assert.ok(context.includes("SysV.StackBelow m 12"));
      assert.match(await page.locator("#assumptions").innerText(),/upper register bits are unspecified/);
      assert.match(await page.locator("#assumptions").innerText(),/Historical image\/header identity/);
    }else if(c.pureQuery){
      assert.ok(context.includes('t.memory.allocations = s.memory.allocations'));
      assert.ok(context.includes('t.memory.bytes = s.memory.bytes'));
      assert.ok(context.includes('setWidth 32'));
      assert.ok(context.includes('SysV.CallEntry'));
      assert.match(await page.locator('#assumptions').innerText(),/Historical image\/header identity/);
      assert.match(await page.locator('#assumptions').innerText(),/does not establish mutex/);
    }else{
      assert.ok(context.includes('Permitted .read'));assert.ok(context.includes('.UB064_modifying_const'));
    }
    assert.match(await page.locator('#assumptions').innerText(),/unproved/i);
    if(c.symbol==='_mi_os_large_page_size'){
      assert.ok((await page.locator('#src').innerText()).includes('_mi_os_page_size()'));
      assert.match(await page.locator('#assumptions').innerText(),/prototype=false/);
    }
    if(c.symbol==='_mi_os_has_overcommit'){
      assert.ok((await page.locator('#src').innerText()).includes('_Bool'));
      assert.ok(context.includes('some .boolean'));
      assert.ok(context.includes('(.integer .bool)'));
      assert.ok(context.includes('globalAddress + 40'));
      assert.ok(context.includes('globalAddress + 42'));
      assert.ok(context.includes('setWidth 8'));
      assert.match(await page.locator('#assumptions').innerText(),/Noncanonical _Bool bytes/);
    }
    await page.getByRole('link',{name:'Corpus function',exact:true}).click();
    await page.waitForFunction(v=>document.querySelector('#corpus-function-search')?.value===v,c.symbol);
    await page.waitForFunction(()=>document.querySelector('#corpus-functions details'));
    await page.locator('#corpus-functions details').filter({hasText:c.address}).first().locator('summary').click();
    await page.locator('#corpus-functions a[href*="'+encodeURIComponent(c.declaration)+'"]').click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    await page.getByRole('link',{name:'Corpus artifact',exact:true}).click();
    await page.waitForFunction(()=>window.explore.view==='corpus-artifact'&&!window.explore.busy);
    await page.locator('a[href*="'+encodeURIComponent(c.declaration)+'"]').click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    await page.screenshot({path:path.join(shots,'corpus-compiler-'+c.symbol+'.png'),fullPage:false});
  }
  assert.deepEqual(pageErrors,[]);
  await page.getByRole('link',{name:'Corpus catalog',exact:true}).first().click();
  await page.waitForFunction(()=>document.querySelector('#corpus-count')?.textContent.includes('842 matching artifacts'));
  const checked=corpusIndex.find(p=>p.function_symbol==='cJSON_IsNull');
  const payload=JSON.parse(fs.readFileSync(path.join(site,'compiler',checked.static_path),'utf8'));
  await page.route('**/'+payload.source.static_path,route=>route.fulfill({status:200,contentType:'text/plain',body:'altered source'}));
  await page.goto(base+'/compiler/?corpus='+encodeURIComponent(checked.declaration));
  await page.waitForFunction(()=>document.querySelector('#status').textContent.includes('error: corpus evidence identity mismatch'));
  assert.equal(await page.locator('body').getAttribute('data-corpus-declaration'),null);
  await page.unroute('**/'+payload.source.static_path);
  console.log('PASS actual registry corpus viewer:32 UNPROVED statements; cJSON/mimalloc/SQLite source hashes/spans, Core identities, real ELF bytes/addresses, ABI/memory/callee/UB context and bidirectional artifact/function links;842 rows retained');

  const binaryIndex=JSON.parse(fs.readFileSync(path.join(site,'compiler/api/equivalences/index.json'),'utf8'));
  assert.equal(binaryIndex.length,16);
  for(const entry of binaryIndex){
    const p=JSON.parse(fs.readFileSync(path.join(site,'compiler',entry.static_path),'utf8'));
    await page.goto(base+'/compiler/?equivalence='+encodeURIComponent(entry.declaration));
    await page.waitForFunction(d=>document.body.dataset.equivalenceDeclaration===d,entry.declaration);
    assert.match(await page.locator('#status').innerText(),/16 binary-equivalence viewer problems · UNPROVED/);
    assert.equal(await page.locator('#binary-statement option').count(),17);
    assert.match(await page.locator('#selection').innerText(),p.pair.profile==='darkhttpd-byte-predicate-v1'?/joint entries for every unsigned byte/:p.pair.profile==='cjson-interior-detach-v1'?/joint entries for every declared five-object/:p.pair.profile==='cjson-finite-list-v1'?/joint entries for every declared finite-list/:p.pair.profile==='legacy-tinycc-isid-v1'?/independently admit every signed32/:/independently be enterable/);
    for(const [i,id] of ['src','tgt'].entries()){
      const a=p.artifacts[i],rendered=await page.locator('#'+id).innerText();
      for(const value of [a.path,a.sha256,a.bytes_hex,'0x'+a.address.toString(16),`${a.frame} bytes below entry RSP`])assert.ok(rendered.includes(value));
      assert.match(await page.locator('#provenance').innerText(),new RegExp(a.source.sha256));
      assert.ok((await page.locator('#provenance').innerText()).includes(a.source.definitions[p.function_symbol].text));
    }
    if(p.pair.profile==='darkhttpd-byte-predicate-v1'){
      const defs=await page.locator('[data-context-module="Silmaril/Elf/Corpus/DarkhttpdLogEncoding/Equivalence/Defs.lean"] pre').textContent();
      for(const required of ['SysV.CallEntry','FnContract.FirstReturn','FnContract.AbiReturn','WritesWithin','∀ input, ∃ a b','setWidth 32'])assert.ok(defs.includes(required),required);
      assert.deepEqual(p.artifacts.map(a=>[a.address,a.size,a.frame]),[[20542,41,12],[10262,21,0]]);
      assert.equal(p.artifacts[1].bytes_hex,'8d 47 e0 3c 5e 0f 97 c0 40 80 ff 22 0f 94 c2 09 d0 0f b6 c0 c3');
      assert.equal(p.pair.value,null);assert.notEqual(p.artifacts[0].bytes_hex,p.artifacts[1].bytes_hex);
      assert.match(await page.locator('#questions').innerText(),/All256 byte inputs/);
      assert.match(await page.locator('#selection').innerText(),/upper56 RDI/);
      assert.match(await page.locator('#assumptions').innerText(),/not an equivalence proof/);
      await page.screenshot({path:path.join(shots,'darkhttpd-equivalence.png'),fullPage:false});
    }else if(p.pair.profile==='cjson-interior-detach-v1'){
      const defs=await page.locator('[data-context-module="Silmaril/Elf/Corpus/CjsonDetach/Equivalence/Defs.lean"] pre').textContent();
      for(const required of ['initialBytesMatch','finalBytesMatch','finalWord','sideOutcome','updateAddress','FnContract.FirstReturn','FnContract.AbiReturn','WritesWithin','Sse9.isa','∀ i, ∃ a b','payload : Fin 5 → Fin 64 → BitVec 8'])assert.ok(defs.includes(required),required);
      assert.deepEqual(p.artifacts.map(a=>[a.address,a.size,a.frame]),[[23724,218,24],[17248,131,0]]);
      assert.notEqual(p.artifacts[0].bytes_hex,p.artifacts[1].bytes_hex);
      assert.ok(p.artifacts[1].bytes_hex.includes('66 0f ef c0'));
      assert.ok(p.artifacts[1].bytes_hex.includes('0f 11 06'));
      assert.match(await page.locator('#questions').innerText(),/arbitrary admissible addresses and320 payload/);
      assert.match(await page.locator('#questions').innerText(),/XMM is SysV caller-clobbered/);
      assert.match(await page.locator('#assumptions').innerText(),/not equivalence proofs/);
      assert.equal(p.pair.value,null);assert.equal(p.pair.object_count,5);
    }else if(p.pair.profile==='cjson-finite-list-v1'){
      const defs=await page.locator('[data-context-module="Silmaril/Elf/Corpus/CjsonArraySize/Equivalence/Defs.lean"] pre').textContent();
      for(const required of ['SysV.CallEntry','FnContract.AbiEntry','FnContract.FirstReturn','FnContract.AbiReturn','WritesWithin','heapMatches','payload : Nat → BitVec 8','∀ i, ∃ a b'])assert.ok(defs.includes(required));
      assert.match(await page.locator('#questions').innerText(),/arbitrary unrelated payload bytes/);
      assert.notEqual(p.artifacts[0].bytes_hex,p.artifacts[1].bytes_hex);
      assert.deepEqual(p.artifacts.map(a=>[a.address,a.size,a.frame]),[[21378,81,32],[16528,35,0]]);
      assert.equal(p.pair.value,null);assert.equal(p.pair.length_bound,64);
      assert.match(await page.locator('#assumptions').innerText(),/not an equivalence proof/);
    }else if(p.pair.profile?.startsWith('legacy-')){
      const identifier=p.function_symbol==='isid';
      const module=identifier?'Silmaril/Elf/Corpus/TinyccClosed/Identifier/Variants/Defs.lean':p.declaration.includes('.AllVariants.')?'Silmaril/Elf/Corpus/MimallocVersion/AllVariants/Defs.lean':'Silmaril/Elf/Corpus/MimallocVersion/Defs.lean';
      const defs=await page.locator('[data-context-module="'+module+'"] pre').textContent();
      for(const required of ['SysV.Implements',identifier?'meaning':'versionMeaning'])assert.ok(defs.includes(required));
      assert.deepEqual(p.artifacts.map(a=>a.frame),identifier?[16,16]:[8,8]);
      assert.match(await page.locator('#assumptions').innerText(),/no saved TU\/Core binding/);
      if(identifier){
        assert.deepEqual(p.artifacts.map(a=>[a.address,a.size]),[[0x7508,51],[0x5e05,53]]);
        assert.match(await page.locator('#selection').innerText(),/every signed32 input/);
        assert.match(await page.locator('#selection').innerText(),/negative inputs/);
      }else assert.equal(p.pair.value,219);
    }else{
      const defs=await page.locator('[data-context-module="Silmaril/Elf/Corpus/SqliteBuildQueries/Equivalence/Defs.lean"] pre').textContent();
      for(const required of ['SysV.Implements','Silmaril.Elf.CodeAt','Safe _ := True','leftFrame rightFrame','meaning value'])assert.ok(defs.includes(required));
      assert.match(await page.locator('#provenance').innerText(),/different version constants/);
      assert.match(await page.locator('#provenance').innerText(),/different SQLITE_THREADSAFE settings/);
    }
    assert.equal(p.source_refinement_assumed,false);assert.equal(p.proof_evidence,null);
    if(!p.pair.profile?.startsWith('legacy-')&&(entry.declaration.endsWith('.versionOptimization')||entry.declaration.endsWith('.smallThreadsafeOptimization')||['darkhttpd-byte-predicate-v1','cjson-finite-list-v1','cjson-interior-detach-v1'].includes(p.pair.profile))){
      assert.notEqual(p.artifacts[0].bytes_hex,p.artifacts[1].bytes_hex);
      assert.equal(p.artifacts[0].frame,p.pair.profile==='darkhttpd-byte-predicate-v1'?12:p.pair.profile==='cjson-interior-detach-v1'?24:p.pair.profile==='cjson-finite-list-v1'?32:8);assert.equal(p.artifacts[1].frame,0);
      if(p.pair.profile==='darkhttpd-byte-predicate-v1')assert.equal(p.artifacts[1].size,21);
      else if(p.pair.profile==='cjson-finite-list-v1')assert.equal(p.artifacts[0].size,81);
      else if(p.pair.profile==='cjson-interior-detach-v1')assert.equal(p.artifacts[1].size,131);
      else if(p.function_symbol==='sqlite3_threadsafe')assert.equal(p.artifacts[1].bytes_hex,'31 c0 c3');
      else assert.equal(p.artifacts[0].bytes_hex,'55 48 89 e5 b8 b1 99 2e 00 5d c3');
    }
    {
      await page.getByRole('link',{name:'Corpus function',exact:true}).first().click();
      await page.waitForFunction(v=>document.querySelector('#corpus-function-search')?.value===v,p.function_symbol);
      await page.waitForFunction(()=>document.querySelector('#corpus-functions details'));
      await page.locator('#corpus-functions details').filter({hasText:'0x'+p.artifacts[0].address.toString(16)}).first().locator('summary').click();
      await page.locator('#corpus-functions a[href*="'+encodeURIComponent(p.declaration)+'"]').click();
      await page.waitForFunction(d=>document.body.dataset.equivalenceDeclaration===d,p.declaration);
      await page.getByRole('link',{name:'Corpus artifact',exact:true}).last().click();
      await page.waitForFunction(()=>window.explore.view==='corpus-artifact'&&!window.explore.busy);
      await page.locator('a[href*="'+encodeURIComponent(p.declaration)+'"]').click();
      await page.waitForFunction(d=>document.body.dataset.equivalenceDeclaration===d,p.declaration);
      await page.screenshot({path:path.join(shots,'sqlite-equivalence-'+p.pair.name+'.png'),fullPage:false});
    }
  }
  assert.deepEqual(pageErrors,[]);
  for(const selected of [binaryIndex.find(x=>x.function_symbol==='needs_logencoding'),binaryIndex[0],binaryIndex.find(x=>x.function_symbol==='cJSON_GetArraySize'),binaryIndex.find(x=>x.function_symbol==='cJSON_DetachItemViaPointer'),binaryIndex.find(x=>x.function_symbol==='isid'),binaryIndex.find(x=>x.function_symbol==='mi_version')]){
    const binaryPayload=JSON.parse(fs.readFileSync(path.join(site,'compiler',selected.static_path),'utf8'));
    const contextResource=binaryPayload.modules[0];
    await page.route('**/'+contextResource.static_path,route=>route.fulfill({status:200,contentType:'text/plain',body:'altered binary context'}));
    await page.goto(base+'/compiler/?equivalence='+encodeURIComponent(binaryPayload.declaration));
    await page.waitForFunction(()=>document.querySelector('#status').textContent.includes('error: binary context identity mismatch'));
    assert.equal(await page.locator('body').getAttribute('data-equivalence-declaration'),null);
    await page.unroute('**/'+contextResource.static_path);
  }
  console.log('PASS16 actual binary-equivalence viewer entries (16 registered statements; zero registered entries unconnected): both real ELF endpoints, different instructions, signed-int/pointer ABI, exact heap updates/private stack frames, source/config receipts and exclusions, UNPROVED status, bidirectional catalog/function links and altered-context rejection;842/707 retained');

} finally {await browser.close();server.kill();}
