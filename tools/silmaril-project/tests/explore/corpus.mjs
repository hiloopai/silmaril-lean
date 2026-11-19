// Real corpus SQLite browser/navigation check. SITE is generated from public corpus receipts.
import assert from 'node:assert/strict';
import {spawn,execFileSync} from 'node:child_process';
import path from 'node:path';
import fs from 'node:fs';
const pw=await import(process.env.PLAYWRIGHT_CORE||'/usr/local/lib/node_modules/playwright-core/index.mjs');
const site=path.resolve(process.argv[2]), screenshot=process.argv[3];
const requestLog=path.join(site,'browser-requests.jsonl');
fs.rmSync(requestLog,{force:true});
const server=spawn('python3',['-I',new URL('./pages_server.py',import.meta.url).pathname,'--root',site,'--port','8789','--log',path.join(site,'browser-requests.jsonl')],{stdio:'ignore'});
const localChrome='/opt/ms-playwright/chromium-1248/chrome-linux64/chrome';
const browser=await pw.chromium.launch({executablePath:process.env.CHROME||(fs.existsSync(localChrome)?localChrome:undefined),args:['--no-sandbox']});
try{
  const page=await browser.newPage({viewport:{width:1440,height:1000}}), errors=[];
  const consoleMessages=[];
  page.on('console',message=>consoleMessages.push({type:message.type(),text:message.text()}));
  page.on('pageerror',e=>errors.push(e.message));
  await page.goto('http://127.0.0.1:8789/index.html#/corpus');
  await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
  assert.match(await page.locator('#main').innerText(),/Software under test/);
  const initialReads=fs.readFileSync(requestLog,'utf8').trim().split('\n').map(JSON.parse).filter(r=>r.path==='/project.sqlite');
  assert.ok(initialReads.reduce((n,r)=>n+(r.method==='GET'?r.bytes:0),0)<2*1024*1024,'landing page reads compact indexes rather than artifact evidence payloads');
  assert.match(await page.locator('#main').innerText(),/32 contextual C → ELF statements/);
  assert.match(await page.locator('#main').innerText(),/16 registered function-equivalence statements · 16 connected binary viewer entries/);
  const combined=Number(execFileSync('python3',['-c',
    "import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); print(c.execute(\"SELECT count(*) FROM sqlite_master WHERE type='table' AND name='projects'\").fetchone()[0]); c.close()",
    path.join(site,'project.sqlite')],{encoding:'utf8'}).trim())>0;
  if(combined)assert.ok(await page.locator('#nav a').count()>2,'published combined database preserves project navigation');
  else assert.equal(await page.locator('#nav a').count(),2,'standalone corpus database gets dedicated navigation');
  assert.equal(await page.locator('#source .err').count(),0,'recognized corpus schema');
  if(screenshot)await page.screenshot({path:screenshot,fullPage:false});
  // Compare the rendered project filter with an independent SQLite query.
  // Delivered profiles may add rows without changing the explorer's behavior.
  const cjsonCount=Number(execFileSync('python3',['-c',
    "import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); print(c.execute(\"SELECT count(*) FROM corpus_artifacts WHERE project='cjson'\").fetchone()[0]); c.close()",
    path.join(site,'project.sqlite')],{encoding:'utf8'}).trim());
  assert.ok(cjsonCount>0,'fixture includes real cJSON artifacts');
  const configurations=JSON.parse(execFileSync('python3',['-c',
    "import sqlite3,json,sys; c=sqlite3.connect(sys.argv[1]); print(json.dumps(c.execute(\"SELECT json_extract(metadata,'$.build.configuration'),count(*) FROM corpus_artifacts GROUP BY 1 ORDER BY 1\").fetchall()))",
    path.join(site,'project.sqlite')],{encoding:'utf8'}));
  assert.deepEqual(await page.getByLabel('configuration',{exact:true}).locator('option').allTextContents(),['All',...configurations.map(([name])=>name)]);
  // Exercise every delivered configuration, including populated version profiles.
  for(const [configuration,count] of configurations){
    await page.getByLabel('configuration',{exact:true}).selectOption(configuration);
    await page.waitForFunction(expected=>document.querySelector('#corpus-count').textContent.startsWith(`${expected} matching`),count);
    assert.ok((await page.locator('#corpus-results tbody tr').first().innerText()).includes(configuration));
  }
  await page.getByLabel('configuration',{exact:true}).selectOption('');
  await page.getByLabel('project',{exact:true}).selectOption('cjson');
  await page.waitForFunction(expected=>document.querySelector('#corpus-count').textContent.startsWith(`${expected} matching`),cjsonCount);
  await page.getByLabel('target',{exact:true}).selectOption('aarch64-linux-gnu');
  await page.getByLabel('optimization',{exact:true}).selectOption('O0');
  await page.getByLabel('stripping',{exact:true}).selectOption('stripped');
  await page.waitForFunction(()=>document.querySelector('#corpus-count').textContent.startsWith('2 matching'));
  await page.locator('#corpus-results a').first().click();
  await page.waitForFunction(()=>window.explore.view==='corpus-artifact'&&!window.explore.busy);
  assert.match(await page.locator('#main').innerText(),/Static tool evidence; runtime use and semantic support are not established/);
  assert.match(await page.locator('#main').innerText(),/Canonical ELF in Git/);
  await page.getByRole('link',{name:/Search all .* symbol rows/}).click();
  await page.waitForFunction(()=>window.explore.view==='corpus-functions'&&!window.explore.busy);
  await page.locator('#corpus-function-search').fill('cJSON_Parse');
  await page.waitForFunction(()=>document.querySelector('#corpus-function-count').textContent.includes('matching symbol rows'));
  await page.waitForFunction(()=>document.querySelector('#corpus-functions').innerText.includes('cJSON_Parse'));
  console.log('Navigating Timings after artifact/function search');
  const timingStart=Date.now();
  const readBytes=()=>fs.readFileSync(requestLog,'utf8').trim().split('\n').map(JSON.parse).filter(r=>r.path==='/project.sqlite'&&r.method==='GET').reduce((n,r)=>n+r.bytes,0);
  const beforeTimingBytes=readBytes();
  await page.goto('http://127.0.0.1:8789/index.html#/corpus-timings');
  try{
    await page.waitForFunction(()=>window.explore.view==='corpus-timings'&&!window.explore.busy);
  }catch(error){
    console.error(JSON.stringify({url:page.url(),errors,consoleMessages,requests:fs.readFileSync(requestLog,'utf8').trim().split('\n').slice(-20).map(JSON.parse)}));
    throw error;
  }
  console.log('Timings navigation ms:',Date.now()-timingStart,'database bytes:',readBytes()-beforeTimingBytes);
  assert.ok(readBytes()-beforeTimingBytes<2*1024*1024,'Timings landing uses compact summary, not full receipts');
  assert.match(await page.locator('#main').innerText(),/actual run receipts/);
  assert.ok(await page.locator('#timing-rows tr').count()<=100);
  await page.getByRole('button',{name:'Next',exact:true}).click();
  assert.match(await page.locator('#timing-page').innerText(),/^101–/);
  await page.getByLabel('Stage',{exact:true}).selectOption('lean-elaboration-and-kernel-check');
  assert.match(await page.locator('#timing-rows').innerText(),/lean-elaboration-and-kernel-check/);
  const receipt=page.locator('#timing-rows details').first();
  const runId=await receipt.getAttribute('data-timing-run');
  await receipt.locator('summary').click();
  await page.waitForFunction(id=>document.querySelector('details[data-timing-run="'+id+'"] pre').textContent.includes('"run_id"'),runId);
  const expected=JSON.parse(execFileSync('python3',['-c',"import sqlite3,sys; print(sqlite3.connect(sys.argv[1]).execute('SELECT metadata FROM corpus_timings WHERE run_id=?',(sys.argv[2],)).fetchone()[0])",path.join(site,'project.sqlite'),runId],{encoding:'utf8'}));
  assert.deepEqual(JSON.parse(await receipt.locator('pre').innerText()),expected);
  if(fs.existsSync(path.join(site,'combined.sqlite'))){
    await page.goto('http://127.0.0.1:8789/index.html?db=combined.sqlite#/corpus');
    await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
    assert.ok(await page.locator('#nav a').count()>10,'project database retains original navigation');
    assert.equal(await page.locator('#nav').getByRole('link',{name:'Progress',exact:true}).count(),1);
    assert.equal(await page.locator('#nav').getByRole('link',{name:'Wasm',exact:true}).count(),1);
  }
  // SQLite INTEGER affinity does not guarantee numeric values in an untrusted DB.
  const evil='corpus-escaping-'+process.pid+'.sqlite';
  fs.copyFileSync(path.join(site,'project.sqlite'),path.join(site,evil));
  try{
    const artifact=execFileSync('python3',['-c',`
import sqlite3,json,sys
c=sqlite3.connect(sys.argv[1]); attack='<img src=x onerror="window.__corpus_xss=1">'
artifact=c.execute('SELECT artifact FROM corpus_functions LIMIT 1').fetchone()[0]
c.execute('UPDATE corpus_functions SET size=? WHERE artifact=?',(attack,artifact))
row=c.execute('SELECT run_id,metadata FROM corpus_timings LIMIT 1').fetchone()
m=json.loads(row[1]);m['peak_rss_kib']=attack;m['exit_code']=attack
c.execute('UPDATE corpus_timings SET metadata=?,stage=? WHERE run_id=?',(json.dumps(m),'!!! escaping receipt',row[0]))
c.execute('UPDATE corpus_timing_summary SET stage=?,peak_rss_kib=?,exit_code=? WHERE run_id=?',('!!! escaping receipt',attack,attack,row[0]));c.commit();c.close();print(artifact)
`,path.join(site,evil)],{encoding:'utf8'}).trim();
    await page.goto(`http://127.0.0.1:8789/index.html?db=${evil}#/corpus-artifact/${artifact}`);
    await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
    assert.equal(await page.evaluate(()=>window.__corpus_xss),undefined);
    assert.equal(await page.locator('#main img').count(),0);
    await page.goto(`http://127.0.0.1:8789/index.html?db=${evil}#/corpus-timings`);
    await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
    await page.locator('#timing-rows details').first().locator('summary').click();
    await page.waitForFunction(()=>document.querySelector('#timing-rows details pre').textContent.includes('onerror'));
    assert.equal(await page.evaluate(()=>window.__corpus_xss),undefined);
    assert.equal(await page.locator('#main img').count(),0);
  }finally{fs.rmSync(path.join(site,evil));}
  // Old public catalogs have receipts but no compact summary table.
  const legacy='corpus-legacy-'+process.pid+'.sqlite';
  try{
    execFileSync('python3',['-c',`
import sqlite3,sys
source=sqlite3.connect(sys.argv[1]); target=sqlite3.connect(sys.argv[2])
target.executescript('CREATE TABLE corpus_meta(key TEXT,value TEXT); CREATE TABLE corpus_artifacts(id TEXT); CREATE TABLE corpus_timings(run_id TEXT PRIMARY KEY,build_id TEXT,stage TEXT,metadata TEXT);')
target.executemany('INSERT INTO corpus_meta VALUES(?,?)',source.execute('SELECT key,value FROM corpus_meta'))
target.execute('INSERT INTO corpus_timings VALUES(?,?,?,?)',source.execute('SELECT * FROM corpus_timings WHERE run_id=?',(sys.argv[3],)).fetchone())
target.commit();target.close();source.close()
`,path.join(site,'project.sqlite'),path.join(site,legacy),runId]);
    await page.goto(`http://127.0.0.1:8789/index.html?db=${legacy}#/corpus-timings`);
    await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy);
    assert.match(await page.locator('#main').innerText(),/1 actual run receipts/);
    await page.locator('#timing-rows summary').click();
    await page.waitForFunction(()=>document.querySelector('#timing-rows pre').textContent.includes('"run_id"'));
    assert.deepEqual(JSON.parse(await page.locator('#timing-rows pre').innerText()),expected);
  }finally{fs.rmSync(path.join(site,legacy),{force:true});}
  assert.deepEqual(errors,[]);
  console.log('PASS corpus database: filters, artifact/source links, stripped mapping search, timings, concrete stated/unproved disclosure');
}finally{await browser.close();server.kill();}
