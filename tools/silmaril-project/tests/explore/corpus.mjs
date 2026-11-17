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
  page.on('pageerror',e=>errors.push(e.message));
  await page.goto('http://127.0.0.1:8789/index.html#/corpus');
  await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
  assert.match(await page.locator('#main').innerText(),/Software under test/);
  const initialReads=fs.readFileSync(requestLog,'utf8').trim().split('\n').map(JSON.parse).filter(r=>r.path==='/project.sqlite');
  assert.ok(initialReads.reduce((n,r)=>n+(r.method==='GET'?r.bytes:0),0)<2*1024*1024,'landing page reads compact indexes rather than artifact evidence payloads');
  assert.match(await page.locator('#main').innerText(),/4 contextual C → ELF statements/);
  assert.match(await page.locator('#main').innerText(),/1 function-equivalence statements/);
  assert.equal(await page.locator('#nav a').count(),2,'standalone corpus database gets dedicated navigation');
  assert.equal(await page.locator('#source .err').count(),0,'recognized corpus schema');
  if(screenshot)await page.screenshot({path:screenshot,fullPage:false});
  await page.getByLabel('project',{exact:true}).selectOption('cjson');
  await page.waitForFunction(()=>document.querySelector('#corpus-count').textContent.startsWith('36 matching'));
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
  await page.goto('http://127.0.0.1:8789/index.html#/corpus-timings');
  await page.waitForFunction(()=>window.explore.view==='corpus-timings'&&!window.explore.busy);
  assert.match(await page.locator('#main').innerText(),/actual run receipts/);
  assert.match(await page.locator('#main').innerText(),/lean-elaboration-and-kernel-check/);
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
c.execute('UPDATE corpus_timings SET metadata=? WHERE run_id=?',(json.dumps(m),row[0]));c.commit();c.close();print(artifact)
`,path.join(site,evil)],{encoding:'utf8'}).trim();
    await page.goto(`http://127.0.0.1:8789/index.html?db=${evil}#/corpus-artifact/${artifact}`);
    await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
    assert.equal(await page.evaluate(()=>window.__corpus_xss),undefined);
    assert.equal(await page.locator('#main img').count(),0);
    await page.goto(`http://127.0.0.1:8789/index.html?db=${evil}#/corpus-timings`);
    await page.waitForFunction(()=>window.explore?.ready&&!window.explore.busy,null,{timeout:60000});
    assert.equal(await page.evaluate(()=>window.__corpus_xss),undefined);
    assert.equal(await page.locator('#main img').count(),0);
  }finally{fs.rmSync(path.join(site,evil));}
  assert.deepEqual(errors,[]);
  console.log('PASS corpus database: filters, artifact/source links, stripped mapping search, timings, concrete stated/unproved disclosure');
}finally{await browser.close();server.kill();}
