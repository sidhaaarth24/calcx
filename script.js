'use strict';
const $ = s => document.querySelector(s), $$ = s => [...document.querySelectorAll(s)];
const expression = $('#expression'), result = $('#result'), toast = $('#toast');
let mode='basic', angle='DEG', engineeringNotation=false, memory=0, lastAnswer=0, history=[];
try { history=JSON.parse(localStorage.getItem('calcx-history')||'[]'); if(!Array.isArray(history)) history=[]; } catch { history=[]; }
let toastTimer;
function notify(message){toast.textContent=message;toast.classList.add('show');clearTimeout(toastTimer);toastTimer=setTimeout(()=>toast.classList.remove('show'),1900)}
function fmt(n){if(!Number.isFinite(n))return 'Error';if(Math.abs(n)<1e-13)n=0;return Number(n.toPrecision(12)).toLocaleString('en-US',{maximumFractionDigits:10})}
function engineeringFmt(n){if(!Number.isFinite(n))return 'Error';if(n===0)return '0';const exponent=Math.floor(Math.log10(Math.abs(n))/3)*3;const mantissa=n/Math.pow(10,exponent);return `${Number(mantissa.toPrecision(8))}e${exponent>=0?'+':''}${exponent}`}
const CONSTANTS={pi:Math.PI,PI:Math.PI,e:Math.E,phi:(1+Math.sqrt(5))/2,c0:299792458,g0:9.80665,Rgas:8.314462618,kB:1.380649e-23,NA:6.02214076e23,hPlanck:6.62607015e-34,Gconst:6.6743e-11,mu0:1.25663706212e-6,eps0:8.8541878128e-12,Ans:()=>lastAnswer};
const FUNCTIONS={
 sin:x=>Math.sin(angle==='DEG'?x*Math.PI/180:x),cos:x=>Math.cos(angle==='DEG'?x*Math.PI/180:x),tan:x=>Math.tan(angle==='DEG'?x*Math.PI/180:x),
 asin:x=>angle==='DEG'?Math.asin(x)*180/Math.PI:Math.asin(x),acos:x=>angle==='DEG'?Math.acos(x)*180/Math.PI:Math.acos(x),atan:x=>angle==='DEG'?Math.atan(x)*180/Math.PI:Math.atan(x),
 sinh:Math.sinh,cosh:Math.cosh,tanh:Math.tanh,asinh:Math.asinh,acosh:Math.acosh,atanh:Math.atanh,
 sqrt:Math.sqrt,cbrt:Math.cbrt,log:Math.log10,ln:Math.log,log2:Math.log2,exp:Math.exp,abs:Math.abs,floor:Math.floor,ceil:Math.ceil,round:Math.round,
 mod:(a,b)=>a%b,min:Math.min,max:Math.max,pow:Math.pow,hypot:Math.hypot
};
function tokenize(input){
 let s=input.replace(/[×·]/g,'*').replace(/[÷]/g,'/').replace(/[−–]/g,'-').replace(/π/g,'pi').replace(/√/g,'sqrt');
 const raw=s.match(/(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?|[A-Za-z_][A-Za-z_0-9]*|[()+\-*/^%!%,]/g)||[];
 if(raw.join('').replace(/\s/g,'')!==s.replace(/\s/g,''))throw Error('Unsupported character in expression');
 const out=[];
 for(let i=0;i<raw.length;i++){
  const prev=out[out.length-1],cur=raw[i];
  const prevEnds=prev&&(prev.type==='number'||prev.type==='constant'||prev.value===')'||prev.value==='!'||prev.value==='%');
  const curStarts=cur==='('?true:/^[A-Za-z_]/.test(cur)&&!FUNCTIONS[cur.toLowerCase()]?true:/^\d/.test(cur)||cur.startsWith('.');
  const curFunc=/^[A-Za-z_]/.test(cur)&&!!FUNCTIONS[cur.toLowerCase()];
  if(prevEnds&&(curStarts||curFunc))out.push({type:'op',value:'*'});
  if(/^\d/.test(cur)||cur.startsWith('.'))out.push({type:'number',value:cur});
  else if(/^[A-Za-z_]/.test(cur))out.push({type:'identifier',value:cur});
  else out.push({type:'op',value:cur});
 }
 return out;
}
function safeEval(input){
 if(!input.trim())return 0;
 const tokens=tokenize(input);let pos=0;
 const peek=()=>tokens[pos]?.value;
 function factorial(n){if(n<0||!Number.isInteger(n)||n>170)throw Error('Factorial needs an integer from 0 to 170');let v=1;for(let i=2;i<=n;i++)v*=i;return v}
 function parsePrimary(){
  const t=tokens[pos++];if(!t)throw Error('Incomplete expression');
  if(t.value==='+'||t.value==='-'){const v=parseExpression(25);return t.value==='-'?-v:v}
  if(t.value==='('){const v=parseExpression(0);if(peek()!==')')throw Error('Missing closing parenthesis');pos++;return v}
  if(t.type==='number')return Number(t.value);
  if(t.type==='identifier'){
   const name=t.value,lower=name.toLowerCase();
   if(FUNCTIONS[lower]){
    if(peek()!=='(')throw Error(`${name} needs parentheses`);pos++;
    const args=[];if(peek()!==')'){while(true){args.push(parseExpression(0));if(peek()===','){pos++;continue}break}}
    if(peek()!==')')throw Error('Missing closing parenthesis');pos++;
    const fn=FUNCTIONS[lower];if((lower==='mod'||lower==='pow')&&args.length!==2)throw Error(`${name} needs two arguments`);if(['min','max','hypot'].includes(lower)&&args.length<1)throw Error(`${name} needs an argument`);if(!['mod','pow','min','max','hypot'].includes(lower)&&args.length!==1)throw Error(`${name} needs one argument`);
    return fn(...args);
   }
   const value=CONSTANTS[name]??CONSTANTS[lower];if(value!==undefined)return typeof value==='function'?value():value;
   throw Error(`Unknown function or constant: ${name}`);
  }
  throw Error(`Unexpected token: ${t.value}`);
 }
 function parseExpression(minBp=0){
  let left=parsePrimary();
  while(pos<tokens.length){const op=peek();
   if(op==='!'||op==='%'){if(40<minBp)break;pos++;left=op==='!'?factorial(left):left/100;continue}
   let lbp,rbp;if(op==='+'||op==='-'){lbp=10;rbp=11}else if(op==='*'||op==='/'){lbp=20;rbp=21}else if(op==='^'){lbp=30;rbp=30}else break;
   if(lbp<minBp)break;pos++;const right=parseExpression(rbp);if(op==='+')left+=right;else if(op==='-')left-=right;else if(op==='*')left*=right;else if(op==='/'){if(right===0)throw Error('Cannot divide by zero');left/=right}else left=Math.pow(left,right);
  }
  if(!Number.isFinite(left))throw Error('Math domain error');return left;
 }
 const value=parseExpression(0);if(pos!==tokens.length)throw Error('Check the expression syntax');return value;
}
function displayValue(v){return engineeringNotation?engineeringFmt(v):fmt(v)}
function preview(){try{const v=safeEval(expression.value);result.textContent=displayValue(v);result.style.removeProperty('color')}catch{result.textContent=expression.value.trim()?'—':'0';result.style.color='var(--muted)'}}
function addHistory(expr,val){history.unshift({expr,val:fmt(val),time:Date.now()});history=history.slice(0,150);try{localStorage.setItem('calcx-history',JSON.stringify(history))}catch{}renderHistory()}
function calculate(){try{const expr=expression.value.trim();if(!expr)return;const val=safeEval(expr);lastAnswer=val;result.textContent=displayValue(val);addHistory(expr,val);expression.value=String(Number(val.toPrecision(12)));expression.focus()}catch(e){notify(e.message||'Could not calculate')}}
function insert(value){const start=expression.selectionStart??expression.value.length,end=expression.selectionEnd??start;expression.setRangeText(value,start,end,'end');expression.focus();preview()}
function insertSmart(value){const atEnd=expression.selectionStart===expression.value.length&&expression.selectionEnd===expression.value.length;const current=expression.value.trim();const unary=['sin(','cos(','tan(','sqrt(','asin(','acos(','atan(','log(','ln(','abs(','exp(','sinh(','cosh(','tanh(','asinh(','acosh(','atanh(','cbrt(','log2('];if(atEnd&&current&&!/[+\-*/^(,]$/.test(current)&&unary.includes(value)){expression.value=`${value}${current})`;expression.setSelectionRange(expression.value.length,expression.value.length);expression.focus();preview();return}if(atEnd&&current&&value==='1/'){expression.value=`1/(${current})`;expression.setSelectionRange(expression.value.length,expression.value.length);expression.focus();preview();return}if(atEnd&&current&&value==='10^'){expression.value=`10^(${current})`;expression.setSelectionRange(expression.value.length,expression.value.length);expression.focus();preview();return}insert(value)}
function escapeHTML(s){return String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
function renderHistory(){const markup=arr=>arr.length?arr.map((h,i)=>`<button class="history-item" type="button" data-history="${i}"><span class="history-expression">${escapeHTML(h.expr)}</span><span class="history-result">${escapeHTML(h.val)}</span></button>`).join(''):'<div class="empty-state"><span>◷</span><p>No calculations yet.</p></div>';$('#recentHistory').innerHTML=markup(history.slice(0,5));$('#fullHistory').innerHTML=markup(history);$$('[data-history]').forEach(el=>el.addEventListener('click',()=>{const h=history[Number(el.dataset.history)];if(!h)return;expression.value=h.expr;preview();showView('calculator')}))}
function closeDrawer(){const sidebar=$('#sidebar');if(sidebar.classList.contains('open'))$('#menuBtn').focus();sidebar.classList.remove('open');sidebar.setAttribute('aria-hidden','true');$('#menuBtn').setAttribute('aria-expanded','false');$('#drawerBackdrop').classList.remove('visible')}
function openDrawer(){const sidebar=$('#sidebar');sidebar.classList.add('open');sidebar.setAttribute('aria-hidden','false');$('#menuBtn').setAttribute('aria-expanded','true');$('#drawerBackdrop').classList.add('visible');$('#drawerClose').focus()}
function showView(name){const normalized=name==='boolean'?'electronic':name;$$('.view').forEach(v=>v.classList.toggle('active',v.id==='view-'+normalized));$$('.nav-item[data-view]').forEach(v=>v.classList.toggle('active',v.dataset.view===normalized));const titles={calculator:'CalcX',converter:'Convert',tools:'Utilities',electronic:'Electronic',boolean:'Electronic',currency:'Currency',history:'History'};$('#pageTitle').textContent=titles[normalized]||titles[name]||'CalcX';closeDrawer();if(normalized==='currency')loadCurrencyRates()}
$$('.nav-item[data-view]').forEach(b=>b.addEventListener('click',()=>showView(b.dataset.view)));$$('[data-goto]').forEach(b=>b.addEventListener('click',()=>showView(b.dataset.goto)));$('#menuBtn').addEventListener('click',()=>$('#sidebar').classList.contains('open')?closeDrawer():openDrawer());$('#drawerClose').addEventListener('click',closeDrawer);$('#drawerBackdrop').addEventListener('click',closeDrawer);document.addEventListener('keydown',e=>{if(e.key==='Escape')closeDrawer()});
function setTheme(theme){document.body.classList.toggle('light',theme==='light');try{localStorage.setItem('calcx-theme',theme)}catch{}$('#themeBtn').textContent='◐'}
let savedTheme='dark';try{savedTheme=localStorage.getItem('calcx-theme')||(matchMedia('(prefers-color-scheme: light)').matches?'light':'dark')}catch{}setTheme(savedTheme);function toggleTheme(){setTheme(document.body.classList.contains('light')?'dark':'light')}$('#themeBtn').addEventListener('click',toggleTheme);
function setMode(next){mode=next;$$('.mode-btn').forEach(b=>b.classList.toggle('selected',b.dataset.mode===mode));$('#scientificKeys').classList.toggle('hidden',mode!=='scientific');$('#engineeringKeys').classList.toggle('hidden',mode!=='engineering');$('#engineeringBar').classList.toggle('hidden',mode!=='engineering');$('#functionEmpty').classList.toggle('hidden',mode!=='basic');preview()}
$$('.mode-btn').forEach(b=>b.addEventListener('click',()=>setMode(b.dataset.mode)));
$('#angleToggle').addEventListener('click',()=>{angle=angle==='DEG'?'RAD':'DEG';$('#angleToggle').textContent=angle;preview();notify(`Angle mode: ${angle}`)});
$('#notationToggle').addEventListener('click',()=>{engineeringNotation=!engineeringNotation;$('#notationToggle').textContent=engineeringNotation?'ON':'OFF';preview()});
$('#keypad').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;const action=b.dataset.action;if(action==='clear'){expression.value='';preview()}else if(action==='backspace'){let a=expression.selectionStart??expression.value.length,bx=expression.selectionEnd??a;if(a===bx&&a>0)a--;expression.setRangeText('',a,bx,'end');expression.focus();preview()}else if(action==='sign'){if(!expression.value)return;expression.value=expression.value.startsWith('-(')?expression.value.slice(2,-1):`-(${expression.value})`;preview()}else if(action==='equals')calculate();else insert(b.dataset.value)});
['scientificKeys','engineeringKeys'].forEach(id=>$('#'+id).addEventListener('click',e=>{const b=e.target.closest('button');if(b)insertSmart(b.dataset.value)}));$('#engineeringBar').addEventListener('click',e=>{const b=e.target.closest('button[data-value]');if(b)insert(b.dataset.value)});
expression.addEventListener('input',preview);expression.addEventListener('paste',()=>setTimeout(preview,0));expression.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();calculate()}if(e.key==='Escape'){expression.value='';preview()}});
document.addEventListener('keydown',e=>{if(e.target.matches('input,textarea,select,button'))return;if(e.key==='1')showView('calculator');if(e.key==='2')showView('converter');if(e.key==='3')showView('tools');if(e.key==='4')showView('electronic');if(e.key==='5')showView('currency');if(e.key.toLowerCase()==='h')showView('history')});
$$('.memory-actions button').forEach(b=>b.addEventListener('click',()=>{let val=0;try{val=safeEval(expression.value)}catch{}const a=b.dataset.action;if(a==='mc')memory=0;if(a==='ms')memory=val;if(a==='mplus')memory+=val;if(a==='mminus')memory-=val;if(a==='mr')insert(String(memory));$('#memoryIndicator').textContent=memory!==0?'M':'';notify(a==='mr'?'Memory recalled':a==='mc'?'Memory cleared':'Memory updated')}));
$('#clearHistory').addEventListener('click',clearHistory);$('#clearHistoryFull').addEventListener('click',clearHistory);function clearHistory(){history=[];try{localStorage.setItem('calcx-history','[]')}catch{}renderHistory();notify('History cleared')}renderHistory();

// Unit conversion tables use canonical base units. Currency is intentionally excluded because exchange rates require live data.
const U={
 Length:{Meter:1,Kilometer:1000,Centimeter:.01,Millimeter:.001,Micrometer:1e-6,Nanometer:1e-9,Mile:1609.344,Yard:.9144,Foot:.3048,Inch:.0254,Nautical_mile:1852},
 Mass:{Kilogram:1,Gram:.001,Milligram:1e-6,Microgram:1e-9,Metric_ton:1000,Pound:.45359237,Ounce:.028349523125,Stone:6.35029318,US_ton:907.18474},
 Area:{Square_meter:1,Square_kilometer:1e6,Square_centimeter:.0001,Square_mile:2589988.110336,Square_yard:.83612736,Square_foot:.09290304,Square_inch:.00064516,Hectare:10000,Acre:4046.8564224},
 Volume:{Liter:1,Milliliter:.001,Cubic_meter:1000,Cubic_centimeter:.001,US_gallon:3.785411784,Imperial_gallon:4.54609,US_quart:.946352946,US_pint:.473176473,Cup:.2365882365,US_fluid_ounce:.0295735296,Cubic_foot:28.3168466},
 Speed:{Meter_per_second:1,Kilometer_per_hour:1/3.6,Mile_per_hour:.44704,Knot:.514444,Foot_per_second:.3048},
 Time:{Second:1,Millisecond:.001,Microsecond:1e-6,Minute:60,Hour:3600,Day:86400,Week:604800,Month_30_days:2592000,Year_365_days:31536000},
 Data:{Bit:1,Byte:8,Kilobit:1000,Kilobyte:8000,Megabit:1e6,Megabyte:8e6,Gigabit:1e9,Gigabyte:8e9,Terabit:1e12,Terabyte:8e12,Kibibyte:8192,Mebibyte:8388608,Gibibyte:8589934592},
 Pressure:{Pascal:1,Kilopascal:1000,Megapascal:1e6,Bar:100000,Atmosphere:101325,PSI:6894.757293,Torr:133.322368},
 Energy:{Joule:1,Kilojoule:1000,Calorie:4.184,Kilocalorie:4184,Watt_hour:3600,Kilowatt_hour:3600000,BTU:1055.05585,Electronvolt:1.602176634e-19},
 Power:{Watt:1,Kilowatt:1000,Megawatt:1e6,Horsepower:745.699872,Metric_horsepower:735.49875},
 Force:{Newton:1,Kilonewton:1000,Dyne:1e-5,Pound_force:4.448221615},
 Angle:{Degree:Math.PI/180,Radian:1,Gradian:Math.PI/200,Arcminute:Math.PI/10800,Arcsecond:Math.PI/648000},
 Frequency:{Hertz:1,Kilohertz:1000,Megahertz:1e6,Gigahertz:1e9,RPM:1/60},
 Fuel_economy:{Km_per_liter:1,Miles_per_gallon_US:.425143707,Miles_per_gallon_Imperial:.35400619,Liters_per_100_km:100},
 Density:{Kilogram_per_cubic_meter:1,Gram_per_cubic_centimeter:1000,Gram_per_milliliter:1000,Pound_per_cubic_foot:16.0184634},
 Torque:{Newton_meter:1,Pound_foot:1.35581795,Pound_inch:.112984829},
 Electric_current:{Ampere:1,Milliampere:.001,Microampere:1e-6,Kiloampere:1000},
 Voltage:{Volt:1,Millivolt:.001,Kilovolt:1000},
 Resistance:{Ohm:1,Kiloohm:1000,Megaohm:1e6},
};
const pretty=s=>s.replaceAll('_',' ').replace(/\b\w/g,c=>c.toUpperCase());const category=$('#category'),fromUnit=$('#fromUnit'),toUnit=$('#toUnit');
Object.keys(U).concat(['Temperature']).forEach(c=>category.add(new Option(pretty(c),c)));
function toCanonical(v,u,c){if(c==='Temperature')return u==='Celsius'?v:u==='Fahrenheit'?(v-32)*5/9:v-273.15;if(c==='Fuel_economy')return u==='Liters_per_100_km'?100/v:v*U[c][u];return v*U[c][u]}
function fromCanonical(v,u,c){if(c==='Temperature')return u==='Celsius'?v:u==='Fahrenheit'?v*9/5+32:v+273.15;if(c==='Fuel_economy')return u==='Liters_per_100_km'?100/v:v/U[c][u];return v/U[c][u]}
function convert(){const c=category.value,v=Number($('#fromValue').value);if(!Number.isFinite(v))return;const answer=fromCanonical(toCanonical(v,fromUnit.value,c),toUnit.value,c);$('#toValue').textContent=fmt(answer);$('#conversionFormula').textContent=`${fmt(v)} ${pretty(fromUnit.value)} = ${fmt(answer)} ${pretty(toUnit.value)}`}
function fillUnits(){const c=category.value,units=c==='Temperature'?['Celsius','Fahrenheit','Kelvin']:Object.keys(U[c]);const oldF=fromUnit.value,oldT=toUnit.value;[fromUnit,toUnit].forEach(sel=>{sel.innerHTML='';units.forEach(u=>sel.add(new Option(pretty(u),u)))});fromUnit.value=units.includes(oldF)?oldF:units[0];toUnit.value=units.includes(oldT)?oldT:units[Math.min(1,units.length-1)];convert()}
category.addEventListener('change',fillUnits);[fromUnit,toUnit,$('#fromValue')].forEach(el=>el.addEventListener('input',convert));$('#swapUnits').addEventListener('click',()=>{const a=fromUnit.value;fromUnit.value=toUnit.value;toUnit.value=a;convert()});$('#copyConversion').addEventListener('click',async()=>{try{await navigator.clipboard.writeText($('#toValue').textContent);notify('Result copied')}catch{notify('Clipboard unavailable') }});fillUnits();
let currencyRateData=null,currencyRateRequest=null,currencyRateRequestId=0;
const currencyNames=typeof Intl.DisplayNames==='function'?new Intl.DisplayNames(['en'],{type:'currency'}):null;
const currencyAmount=$('#currencyAmount'),currencyFrom=$('#currencyFrom'),currencyTo=$('#currencyTo'),currencyResult=$('#currencyResult'),currencyRate=$('#currencyRate'),currencyStatus=$('#currencyStatus');
function renderCurrencyConversion(){
 const amount=Number(currencyAmount.value),from=currencyFrom.value,to=currencyTo.value;
 if(!currencyRateData){currencyResult.textContent='—';currencyRate.textContent='Rates are unavailable.';return}
 if(!from||!to){currencyResult.textContent='—';currencyRate.textContent='Choose currencies to see the rate.';return}
 const fromRate=currencyRateData.rates[from],toRate=currencyRateData.rates[to],rate=toRate/fromRate,converted=amount*rate;
 if(!Number.isFinite(rate)||rate<=0){currencyResult.textContent='—';currencyRate.textContent=`Rate unavailable for ${from} and ${to}.`;return}
 const format=value=>new Intl.NumberFormat(undefined,{maximumFractionDigits:8}).format(value);
 currencyRate.textContent=`1 ${from} = ${format(rate)} ${to}`;
 if(!Number.isFinite(amount)||amount<0||currencyAmount.value.trim()===''){currencyResult.textContent='—';return}
 if(!Number.isFinite(converted)){currencyResult.textContent='—';return}
 currencyResult.textContent=`${format(converted)} ${to}`;
}
function fillCurrencyOptions(rates){
 const codes=Object.keys(rates).filter(code=>/^[A-Z]{3}$/.test(code)&&Number.isFinite(rates[code])&&rates[code]>0&&(!currencyNames||currencyNames.of(code)!==code)).sort();
 [currencyFrom,currencyTo].forEach(select=>{
  const selected=select.value;
  select.replaceChildren(new Option('Choose currency',''),...codes.map(code=>new Option(currencyNames?`${code} — ${currencyNames.of(code)}`:code,code)));
  if(codes.includes(selected))select.value=selected;
  else select.value='';
 });
}
async function loadCurrencyRates(force=false){
 if(currencyRateData&&!force){renderCurrencyConversion();return}
 if(currencyRateRequest&&!force)return currencyRateRequest;
 const requestId=++currencyRateRequestId;
 currencyStatus.dataset.state='loading';
 currencyStatus.textContent='Fetching the latest available rates…';
 currencyRateRequest=(async()=>{
  try{
   const response=await fetch('https://api.fxratesapi.com/latest?base=INR',{cache:'no-store'});
   if(!response.ok)throw new Error(`Rate service returned HTTP ${response.status}`);
   const data=await response.json();
   if(data.success!==true||data.base!=='INR'||!data.rates||!Number.isFinite(Number(data.timestamp)))throw new Error(data.error||'The rate service returned an invalid response');
   const rates=Object.fromEntries(Object.entries(data.rates).map(([code,rate])=>[code,Number(rate)]));
   if(!(rates.INR>0)||!(rates.BDT>0))throw new Error('The rate service did not return the required currencies');
   if(requestId!==currencyRateRequestId)return;
   currencyRateData={rates,timestamp:Number(data.timestamp)};
   fillCurrencyOptions(rates);
   currencyStatus.dataset.state='ready';
   currencyStatus.textContent=`Provider timestamp: ${new Date(currencyRateData.timestamp*1000).toLocaleString()}.`;
   renderCurrencyConversion();
  }catch(error){
   if(requestId!==currencyRateRequestId)return;
   currencyRateData=null;
   currencyStatus.dataset.state='error';
   currencyStatus.textContent=`Could not load exchange rates: ${error instanceof Error?error.message:'Unexpected rate service error'}. Check your connection and try again.`;
   currencyResult.textContent='—';
   currencyRate.textContent='Choose currencies to see the rate.';
   console.error('Currency rate request failed',error);
  }finally{
   if(requestId===currencyRateRequestId)currencyRateRequest=null;
  }
 })();
 return currencyRateRequest;
}
currencyAmount.addEventListener('input',renderCurrencyConversion);
[currencyFrom,currencyTo].forEach(select=>select.addEventListener('change',renderCurrencyConversion));
$('#currencySwap').addEventListener('click',()=>{const from=currencyFrom.value;currencyFrom.value=currencyTo.value;currencyTo.value=from;renderCurrencyConversion()});
$('#refreshCurrencyRates').addEventListener('click',()=>loadCurrencyRates(true));
// Quick tools: each calculator updates independently as its fields change.
let financialUSCurrency=false;
const num=id=>Number($('#'+id).value)||0,hasValue=id=>$('#'+id).value.trim()!=='',money=n=>`${financialUSCurrency?'$':'₹'}${Number(n).toLocaleString(financialUSCurrency?'en-US':'en-IN',{minimumFractionDigits:2,maximumFractionDigits:2})}`;
function gcd(a,b){a=Math.abs(Math.round(a));b=Math.abs(Math.round(b));while(b)[a,b]=[b,a%b];return a}
function updateTools(){
 $('#pctResult').textContent=hasValue('pct')&&hasValue('pctBase')?fmt(num('pct')*num('pctBase')/100):'—';
 if(hasValue('price')&&hasValue('discount')){const price=num('price'),discount=Math.min(100,Math.max(0,num('discount'))),saving=price*discount/100;$('#discountResult').textContent=money(price-saving);$('#discountSaving').textContent=`You save ${money(saving)}`}else{$('#discountResult').textContent=$('#discountSaving').textContent='—'}
 const rawValues=$('#averageInput').value.split(/[,;\s]+/).filter(Boolean),values=rawValues.map(Number).sort((a,b)=>a-b);if(values.length&&values.every(Number.isFinite)){const mean=values.reduce((a,b)=>a+b,0)/values.length,mid=Math.floor(values.length/2),counts=new Map();values.forEach(value=>counts.set(value,(counts.get(value)||0)+1));const maxCount=Math.max(...counts.values()),modes=[...counts].filter(([,count])=>count===maxCount&&count>1).map(([value])=>fmt(value));$('#averageResult').textContent=fmt(mean);$('#medianResult').textContent=fmt(values.length%2?values[mid]:(values[mid-1]+values[mid])/2);$('#modeResult').textContent=modes.length?modes.join(', '):'None';$('#rangeResult').textContent=fmt(values[values.length-1]-values[0])}else{$('#averageResult').textContent=$('#medianResult').textContent=$('#modeResult').textContent=$('#rangeResult').textContent='—'}
 if(hasValue('bill')&&hasValue('tip')&&hasValue('people')){const people=Math.max(1,Math.floor(num('people'))),total=num('bill')*(1+num('tip')/100);$('#tipResult').textContent=money(total/people);$('#tipTotal').textContent=`Total with tip: ${money(total)}`}else{$('#tipResult').textContent=$('#tipTotal').textContent='—'}
 if(hasValue('principal')&&hasValue('rate')&&hasValue('years')){const principal=num('principal'),rate=num('rate')/100,years=Math.max(0,num('years')),freq=Math.max(1,num('compoundFreq'));const future=principal*Math.pow(1+rate/freq,freq*years);$('#compoundResult').textContent=money(future);$('#compoundGain').textContent=`Interest earned: ${money(future-principal)}`}else{$('#compoundResult').textContent=$('#compoundGain').textContent='—'}
 if(hasValue('ratioA')&&hasValue('ratioB')){const a=num('ratioA'),b=num('ratioB'),div=gcd(a,b);$('#ratioResult').textContent=div?`${a/div} : ${b/div}`:'—'}else{$('#ratioResult').textContent='—'}
 if(hasValue('gstAmount')){const gstAmount=num('gstAmount'),gst=num('gstRate')/100;$('#gstResult').textContent=money(gstAmount*(1+gst));$('#gstBreakdown').textContent=`GST amount: ${money(gstAmount*gst)}`}else{$('#gstResult').textContent=$('#gstBreakdown').textContent='—'}
 if(hasValue('loanAmount')&&hasValue('loanRate')&&hasValue('loanYears')){const loan=num('loanAmount'),monthlyRate=num('loanRate')/1200,months=Math.max(0,Math.round(num('loanYears')*12));const emi=months?(monthlyRate?loan*monthlyRate*Math.pow(1+monthlyRate,months)/(Math.pow(1+monthlyRate,months)-1):loan/months):0;$('#emiResult').textContent=money(emi);$('#emiTotal').textContent=`Total repayment: ${money(emi*months)}`}else{$('#emiResult').textContent=$('#emiTotal').textContent='—'}
 if(hasValue('changeStart')&&hasValue('changeEnd')){const start=num('changeStart'),change=num('changeEnd')-start;if(start===0){$('#changeResult').textContent='—';$('#changeAmount').textContent=`Change: ${fmt(change)} (percentage is undefined from zero)`}else{const percent=change/Math.abs(start)*100;$('#changeResult').textContent=`${percent>0?'+':''}${fmt(percent)}% ${percent>0?'increase':percent<0?'decrease':'change'}`;$('#changeAmount').textContent=`Absolute change: ${fmt(change)}`}}else{$('#changeResult').textContent=$('#changeAmount').textContent='—'}
 if(hasValue('simplePrincipal')&&hasValue('simpleRate')&&hasValue('simpleYears')){const principal=num('simplePrincipal'),rate=num('simpleRate'),years=num('simpleYears');if(principal<0||rate<0||years<0){$('#simpleResult').textContent='—';$('#simpleInterest').textContent='Values must be non-negative'}else{const interest=principal*rate/100*years;$('#simpleResult').textContent=money(principal+interest);$('#simpleInterest').textContent=`Interest: ${money(interest)}`}}else{$('#simpleResult').textContent=$('#simpleInterest').textContent='—'}
 if(hasValue('fuelDistance')&&hasValue('fuelEfficiency')&&hasValue('fuelPrice')){const distance=num('fuelDistance'),efficiency=num('fuelEfficiency'),price=num('fuelPrice');if(distance<0||efficiency<=0||price<0){$('#fuelResult').textContent='—';$('#fuelNeeded').textContent='Enter non-negative values and positive efficiency'}else{const fuel=distance/efficiency;$('#fuelResult').textContent=money(fuel*price);$('#fuelNeeded').textContent=`Fuel needed: ${fmt(fuel)} L`}}else{$('#fuelResult').textContent=$('#fuelNeeded').textContent='—'}
 if(hasValue('costPrice')&&hasValue('sellingPrice')){const cost=num('costPrice'),selling=num('sellingPrice');if(cost<0||selling<0){$('#profitResult').textContent='—';$('#marginDetails').textContent='Prices must be non-negative'}else{const difference=selling-cost,margin=selling?`${fmt(difference/selling*100)}%`:'N/A',markup=cost?`${fmt(difference/cost*100)}%`:'N/A';$('#profitResult').textContent=difference>0?`Profit ${money(difference)}`:difference<0?`Loss ${money(Math.abs(difference))}`:'Break-even';$('#marginDetails').textContent=`Margin: ${margin} · Markup: ${markup}`}}else{$('#profitResult').textContent=$('#marginDetails').textContent='—'}
 if(hasValue('hcfA')&&hasValue('hcfB')){const a=num('hcfA'),b=num('hcfB');if(!Number.isSafeInteger(a)||!Number.isSafeInteger(b)){$('#hcfResult').textContent='—';$('#lcmResult').textContent='Enter whole numbers within the safe integer range'}else{const divisor=gcd(a,b),lcm=divisor?BigInt(Math.abs(a/divisor))*BigInt(Math.abs(b)):0n;$('#hcfResult').textContent=String(divisor);$('#lcmResult').textContent=`Least common multiple: ${lcm.toString()}`}}else{$('#hcfResult').textContent=$('#lcmResult').textContent='—'}
 if(hasValue('bmiWeight')&&hasValue('bmiHeight')){const weight=num('bmiWeight'),height=num('bmiHeight')/100;if(weight<=0||height<=0){$('#bmiResult').textContent='—';$('#bmiNote').textContent='Enter positive weight and height values'}else{const bmi=weight/(height*height);if(!Number.isFinite(bmi)){$('#bmiResult').textContent='—';$('#bmiNote').textContent='Values are outside the supported range'}else{const category=bmi<18.5?'Below adult reference range':bmi<25?'Within adult reference range':bmi<30?'Above adult reference range':'High adult reference range';$('#bmiResult').textContent=fmt(bmi);$('#bmiNote').textContent=`${category}; not a diagnosis`}}}else{$('#bmiResult').textContent='—';$('#bmiNote').textContent='General adult reference only; not a diagnosis.'}
 if(hasValue('savingsTarget')&&hasValue('savingsCurrent')&&hasValue('savingsMonthly')){const target=num('savingsTarget'),current=num('savingsCurrent'),monthly=num('savingsMonthly');if(target<0||current<0||monthly<0){$('#savingsResult').textContent='—';$('#savingsNote').textContent='Values must be non-negative'}else if(current>=target){$('#savingsResult').textContent='Goal reached';$('#savingsNote').textContent=`Saved so far: ${money(current)}`}else if(monthly===0){$('#savingsResult').textContent='—';$('#savingsNote').textContent='Enter a monthly saving amount above zero'}else{const remaining=target-current,months=Math.ceil(remaining/monthly);if(!Number.isFinite(months)){$('#savingsResult').textContent='—';$('#savingsNote').textContent='Goal timeline is outside the supported range'}else{$('#savingsResult').textContent=`${months} ${months===1?'month':'months'}`;$('#savingsNote').textContent=`Remaining: ${money(remaining)} at ${money(monthly)} per month`}}}else{$('#savingsResult').textContent=$('#savingsNote').textContent='—'}
 if(hasValue('unitPriceA')&&hasValue('unitQuantityA')&&hasValue('unitPriceB')&&hasValue('unitQuantityB')){const priceA=num('unitPriceA'),quantityA=num('unitQuantityA'),priceB=num('unitPriceB'),quantityB=num('unitQuantityB');if(priceA<0||priceB<0||quantityA<=0||quantityB<=0){$('#unitPriceResult').textContent='—';$('#unitPriceNote').textContent='Prices cannot be negative; quantities must be positive'}else{const perA=priceA/quantityA,perB=priceB/quantityB;if(!Number.isFinite(perA)||!Number.isFinite(perB)){$('#unitPriceResult').textContent='—';$('#unitPriceNote').textContent='Values are outside the supported range'}else{$('#unitPriceResult').textContent=Math.abs(perA-perB)<1e-10?'Same unit price':perA<perB?'Item A':'Item B';$('#unitPriceNote').textContent=`A: ${money(perA)} / unit · B: ${money(perB)} / unit`}}}else{$('#unitPriceResult').textContent=$('#unitPriceNote').textContent='—'}
 const fractionOperation=$('#fractionOperation').value,fractionFields=['fractionNumerator','fractionDenominator',...(fractionOperation==='simplify'?[]:['fractionNumeratorB','fractionDenominatorB'])],fractionSecondFields=$$('.fraction-second');fractionSecondFields.forEach(field=>field.classList.toggle('hidden',fractionOperation==='simplify'));if(fractionFields.every(hasValue)){const values=fractionFields.map(id=>Number($('#'+id).value));if(values.some(value=>!Number.isSafeInteger(value))){$('#fractionResult').textContent='—';$('#fractionNote').textContent='Enter whole numbers within the safe integer range'}else{let [a,b,c=0,d=1]=values.map(BigInt);if(b===0n||fractionOperation!=='simplify'&&d===0n){$('#fractionResult').textContent='—';$('#fractionNote').textContent='Denominators cannot be zero'}else{if(b<0n){a=-a;b=-b}if(d<0n){c=-c;d=-d}if(fractionOperation==='add'||fractionOperation==='subtract'){a=a*d+(fractionOperation==='add'?1n:-1n)*c*b;b*=d}else if(fractionOperation==='multiply'){a*=c;b*=d}else if(fractionOperation==='divide'){if(c===0n){$('#fractionResult').textContent='—';$('#fractionNote').textContent='Cannot divide by a zero fraction';a=null}else{a*=d;b*=c}}if(a!==null){if(b<0n){a=-a;b=-b}const absA=a<0n?-a:a,absB=b<0n?-b:b;let x=absA,y=absB;while(y)[x,y]=[y,x%y];const divisor=x||1n,numerator=a/divisor,denominator=b/divisor;$('#fractionResult').textContent=denominator===1n?String(numerator):`${numerator}/${denominator}`;$('#fractionNote').textContent=fractionOperation==='simplify'?'Fraction reduced to lowest terms':`Decimal: ${fmt(Number(numerator)/Number(denominator))}`}}}}else{$('#fractionResult').textContent=$('#fractionNote').textContent='—'}
 if(hasValue('primeNumber')){const value=num('primeNumber');if(!Number.isSafeInteger(value)||value<2||value>1_000_000_000){$('#primeResult').textContent='—';$('#primeNote').textContent='Enter a whole number from 2 to 1 billion'}else{let isPrime=true;for(let divisor=2;divisor*divisor<=value;divisor++){if(value%divisor===0){isPrime=false;break}}$('#primeResult').textContent=isPrime?'Prime':'Not prime';$('#primeNote').textContent=`${value} is ${isPrime?'a prime number':'not a prime number'}`}}else{$('#primeResult').textContent=$('#primeNote').textContent='—'}
 const geometryShape=$('#geometryShape').value,geometryWidthField=$('#geometryWidthField');geometryWidthField.classList.toggle('hidden',geometryShape!=='rectangle');$('#geometryLengthLabel').textContent=geometryShape==='circle'?'Radius (units)':geometryShape==='square'?'Side (units)':'Length (units)';
 if(hasValue('geometryLength')&&(geometryShape!=='rectangle'||hasValue('geometryWidth'))){const first=num('geometryLength'),second=num('geometryWidth');if(first<0||(geometryShape==='rectangle'&&second<0)){$('#geometryArea').textContent='—';$('#geometryPerimeter').textContent='Dimensions must be non-negative'}else{let area,perimeter,label;if(geometryShape==='circle'){area=Math.PI*first*first;perimeter=2*Math.PI*first;label='Circumference'}else{const width=geometryShape==='square'?first:second;area=first*width;perimeter=2*(first+width);label='Perimeter'}if(!Number.isFinite(area)||!Number.isFinite(perimeter)){$('#geometryArea').textContent='—';$('#geometryPerimeter').textContent='Dimensions are outside the supported range'}else{$('#geometryArea').textContent=`${fmt(area)} square units`;$('#geometryPerimeter').textContent=`${label}: ${fmt(perimeter)} units`}}}else{$('#geometryArea').textContent=$('#geometryPerimeter').textContent='—'}
 if(hasValue('dateCalcStart')&&hasValue('dateCalcOffset')){const start=readDateParts($('#dateCalcStart').value),offset=num('dateCalcOffset');if(!start||!Number.isSafeInteger(offset)){$('#dateCalcResult').textContent='—';$('#dateCalcNote').textContent='Enter a valid date and a whole number of days'}else{const date=new Date((dayNumber(start)+offset)*86400000),year=date.getUTCFullYear();if(!Number.isFinite(date.getTime())||year<1||year>9999){$('#dateCalcResult').textContent='—';$('#dateCalcNote').textContent='Resulting date is outside the supported range'}else{$('#dateCalcResult').textContent=`${year}-${String(date.getUTCMonth()+1).padStart(2,'0')}-${String(date.getUTCDate()).padStart(2,'0')}`;$('#dateCalcNote').textContent=offset<0?`${Math.abs(offset)} days before the starting date`:`${offset} days after the starting date`}}}else{$('#dateCalcResult').textContent=$('#dateCalcNote').textContent='—'}
 if(hasValue('timeStart')&&hasValue('timeEnd')){const [startHour,startMinute]=$('#timeStart').value.split(':').map(Number),[endHour,endMinute]=$('#timeEnd').value.split(':').map(Number);let minutes=endHour*60+endMinute-(startHour*60+startMinute);if(minutes<0)minutes+=1440;$('#timeDurationResult').textContent=`${Math.floor(minutes/60)} hr ${minutes%60} min`;$('#timeDurationNote').textContent=`${minutes} total minutes${endHour*60+endMinute<startHour*60+startMinute?' · ends the next day':''}`}else{$('#timeDurationResult').textContent=$('#timeDurationNote').textContent='—'}
 if(hasValue('sipMonthly')&&hasValue('sipRate')&&hasValue('sipYears')){const monthly=num('sipMonthly'),annualRate=num('sipRate'),years=num('sipYears'),months=Math.round(years*12),monthlyRate=annualRate/1200;if(monthly<0||annualRate<0||years<0||!Number.isSafeInteger(months)){$('#sipResult').textContent='—';$('#sipInvested').textContent='Enter non-negative values and a supported period'}else{const invested=monthly*months,future=monthly*(monthlyRate?((1+monthlyRate)**months-1)/monthlyRate:months);if(!Number.isFinite(invested)||!Number.isFinite(future)){$('#sipResult').textContent='—';$('#sipInvested').textContent='Values are outside the supported range'}else{$('#sipResult').textContent=money(future);$('#sipInvested').textContent=`Invested: ${money(invested)} · Growth: ${money(future-invested)}`}}}else{$('#sipResult').textContent='—';$('#sipInvested').textContent='Excludes taxes and fees.'}
 if(hasValue('breakEvenFixed')&&hasValue('breakEvenPrice')&&hasValue('breakEvenVariable')){const fixed=num('breakEvenFixed'),price=num('breakEvenPrice'),variable=num('breakEvenVariable'),contribution=price-variable;if(fixed<0||price<0||variable<0){$('#breakEvenResult').textContent='—';$('#breakEvenRevenue').textContent='Values must be non-negative'}else if(contribution<=0){$('#breakEvenResult').textContent='No break-even';$('#breakEvenRevenue').textContent='Price must exceed variable cost per unit'}else{const units=Math.ceil(fixed/contribution),revenue=units*price;if(!Number.isFinite(units)||!Number.isFinite(revenue)){$('#breakEvenResult').textContent='—';$('#breakEvenRevenue').textContent='Values are outside the supported range'}else{$('#breakEvenResult').textContent=`${units} ${units===1?'unit':'units'}`;$('#breakEvenRevenue').textContent=`Break-even revenue: ${money(revenue)}`}}}else{$('#breakEvenResult').textContent=$('#breakEvenRevenue').textContent='—'}
 if(hasValue('bmrAge')&&hasValue('bmrWeight')&&hasValue('bmrHeight')){const age=num('bmrAge'),weight=num('bmrWeight'),height=num('bmrHeight');if(!Number.isSafeInteger(age)||age<1||weight<=0||height<=0){$('#bmrResult').textContent='—';$('#bmrNote').textContent='Enter a positive whole-number age, weight, and height'}else{const bmr=10*weight+6.25*height-5*age+($('#bmrSex').value==='male'?5:-161);if(!Number.isFinite(bmr)||bmr<=0){$('#bmrResult').textContent='—';$('#bmrNote').textContent='Values are outside the supported range'}else{$('#bmrResult').textContent=`${fmt(bmr)} kcal/day`;$('#bmrNote').textContent='Mifflin–St Jeor estimate; individual needs vary.'}}}else{$('#bmrResult').textContent='—';$('#bmrNote').textContent='Formula-based estimate; individual needs vary.'}
 if(hasValue('paceDistance')&&hasValue('paceHours')&&hasValue('paceMinutes')){const distance=num('paceDistance'),hours=num('paceHours'),minutes=num('paceMinutes'),totalMinutes=hours*60+minutes;if(distance<=0||hours<0||!Number.isSafeInteger(hours)||minutes<0||minutes>59||!Number.isSafeInteger(minutes)||totalMinutes<=0){$('#paceResult').textContent='—';$('#paceSpeed').textContent='Enter a positive distance and valid duration'}else{const secondsPerKm=Math.round(totalMinutes*60/distance),speed=distance/(totalMinutes/60);if(!Number.isFinite(secondsPerKm)||!Number.isFinite(speed)){$('#paceResult').textContent='—';$('#paceSpeed').textContent='Values are outside the supported range'}else{$('#paceResult').textContent=`${Math.floor(secondsPerKm/60)}:${String(secondsPerKm%60).padStart(2,'0')} / km`;$('#paceSpeed').textContent=`Average speed: ${fmt(speed)} km/h`}}}else{$('#paceResult').textContent=$('#paceSpeed').textContent='—'}
 if(hasValue('quadraticA')&&hasValue('quadraticB')&&hasValue('quadraticC')){const a=num('quadraticA'),b=num('quadraticB'),c=num('quadraticC');if(a===0){if(b===0){$('#quadraticResult').textContent=c===0?'All real numbers':'No solution';$('#quadraticNote').textContent=c===0?'The equation is true for every x':'This equation has no solution'}else{const root=-c/b;$('#quadraticResult').textContent=Number.isFinite(root)?`x = ${fmt(root)}`:'—';$('#quadraticNote').textContent='Reduced to a linear equation'}}else{const discriminant=b*b-4*a*c;if(!Number.isFinite(discriminant)){$('#quadraticResult').textContent='—';$('#quadraticNote').textContent='Coefficients are outside the supported range'}else if(discriminant>0){const first=(-b+Math.sqrt(discriminant))/(2*a),second=(-b-Math.sqrt(discriminant))/(2*a);$('#quadraticResult').textContent=Number.isFinite(first)&&Number.isFinite(second)?`x₁ = ${fmt(first)}, x₂ = ${fmt(second)}`:'—';$('#quadraticNote').textContent='Two real roots'}else if(discriminant===0){const root=-b/(2*a);$('#quadraticResult').textContent=Number.isFinite(root)?`x = ${fmt(root)}`:'—';$('#quadraticNote').textContent='One repeated real root'}else{const real=-b/(2*a),imaginary=Math.sqrt(-discriminant)/(2*Math.abs(a));$('#quadraticResult').textContent=Number.isFinite(real)&&Number.isFinite(imaginary)?`x = ${fmt(real)} ± ${fmt(imaginary)}i`:'—';$('#quadraticNote').textContent='Two complex roots'}}}else{$('#quadraticResult').textContent=$('#quadraticNote').textContent='—'}
 if(hasValue('factorialNumber')){const value=num('factorialNumber');if(!Number.isSafeInteger(value)||value<0||value>18){$('#factorialResult').textContent='—';$('#factorialNote').textContent='Enter a whole number from 0 to 18'}else{let factorial=1;for(let factor=2;factor<=value;factor++)factorial*=factor;$('#factorialResult').textContent=factorial.toLocaleString('en-IN');$('#factorialNote').textContent=`${value}! = ${factorial.toLocaleString('en-IN')}`}}else{$('#factorialResult').textContent=$('#factorialNote').textContent='—'}
 if(hasValue('dateDiffStart')&&hasValue('dateDiffEnd')){const start=readDateParts($('#dateDiffStart').value),end=readDateParts($('#dateDiffEnd').value);if(!start||!end){$('#dateDiffResult').textContent='—';$('#dateDiffNote').textContent='Enter two valid dates'}else{const days=Math.abs(dayNumber(end)-dayNumber(start));$('#dateDiffResult').textContent=`${days} ${days===1?'day':'days'}`;$('#dateDiffNote').textContent=days===0?'Both dates are the same day':'The start date is not counted.'}}else{$('#dateDiffResult').textContent='—';$('#dateDiffNote').textContent='The start date is not counted.'}
 updateAge();updateAgeGap();
}
function daysInMonth(year,month){const date=new Date(0);date.setUTCHours(0,0,0,0);date.setUTCFullYear(year,month+1,0);return date.getUTCDate()}
function dayNumber({year,month,day}){const date=new Date(0);date.setUTCHours(0,0,0,0);date.setUTCFullYear(year,month,day);return date.getTime()/86400000}
function readDateParts(value){
 if(!value)return null;
 const [year,monthValue,day]=value.split('-').map(Number),month=monthValue-1;
 if(!Number.isInteger(year)||year<1||month<0||month>11||day<1||day>daysInMonth(year,month))return null;
 return{year,month,day}
}
function calendarDifference(start,end){
 let years=end.year-start.year;
 const birthdayDay=Math.min(start.day,daysInMonth(end.year,start.month));
 if(end.month<start.month||(end.month===start.month&&end.day<birthdayDay))years--;
 let months=(end.year-(start.year+years))*12+end.month-start.month;
 const anniversaryAt=offset=>{const index=(start.year+years)*12+start.month+offset,year=Math.floor(index/12),month=index-year*12;return{year,month,day:Math.min(start.day,daysInMonth(year,month))}};
 let anniversary=anniversaryAt(months);
 if(end.day<anniversary.day){months--;anniversary=anniversaryAt(months)}
 const days=dayNumber(end)-dayNumber(anniversary);
 return{years,months,days}
}
function formatDateDifference({years,months,days}){
 const parts=[];
 if(years)parts.push(`${years} ${years===1?'year':'years'}`);
 if(months)parts.push(`${months} ${months===1?'month':'months'}`);
 parts.push(`${days} ${days===1?'day':'days'}`);
 return parts.join(', ')
}
function maxBirthDate(today){return`${today.year}-${String(today.month+1).padStart(2,'0')}-${String(today.day).padStart(2,'0')}`}
function updateAge(){
 const input=$('#birthDate'),result=$('#ageResult'),note=$('#ageNextBirthday'),now=new Date(),today={year:now.getFullYear(),month:now.getMonth(),day:now.getDate()};
 input.max=maxBirthDate(today);
 const birth=readDateParts(input.value);
 if(!birth){result.textContent='—';note.textContent=input.value?'Enter a valid date of birth':'Enter your date of birth';return}
 if(dayNumber(birth)>dayNumber(today)){result.textContent='—';note.textContent='Date of birth must not be in the future';return}
 result.textContent=formatDateDifference(calendarDifference(birth,today));
 let nextBirthday={year:today.year,month:birth.month,day:Math.min(birth.day,daysInMonth(today.year,birth.month))};
 if(dayNumber(nextBirthday)<=dayNumber(today)){nextBirthday.year++;nextBirthday.day=Math.min(birth.day,daysInMonth(nextBirthday.year,birth.month))}
 const daysUntil=dayNumber(nextBirthday)-dayNumber(today);
 note.textContent=daysUntil===0?'Happy birthday!':`Next birthday in ${daysUntil} ${daysUntil===1?'day':'days'}`;
}
function updateAgeGap(){
 const firstInput=$('#birthDateOne'),secondInput=$('#birthDateTwo'),result=$('#ageGapResult'),note=$('#ageGapNote'),now=new Date(),today={year:now.getFullYear(),month:now.getMonth(),day:now.getDate()};
 firstInput.max=secondInput.max=maxBirthDate(today);
 const first=readDateParts(firstInput.value),second=readDateParts(secondInput.value);
 if(!first||!second){result.textContent='—';note.textContent=firstInput.value&&secondInput.value?'Enter valid dates of birth':'Enter both dates of birth';return}
 if(dayNumber(first)>dayNumber(today)||dayNumber(second)>dayNumber(today)){result.textContent='—';note.textContent='Dates of birth must not be in the future';return}
 const firstDay=dayNumber(first),secondDay=dayNumber(second);
 if(firstDay===secondDay){result.textContent='0 days';note.textContent='Both people are the same age';return}
 const firstOlder=firstDay<secondDay;
 result.textContent=formatDateDifference(calendarDifference(firstOlder?first:second,firstOlder?second:first));
 note.textContent=`Person ${firstOlder?'1':'2'} is older`;
}
const financialCalculatorRecipes={
 loan:{fields:[['amount','Loan amount ($)'],['rate','Annual interest (%)'],['years','Term (years)']],label:'Monthly payment',run:v=>{const months=v.years*12,rate=v.rate/1200;if(v.amount<=0||months<=0||v.rate<0)return null;const payment=rate?v.amount*rate/(1-(1+rate)**-months):v.amount/months;return [money(payment),`Total paid: ${money(payment*months)} · Interest: ${money(payment*months-v.amount)}`]}},
 mortgage:{fields:[['price','Home price ($)'],['down','Down payment ($)'],['rate','Interest rate (%)'],['years','Term (years)']],label:'Estimated monthly principal & interest',run:v=>{const principal=v.price-v.down,months=v.years*12,rate=v.rate/1200;if(principal<=0||months<=0||v.rate<0)return null;const payment=rate?principal*rate/(1-(1+rate)**-months):principal/months;return [money(payment),`Loan amount: ${money(principal)} · Excludes taxes and insurance`]}},
 payoff:{fields:[['balance','Current balance ($)'],['rate','APR (%)'],['payment','Monthly payment ($)']],label:'Estimated payoff time',run:v=>{const monthlyRate=v.rate/1200;if(v.balance<=0||v.payment<=0||v.rate<0||v.payment<=v.balance*monthlyRate)return null;const months=monthlyRate?Math.ceil(-Math.log(1-v.balance*monthlyRate/v.payment)/Math.log(1+monthlyRate)):Math.ceil(v.balance/v.payment);return [`${months} months`,`Estimated interest: ${money(v.payment*months-v.balance)}`]}},
 affordability:{fields:[['income','Gross monthly income ($)'],['debts','Monthly debt payments ($)'],['rate','Mortgage rate (%)'],['years','Term (years)']],label:'Estimated affordable home price',run:v=>{const payment=v.income*.28-v.debts,months=v.years*12,r=v.rate/1200;if(payment<=0||months<=0||r<0)return null;const loan=r?payment*(1-(1+r)**-months)/r:payment*months;return [money(loan),`Uses a 28% housing guideline; excludes taxes, insurance, and down payment`]}},
 dti:{fields:[['income','Gross monthly income ($)'],['debts','Monthly debt payments ($)']],label:'Debt-to-income ratio',run:v=>v.income>0&&v.debts>=0?[`${fmt(v.debts/v.income*100)}%`,`Monthly debts: ${money(v.debts)} of ${money(v.income)}`]:null},
 rental:{fields:[['price','Property purchase price ($)'],['rent','Monthly rent ($)'],['expenses','Monthly operating expenses ($)']],label:'Estimated cap rate',run:v=>v.price>0&&v.rent>=0&&v.expenses>=0?[`${fmt((v.rent-v.expenses)*12/v.price*100)}%`,`Annual net operating income: ${money((v.rent-v.expenses)*12)}`]:null},
 rentBuy:{fields:[['rent','Monthly rent ($)'],['price','Home price ($)'],['down','Down payment ($)'],['rate','Mortgage rate (%)'],['years','Years to compare']],label:'Estimated monthly ownership payment',run:v=>{const principal=v.price-v.down,months=v.years*12,r=v.rate/1200;if(v.rent<0||principal<=0||months<=0||r<0)return null;const mortgage=r?principal*r/(1-(1+r)**-months):principal/months;return [money(mortgage),`${mortgage<v.rent?'Mortgage P&I is below':'Mortgage P&I is above'} rent by ${money(Math.abs(mortgage-v.rent))} · Excludes tax, maintenance, and equity`]}},
 rent:{fields:[['rent','Monthly rent ($)'],['utilities','Monthly utilities ($)'],['insurance','Monthly renters insurance ($)']],label:'Estimated monthly housing cost',run:v=>v.rent>=0&&v.utilities>=0&&v.insurance>=0?[money(v.rent+v.utilities+v.insurance),`Annual housing cost: ${money((v.rent+v.utilities+v.insurance)*12)}`]:null},
 downPayment:{fields:[['price','Home price ($)'],['percent','Down payment percentage (%)']],label:'Down payment amount',run:v=>v.price>0&&v.percent>=0&&v.percent<=100?[money(v.price*v.percent/100),`Estimated loan amount: ${money(v.price*(1-v.percent/100))}`]:null},
 refinance:{fields:[['balance','Remaining loan balance ($)'],['oldRate','Current rate (%)'],['newRate','New rate (%)'],['years','Remaining term (years)'],['closing','Closing costs ($)']],label:'Estimated monthly savings',run:v=>{const months=v.years*12;if(v.balance<=0||months<=0||v.oldRate<0||v.newRate<0||v.closing<0)return null;const pay=rate=>{const r=rate/1200;return r?v.balance*r/(1-(1+r)**-months):v.balance/months};const savings=pay(v.oldRate)-pay(v.newRate);return [money(savings),`${savings>0?`Closing-cost break-even: ${fmt(v.closing/savings)} months`:'The new rate does not lower the payment'}`]}},
 debtConsolidation:{fields:[['balance','Debt balance ($)'],['oldRate','Current average APR (%)'],['newRate','Consolidation APR (%)'],['years','Repayment term (years)']],label:'Estimated monthly payment after consolidation',run:v=>{const months=v.years*12;if(v.balance<=0||months<=0||v.oldRate<0||v.newRate<0)return null;const pay=rate=>{const r=rate/1200;return r?v.balance*r/(1-(1+r)**-months):v.balance/months};const old=pay(v.oldRate),next=pay(v.newRate);return [money(next),`Compared with same-term current debt: ${money(old-next)} monthly savings · Excludes fees`]}},
 autoCompare:{fields:[['price','Vehicle price ($)'],['rebate','Cash rebate ($)'],['lowRate','Low financing APR (%)'],['highRate','Alternative APR (%)'],['years','Loan term (years)']],label:'Lower-cost option',run:v=>{const months=v.years*12;if(v.price<=0||v.rebate<0||v.rebate>=v.price||months<=0||v.lowRate<0||v.highRate<0)return null;const pay=(amount,rate)=>{const r=rate/1200;return r?amount*r/(1-(1+r)**-months):amount/months};const lowTotal=pay(v.price,v.lowRate)*months,cashTotal=pay(v.price-v.rebate,v.highRate)*months+v.rebate;return [`${lowTotal<cashTotal?'Low-rate financing':'Cash rebate'}`,`Low-rate payments: ${money(lowTotal)} · Rebate + alternative payments: ${money(cashTotal)}`]}},
 lease:{fields:[['cap','Negotiated vehicle price ($)'],['residual','Residual value (%)'],['rate','Money factor'],['months','Lease term (months)'],['down','Due at signing ($)']],label:'Estimated monthly lease payment',run:v=>{if(v.cap<=0||v.months<=0||v.residual<0||v.residual>100||v.rate<0)return null;const residual=v.cap*v.residual/100,base=(v.cap-residual)/v.months,finance=(v.cap+residual)*v.rate;return [money(base+finance),`Before tax; estimated total due: ${money((base+finance)*v.months+v.down)}`]}},
 growth:{fields:[['principal','Initial amount ($)'],['rate','Annual return (%)'],['years','Years']],label:'Future value',run:v=>{if(v.principal<0||v.rate<=-100||v.years<0)return null;const future=v.principal*(1+v.rate/100)**v.years;return [money(future),`Growth: ${money(future-v.principal)}`]}},
 presentValue:{fields:[['future','Future amount ($)'],['rate','Annual discount rate (%)'],['years','Years until received']],label:'Present value',run:v=>v.future>=0&&v.rate>-100&&v.years>=0?[money(v.future/(1+v.rate/100)**v.years),`Discounted at ${fmt(v.rate)}% per year`]:null},
 monthlyGrowth:{fields:[['initial','Initial investment ($)'],['monthly','Monthly contribution ($)'],['rate','Annual return (%)'],['years','Years']],label:'Estimated future value',run:v=>{const months=Math.round(v.years*12),r=v.rate/1200;if(v.initial<0||v.monthly<0||v.years<0||v.rate<=-1200)return null;const future=v.initial*(1+r)**months+v.monthly*(r?((1+r)**months-1)/r:months);return [money(future),`Contributions: ${money(v.initial+v.monthly*months)} · Assumes monthly deposits`]}},
 apr:{fields:[['amount','Amount borrowed ($)'],['fee','Upfront fees ($)'],['rate','Nominal annual rate (%)'],['years','Term (years)']],label:'Estimated effective APR',run:v=>{const months=Math.round(v.years*12),principal=v.amount-v.fee;if(principal<=0||months<=0||v.rate<0)return null;const r=v.rate/1200,payment=r?v.amount*r/(1-(1+r)**-months):v.amount/months;let low=0,high=1;for(let i=0;i<80;i++){const mid=(low+high)/2,pv=payment*(1-(1+mid)**-months)/mid;if(pv>principal)low=mid;else high=mid}return [`${fmt(((low+high)/2)*1200)}%`,`Approximate annualized rate including the fee`]}},
 bond:{fields:[['face','Face value ($)'],['price','Purchase price ($)'],['coupon','Annual coupon rate (%)'],['years','Years to maturity']],label:'Estimated yield to maturity',run:v=>{if(v.face<=0||v.price<=0||v.years<=0)return null;const annualCoupon=v.face*v.coupon/100,yieldRate=(annualCoupon+(v.face-v.price)/v.years)/((v.face+v.price)/2)*100;return [`${fmt(yieldRate)}%`,`Approximation; assumes annual coupons and holding to maturity`]}},
 roi:{fields:[['investment','Initial investment ($)'],['value','Ending value ($)'],['years','Years held']],label:'Annualized return',run:v=>v.investment>0&&v.value>=0&&v.years>0?[`${fmt(((v.value/v.investment)**(1/v.years)-1)*100)}%`,`Total return: ${fmt((v.value/v.investment-1)*100)}%`]:null},
 payback:{fields:[['investment','Initial investment ($)'],['cashflow','Annual net cash flow ($)']],label:'Payback period',run:v=>v.investment>=0&&v.cashflow>0?[`${fmt(v.investment/v.cashflow,2)} years`,`Annual cash flow: ${money(v.cashflow)}`]:null},
 annuity:{fields:[['principal','Annuity principal ($)'],['rate','Annual return (%)'],['years','Payout period (years)']],label:'Estimated monthly payout',run:v=>{const months=v.years*12,r=v.rate/1200;if(v.principal<=0||months<=0||r<0)return null;const payout=r?v.principal*r/(1-(1+r)**-months):v.principal/months;return [money(payout),`Total payouts: ${money(payout*months)} · Before taxes and fees`]}},
 pension:{fields:[['salary','Final average annual salary ($)'],['service','Years of service'],['multiplier','Benefit multiplier (%)']],label:'Estimated annual pension',run:v=>v.salary>0&&v.service>=0&&v.multiplier>=0?[money(v.salary*v.service*v.multiplier/100),`Estimated monthly benefit: ${money(v.salary*v.service*v.multiplier/1200)}`]:null},
 social:{fields:[['benefit','Monthly benefit at full retirement age ($)'],['claim','Claiming age'],['fullAge','Full retirement age']],label:'Estimated monthly Social Security benefit',run:v=>{if(v.benefit<=0||v.claim<62||v.fullAge<62||v.claim>70)return null;const months=Math.round((v.claim-v.fullAge)*12),factor=months<0?1+Math.max(-36,months)*5/900+Math.min(0,months+36)*5/1200:1+Math.min(48,months)*2/300;return [money(v.benefit*factor),`Simplified estimate; actual benefits depend on SSA earnings records and rules`]}},
 rmd:{fields:[['balance','Retirement account balance ($)'],['age','Age'],['divisor','IRS life-expectancy divisor']],label:'Estimated required minimum distribution',run:v=>v.balance>=0&&v.age>=73&&v.divisor>0?[money(v.balance/v.divisor),`Uses the divisor you provide; verify the applicable IRS table and account rules`]:null},
 federalTax:{fields:[['income','Taxable income ($)']],label:'Estimated 2025 federal income tax (single filer)',run:v=>{if(v.income<0)return null;const brackets=[[11925,.10],[48475,.12],[103350,.22],[197300,.24],[250525,.32],[626350,.35],[Infinity,.37]];let lower=0,tax=0;for(const [upper,rate] of brackets){tax+=Math.max(0,Math.min(v.income,upper)-lower)*rate;if(v.income<=upper)break;lower=upper}return [money(tax),`Federal income tax estimate only; excludes deductions, credits, state, and payroll taxes`]}},
 federalTaxJoint:{fields:[['income','Joint taxable income ($)']],label:'Estimated 2025 federal income tax (married filing jointly)',run:v=>{if(v.income<0)return null;const brackets=[[23850,.10],[96950,.12],[206700,.22],[394600,.24],[501050,.32],[751600,.35],[Infinity,.37]];let lower=0,tax=0;for(const [upper,rate] of brackets){tax+=Math.max(0,Math.min(v.income,upper)-lower)*rate;if(v.income<=upper)break;lower=upper}return [money(tax),`Federal income tax estimate only; excludes deductions, credits, state, and payroll taxes`]}},
 estate:{fields:[['estate','Taxable estate value ($)'],['exemption','Applicable exemption ($)'],['rate','Estimated tax rate (%)']],label:'Estimated estate tax',run:v=>v.estate>=0&&v.exemption>=0&&v.rate>=0?[money(Math.max(0,v.estate-v.exemption)*v.rate/100),`Uses your entered exemption and rate; confirm current federal and state rules`]:null},
 paycheck:{fields:[['salary','Gross annual salary ($)'],['tax','Estimated tax withholding (%)'],['deductions','Other annual deductions ($)']],label:'Estimated monthly take-home pay',run:v=>v.salary>=0&&v.tax>=0&&v.tax<=100&&v.deductions>=0?[money((v.salary*(1-v.tax/100)-v.deductions)/12),`Uses the withholding rate you enter; excludes detailed payroll calculations`]:null},
 tax:{fields:[['amount','Purchase amount ($)'],['rate','Tax rate (%)']],label:'Tax-inclusive total',run:v=>v.amount>=0&&v.rate>=0?[money(v.amount*(1+v.rate/100)),`Tax: ${money(v.amount*v.rate/100)}`]:null},
 currency:{fields:[['amount','Amount to convert'],['rate','Exchange rate (target units per 1 source unit)']],label:'Converted amount',run:v=>v.amount>=0&&v.rate>0?[fmt(v.amount*v.rate),`Uses your exchange rate; no live currency feed`]:null},
 inflation:{fields:[['amount','Current amount ($)'],['rate','Annual inflation (%)'],['years','Years']],label:'Future equivalent cost',run:v=>v.amount>=0&&v.rate>-100&&v.years>=0?[money(v.amount*(1+v.rate/100)**v.years),`Additional amount: ${money(v.amount*((1+v.rate/100)**v.years-1))}`]:null},
 depreciation:{fields:[['cost','Asset cost ($)'],['salvage','Salvage value ($)'],['years','Useful life (years)']],label:'Annual straight-line depreciation',run:v=>v.cost>=v.salvage&&v.salvage>=0&&v.years>0?[money((v.cost-v.salvage)/v.years),`Estimated book value after 1 year: ${money(v.cost-(v.cost-v.salvage)/v.years)}`]:null},
 margin:{fields:[['cost','Cost ($)'],['price','Selling price ($)']],label:'Profit margin',run:v=>v.cost>=0&&v.price>0?[`${fmt((v.price-v.cost)/v.price*100)}%`,`Markup on cost: ${fmt(v.cost?(v.price-v.cost)/v.cost*100:0)}%`]:null},
 budget:{fields:[['income','Monthly take-home income ($)'],['housing','Housing ($)'],['living','Living expenses ($)'],['debt','Debt payments ($)'],['savings','Savings ($)']],label:'Unallocated monthly balance',run:v=>v.income>=0&&v.housing>=0&&v.living>=0&&v.debt>=0&&v.savings>=0?[money(v.income-v.housing-v.living-v.debt-v.savings),`Expenses and savings: ${money(v.housing+v.living+v.debt+v.savings)}`]:null},
 commission:{fields:[['sales','Sales amount ($)'],['rate','Commission rate (%)'],['base','Base pay ($)']],label:'Total compensation',run:v=>v.sales>=0&&v.rate>=0&&v.base>=0?[money(v.base+v.sales*v.rate/100),`Commission earned: ${money(v.sales*v.rate/100)}`]:null},
 college:{fields:[['cost','Current annual college cost ($)'],['inflation','Annual cost increase (%)'],['years','Years until enrollment']],label:'Estimated annual cost at enrollment',run:v=>v.cost>=0&&v.inflation>=0&&v.years>=0?[money(v.cost*(1+v.inflation/100)**v.years),`Estimated four-year total at constant future cost: ${money(v.cost*(1+v.inflation/100)**v.years*4)}`]:null}
};
const financialCalculatorCatalog=[
 ['Mortgage Calculator','mortgage'],['Amortization Calculator','loan'],['Mortgage Payoff Calculator','payoff'],['House Affordability Calculator','affordability'],['Rent Calculator','rent'],['Debt-to-Income Ratio Calculator','dti'],['Real Estate Calculator','rental'],['Refinance Calculator','refinance'],['Rental Property Calculator','rental'],['APR Calculator','apr'],['FHA Loan Calculator','mortgage'],['VA Mortgage Calculator','mortgage'],['Home Equity Loan Calculator','loan'],['HELOC Calculator','loan'],['Down Payment Calculator','downPayment'],['Rent vs. Buy Calculator','rentBuy'],
 ['Auto Loan Calculator','loan'],['Cash Back or Low Interest Calculator','autoCompare'],['Auto Lease Calculator','lease'],
 ['Interest Calculator','growth'],['Investment Calculator','monthlyGrowth'],['Finance Calculator','loan'],['Interest Rate Calculator','roi'],['Savings Calculator','monthlyGrowth'],['CD Calculator','growth'],['Bond Calculator','bond'],['Mutual Fund Calculator','monthlyGrowth'],['Average Return Calculator','roi'],['IRR Calculator','roi'],['ROI Calculator','roi'],['Payback Period Calculator','payback'],['Present Value Calculator','presentValue'],['Future Value Calculator','growth'],
 ['401K Calculator','monthlyGrowth'],['Pension Calculator','pension'],['Social Security Calculator','social'],['Annuity Calculator','annuity'],['Annuity Payout Calculator','annuity'],['Roth IRA Calculator','monthlyGrowth'],['IRA Calculator','monthlyGrowth'],['RMD Calculator','rmd'],
 ['Income Tax Calculator','federalTax'],['Salary Calculator','paycheck'],['Marriage Tax Calculator','federalTaxJoint'],['Estate Tax Calculator','estate'],['Take-Home Paycheck Calculator','paycheck'],
 ['Loan Calculator','loan'],['Payment Calculator','loan'],['Currency Calculator','currency'],['Inflation Calculator','inflation'],['Sales Tax Calculator','tax'],['Credit Card Calculator','payoff'],['Credit Cards Payoff Calculator','payoff'],['Debt Payoff Calculator','payoff'],['Debt Consolidation Calculator','debtConsolidation'],['Repayment Calculator','loan'],['Student Loan Calculator','loan'],['College Cost Calculator','college'],['VAT Calculator','tax'],['Depreciation Calculator','depreciation'],['Margin Calculator','margin'],['Business Loan Calculator','loan'],['Personal Loan Calculator','loan'],['Boat Loan Calculator','loan'],['Lease Calculator','lease'],['Budget Calculator','budget'],['Commission Calculator','commission']
];
function renderFinancialCalculators(){
 const grid=$('#view-tools .tool-grid');
 financialCalculatorCatalog.forEach(([title,recipeName],index)=>{
  const recipe=financialCalculatorRecipes[recipeName];
  const card=document.createElement('article');card.className='panel tool-card financial-tool-card';card.dataset.financialIndex=String(index);
  const fields=recipe.fields.map(([key,label])=>`<label class="field-control"><span>${label}</span><input type="number" step="any" data-financial-field="${key}" aria-label="${label}"></label>`).join('');
  card.innerHTML=`<div class="tool-card-head"><div class="tool-symbol">$</div><div><h3>${title}</h3><p>Estimate using your inputs.</p></div></div><div class="tool-fields two-fields">${fields}</div><div class="tool-output"><span>${recipe.label}</span><output>—</output><small>Enter values to calculate.</small></div>`;
  grid.append(card);toolCategoryByName[title]='financial';
 });
}
function updateFinancialCalculators(){
 $$('.financial-tool-card').forEach(card=>{
  const recipe=financialCalculatorRecipes[financialCalculatorCatalog[Number(card.dataset.financialIndex)][1]],inputs=[...card.querySelectorAll('[data-financial-field]')],output=card.querySelector('output'),note=card.querySelector('small');
  if(inputs.some(input=>input.value.trim()==='')){output.textContent='—';note.textContent='Enter values to calculate.';return}
  const values=Object.fromEntries(inputs.map(input=>[input.dataset.financialField,Number(input.value)]));
  if(Object.values(values).some(value=>!Number.isFinite(value))){output.textContent='—';note.textContent='Enter valid numbers.';return}
  let result;
  try{financialUSCurrency=true;result=recipe.run(values)}finally{financialUSCurrency=false}
  if(!result||result.some(value=>typeof value==='number'&&!Number.isFinite(value)||typeof value==='string'&&/\b(?:NaN|Infinity)\b/.test(value))){output.textContent='—';note.textContent='Check the inputs and supported ranges.';return}
  [output.textContent,note.textContent]=result;
 });
}
const otherCalculatorRecipes={
 time:{fields:[['start','Start time','time'],['end','End time','time']],label:'Elapsed time',run:v=>{const [sh,sm]=v.start.split(':').map(Number),[eh,em]=v.end.split(':').map(Number);let minutes=eh*60+em-sh*60-sm;if(minutes<0)minutes+=1440;return [`${Math.floor(minutes/60)} hr ${minutes%60} min`,`${minutes} total minutes${eh*60+em<sh*60+sm?' · crosses midnight':''}`]}},
 hours:{fields:[['hours','Hours','number'],['minutes','Minutes','number'],['seconds','Seconds','number']],label:'Total hours',run:v=>[fmt(v.hours+v.minutes/60+v.seconds/3600),`${fmt(v.hours*3600+v.minutes*60+v.seconds)} total seconds`]},
 timeCard:{fields:[['start','Clock-in time','time'],['end','Clock-out time','time'],['break','Unpaid break (minutes)','number'],['rate','Hourly pay ($)','number']],label:'Hours worked',run:v=>{const [sh,sm]=v.start.split(':').map(Number),[eh,em]=v.end.split(':').map(Number);let minutes=eh*60+em-sh*60-sm;if(minutes<0)minutes+=1440;minutes-=v.break;if(minutes<0||v.rate<0)return null;return [`${fmt(minutes/60)} hours`,`Estimated pay: $${(minutes/60*v.rate).toFixed(2)}`]}},
 timeZone:{fields:[['time','Local time','time'],['from','Current UTC offset (hours)','number'],['to','Target UTC offset (hours)','number']],label:'Converted local time',run:v=>{const [h,m]=v.time.split(':').map(Number),total=h*60+m+(v.to-v.from)*60,day=Math.floor(total/1440),minute=((total%1440)+1440)%1440;return [`${String(Math.floor(minute/60)).padStart(2,'0')}:${String(minute%60).padStart(2,'0')}`,day<0?'Previous day':day>0?'Next day':'Same day']}},
 dateDiff:{fields:[['start','Start date','date'],['end','End date','date']],label:'Days between dates',run:v=>{const a=Date.parse(`${v.start}T00:00:00Z`),b=Date.parse(`${v.end}T00:00:00Z`);return [fmt(Math.abs(b-a)/86400000)+' days',b<a?'End date is earlier than start date':'Start date is not counted']}},
 weekday:{fields:[['date','Date','date']],label:'Day of the week',run:v=>[new Date(`${v.date}T00:00:00Z`).toLocaleDateString('en-US',{weekday:'long',timeZone:'UTC'}),v.date]},
 ip:{fields:[['address','IPv4 address','text'],['prefix','Prefix length (0–32)','number']],label:'Network details',run:v=>{const octets=v.address.split('.').map(Number),prefix=v.prefix;if(octets.length!==4||octets.some(n=>!Number.isInteger(n)||n<0||n>255)||!Number.isInteger(prefix)||prefix<0||prefix>32)return null;const ip=octets.reduce((n,x)=>((n<<8)|x)>>>0,0),mask=prefix===0?0:(0xffffffff<<(32-prefix))>>>0,network=(ip&mask)>>>0,broadcast=(network|(~mask>>>0))>>>0,print=n=>[n>>>24,(n>>>16)&255,(n>>>8)&255,n&255].join('.'),hosts=prefix>=31?2**(32-prefix):2**(32-prefix)-2;return [`${print(network)}/${prefix}`,`Mask ${print(mask)} · Broadcast ${print(broadcast)} · ${hosts} usable hosts`]}},
 password:{fields:[['length','Password length (8–128)','number']],label:'Generated password',run:()=>['','Choose a length, then generate a password.']},
 bandwidth:{fields:[['size','File size (MB)','number'],['speed','Connection speed (Mbps)','number']],label:'Estimated download time',run:v=>{if(v.size<0||v.speed<=0)return null;const seconds=v.size*8/v.speed;return [`${fmt(seconds/60)} minutes`,`${fmt(seconds)} seconds at the stated speed`]}},
 base64:{fields:[['text','Text','text'],['mode','Action','select',[['encode','Encode'],['decode','Decode']]]],label:'Base64 result',run:v=>{try{if(v.mode==='encode'){const bytes=new TextEncoder().encode(v.text);let binary='';bytes.forEach(byte=>binary+=String.fromCharCode(byte));return [btoa(binary),'Encoded locally in your browser']}const binary=atob(v.text),bytes=Uint8Array.from(binary,char=>char.charCodeAt(0));return [new TextDecoder('utf-8',{fatal:true}).decode(bytes),'Decoded locally in your browser']}catch{return null}}},
 url:{fields:[['text','Text or URL component','text'],['mode','Action','select',[['encode','Encode'],['decode','Decode']]]],label:'URL encoding result',run:v=>{try{return [v.mode==='encode'?encodeURIComponent(v.text):decodeURIComponent(v.text),''] }catch{return null}}},
 concrete:{fields:[['length','Length (feet)','number'],['width','Width (feet)','number'],['depth','Thickness (inches)','number'],['waste','Extra material (%)','number']],label:'Concrete required',run:v=>{if(v.length<=0||v.width<=0||v.depth<=0||v.waste<0)return null;const yards=v.length*v.width*(v.depth/12)/27*(1+v.waste/100);return [`${fmt(yards,2)} cubic yards`,`Includes ${fmt(v.waste)}% extra`]}},
 btu:{fields:[['area','Room area (sq ft)','number'],['factor','Sun exposure factor (0.9–1.3)','number'],['people','People beyond two','number']],label:'Estimated cooling capacity',run:v=>v.area>0&&v.factor>=.9&&v.factor<=1.3&&v.people>=0?[`${fmt((v.area*20+v.people*600)*v.factor)} BTU/hr`,'Rule-of-thumb estimate; insulation, climate, and windows affect sizing']:null},
 area:{fields:[['length','Length (feet)','number'],['width','Width (feet)','number']],label:'Area',run:v=>v.length>0&&v.width>0?[`${fmt(v.length*v.width)} sq ft`,`Perimeter: ${fmt(2*(v.length+v.width))} ft`]:null},
 stairs:{fields:[['height','Floor-to-floor height (inches)','number'],['rise','Maximum desired riser height (inches)','number'],['tread','Tread depth (inches)','number']],label:'Stair layout estimate',run:v=>{if(v.height<=0||v.rise<=0||v.tread<=0)return null;const risers=Math.ceil(v.height/v.rise),actual=v.height/risers;return [`${risers} risers`,`${fmt(actual)} in per riser · Approx. run ${fmt((risers-1)*v.tread)} in`]}},
 roof:{fields:[['length','Building length (feet)','number'],['width','Building width (feet)','number'],['pitch','Roof pitch (rise per 12 in)','number'],['waste','Extra material (%)','number']],label:'Estimated roof surface area',run:v=>{if(v.length<=0||v.width<=0||v.pitch<0||v.waste<0)return null;const area=v.length*v.width*Math.sqrt(1+(v.pitch/12)**2)*(1+v.waste/100);return [`${fmt(area)} sq ft`,`Includes ${fmt(v.waste)}% extra`]}},
 tile:{fields:[['area','Surface area (sq ft)','number'],['length','Tile length (inches)','number'],['width','Tile width (inches)','number'],['waste','Extra material (%)','number']],label:'Tiles to purchase',run:v=>{if(v.area<=0||v.length<=0||v.width<=0||v.waste<0)return null;const count=Math.ceil(v.area*144/(v.length*v.width)*(1+v.waste/100));return [`${count} tiles`,`Includes ${fmt(v.waste)}% extra`]}},
 bulk:{fields:[['length','Length (feet)','number'],['width','Width (feet)','number'],['depth','Depth (inches)','number']],label:'Material volume',run:v=>{if(v.length<=0||v.width<=0||v.depth<=0)return null;const cubicFeet=v.length*v.width*v.depth/12;return [`${fmt(cubicFeet/27)} cubic yards`,`${fmt(cubicFeet)} cubic feet`]}},
 gpa:{fields:[['grades','Grades separated by commas (A, B+, 3.5)','text']],label:'Grade point average',run:v=>{const points={A:4,'A-':3.7,'B+':3.3,B:3,'B-':2.7,'C+':2.3,C:2,'C-':1.7,'D+':1.3,D:1,'D-':.7,F:0},items=v.grades.split(/[,\s]+/).filter(Boolean).map(g=>points[g.toUpperCase()]??Number(g));if(!items.length||items.some(n=>!Number.isFinite(n)||n<0||n>4))return null;const avg=items.reduce((a,b)=>a+b,0)/items.length;return [fmt(avg),`${items.length} grades · 4.0 scale`]}},
 sgpa:{fields:[['points','Course grade points (comma-separated, 0–10)','text'],['credits','Course credits (same order)','text']],label:'Semester Grade Point Average (SGPA)',description:'Calculate a credit-weighted GPA for one semester.',run:v=>runWeightedGradeAverage(v,'courses')},
 cgpa:{fields:[['points','Semester GPAs (comma-separated, 0–10)','text'],['credits','Credits earned per semester (same order)','text']],label:'Cumulative Grade Point Average (CGPA)',description:'Combine semester GPAs weighted by credits earned.',run:v=>runWeightedGradeAverage(v,'semesters')},
 ygpa:{fields:[['points','Course grade points (comma-separated, 0–10)','text'],['credits','Course credits (same order)','text']],label:'Yearly Grade Point Average (YGPA)',description:'Calculate a credit-weighted GPA for one academic year.',run:v=>runWeightedGradeAverage(v,'courses')},
 ogpa:{fields:[['points','Yearly GPAs (comma-separated, 0–10)','text'],['credits','Credits earned per year (same order)','text']],label:'Overall Grade Point Average (OGPA)',description:'Combine yearly GPAs weighted by credits earned.',run:v=>runWeightedGradeAverage(v,'years')},
 grade:{fields:[['earned','Points earned','number'],['possible','Points possible','number']],label:'Percentage grade',run:v=>{if(v.earned<0||v.possible<=0)return null;const score=v.earned/v.possible*100,letter=score>=90?'A':score>=80?'B':score>=70?'C':score>=60?'D':'F';return [`${fmt(score)}% (${letter})`,`${fmt(v.earned)} of ${fmt(v.possible)} points`]}},
 bra:{fields:[['band','Underbust measurement (inches)','number'],['bust','Bust measurement (inches)','number']],label:'Estimated bra size (US)',run:v=>{if(v.band<=0||v.bust<=0)return null;const band=Math.round(v.band/2)*2,cup=Math.max(0,Math.min(11,Math.round(v.bust-band))),letters='A B C D DD DDD G H I J K L'.split(' ');return [`${band}${letters[cup]}`,`Approximate sizing; brand and fit vary`]}},
 shoe:{fields:[['size','US shoe size','number'],['system','US sizing','select',[['men','Men'],['women','Women']]]],label:'Approximate shoe-size conversions',run:v=>{if(v.size<1||v.size>18)return null;const cm=(v.size+(v.system==='men'?24:22.5))/3*2.54,eu=v.system==='men'?v.size*1.5+33:v.size+30;return [`${fmt(cm)} cm`,`${fmt(eu)} EU · Approximate conversion`]}},
 golf:{fields:[['scores','Score differentials separated by commas','text']],label:'Estimated golf handicap index',run:v=>{const scores=v.scores.split(/[,\s]+/).filter(Boolean).map(Number);if(scores.length<3||scores.some(n=>!Number.isFinite(n)||n<0))return null;const count=Math.min(8,scores.length),average=scores.sort((a,b)=>a-b).slice(0,count).reduce((a,b)=>a+b,0)/count;return [fmt(average*.96),`Average of the lowest ${count} entered differentials × 0.96; official rules may differ`]}},
 sleep:{fields:[['wake','Desired wake-up time','time']],label:'Suggested bedtimes',run:v=>{const [h,m]=v.wake.split(':').map(Number),wake=h*60+m;const times=[9,7.5,6].map(hours=>{const minute=((wake-Math.round(hours*60)-15)%1440+1440)%1440;return `${String(Math.floor(minute/60)).padStart(2,'0')}:${String(minute%60).padStart(2,'0')}`});return [times.join(' · '),'For 9, 7.5, or 6 hours of sleep plus 15 minutes to fall asleep']}},
 wind:{fields:[['temp','Air temperature (°F)','number'],['speed','Wind speed (mph)','number']],label:'Wind chill',run:v=>{if(v.temp>50||v.speed<3)return null;const w=v.speed**.16,chill=35.74+.6215*v.temp-35.75*w+.4275*v.temp*w;return [`${fmt(chill)} °F`,'NOAA formula; valid for temperatures ≤50°F and wind ≥3 mph']}},
 heat:{fields:[['temp','Air temperature (°F)','number'],['humidity','Relative humidity (%)','number']],label:'Heat index',run:v=>{if(v.temp<80||v.humidity<0||v.humidity>100)return null;const t=v.temp,r=v.humidity,index=-42.379+2.04901523*t+10.14333127*r-.22475541*t*r-.00683783*t*t-.05481717*r*r+.00122874*t*t*r+.00085282*t*r*r-.00000199*t*t*r*r;return [`${fmt(index)} °F`,'Rothfusz estimate; most applicable at heat index ≥80°F']}},
 dew:{fields:[['temp','Air temperature (°C)','number'],['humidity','Relative humidity (%)','number']],label:'Dew point',run:v=>{if(v.humidity<=0||v.humidity>100)return null;const a=17.625,b=243.04,g=Math.log(v.humidity/100)+a*v.temp/(b+v.temp);return [`${fmt(b*g/(a-g))} °C`,'Magnus approximation']}},
 humidity:{fields:[['temp','Air temperature (°C)','number'],['dewpoint','Dew point (°C)','number']],label:'Relative humidity',description:'Estimate relative humidity from air temperature and dew point using a Magnus approximation.',run:v=>{if(v.temp< -80||v.temp>60||v.dewpoint< -80||v.dewpoint>v.temp)return null;const vaporPressure=t=>6.112*Math.exp(17.62*t/(243.12+t)),rh=100*vaporPressure(v.dewpoint)/vaporPressure(v.temp);return [`${fmt(rh)}%`,'Estimated from air temperature and dew point']}},
 feelsLike:{fields:[['temp','Air temperature (°C)','number'],['humidity','Relative humidity (%)','number'],['wind','Wind speed at 10 m (m/s)','number']],label:'Apparent temperature',description:'Shade-based apparent-temperature estimate; solar radiation is not included.',run:v=>{if(v.temp< -50||v.temp>60||v.humidity<0||v.humidity>100||v.wind<0)return null;const vaporPressure=v.humidity/100*6.105*Math.exp(17.27*v.temp/(237.7+v.temp)),apparent=v.temp+.33*vaporPressure-.70*v.wind-4;return [`${fmt(apparent)} °C`,`${fmt(apparent*9/5+32)} °F · Shade-based estimate; solar radiation is not included`]}},
 uv:{fields:[['irradiance','Erythemally weighted UV irradiance (W/m²)','number']],label:'UV Index',description:'Convert erythemally weighted UV irradiance to the UV Index.',run:v=>{if(v.irradiance<0)return null;const index=40*v.irradiance,category=index<3?'Low':index<6?'Moderate':index<8?'High':index<11?'Very high':'Extreme';return [`${fmt(index)}`,category]}},
 wetBulb:{fields:[['temp','Air temperature (°C)','number'],['humidity','Relative humidity (%)','number']],label:'Wet-bulb temperature',description:'Approximation using air temperature and relative humidity.',run:v=>{if(v.temp< -20||v.temp>50||v.humidity<5||v.humidity>99)return null;const t=v.temp,rh=v.humidity,wet=t*Math.atan(.151977*Math.sqrt(rh+8.313659))+Math.atan(t+rh)-Math.atan(rh-1.676331)+.00391838*rh**1.5*Math.atan(.023101*rh)-4.686035;return [`${fmt(wet)} °C`,'Stull approximation; valid for −20 to 50°C and 5 to 99% relative humidity']}},
 cloudBase:{fields:[['temp','Surface air temperature (°C)','number'],['dewpoint','Surface dew point (°C)','number']],label:'Estimated cloud-base height',description:'Estimate lifting condensation level from surface temperature and dew point.',run:v=>{if(v.temp< -80||v.temp>60||v.dewpoint< -80||v.dewpoint>v.temp)return null;const height=125*(v.temp-v.dewpoint);return [`${fmt(height)} m`,`${fmt(height*3.28084)} ft · Approximate lifting condensation level`]}},
 pressure:{fields:[['altitude','Elevation above sea level (m)','number'],['seaLevel','Sea-level pressure (hPa)','number']],label:'Estimated station pressure',description:'Estimate local pressure using the standard-atmosphere barometric formula.',run:v=>{if(v.altitude< -500||v.altitude>10000||v.seaLevel<=0)return null;const pressure=v.seaLevel*Math.pow(1-2.25577e-5*v.altitude,5.25588);return [`${fmt(pressure)} hPa`,`${fmt(pressure/10)} kPa · Standard-atmosphere estimate`]}},
 windSpeed:{fields:[['speed','Wind speed (m/s)','number']],label:'Wind speed conversions',description:'Convert wind speed and estimate its Beaufort force.',run:v=>{if(v.speed<0||v.speed>200)return null;const thresholds=[.3,1.6,3.4,5.5,8,10.8,13.9,17.2,20.8,24.5,28.5,32.7],beaufort=thresholds.findIndex(limit=>v.speed<limit);return [`${fmt(v.speed*3.6)} km/h`,`${fmt(v.speed*2.236936)} mph · ${fmt(v.speed*1.943844)} knots · Beaufort ${beaufort<0?12:beaufort}`]}},
 rainfall:{fields:[['depth','Rainfall depth (mm)','number'],['area','Collection area (m²)','number']],label:'Collected rainwater volume',description:'Estimate collected water assuming all rainfall reaches the collection area.',run:v=>{if(v.depth<0||v.area<0)return null;const liters=v.depth*v.area;return [`${fmt(liters)} L`,`${fmt(liters/1000)} m³ · Assumes 100% collection efficiency`]}},
 solarRadiation:{fields:[['irradiance','Average solar irradiance (W/m²)','number'],['hours','Exposure duration (hours)','number']],label:'Solar energy per area',description:'Estimate incident solar energy from average irradiance and exposure duration.',run:v=>{if(v.irradiance<0||v.hours<0)return null;const energy=v.irradiance*v.hours/1000;return [`${fmt(energy)} kWh/m²`,`${fmt(energy*3.6)} MJ/m² over ${fmt(v.hours)} hours`]}},
 mileage:{fields:[['distance','Distance driven (miles)','number'],['fuel','Fuel used (US gallons)','number']],label:'Fuel economy',run:v=>v.distance>=0&&v.fuel>0?[`${fmt(v.distance/v.fuel)} mpg`,`Fuel used: ${fmt(v.fuel)} gallons`]:null},
 horsepower:{fields:[['torque','Torque (lb-ft)','number'],['rpm','Engine speed (RPM)','number']],label:'Horsepower',run:v=>v.torque>=0&&v.rpm>=0?[`${fmt(v.torque*v.rpm/5252)} hp`,`Based on torque × RPM ÷ 5,252`]:null},
 engineHorsepower:{fields:[['torque','Torque (N·m)','number'],['rpm','Engine speed (RPM)','number']],label:'Engine power',run:v=>v.torque>=0&&v.rpm>=0?[`${fmt(v.torque*v.rpm/9549)} kW`,`Approximately ${fmt(v.torque*v.rpm/7127)} hp`]:null},
 tire:{fields:[['width','Tire width (mm)','number'],['aspect','Aspect ratio (%)','number'],['rim','Wheel diameter (inches)','number']],label:'Overall tire diameter',run:v=>{if(v.width<=0||v.aspect<=0||v.rim<=0)return null;const side=v.width*v.aspect/100/25.4,diameter=2*side+v.rim;return [`${fmt(diameter)} in`,`${fmt(diameter*25.4)} mm · Circumference ${fmt(diameter*Math.PI)} in`]}},
 height:{fields:[['feet','Height (feet)','number'],['inches','Additional inches','number']],label:'Height in centimeters',run:v=>v.feet>=0&&v.inches>=0?[`${fmt((v.feet*12+v.inches)*2.54)} cm`,`${fmt(v.feet*12+v.inches)} total inches`]:null},
 convert:{fields:[['value','Value','number'],['from','Convert from','select',[['m','Meters'],['ft','Feet'],['in','Inches'],['cm','Centimeters']]],['to','Convert to','select',[['m','Meters'],['ft','Feet'],['in','Inches'],['cm','Centimeters']]]],label:'Converted length',run:v=>{const factors={m:1,ft:.3048,in:.0254,cm:.01},answer=v.value*factors[v.from]/factors[v.to];return [fmt(answer),`${v.value} ${v.from} = ${fmt(answer)} ${v.to}`]}},
 gdp:{fields:[['gdp','GDP ($)','number'],['population','Population','number']],label:'GDP per capita',run:v=>v.gdp>=0&&v.population>0?[`$${fmt(v.gdp/v.population)}`,'GDP divided by population'] :null},
 density:{fields:[['mass','Mass (kg)','number'],['volume','Volume (m³)','number']],label:'Density',run:v=>v.mass>=0&&v.volume>0?[`${fmt(v.mass/v.volume)} kg/m³`,`${fmt(v.mass/v.volume/1000)} g/cm³`]:null},
 mass:{fields:[['mass','Mass (kg)','number']],label:'Mass conversions',run:v=>v.mass>=0?[`${fmt(v.mass*2.20462262)} lb`,`${fmt(v.mass*1000)} g · ${fmt(v.mass*35.27396)} oz`]:null},
 speed:{fields:[['distance','Distance (km)','number'],['time','Time (hours)','number']],label:'Average speed',run:v=>v.distance>=0&&v.time>0?[`${fmt(v.distance/v.time)} km/h`,`${fmt(v.distance/v.time/1.609344)} mph`]:null},
 molarity:{fields:[['moles','Solute amount (moles)','number'],['volume','Solution volume (liters)','number']],label:'Molarity',run:v=>v.moles>=0&&v.volume>0?[`${fmt(v.moles/v.volume)} mol/L`,`${fmt(v.moles/v.volume)} M`]:null},
 molecular:{fields:[['formula','Chemical formula (e.g. H2O)','text']],label:'Molecular mass',run:v=>{const atomic={H:1.008,He:4.0026,Li:6.94,Be:9.0122,B:10.81,C:12.011,N:14.007,O:15.999,F:18.998,Ne:20.18,Na:22.99,Mg:24.305,Al:26.982,Si:28.085,P:30.974,S:32.06,Cl:35.45,Ar:39.948,K:39.098,Ca:40.078,Fe:55.845,Cu:63.546,Zn:65.38,Br:79.904,Ag:107.868,I:126.904,Au:196.967};const tokens=v.formula.match(/[A-Z][a-z]?\d*/g)||[];if(!tokens.length||tokens.join('')!==v.formula)return null;let mass=0;for(const token of tokens){const [,symbol,countText]=token.match(/^([A-Z][a-z]?)(\d*)$/)||[];if(!atomic[symbol])return null;mass+=atomic[symbol]*(Number(countText)||1)}return [`${fmt(mass)} g/mol`,v.formula] }},
 roman:{fields:[['value','Number or Roman numeral','text'],['mode','Convert','select',[['toRoman','Number to Roman'],['toNumber','Roman to number']]]],label:'Conversion result',run:v=>{if(v.mode==='toRoman'){let n=Number(v.value);if(!Number.isInteger(n)||n<1||n>3999)return null;let result='';for(const [value,symbol] of [[1000,'M'],[900,'CM'],[500,'D'],[400,'CD'],[100,'C'],[90,'XC'],[50,'L'],[40,'XL'],[10,'X'],[9,'IX'],[5,'V'],[4,'IV'],[1,'I']])while(n>=value){result+=symbol;n-=value}return [result,'Number converted to Roman numerals']}const numeral=v.value.toUpperCase();if(!/^(?=[MDCLXVI]+$)M{0,3}(CM|CD|D?C{0,3})(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})$/.test(numeral))return null;const values={I:1,V:5,X:10,L:50,C:100,D:500,M:1000};let total=0;for(let i=0;i<numeral.length;i++)total+=values[numeral[i]]<(values[numeral[i+1]]||0)?-values[numeral[i]]:values[numeral[i]];return [String(total),`${numeral} converted to a number`]}},
 voltage:{fields:[['current','Current (amps)','number'],['length','One-way wire length (feet)','number'],['resistance','Wire resistance (Ω per 1,000 ft)','number'],['voltage','Supply voltage (V)','number']],label:'Estimated voltage drop',run:v=>{if(v.current<0||v.length<0||v.resistance<0||v.voltage<=0)return null;const drop=2*v.current*v.length*v.resistance/1000;return [`${fmt(drop)} V`,`${fmt(drop/v.voltage*100)}% of supply voltage`]}},
 resistor:{fields:[['voltage','Voltage (V)','number'],['current','Current (A)','number']],label:'Resistance',run:v=>v.voltage>=0&&v.current>0?[`${fmt(v.voltage/v.current)} Ω`,`Power: ${fmt(v.voltage*v.current)} W`]:null},
 ohms:{fields:[['voltage','Voltage (V)','number'],['current','Current (A)','number'],['resistance','Resistance (Ω)','number']],label:'Calculated value',run:v=>{const missing=Object.entries(v).filter(([,n])=>!Number.isFinite(n));if(missing.length!==1)return null;const [key]=missing[0];return key==='voltage'&&v.current>=0&&v.resistance>=0?[`${fmt(v.current*v.resistance)} V`,'V = I × R']:key==='current'&&v.resistance>0&&v.voltage>=0?[`${fmt(v.voltage/v.resistance)} A`,'I = V ÷ R']:key==='resistance'&&v.current>0&&v.voltage>=0?[`${fmt(v.voltage/v.current)} Ω`,'R = V ÷ I']:null}},
 electricity:{fields:[['watts','Power draw (watts)','number'],['hours','Hours used per day','number'],['days','Days per month','number'],['rate','Electricity rate ($/kWh)','number']],label:'Estimated monthly electricity cost',run:v=>{if(v.watts<0||v.hours<0||v.hours>24||v.days<0||v.rate<0)return null;const kwh=v.watts/1000*v.hours*v.days;return [`$${(kwh*v.rate).toFixed(2)}`,`${fmt(kwh)} kWh per month`]}},
 capacitiveReactance:{fields:[['frequency','Frequency (Hz)','number'],['capacitance','Capacitance (µF)','number']],label:'Capacitive reactance',run:v=>{if(v.frequency<=0||v.capacitance<=0)return null;const reactance=1/(2*Math.PI*v.frequency*v.capacitance*1e-6);return Number.isFinite(reactance)?[`${fmt(reactance)} Ω`,`${fmt(reactance/1000)} kΩ · Xc = 1/(2πfC)`]:null}},
 inductiveReactance:{fields:[['frequency','Frequency (Hz)','number'],['inductance','Inductance (mH)','number']],label:'Inductive reactance',run:v=>{if(v.frequency<=0||v.inductance<=0)return null;const reactance=2*Math.PI*v.frequency*v.inductance*1e-3;return Number.isFinite(reactance)?[`${fmt(reactance)} Ω`,`${fmt(reactance/1000)} kΩ · XL = 2πfL`]:null}},
 resonantFrequency:{fields:[['inductance','Inductance (mH)','number'],['capacitance','Capacitance (µF)','number']],label:'Resonant frequency',run:v=>{if(v.inductance<=0||v.capacitance<=0)return null;const frequency=1/(2*Math.PI*Math.sqrt(v.inductance*1e-3*v.capacitance*1e-6));return Number.isFinite(frequency)?[`${fmt(frequency)} Hz`,`${fmt(frequency/1000)} kHz · f₀ = 1/(2π√LC)`]:null}},
 batteryLife:{fields:[['capacity','Battery capacity (mAh)','number'],['current','Average current draw (mA)','number']],label:'Estimated battery life',run:v=>{if(v.capacity<=0||v.current<=0)return null;const hours=v.capacity/v.current;return Number.isFinite(hours)?[`${fmt(hours)} hours`,`${fmt(hours/24)} days · Ideal estimate; actual life varies with usable capacity and load`]:null}},
 dice:{fields:[['sides','Number of sides per die','number'],['count','Number of dice','number']],label:'Roll result',run:()=>['','Press Roll to generate random dice.']},
 love:{fields:[['first','First name','text'],['second','Second name','text']],label:'Compatibility score',run:v=>{const names=[v.first.trim().toLowerCase(),v.second.trim().toLowerCase()].sort().join('|');if(!v.first.trim()||!v.second.trim())return null;let hash=0;for(const char of names)hash=(hash*31+char.charCodeAt(0))>>>0;return [`${hash%101}%`,'For entertainment only; not a measure of compatibility']}}
};
function runWeightedGradeAverage(values,period){
 const points=parseNumberList(values.points),credits=parseNumberList(values.credits);
 if(!points||!credits||points.length!==credits.length||points.some(point=>point<0||point>10)||credits.some(credit=>credit<=0))return null;
 const totalCredits=credits.reduce((sum,credit)=>sum+credit,0),average=points.reduce((sum,point,index)=>sum+point*credits[index],0)/totalCredits;
 return [fmt(average),`${points.length} ${period} · ${fmt(totalCredits)} total credits · weighted by credits`];
}
const otherCalculatorCatalog=[
 ['Time Calculator','time'],['Hours Calculator','hours'],['Time Card Calculator','timeCard'],['Time Zone Calculator','timeZone'],['Day Counter','dateDiff'],['Day of the Week Calculator','weekday'],
 ['IP Subnet Calculator','ip'],['Password Generator','password'],['Bandwidth Calculator','bandwidth'],['Base64 Encode / Decode','base64'],['URL Encode / Decode','url'],
 ['Concrete Calculator','concrete'],['BTU Calculator','btu'],['Square Footage Calculator','area'],['Stair Calculator','stairs'],['Roofing Calculator','roof'],['Tile Calculator','tile'],['Mulch Calculator','bulk'],['Gravel Calculator','bulk'],
 ['GPA Calculator','gpa'],['SGPA Calculator','sgpa'],['CGPA Calculator','cgpa'],['YGPA Calculator','ygpa'],['OGPA Calculator','ogpa'],['Grade Calculator','grade'],['Bra Size Calculator','bra'],['Shoe Size Conversion','shoe'],['Golf Handicap Calculator','golf'],['Sleep Calculator','sleep'],
 ['Wind Chill Calculator','wind'],['Heat Index Calculator','heat'],['Dew Point Calculator','dew'],
 ['Humidity Calculator','humidity'],['Feels Like Calculator','feelsLike'],['UV Index Calculator','uv'],['Wet Bulb Temperature Calculator','wetBulb'],['Cloud Base Calculator','cloudBase'],['Atmospheric Pressure Calculator','pressure'],['Wind Speed Calculator','windSpeed'],['Rainfall Calculator','rainfall'],['Solar Radiation Calculator','solarRadiation'],
 ['Gas Mileage Calculator','mileage'],['Horsepower Calculator','horsepower'],['Engine Horsepower Calculator','engineHorsepower'],['Mileage Calculator','mileage'],['Tire Size Calculator','tire'],
 ['Height Calculator','height'],['Conversion Calculator','convert'],['GDP Calculator','gdp'],['Density Calculator','density'],['Mass Calculator','mass'],['Weight Calculator','mass'],['Speed Calculator','speed'],['Molarity Calculator','molarity'],['Molecular Weight Calculator','molecular'],['Roman Numeral Converter','roman'],
 ['Voltage Drop Calculator','voltage'],['Resistor Calculator','resistor'],['Ohms Law Calculator','ohms'],['Electricity Calculator','electricity'],
 ['Capacitive Reactance Calculator','capacitiveReactance'],['Inductive Reactance Calculator','inductiveReactance'],['Resonant Frequency Calculator','resonantFrequency'],['Battery Life Calculator','batteryLife'],
 ['Dice Roller','dice'],['Love Calculator','love']
];
function renderOtherCalculators(){
 const grid=$('#view-tools .tool-grid');
 otherCalculatorCatalog.forEach(([title,recipeName],index)=>{
  const recipe=otherCalculatorRecipes[recipeName];
  const card=document.createElement('article');card.className='panel tool-card other-tool-card';card.dataset.otherIndex=String(index);
  const fields=recipe.fields.map(([key,label,type='number',options])=>`<label class="field-control"><span>${label}</span>${type==='select'?`<select data-other-field="${key}" aria-label="${label}">${options.map(([value,text])=>`<option value="${value}">${text}</option>`).join('')}</select>`:`<input type="${type}" ${type==='number'?'step="any"':''} data-other-field="${key}" aria-label="${label}">`}</label>`).join('');
  const button=['password','dice'].includes(recipeName)?`<button class="outline-btn other-generate" type="button">${recipeName==='password'?'Generate password':'Roll dice'}</button>`:'';
  card.innerHTML=`<div class="tool-card-head"><div class="tool-symbol">${recipeName==='ip'?'⌘':'↗'}</div><div><h3>${title}</h3><p>${recipe.description||'Enter values to calculate.'}</p></div></div><div class="tool-fields two-fields">${fields}</div>${button}<div class="tool-output"><span>${recipe.label}</span><output>—</output><small>${recipe.note||'Enter values to calculate.'}</small></div>`;
  grid.append(card);toolCategoryByName[title]='other';
 });
}
function updateOtherCalculators(){
 $$('.other-tool-card').forEach(card=>{
  const recipe=otherCalculatorRecipes[otherCalculatorCatalog[Number(card.dataset.otherIndex)][1]],inputs=[...card.querySelectorAll('[data-other-field]')],output=card.querySelector('output'),note=card.querySelector('small');
  const values=Object.fromEntries(inputs.map(input=>[input.dataset.otherField,input.type==='number'?(input.value.trim()===''?NaN:Number(input.value)):input.value]));
  if(recipe===otherCalculatorRecipes.ohms){if(Object.values(values).filter(Number.isFinite).length!==2){output.textContent='—';note.textContent='Enter exactly two values to calculate the third.';return}}
  else if(inputs.some(input=>input.value.trim()==='')){output.textContent='—';note.textContent='Enter values to calculate.';return}
  if(recipe!==otherCalculatorRecipes.ohms&&Object.values(values).some(value=>typeof value==='number'&&!Number.isFinite(value))){output.textContent='—';note.textContent='Enter valid numbers.';return}
  const result=recipe.run(values);
  if(!result||result.some(value=>typeof value==='number'&&!Number.isFinite(value)||typeof value==='string'&&/\b(?:NaN|Infinity)\b/.test(value))){output.textContent='—';note.textContent='Check the inputs and supported ranges.';return}
  [output.textContent,note.textContent]=result;
 });
}
const healthCalculatorRecipes={
 calories:{fields:[['age','Age (years)','number'],['weight','Weight (kg)','number'],['height','Height (cm)','number'],['sex','Sex used by formula','select',[['female','Female'],['male','Male']]],['activity','Activity level','select',[['1.2','Sedentary'],['1.375','Light'],['1.55','Moderate'],['1.725','High'],['1.9','Very high']]]],label:'Estimated daily calories to maintain weight',run:v=>{const bmr=10*v.weight+6.25*v.height-5*v.age+(v.sex==='male'?5:-161);return v.age>0&&v.weight>0&&v.height>0?[`${fmt(bmr*Number(v.activity))} kcal/day`,'Mifflin–St Jeor estimate; activity and individual needs vary']:null}},
 bodyFat:{fields:[['sex','Formula','select',[['male','Male'],['female','Female']]],['height','Height (inches)','number'],['waist','Waist (inches)','number'],['neck','Neck (inches)','number'],['hip','Hip (inches; women)','number']],label:'Estimated body fat',run:v=>{if(v.height<=0||v.waist<=0||v.neck<=0)return null;const isFemale=v.sex==='female',measure=isFemale?v.waist+v.hip-v.neck:v.waist-v.neck;if(measure<=0||isFemale&&v.hip<=0)return null;const percent=(isFemale?163.205*Math.log10(measure)-97.684*Math.log10(v.height)-78.387:86.01*Math.log10(measure)-70.041*Math.log10(v.height)+36.76);return percent>=0&&percent<=75?[`${fmt(percent)}%`,'Tape-measure estimate; not a diagnosis']:null}},
 idealWeight:{fields:[['height','Height (cm)','number'],['sex','Formula','select',[['female','Female'],['male','Male']]]],label:'Estimated ideal body weight',run:v=>{const inches=v.height/2.54;if(inches<60||inches>84)return null;const kg=(v.sex==='male'?50:45.5)+2.3*(inches-60);return [`${fmt(kg)} kg`,`Devine formula estimate at ${fmt(v.height)} cm`]}},
 leanMass:{fields:[['weight','Weight (kg)','number'],['fat','Body fat (%)','number']],label:'Estimated lean body mass',run:v=>v.weight>0&&v.fat>=0&&v.fat<=75?[`${fmt(v.weight*(1-v.fat/100))} kg`,`Fat mass: ${fmt(v.weight*v.fat/100)} kg`]:null},
 healthyWeight:{fields:[['height','Height (cm)','number']],label:'Adult BMI reference weight range',run:v=>{const m=v.height/100;if(m<=0)return null;return [`${fmt(18.5*m*m)}–${fmt(24.9*m*m)} kg`,'Based on adult BMI 18.5–24.9; not a personal medical target']}},
 caloriesBurned:{fields:[['weight','Weight (kg)','number'],['minutes','Exercise duration (minutes)','number'],['met','Activity MET value','number']],label:'Estimated calories burned',run:v=>v.weight>0&&v.minutes>=0&&v.met>0?[`${fmt(v.met*3.5*v.weight/200*v.minutes)} kcal`,'MET-based estimate; actual energy use varies'] :null},
 oneRep:{fields:[['weight','Lifted weight (kg)','number'],['reps','Repetitions (1–10)','number']],label:'Estimated one-rep maximum',run:v=>v.weight>0&&Number.isInteger(v.reps)&&v.reps>=1&&v.reps<=10?[`${fmt(v.reps===1?v.weight:v.weight*(1+v.reps/30))} kg`,'Epley estimate; avoid maximal lifts without appropriate supervision']:null},
 targetHeart:{fields:[['age','Age (years)','number'],['resting','Resting heart rate (bpm)','number'],['intensity','Target intensity (%)','number']],label:'Target heart rate',run:v=>{if(v.age<1||v.resting<30||v.resting>120||v.intensity<50||v.intensity>100)return null;const max=208-.7*v.age;return [`${Math.round(v.resting+(max-v.resting)*v.intensity/100)} bpm`,`Estimated max heart rate: ${Math.round(max)} bpm · Formula-based guidance only`]}},
 tdee:{fields:[['age','Age (years)','number'],['weight','Weight (kg)','number'],['height','Height (cm)','number'],['sex','Sex used by formula','select',[['female','Female'],['male','Male']]],['activity','Activity level','select',[['1.2','Sedentary'],['1.375','Light'],['1.55','Moderate'],['1.725','High'],['1.9','Very high']]]],label:'Estimated total daily energy expenditure',run:v=>{const bmr=10*v.weight+6.25*v.height-5*v.age+(v.sex==='male'?5:-161);return v.age>0&&v.weight>0&&v.height>0?[`${fmt(bmr*Number(v.activity))} kcal/day`,'Mifflin–St Jeor estimate; activity and individual needs vary']:null}},
 pregnancy:{fields:[['lmp','First day of last period','date'],['cycle','Average cycle length (days)','number']],label:'Pregnancy estimate',run:v=>{const lmp=new Date(`${v.lmp}T00:00:00Z`),today=new Date(),todayUTC=Date.UTC(today.getUTCFullYear(),today.getUTCMonth(),today.getUTCDate()),days=Math.floor((todayUTC-lmp.getTime())/86400000),due=new Date(lmp.getTime()+(280+v.cycle-28)*86400000);if(!Number.isInteger(v.cycle)||v.cycle<20||v.cycle>45||days<0)return null;return [`${Math.floor(days/7)} weeks ${days%7} days`,`Estimated due date: ${due.toISOString().slice(0,10)} · Clinical dating may differ`]}},
 dueDate:{fields:[['lmp','First day of last period','date'],['cycle','Average cycle length (days)','number']],label:'Estimated due date',run:v=>{if(!Number.isInteger(v.cycle)||v.cycle<20||v.cycle>45)return null;const date=new Date(`${v.lmp}T00:00:00Z`);date.setUTCDate(date.getUTCDate()+280+v.cycle-28);return [date.toISOString().slice(0,10),'Estimate based on last period and cycle length; confirm with a clinician']}},
 ovulation:{fields:[['lmp','First day of last period','date'],['cycle','Average cycle length (days)','number']],label:'Estimated ovulation date',run:v=>{if(!Number.isInteger(v.cycle)||v.cycle<20||v.cycle>45)return null;const date=new Date(`${v.lmp}T00:00:00Z`);date.setUTCDate(date.getUTCDate()+v.cycle-14);const fertileStart=new Date(date.getTime()-5*86400000),fertileEnd=new Date(date.getTime()+86400000);return [date.toISOString().slice(0,10),`Estimated fertile window: ${fertileStart.toISOString().slice(0,10)} to ${fertileEnd.toISOString().slice(0,10)}`]}},
 conception:{fields:[['lmp','First day of last period','date'],['cycle','Average cycle length (days)','number']],label:'Estimated conception timing',run:v=>{if(!Number.isInteger(v.cycle)||v.cycle<20||v.cycle>45)return null;const ovulation=new Date(`${v.lmp}T00:00:00Z`);ovulation.setUTCDate(ovulation.getUTCDate()+v.cycle-14);const start=new Date(ovulation.getTime()-5*86400000);return [ovulation.toISOString().slice(0,10),`Estimated fertile window begins ${start.toISOString().slice(0,10)}; dates are approximate`]}},
 pregnancyWeight:{fields:[['weight','Pre-pregnancy weight (kg)','number'],['height','Height (cm)','number'],['week','Current pregnancy week (1–40)','number']],label:'Singleton pregnancy weight-gain range',run:v=>{const height=v.height/100,bmi=v.weight/(height*height);if(v.weight<=0||height<=0||!Number.isInteger(v.week)||v.week<1||v.week>40)return null;const ranges=bmi<18.5?[12.5,18,.44,.58]:bmi<25?[11.5,16,.4,.5]:bmi<30?[7,11.5,.23,.33]:[5,9,.17,.27],weeks=Math.max(0,v.week-13),low=v.week<=13?.5:.5+weeks*ranges[2],high=v.week<=13?2:2+weeks*ranges[3];return [`${fmt(low)}–${fmt(high)} kg`,`BMI-based guide for singleton pregnancy; recommended total gain ${ranges[0]}–${ranges[1]} kg. Ask your clinician for personal guidance.`]}},
 period:{fields:[['lmp','First day of last period','date'],['cycle','Average cycle length (days)','number'],['duration','Period duration (days)','number']],label:'Estimated next period',run:v=>{if(!Number.isInteger(v.cycle)||v.cycle<20||v.cycle>45||!Number.isInteger(v.duration)||v.duration<1||v.duration>10)return null;const start=new Date(`${v.lmp}T00:00:00Z`);start.setUTCDate(start.getUTCDate()+v.cycle);const end=new Date(start.getTime()+(v.duration-1)*86400000);return [start.toISOString().slice(0,10),`Estimated period end: ${end.toISOString().slice(0,10)}`]}},
 macro:{fields:[['calories','Daily calories (kcal)','number'],['protein','Protein share (%)','number'],['carbs','Carbohydrate share (%)','number'],['fat','Fat share (%)','number']],label:'Daily macro targets',run:v=>Math.abs(v.protein+v.carbs+v.fat-100)<.1&&v.calories>0?[`${fmt(v.protein*v.calories/400)} g protein`,`Carbohydrate ${fmt(v.carbs*v.calories/400)} g · Fat ${fmt(v.fat*v.calories/900)} g`]:null},
 carbohydrate:{fields:[['calories','Daily calories (kcal)','number'],['share','Carbohydrate share (%)','number']],label:'Daily carbohydrate target',run:v=>v.calories>0&&v.share>=0&&v.share<=100?[`${fmt(v.calories*v.share/4)} g/day`,`${fmt(v.calories*v.share)} kcal from carbohydrates`]:null},
 protein:{fields:[['weight','Weight (kg)','number'],['target','Protein target (g per kg)','number']],label:'Daily protein target',run:v=>v.weight>0&&v.target>=0?[`${fmt(v.weight*v.target)} g/day`,`${fmt(v.weight*v.target*4)} kcal from protein`]:null},
 fatIntake:{fields:[['calories','Daily calories (kcal)','number'],['share','Fat share (%)','number']],label:'Daily fat target',run:v=>v.calories>0&&v.share>=0&&v.share<=100?[`${fmt(v.calories*v.share/9)} g/day`,`${fmt(v.calories*v.share)} kcal from fat`]:null},
 gfr:{fields:[['creatinine','Serum creatinine (mg/dL)','number'],['age','Age (years)','number'],['sex','Formula input','select',[['female','Female'],['male','Male']]]],label:'Estimated GFR (2021 CKD-EPI)',run:v=>{if(v.creatinine<=0||v.age<18||v.age>120)return null;const female=v.sex==='female',k=female?.7:.9,a=female?-.241:-.302,scr=v.creatinine;const egfr=142*Math.min(scr/k,1)**a*Math.max(scr/k,1)**-1.2*.9938**v.age*(female?1.012:1);return [`${fmt(egfr)} mL/min/1.73m²`,'Screening estimate only; kidney health requires clinician interpretation']}},
 bodyType:{fields:[['waist','Waist (cm)','number'],['hip','Hip (cm)','number'],['sex','Reference','select',[['female','Female'],['male','Male']]]],label:'Waist-to-hip ratio',run:v=>{if(v.waist<=0||v.hip<=0)return null;const ratio=v.waist/v.hip,threshold=v.sex==='male'?.9:.85;return [`${fmt(ratio)}`,`${ratio>=threshold?'Higher':'Lower'} central measurement ratio; not a diagnosis`]}},
 bsa:{fields:[['weight','Weight (kg)','number'],['height','Height (cm)','number']],label:'Body surface area',run:v=>v.weight>0&&v.height>0?[`${fmt(Math.sqrt(v.weight*v.height/3600))} m²`,'Mosteller formula estimate']:null},
 bac:{fields:[['weight','Body weight (kg)','number'],['drinks','US standard drinks (14 g alcohol each)','number'],['hours','Hours since drinking began','number'],['sex','Formula input','select',[['female','Female'],['male','Male']]]],label:'Estimated blood alcohol concentration',run:v=>{if(v.weight<=0||v.drinks<0||v.hours<0)return null;const grams=v.drinks*14,r=v.sex==='male'?.68:.55,bac=Math.max(0,grams/(r*v.weight*10)-.015*v.hours);return [`${fmt(bac,3)}%`,`Very rough estimate; absorption varies. Do not use this to decide whether it is safe to drive.`]}}
};
const healthCalculatorCatalog=[
 ['Calorie Calculator','calories'],['Body Fat Calculator','bodyFat'],['Ideal Weight Calculator','idealWeight'],['Army Body Fat Calculator','bodyFat'],['Lean Body Mass Calculator','leanMass'],['Healthy Weight Calculator','healthyWeight'],['Calories Burned Calculator','caloriesBurned'],['One Rep Max Calculator','oneRep'],['Target Heart Rate Calculator','targetHeart'],
 ['Pregnancy Calculator','pregnancy'],['Pregnancy Weight Gain Calculator','pregnancyWeight'],['Pregnancy Conception Calculator','conception'],['Due Date Calculator','dueDate'],['Ovulation Calculator','ovulation'],['Conception Calculator','conception'],['Period Calculator','period'],
 ['Macro Calculator','macro'],['Carbohydrate Calculator','carbohydrate'],['Protein Calculator','protein'],['Fat Intake Calculator','fatIntake'],['TDEE Calculator','tdee'],['GFR Calculator','gfr'],['Body Type Calculator','bodyType'],['Body Surface Area Calculator','bsa'],['BAC Calculator','bac']
];
function renderHealthCalculators(){
 const grid=$('#view-tools .tool-grid');
 healthCalculatorCatalog.forEach(([title,recipeName],index)=>{
  const recipe=healthCalculatorRecipes[recipeName];
  const fields=recipe.fields.map(([key,label,type='number',options])=>`<label class="field-control"><span>${label}</span>${type==='select'?`<select data-health-field="${key}" aria-label="${label}">${options.map(([value,text])=>`<option value="${value}">${text}</option>`).join('')}</select>`:`<input type="${type}" ${type==='number'?'step="any"':''} data-health-field="${key}" aria-label="${label}">`}</label>`).join('');
  const card=document.createElement('article');card.className='panel tool-card health-tool-card';card.dataset.healthIndex=String(index);
  card.innerHTML=`<div class="tool-card-head"><div class="tool-symbol">◉</div><div><h3>${title}</h3><p>Estimate using your inputs.</p></div></div><div class="tool-fields two-fields">${fields}</div><div class="tool-output"><span>${recipe.label}</span><output>—</output><small>General estimate only; individual circumstances vary.</small></div>`;
  grid.append(card);toolCategoryByName[title]='health';
 });
}
function updateHealthCalculators(){
 $$('.health-tool-card').forEach(card=>{
  const recipe=healthCalculatorRecipes[healthCalculatorCatalog[Number(card.dataset.healthIndex)][1]],inputs=[...card.querySelectorAll('[data-health-field]')],output=card.querySelector('output'),note=card.querySelector('small');
  const values=Object.fromEntries(inputs.map(input=>[input.dataset.healthField,input.type==='number'?(input.value.trim()===''?NaN:Number(input.value)):input.value]));
  const requiredInputs=recipe===healthCalculatorRecipes.bodyFat&&values.sex==='male'?inputs.filter(input=>input.dataset.healthField!=='hip'):inputs;
  if(requiredInputs.some(input=>input.value.trim()==='')){output.textContent='—';note.textContent='Enter the required values to calculate.';return}
  if(inputs.some(input=>input.type==='number'&&input.value.trim()!==''&&!Number.isFinite(Number(input.value)))){output.textContent='—';note.textContent='Enter valid numbers.';return}
  const result=recipe.run(values);
  if(!result||result.some(value=>typeof value==='number'&&!Number.isFinite(value)||typeof value==='string'&&/\b(?:NaN|Infinity)\b/.test(value))){output.textContent='—';note.textContent='Check the inputs and supported ranges.';return}
  [output.textContent,note.textContent]=result;
 });
}
function secureRandomInteger(max){
 if(!Number.isSafeInteger(max)||max<1||!globalThis.crypto?.getRandomValues)return null;
 const limit=Math.floor(0x100000000/max)*max,buffer=new Uint32Array(1);
 do{globalThis.crypto.getRandomValues(buffer)}while(buffer[0]>=limit);
 return buffer[0]%max;
}
function generateOtherResult(event){
 const button=event.target.closest('.other-generate');if(!button)return;
 const card=button.closest('.other-tool-card'),recipeName=otherCalculatorCatalog[Number(card.dataset.otherIndex)][1],output=card.querySelector('output'),note=card.querySelector('small'),inputs=[...card.querySelectorAll('[data-other-field]')];
 if(!globalThis.crypto?.getRandomValues){output.textContent='—';note.textContent='Secure random generation is unavailable in this browser.';return}
 if(recipeName==='password'){
  const length=Number(inputs[0].value),groups=['ABCDEFGHJKLMNPQRSTUVWXYZ','abcdefghijkmnopqrstuvwxyz','23456789','!@#$%^&*()-_=+'];
  if(!Number.isInteger(length)||length<8||length>128){output.textContent='—';note.textContent='Choose a length from 8 to 128.';return}
  const pool=groups.join(''),password=groups.map(group=>group[secureRandomInteger(group.length)]);
  while(password.length<length)password.push(pool[secureRandomInteger(pool.length)]);
  for(let i=password.length-1;i>0;i--){const j=secureRandomInteger(i+1);[password[i],password[j]]=[password[j],password[i]]}
  output.textContent=password.join('');note.textContent='Generated locally with the browser cryptographic random source.';
  return;
 }
 const sides=Number(inputs[0].value),count=Number(inputs[1].value);
 if(!Number.isInteger(sides)||sides<2||sides>10000||!Number.isInteger(count)||count<1||count>100){output.textContent='—';note.textContent='Use 2–10,000 sides and 1–100 dice.';return}
 const rolls=Array.from({length:count},()=>secureRandomInteger(sides)+1);
 output.textContent=rolls.join(', ');note.textContent=`Total: ${rolls.reduce((sum,value)=>sum+value,0)}`;
}
const mathCalculatorRecipes={
 scientific:{fields:[['expression','Expression (for example 2*sin(30)+sqrt(9)','text']],label:'Result',run:v=>{try{return [fmt(safeEval(v.expression)),'Uses CalcX scientific functions; angle mode is degrees'] }catch(error){return null}}},
 random:{fields:[['minimum','Minimum integer'],['maximum','Maximum integer']],label:'Random integer',run:v=>{if(!Number.isSafeInteger(v.minimum)||!Number.isSafeInteger(v.maximum)||v.maximum<v.minimum||v.maximum-v.minimum>=4294967296)return null;const value=secureRandomInteger(v.maximum-v.minimum+1);return value===null?null:[String(v.minimum+value),'Generated locally with the browser random source']}},
 percentError:{fields:[['actual','Actual or experimental value'],['expected','Expected or reference value']],label:'Percent error',run:v=>v.expected!==0?[`${fmt(Math.abs(v.actual-v.expected)/Math.abs(v.expected)*100)}%`,`|actual − expected| ÷ |expected| × 100`]:null},
 exponent:{fields:[['base','Base'],['exponent','Exponent']],label:'Power',run:v=>{const result=Math.pow(v.base,v.exponent);return Number.isFinite(result)?[fmt(result),`${fmt(v.base)} raised to ${fmt(v.exponent)}`]:null}},
 binary:{fields:[['a','Binary number A','text'],['operation','Operation','select',[['add','Add'],['subtract','Subtract'],['multiply','Multiply'],['divide','Divide']]],['b','Binary number B','text']],label:'Binary result',run:v=>runRadixOperation(v,2)},
 hex:{fields:[['a','Hexadecimal number A','text'],['operation','Operation','select',[['add','Add'],['subtract','Subtract'],['multiply','Multiply'],['divide','Divide']]],['b','Hexadecimal number B','text']],label:'Hexadecimal result',run:v=>runRadixOperation(v,16)},
 halfLife:{fields:[['amount','Starting amount'],['halfLife','Half-life (time units)'],['elapsed','Elapsed time (same units)']],label:'Amount remaining',run:v=>v.amount>=0&&v.halfLife>0&&v.elapsed>=0?[fmt(v.amount*Math.pow(.5,v.elapsed/v.halfLife)),`Fraction remaining: ${fmt(Math.pow(.5,v.elapsed/v.halfLife)*100)}%`]:null},
 log:{fields:[['value','Number (x)'],['base','Logarithm base']],label:'Logarithm',run:v=>v.value>0&&v.base>0&&v.base!==1?[fmt(Math.log(v.value)/Math.log(v.base)),`log base ${fmt(v.base)} of ${fmt(v.value)}`]:null},
 root:{fields:[['value','Number'],['index','Root index (positive integer)']],label:'Root',run:v=>{if(!Number.isInteger(v.index)||v.index<1||v.index>99||v.value<0&&v.index%2===0)return null;const result=v.value<0?-Math.pow(-v.value,1/v.index):Math.pow(v.value,1/v.index);return Number.isFinite(result)?[fmt(result),`${v.index}${v.index===2?'nd':'th'} root`]:null}},
 lcm:{fields:[['numbers','Whole numbers (comma separated)','text']],label:'Least common multiple',run:v=>{const parts=v.numbers.split(/[,;\s]+/).filter(Boolean);if(!parts.length||parts.length>100||parts.some(part=>!/^[-+]?\d+$/.test(part)))return null;const values=parts.map(part=>BigInt(part));let result=0n;for(const value of values){let a=result<0n?-result:result,b=value<0n?-value:value;while(b)[a,b]=[b,a%b];result=a===0n?0n:(result/a)*value;if(result<0n)result=-result}return [result.toString(),`${values.length} whole numbers`]}},
 factor:{fields:[['value','Whole number (up to 1 trillion)']],label:'Prime factorization',run:v=>{if(!Number.isSafeInteger(v.value)||Math.abs(v.value)>1e12||v.value===0)return null;let n=Math.abs(v.value);if(n===1)return [String(v.value),'1 has no prime factors'];const factors=[];for(let p=2;p*p<=n;p+=(p===2?1:2)){let count=0;while(n%p===0){n/=p;count++}if(count)factors.push(count===1?String(p):`${p}^${count}`)}if(n>1)factors.push(String(n));return [`${v.value<0?'-1 × ':''}${factors.join(' × ')}`,'Prime factorization']}},
 rounding:{fields:[['value','Number to round'],['places','Decimal places (−10 to 15)']],label:'Rounded number',run:v=>{if(!Number.isInteger(v.places)||v.places< -10||v.places>15)return null;const factor=10**Math.abs(v.places),rounded=v.places>=0?Math.sign(v.value)*Math.round(Math.abs(v.value)*factor)/factor:Math.sign(v.value)*Math.round(Math.abs(v.value)/factor)*factor;return Number.isFinite(rounded)?[fmt(rounded),`${v.places} decimal places`]:null}},
 matrix:{fields:[['a','Matrix A (rows separated by ;, values by ,)','text'],['operation','Operation','select',[['add','Add'],['subtract','Subtract'],['multiply','Multiply']]],['b','Matrix B (rows separated by ;, values by ,)','text']],label:'Matrix result',run:v=>{const parse=text=>text.split(';').map(row=>row.split(',').map(value=>value.trim()===''?NaN:Number(value))),a=parse(v.a),b=parse(v.b);if([...a,...b].some(row=>!row.length||row.some(n=>!Number.isFinite(n)))||a.length>6||b.length>6||a.some(row=>row.length>6)||b.some(row=>row.length>6)||a.some(row=>row.length!==a[0].length)||b.some(row=>row.length!==b[0].length))return null;let result;if(v.operation==='multiply'){if(a[0].length!==b.length)return null;result=a.map(row=>b[0].map((_,column)=>row.reduce((sum,value,index)=>sum+value*b[index][column],0)))}else{if(a.length!==b.length||a[0].length!==b[0].length)return null;result=a.map((row,i)=>row.map((value,j)=>value+(v.operation==='add'?1:-1)*b[i][j]))}if(result.some(row=>row.some(value=>!Number.isFinite(value))))return null;return [result.map(row=>`[${row.map(fmt).join(', ')}]`).join('\\n'),'Enter rectangular matrices with at most 6 rows and columns']}},
 scientificNotation:{fields:[['value','Number']],label:'Scientific notation',run:v=>{if(v.value===0)return ['0 × 10⁰','Zero'];const [mantissa,exponent]=v.value.toExponential(10).split('e');return [`${fmt(Number(mantissa))} × 10^${Number(exponent)}`,`Normalized mantissa between 1 and 10 in magnitude`]}},
 bigNumber:{fields:[['a','Whole number A','text'],['operation','Operation','select',[['add','Add'],['subtract','Subtract'],['multiply','Multiply'],['divide','Integer divide']]],['b','Whole number B','text']],label:'Exact integer result',run:v=>{if(v.a.length>2000||v.b.length>2000||!/^[-+]?\d+$/.test(v.a)||!/^[-+]?\d+$/.test(v.b))return null;const a=BigInt(v.a),b=BigInt(v.b);if(v.operation==='divide'&&b===0n)return null;const result=v.operation==='add'?a+b:v.operation==='subtract'?a-b:v.operation==='multiply'?a*b:a/b;return [result.toString(),v.operation==='divide'?`Remainder: ${String(a%b)}`:'Exact integer arithmetic']}},
 standardDeviation:{fields:[['numbers','Numbers (comma separated)','text'],['kind','Data type','select',[['sample','Sample'],['population','Population']]]],label:'Standard deviation',run:v=>{const values=parseNumberList(v.numbers);if(!values||!values.length)return null;const mean=values.reduce((sum,n)=>sum+n,0)/values.length,denominator=values.length-(v.kind==='sample'?1:0);if(denominator<=0)return null;const variance=values.reduce((sum,n)=>sum+(n-mean)**2,0)/denominator;return [`${fmt(Math.sqrt(variance))}`,`${v.kind==='sample'?'Sample':'Population'} variance: ${fmt(variance)}`]}},
 sequence:{fields:[['numbers','Sequence terms (comma separated)','text']],label:'Next sequence terms',run:v=>{const values=parseNumberList(v.numbers);if(!values||values.length<3||values.length>100)return null;const diffs=values.slice(1).map((n,i)=>n-values[i]),tol=n=>1e-9*Math.max(1,Math.abs(n));if(diffs.slice(1).every(n=>Math.abs(n-diffs[0])<=tol(diffs[0]))){const next=Array.from({length:5},(_,i)=>values.at(-1)+diffs[0]*(i+1));return [next.map(fmt).join(', '),`Arithmetic sequence; common difference ${fmt(diffs[0])}`]}if(values[0]!==0){const ratio=values[1]/values[0];if(Number.isFinite(ratio)&&values.slice(1).every((n,i)=>Math.abs(n-values[i]*ratio)<=tol(n))){const next=Array.from({length:5},(_,i)=>values.at(-1)*ratio**(i+1));return [next.map(fmt).join(', '),`Geometric sequence; common ratio ${fmt(ratio)}`]}}return null}},
 sampleSize:{fields:[['population','Population size'],['confidence','Confidence level','select',[['90','90%'],['95','95%'],['99','99%']]],['margin','Margin of error (%)'],['proportion','Expected proportion (%)']],label:'Required sample size',run:v=>{if(!Number.isSafeInteger(v.population)||v.population<1||v.margin<=0||v.margin>100||v.proportion<0||v.proportion>100)return null;const z={90:1.644854,95:1.959964,99:2.575829}[v.confidence],p=v.proportion/100,e=v.margin/100,unadjusted=z*z*p*(1-p)/(e*e),adjusted=unadjusted/(1+(unadjusted-1)/v.population);return [`${Math.min(v.population,Math.ceil(adjusted))} people`,`Finite-population correction; assumes a random sample and ${v.confidence}% confidence`]}},
 probability:{fields:[['trials','Number of trials (0–1,000)'],['successes','Successes (k)'],['probability','Success probability (%)']],label:'Probability of exactly k successes',run:v=>{if(!Number.isInteger(v.trials)||v.trials<0||v.trials>1000||!Number.isInteger(v.successes)||v.successes<0||v.successes>v.trials||v.probability<0||v.probability>100)return null;const p=v.probability/100;if(p===0)return [`${v.successes===0?'100':'0'}%`,'Binomial probability'];if(p===1)return [`${v.successes===v.trials?'100':'0'}%`,'Binomial probability'];let logCombination=0;for(let i=1;i<=v.successes;i++)logCombination+=Math.log(v.trials-v.successes+i)-Math.log(i);const result=Math.exp(logCombination+v.successes*Math.log(p)+(v.trials-v.successes)*Math.log1p(-p));return [`${fmt(result*100)}%`,'Binomial model; trials assumed independent with constant probability']}},
 statistics:{fields:[['numbers','Numbers (comma separated)','text']],label:'Descriptive statistics',run:v=>{const values=parseNumberList(v.numbers);if(!values||!values.length)return null;const sorted=[...values].sort((a,b)=>a-b),mean=values.reduce((sum,n)=>sum+n,0)/values.length,mid=Math.floor(values.length/2),counts=new Map();values.forEach(n=>counts.set(n,(counts.get(n)||0)+1));const max=Math.max(...counts.values()),modes=[...counts].filter(([,count])=>count===max&&count>1).map(([n])=>fmt(n)),variance=values.reduce((sum,n)=>sum+(n-mean)**2,0)/values.length;return [`Mean ${fmt(mean)} · Median ${fmt(values.length%2?sorted[mid]:(sorted[mid-1]+sorted[mid])/2)} · Range ${fmt(sorted.at(-1)-sorted[0])}`,`Mode ${modes.length?modes.join(', '):'none'} · Population SD ${fmt(Math.sqrt(variance))} · n = ${values.length}`]}},
 permutation:{fields:[['n','Total items (n)'],['r','Selected items (r)'],['kind','Calculate','select',[['permutation','Permutation nPr'],['combination','Combination nCr']]]],label:'Result',run:v=>{if(!Number.isInteger(v.n)||!Number.isInteger(v.r)||v.n<0||v.n>1000||v.r<0||v.r>v.n)return null;let result=1n;for(let i=0;i<v.r;i++)result*=BigInt(v.n-i);if(v.kind==='combination')for(let i=2;i<=v.r;i++)result/=BigInt(i);return [result.toString(),v.kind==='combination'?'Order does not matter':'Order matters']}},
 zscore:{fields:[['value','Observed value'],['mean','Mean'],['deviation','Standard deviation']],label:'Z-score',run:v=>v.deviation>0?[fmt((v.value-v.mean)/v.deviation),'Number of standard deviations from the mean']:null},
 confidence:{fields:[['mean','Sample mean'],['deviation','Standard deviation'],['size','Sample size'],['confidence','Confidence level','select',[['90','90%'],['95','95%'],['99','99%']]]],label:'Confidence interval for the mean',run:v=>{if(v.deviation<0||!Number.isInteger(v.size)||v.size<1)return null;const z={90:1.644854,95:1.959964,99:2.575829}[v.confidence],margin=z*v.deviation/Math.sqrt(v.size);return [`${fmt(v.mean-margin)} to ${fmt(v.mean+margin)}`,`Normal approximation at ${v.confidence}%; assumes known σ or a sufficiently large sample`]}},
 triangle:{fields:[['a','Side a'],['b','Side b'],['c','Side c']],label:'Triangle measurements',run:v=>{if(v.a<=0||v.b<=0||v.c<=0||v.a+v.b<=v.c||v.a+v.c<=v.b||v.b+v.c<=v.a)return null;const perimeter=v.a+v.b+v.c,s=perimeter/2,area=Math.sqrt(s*(s-v.a)*(s-v.b)*(s-v.c)),angle=(opposite,side1,side2)=>Math.acos(Math.max(-1,Math.min(1,(side1*side1+side2*side2-opposite*opposite)/(2*side1*side2))))*180/Math.PI;return [`Area ${fmt(area)} · Perimeter ${fmt(perimeter)}`,`Angles: ${fmt(angle(v.a,v.b,v.c))}°, ${fmt(angle(v.b,v.a,v.c))}°, ${fmt(angle(v.c,v.a,v.b))}°`]}},
 volume:{fields:[['shape','Solid','select',[['prism','Rectangular prism'],['sphere','Sphere'],['cylinder','Cylinder'],['cone','Cone']]],['length','Length'],['width','Width'],['height','Height'],['radius','Radius']],label:'Volume',visibleFields:v=>v.shape==='prism'?['shape','length','width','height']:v.shape==='sphere'?['shape','radius']:['shape','radius','height'],run:v=>{const result=v.shape==='prism'?v.length*v.width*v.height:v.shape==='sphere'?4*Math.PI*v.radius**3/3:v.shape==='cylinder'?Math.PI*v.radius**2*v.height:Math.PI*v.radius**2*v.height/3;return Number.isFinite(result)&&result>0?[`${fmt(result)} cubic units`,`${pretty(v.shape)} volume`]:null},requiredFields:v=>v.shape==='prism'?['length','width','height']:v.shape==='sphere'?['radius']:['radius','height']},
 slope:{fields:[['x1','Point 1 x'],['y1','Point 1 y'],['x2','Point 2 x'],['y2','Point 2 y']],label:'Slope',run:v=>v.x1!==v.x2?[fmt((v.y2-v.y1)/(v.x2-v.x1)),`Line through (${fmt(v.x1)}, ${fmt(v.y1)}) and (${fmt(v.x2)}, ${fmt(v.y2)})`]:['Undefined','Vertical line; x-coordinates are equal']},
 distance:{fields:[['x1','Point 1 x'],['y1','Point 1 y'],['x2','Point 2 x'],['y2','Point 2 y']],label:'Distance',run:v=>[fmt(Math.hypot(v.x2-v.x1,v.y2-v.y1)),'Euclidean distance in the same units as the coordinates']},
 circle:{fields:[['radius','Radius']],label:'Circle measurements',run:v=>v.radius>0?[`Area ${fmt(Math.PI*v.radius*v.radius)}`,`Circumference ${fmt(2*Math.PI*v.radius)} · Diameter ${fmt(2*v.radius)}`]:null},
 surfaceArea:{fields:[['shape','Solid','select',[['prism','Rectangular prism'],['sphere','Sphere'],['cylinder','Cylinder'],['cone','Cone']]],['length','Length'],['width','Width'],['height','Height'],['radius','Radius']],label:'Total surface area',visibleFields:v=>v.shape==='prism'?['shape','length','width','height']:v.shape==='sphere'?['shape','radius']:['shape','radius','height'],run:v=>{const result=v.shape==='prism'?2*(v.length*v.width+v.length*v.height+v.width*v.height):v.shape==='sphere'?4*Math.PI*v.radius**2:v.shape==='cylinder'?2*Math.PI*v.radius*(v.radius+v.height):Math.PI*v.radius*(v.radius+Math.hypot(v.radius,v.height));return Number.isFinite(result)&&result>0?[`${fmt(result)} square units`,`Total surface area of a ${pretty(v.shape).toLowerCase()}`]:null},requiredFields:v=>v.shape==='prism'?['length','width','height']:v.shape==='sphere'?['radius']:['radius','height']},
 pythagorean:{fields:[['a','Leg a'],['b','Leg b'],['c','Hypotenuse c']],label:'Missing side',allowOneMissing:true,run:v=>{const missing=Object.entries(v).filter(([key,value])=>key!=='shape'&&!Number.isFinite(value));if(missing.length!==1)return null;const[key]=missing;if(Object.values(v).some(value=>Number.isFinite(value)&&value<=0))return null;const value=key==='a'?Math.sqrt(v.c*v.c-v.b*v.b):key==='b'?Math.sqrt(v.c*v.c-v.a*v.a):Math.hypot(v.a,v.b);return Number.isFinite(value)&&value>0?[`${key} = ${fmt(value)}`,'Pythagorean theorem: a² + b² = c²'] :null}},
 rightTriangle:{fields:[['a','Leg a'],['b','Leg b'],['c','Hypotenuse c']],label:'Right triangle measurements',allowOneMissing:true,run:v=>{const missing=Object.entries(v).filter(([key,value])=>key!=='shape'&&!Number.isFinite(value));if(missing.length!==1||Object.values(v).some(value=>Number.isFinite(value)&&value<=0))return null;const[key]=missing,side=key==='a'?Math.sqrt(v.c*v.c-v.b*v.b):key==='b'?Math.sqrt(v.c*v.c-v.a*v.a):Math.hypot(v.a,v.b);if(!Number.isFinite(side)||side<=0)return null;const a=key==='a'?side:v.a,b=key==='b'?side:v.b,c=key==='c'?side:v.c;return [`Hypotenuse ${fmt(c)} · Area ${fmt(a*b/2)}`,`Legs ${fmt(a)} and ${fmt(b)} · Acute angles ${fmt(Math.atan2(a,b)*180/Math.PI)}° and ${fmt(Math.atan2(b,a)*180/Math.PI)}°`]}},
};
function parseNumberList(text){const parts=text.split(/[,;\s]+/).filter(Boolean);if(!parts.length)return null;const values=parts.map(Number);return values.every(Number.isFinite)?values:null}
function runRadixOperation(v,radix){const pattern=radix===2?/^[01]+$/:/^[\da-f]+$/i;if(v.a.length>256||v.b.length>256||!pattern.test(v.a)||!pattern.test(v.b))return null;const a=BigInt(`${radix===2?'0b':'0x'}${v.a}`),b=BigInt(`${radix===2?'0b':'0x'}${v.b}`);if(v.operation==='divide'&&b===0n)return null;const result=v.operation==='add'?a+b:v.operation==='subtract'?a-b:v.operation==='multiply'?a*b:a/b,base=result<0n?(-result).toString(radix):result.toString(radix);return [`${result<0n?'-':''}${radix===16?'0x':''}${base.toUpperCase()}`,v.operation==='divide'?`Integer quotient; remainder ${(a%b).toString(radix).toUpperCase()}`:`${radix===2?'Binary':'Hexadecimal'} arithmetic`]}
const mathCalculatorCatalog=[
 ['Scientific Calculator','scientific'],['Random Number Generator','random'],['Percent Error Calculator','percentError'],['Exponent Calculator','exponent'],['Binary Calculator','binary'],['Hex Calculator','hex'],['Half-Life Calculator','halfLife'],['Log Calculator','log'],['Root Calculator','root'],['Least Common Multiple Calculator','lcm'],['Factor Calculator','factor'],['Rounding Calculator','rounding'],['Matrix Calculator','matrix'],['Scientific Notation Calculator','scientificNotation'],['Big Number Calculator','bigNumber'],
 ['Standard Deviation Calculator','standardDeviation'],['Number Sequence Calculator','sequence'],['Sample Size Calculator','sampleSize'],['Probability Calculator','probability'],['Statistics Calculator','statistics'],['Permutation and Combination Calculator','permutation'],['Z-score Calculator','zscore'],['Confidence Interval Calculator','confidence'],
 ['Triangle Calculator','triangle'],['Volume Calculator','volume'],['Slope Calculator','slope'],['Distance Calculator','distance'],['Circle Calculator','circle'],['Surface Area Calculator','surfaceArea'],['Pythagorean Theorem Calculator','pythagorean'],['Right Triangle Calculator','rightTriangle']
];
function renderMathCalculators(){
 const grid=$('#view-tools .tool-grid');
 mathCalculatorCatalog.forEach(([title,recipeName],index)=>{
  const recipe=mathCalculatorRecipes[recipeName];
  const fields=recipe.fields.map(([key,label,type='number',options])=>`<label class="field-control" data-math-control="${key}"><span>${label}</span>${type==='select'?`<select data-math-field="${key}" aria-label="${label}">${options.map(([value,text])=>`<option value="${value}">${text}</option>`).join('')}</select>`:`<input type="${type}" ${type==='number'?'step="any"':''} data-math-field="${key}" aria-label="${label}">`}</label>`).join('');
  const card=document.createElement('article');card.className='panel tool-card math-tool-card';card.dataset.mathIndex=String(index);
  card.innerHTML=`<div class="tool-card-head"><div class="tool-symbol">∑</div><div><h3>${title}</h3><p>Enter values to calculate.</p></div></div><div class="tool-fields two-fields">${fields}</div><div class="tool-output"><span>${recipe.label}</span><output>—</output><small>Enter values to calculate.</small></div>`;
  grid.append(card);toolCategoryByName[title]='math';
 });
}
function updateMathCalculators(){
 $$('.math-tool-card').forEach(card=>{
  const recipe=mathCalculatorRecipes[mathCalculatorCatalog[Number(card.dataset.mathIndex)][1]],inputs=[...card.querySelectorAll('[data-math-field]')],output=card.querySelector('output'),note=card.querySelector('small');
  const values=Object.fromEntries(inputs.map(input=>[input.dataset.mathField,input.type==='number'?(input.value.trim()===''?NaN:Number(input.value)):input.value]));
  const visible=recipe.visibleFields?recipe.visibleFields(values):inputs.map(input=>input.dataset.mathField);
  card.querySelectorAll('[data-math-control]').forEach(control=>control.classList.toggle('hidden',!visible.includes(control.dataset.mathControl)));
  const required=recipe.requiredFields?recipe.requiredFields(values):inputs.filter(input=>input.type!=='number'||input.value.trim()!=='').map(input=>input.dataset.mathField);
  const missing=required.filter(key=>!inputs.some(input=>input.dataset.mathField===key&&input.value.trim()!==''));
  if(recipe.allowOneMissing){const blanks=inputs.filter(input=>input.type==='number'&&input.value.trim()==='').length;if(blanks!==1){output.textContent='—';note.textContent='Enter exactly two of the three side lengths.';return}}
  else if(missing.length){output.textContent='—';note.textContent='Enter the required values to calculate.';return}
  if(inputs.some(input=>input.type==='number'&&input.value.trim()!==''&&!Number.isFinite(Number(input.value)))){output.textContent='—';note.textContent='Enter valid numbers.';return}
  const result=recipe.run(values);
  if(!result||result.some(value=>typeof value==='number'&&!Number.isFinite(value)||typeof value==='string'&&/\b(?:NaN|Infinity)\b/.test(value))){output.textContent='—';note.textContent='Check the inputs and supported ranges.';return}
  [output.textContent,note.textContent]=result;
 });
}
const toolCategoryByName={
 'Percentage Calculator':'math','Age calculator':'other','Age gap':'other',Discount:'financial','Mean, Median, Mode, Range Calculator':'math','Tip split':'financial',
 'Compound interest':'financial','Ratio Calculator':'math','GST calculator':'financial','Loan EMI':'financial','Percentage change':'math',
 'Simple interest':'financial','Fuel cost':'financial','Profit margin & markup':'financial','Greatest Common Factor Calculator':'math',
 'BMI calculator':'health','Savings goal':'financial','Unit price comparison':'financial','Fraction Calculator':'math',
 'Prime number checker':'math','Area Calculator':'math','Date calculator':'other','Time duration':'other','Fuel cost':'other','Tip split':'other',
 'SIP return calculator':'financial','Break-even point':'financial','BMR calculator':'health','Running pace':'health',
 'Quadratic Formula Calculator':'math','Factorial calculator':'math','Date difference':'other'
};
function getToolSubcategory(title,category){
 const name=title.toLowerCase();
 if(/sleep calculator/.test(name))return'health';
 if(/wind chill|heat index|dew point|humidity calculator|feels like|uv index|wet bulb|cloud base|atmospheric pressure|wind speed calculator|rainfall calculator|solar radiation/.test(name))return'weather';
 if(/gpa calculator|grade calculator/.test(name))return'education';
 if(category==='financial'){
  if(/mortgage|real estate|rental|rent|home equity|heloc|house affordability|down payment|fha|va mortgage|property|refinance/.test(name))return'mortgage-real-estate';
  if(/investment|savings|bond|mutual fund|return calculator|irr|roi|payback|present value|future value|401k|pension|social security|annuity|roth ira|\bira\b|\brmd\b|\bcd calculator\b|interest/.test(name))return'investment';
  if(/tax|gst|vat|salary|paycheck|income/.test(name))return'tax-salary';
  if(/business|budget|commission|margin|break-even|depreciation/.test(name))return'business-budget';
  if(/loan|debt|credit card|payoff|repayment|lease|amortization|payment|apr|cash back/.test(name))return'loans-debt';
  return'finance';
 }
 if(category==='health'){
  if(/pregnancy|due date|ovulation|conception|period calculator/.test(name))return'pregnancy';
  if(/bmi|bmr|calorie|body fat|ideal weight|lean body|healthy weight|one rep|heart rate|macro|carbohydrate|protein|fat intake|tdee|running pace/.test(name))return'fitness';
  return'health';
 }
 if(category==='math'){
  if(/triangle|volume|slope|distance|area calculator|circle|surface area|pythagorean/.test(name))return'geometry';
  if(/statistics|standard deviation|sequence|sample size|probability|mean, median|permutation|combination|z-score|confidence interval/.test(name))return'statistics';
  return'math';
 }
 if(/date|time|day counter|day of the week|hours calculator|age calculator|age gap/.test(name))return'date-time';
 if(/concrete|btu|square footage|stair|roofing|tile calculator|mulch|gravel/.test(name))return'housing';
 if(/conversion|height calculator|density calculator|mass calculator|weight calculator|molarity|molecular weight/.test(name))return'measuring-units';
 if(/voltage|resistor|ohms|electricity calculator|reactance|resonant frequency|battery life calculator/.test(name))return'electronics-circuits';
 if(/ip subnet|password generator|bandwidth|base64|url encode/.test(name))return'internet';
 if(/fuel|mileage|horsepower|tire size|speed calculator/.test(name))return'transportation';
 if(/dice roller|love calculator/.test(name))return'entertainment';
 return'other';
}
renderFinancialCalculators();
renderOtherCalculators();
renderHealthCalculators();
renderMathCalculators();
$('#view-tools').addEventListener('click',generateOtherResult);
const toolCategoryLabels={financial:'Financial Calculators',health:'Fitness & Health Calculators',math:'Math Calculators',other:'Other Calculators'};
function setupCalculatorDirectory(){
 const cards=$$('#view-tools .tool-card'),directory=$('#toolDirectory'),linksByCard=new Map(),groups=new Map();
 Object.entries(toolCategoryLabels).forEach(([category,label])=>{
  const group=document.createElement('section');group.className='tool-directory-group';group.dataset.toolCategory=category;
  const heading=document.createElement('h2');heading.textContent=label;group.append(heading);
  const list=document.createElement('div');list.className='tool-directory-links';group.append(list);
  directory.append(group);groups.set(category,{group,list});
 });
 cards.forEach(card=>{
  const title=card.querySelector('h3').textContent.trim(),category=toolCategoryByName[title];
  if(!category)throw new Error(`Missing calculator category for "${title}"`);
  card.dataset.subcategory=getToolSubcategory(title,category);
  const id=`tool-${title.toLowerCase().replace(/&/g,' and ').replace(/[^a-z0-9]+/g,'-').replace(/^-|-$/g,'')}`;
  card.id=id;card.dataset.category=category;
  const link=document.createElement('button');link.type='button';link.className='tool-directory-link';link.textContent=title;link.dataset.toolTarget=id;link.setAttribute('aria-label',`Open ${title}`);
  groups.get(category).list.append(link);linksByCard.set(card,link);
  const description=card.querySelector('.tool-card-head p')?.textContent||'';
  const fields=[...card.querySelectorAll('.field-control span')].map(field=>field.textContent).join(' ');
  card.dataset.search=`${title} ${description} ${fields}`.toLowerCase();
 });
 const filters=$$('.calculator-category-filter'),search=$('#toolSearch'),allCount=cards.length;
 filters.forEach(button=>{
  const category=button.dataset.toolCategory,count=category==='all'?allCount:cards.filter(card=>card.dataset.subcategory===category).length;
  button.querySelector('[data-category-count]').textContent=String(count);
 });
 let activeCategory='all';
 const applyFilters=()=>{
  const query=search.value.trim().toLowerCase();
  directory.classList.toggle('category-filtered',activeCategory!=='all');
  let visible=0;
  cards.forEach(card=>{
   const matches=(activeCategory==='all'||card.dataset.subcategory===activeCategory)&&card.dataset.search.includes(query);
   card.classList.toggle('tool-card-hidden',!matches);
   linksByCard.get(card).classList.toggle('tool-directory-link-hidden',!matches);
   if(matches)visible++;
  });
  groups.forEach(({group,list})=>group.classList.toggle('tool-directory-group-hidden',!list.querySelector('.tool-directory-link:not(.tool-directory-link-hidden)')));
  $('#toolNoResults').hidden=visible>0;
 };
 filters.forEach(button=>button.addEventListener('click',()=>{
  activeCategory=button.dataset.toolCategory;
  filters.forEach(filter=>{const selected=filter===button;filter.classList.toggle('active',selected);filter.setAttribute('aria-pressed',String(selected))});
  applyFilters();
 }));
 search.addEventListener('input',applyFilters);
 directory.addEventListener('click',event=>{
  const link=event.target.closest('.tool-directory-link');
  if(!link)return;
  const card=document.getElementById(link.dataset.toolTarget);
  if(!card){console.error(`Calculator panel not found: ${link.dataset.toolTarget}`);return}
  card.scrollIntoView({behavior:'smooth',block:'center'});
  card.classList.add('tool-card-highlight');
  card.querySelector('input,select')?.focus({preventScroll:true});
  setTimeout(()=>card.classList.remove('tool-card-highlight'),1500);
 });
 applyFilters();
}
setupCalculatorDirectory();
$('#view-tools').addEventListener('input',event=>{updateTools();if(event.target.closest('.financial-tool-card'))updateFinancialCalculators();if(event.target.closest('.other-tool-card'))updateOtherCalculators();if(event.target.closest('.health-tool-card'))updateHealthCalculators();if(event.target.closest('.math-tool-card'))updateMathCalculators()});$('#view-tools').addEventListener('change',event=>{updateTools();if(event.target.closest('.financial-tool-card'))updateFinancialCalculators();if(event.target.closest('.other-tool-card'))updateOtherCalculators();if(event.target.closest('.health-tool-card'))updateHealthCalculators();if(event.target.closest('.math-tool-card'))updateMathCalculators()});updateTools();updateFinancialCalculators();updateOtherCalculators();updateHealthCalculators();updateMathCalculators();

const booleanGateNames=['AND','OR','NOT','XOR','XNOR','NAND','NOR'];
const booleanGateExpressions={AND:'A AND B',OR:'A OR B',NOT:"NOT A",XOR:'A XOR B',XNOR:'NOT (A XOR B)',NAND:'NOT (A AND B)',NOR:'NOT (A OR B)'};
function evaluateBooleanGate(operation,a,b=false){
 if(operation==='AND')return a&&b;
 if(operation==='OR')return a||b;
 if(operation==='NOT')return !a;
 if(operation==='XOR')return a!==b;
 if(operation==='XNOR')return a===b;
 if(operation==='NAND')return !(a&&b);
 if(operation==='NOR')return !(a||b);
 return false;
}
function updateBooleanAlgebra(){
 const operation=$('#booleanAlgebraOperation').value,a=$('#booleanAlgebraA').value==='1',b=$('#booleanAlgebraB').value==='1';
 $('#booleanAlgebraBField').classList.toggle('boolean-field-hidden',operation==='NOT');
 $('#booleanAlgebraResult').textContent=String(Number(evaluateBooleanGate(operation,a,b)));
 $('#booleanAlgebraNote').textContent=booleanGateExpressions[operation];
}
function updateLogicGateTable(){
 const a=$('#logicGateA').value==='1',b=$('#logicGateB').value==='1';
 $('#logicGateRows').innerHTML=booleanGateNames.map(name=>`<tr><th scope="row">${name}</th><td>${Number(evaluateBooleanGate(name,a,b))}</td></tr>`).join('');
}
function renderGateTruthTable(operation){
 const head=$('#truthTableHead'),rows=$('#truthTableRows');
 if(operation==='NOT'){
  head.innerHTML='<tr><th>A</th><th>NOT A</th></tr>';
  rows.innerHTML=[0,1].map(a=>`<tr><td>${a}</td><td>${Number(evaluateBooleanGate(operation,a===1))}</td></tr>`).join('');
  return;
 }
 head.innerHTML=`<tr><th>A</th><th>B</th><th>${operation}</th></tr>`;
 rows.innerHTML=[0,1].flatMap(a=>[0,1].map(b=>`<tr><td>${a}</td><td>${b}</td><td>${Number(evaluateBooleanGate(operation,a===1,b===1))}</td></tr>`)).join('');
}
function readBooleanInteger(text,signed,bits){
 const valueText=text.trim();
 if(!/^[+-]?\d+$/.test(valueText)||valueText.length>21)return{error:'Enter a whole-number integer.'};
 const value=BigInt(valueText),width=BigInt(bits),minimum=signed?-(1n<<(width-1n)):0n,maximum=signed?(1n<<(width-1n))-1n:(1n<<width)-1n;
 if(value<minimum||value>maximum)return{error:`Use a value from ${minimum} to ${maximum} for this ${signed?'signed':'unsigned'} ${bits}-bit width.`};
 return{value};
}
function updateTruthTable(){
 const operation=$('#truthGate').value,signed=$('#truthSignedness').value==='signed',bits=Number($('#truthBitWidth').value),operandA=$('#truthOperandA').value.trim(),operandB=$('#truthOperandB').value.trim();
 $('#truthOperandBField').classList.toggle('boolean-field-hidden',operation==='NOT');
 renderGateTruthTable(operation);
 const output=$('#truthWordResult'),note=$('#truthWordNote');
 if(!operandA||(operation!=='NOT'&&!operandB)){output.textContent='—';note.textContent='Enter integer operands to calculate.';return}
 const parsedA=readBooleanInteger(operandA,signed,bits),parsedB=operation==='NOT'?null:readBooleanInteger(operandB,signed,bits);
 if(parsedA.error||parsedB?.error){output.textContent='—';note.textContent=parsedA.error||parsedB.error;return}
 const mask=(1n<<BigInt(bits))-1n,a=BigInt.asUintN(bits,parsedA.value),b=parsedB?BigInt.asUintN(bits,parsedB.value):0n;
 let raw;
 if(operation==='AND')raw=a&b;
 else if(operation==='OR')raw=a|b;
 else if(operation==='NOT')raw=~a;
 else if(operation==='XOR')raw=a^b;
 else if(operation==='XNOR')raw=~(a^b);
 else if(operation==='NAND')raw=~(a&b);
 else raw=~(a|b);
 raw&=mask;
 const result=signed?BigInt.asIntN(bits,raw):raw;
 output.textContent=result.toString();
 note.textContent=`Binary: ${raw.toString(2).padStart(bits,'0')} · ${signed?'signed':'unsigned'} ${bits}-bit result`;
}
function parseKmapTerms(text,maxMinterm){
 const trimmed=text.trim();
 if(!trimmed)return[];
 const parts=trimmed.split(/[,\s]+/);
 if(parts.some(part=>! /^\d+$/.test(part)))return null;
 const terms=parts.map(Number);
 if(terms.some(term=>!Number.isInteger(term)||term<0||term>maxMinterm)||new Set(terms).size!==terms.length)return null;
 return terms;
}
function combineKmapImplicants(first,second){
 let difference=-1;
 for(let i=0;i<first.length;i++){
  if(first[i]===second[i])continue;
  if(first[i]==='-'||second[i]==='-'||difference!==-1)return null;
  difference=i;
 }
 return difference===-1?null:`${first.slice(0,difference)}-${first.slice(difference+1)}`;
}
function kmapImplicantCovers(implicant,minterm){
 const bits=minterm.toString(2).padStart(implicant.length,'0');
 return implicant.split('').every((bit,index)=>bit==='-'||bit===bits[index]);
}
function minimizeKmap(variables,ones,dontCares){
 const maxMinterm=2**variables-1;
 if(ones.length===0)return'0';
 if(ones.length+dontCares.length===maxMinterm+1)return'1';
 let current=[...new Set([...ones,...dontCares].map(value=>value.toString(2).padStart(variables,'0')))],primeSet=new Set();
 while(current.length){
  const combined=new Set(),next=new Set();
  for(let i=0;i<current.length;i++)for(let j=i+1;j<current.length;j++){
   const result=combineKmapImplicants(current[i],current[j]);
   if(result){combined.add(current[i]);combined.add(current[j]);next.add(result)}
  }
  current.forEach(term=>{if(!combined.has(term))primeSet.add(term)});
  current=[...next];
 }
 const requiredMask=ones.reduce((mask,minterm)=>mask|(1<<minterm),0);
 const primes=[...primeSet].map(pattern=>({pattern,mask:ones.reduce((mask,minterm)=>mask|(kmapImplicantCovers(pattern,minterm)?1<<minterm:0),0)})).filter(item=>item.mask);
 let best=null;
 function search(covered,chosen){
  if(covered===requiredMask){
   const literalCount=chosen.reduce((sum,index)=>sum+primes[index].pattern.replace(/-/g,'').length,0);
   if(!best||chosen.length<best.length||chosen.length===best.length&&literalCount<best.literalCount)best={indexes:chosen,length:chosen.length,literalCount};
   return;
  }
  if(best&&chosen.length>=best.length)return;
  let candidates=null;
  for(let minterm=0;minterm<=maxMinterm;minterm++){
   const bit=1<<minterm;
   if(!(requiredMask&bit)||covered&bit)continue;
   const options=primes.map((prime,index)=>({prime,index})).filter(({prime,index})=>prime.mask&bit&&!chosen.includes(index));
   if(!candidates||options.length<candidates.length)candidates=options;
  }
  if(!candidates?.length)return;
  candidates.sort((a,b)=>a.prime.pattern.replace(/-/g,'').length-b.prime.pattern.replace(/-/g,'').length);
  candidates.forEach(({prime,index})=>search(covered|prime.mask,[...chosen,index]));
 }
 search(0,[]);
 if(!best)return'—';
 return best.indexes.map(index=>{
  const pattern=primes[index].pattern,term=pattern.split('').map((bit,position)=>bit==='-'?'':bit==='1'?'ABCD'[position]:`${'ABCD'[position]}'`).join('');
  return term||'1';
 }).join(' + ');
}
function renderKmapTable(variables,ones,dontCares){
 const rowBits=Math.floor(variables/2),columnBits=variables-rowBits,rowCount=2**rowBits,columnCount=2**columnBits,gray=value=>value^(value>>1);
 const rowHeaders=Array.from({length:rowCount},(_,index)=>gray(index).toString(2).padStart(rowBits,'0'));
 const columnHeaders=Array.from({length:columnCount},(_,index)=>gray(index).toString(2).padStart(columnBits,'0'));
 const head=`<thead><tr><th>${'ABCD'.slice(0,rowBits)}\\${'ABCD'.slice(rowBits,variables)}</th>${columnHeaders.map(bits=>`<th scope="col">${bits}</th>`).join('')}</tr></thead>`;
 const body=rowHeaders.map((row,index)=>{
  const rowValue=gray(index),cells=columnHeaders.map((column,columnIndex)=>{
   const minterm=(rowValue<<columnBits)|gray(columnIndex),value=ones.includes(minterm)?'1':dontCares.includes(minterm)?'X':'0',cellClass=value==='1'?'kmap-one':value==='X'?'kmap-dont-care':'';
   return`<td class="${cellClass}">${value}</td>`;
  }).join('');
  return`<tr><th scope="row">${row}</th>${cells}</tr>`;
 }).join('');
 $('#kmapTable').innerHTML=`${head}<tbody>${body}</tbody>`;
}
function updateKmap(){
 const variables=Number($('#kmapVariables').value),maxMinterm=2**variables-1,onesText=$('#kmapMinterms').value,dontCareText=$('#kmapDontCares').value,output=$('#kmapExpression'),note=$('#kmapNote'),wrap=$('#kmapTableWrap');
 if(!onesText.trim()){output.textContent='—';note.textContent='Enter the minterms where the function is 1.';wrap.hidden=true;return}
 const ones=parseKmapTerms(onesText,maxMinterm),dontCares=parseKmapTerms(dontCareText,maxMinterm);
 if(!ones||!dontCares){output.textContent='—';note.textContent=`Enter unique minterms from 0 to ${maxMinterm}.`;wrap.hidden=true;return}
 if(ones.some(term=>dontCares.includes(term))){output.textContent='—';note.textContent="A term cannot be both an ON minterm and a don't-care.";wrap.hidden=true;return}
 output.textContent=minimizeKmap(variables,ones,dontCares);
 note.textContent=`ON minterms: ${ones.join(', ')} · Don't cares: ${dontCares.length?dontCares.join(', '):'none'}`;
 renderKmapTable(variables,ones,dontCares);wrap.hidden=false;
}
function renderFlipFlopTable(){
 const type=$('#flipFlopType').value,head=$('#flipFlopTableHead'),rows=$('#flipFlopTableRows'),note=$('#flipFlopNote');
 let inputs=[],states=[],nextState;
 if(type==='SR'){
  inputs=['S','R'];states=[0,1];nextState=(values,q)=>values[0]&&values[1]?'X':values[0]?1:values[1]?0:q;
  note.textContent='Active-high SR table; S = 1 and R = 1 is an invalid state.';
 }else if(type==='D'){
  inputs=['D'];states=[0,1];nextState=values=>values[0];
  note.textContent='The next state follows D on the active clock edge.';
 }else if(type==='JK'){
  inputs=['J','K'];states=[0,1];nextState=(values,q)=>values[0]?(values[1]?1-q:1):(values[1]?0:q);
  note.textContent='When J = K = 1, the output toggles.';
 }else{
  inputs=['T'];states=[0,1];nextState=(values,q)=>values[0]?1-q:q;
  note.textContent='T = 1 toggles the output; T = 0 holds it.';
 }
 const headings=[...inputs,'Q','Q⁺'];
 head.innerHTML=`<tr>${headings.map(label=>`<th scope="col">${label}</th>`).join('')}</tr>`;
 const combinations=inputs.length===1?[[0],[1]]:[[0,0],[0,1],[1,0],[1,1]];
 rows.innerHTML=combinations.flatMap(values=>states.map(q=>{
  const result=nextState(values,q);
  return`<tr>${[...values,q,result].map(value=>`<td>${value}</td>`).join('')}</tr>`;
 })).join('');
}
function initBooleanTools(){
 ['change','input'].forEach(eventName=>{
  $('#booleanAlgebraOperation').addEventListener(eventName,updateBooleanAlgebra);
  $('#booleanAlgebraA').addEventListener(eventName,updateBooleanAlgebra);
  $('#booleanAlgebraB').addEventListener(eventName,updateBooleanAlgebra);
  $('#logicGateA').addEventListener(eventName,updateLogicGateTable);
  $('#logicGateB').addEventListener(eventName,updateLogicGateTable);
  ['truthGate','truthSignedness','truthBitWidth','truthOperandA','truthOperandB'].forEach(id=>$('#'+id).addEventListener(eventName,updateTruthTable));
  ['kmapVariables','kmapMinterms','kmapDontCares'].forEach(id=>$('#'+id).addEventListener(eventName,updateKmap));
  $('#flipFlopType').addEventListener(eventName,renderFlipFlopTable);
 });
 updateBooleanAlgebra();updateLogicGateTable();updateTruthTable();updateKmap();renderFlipFlopTable();
}
initBooleanTools();
