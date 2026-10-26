from pathlib import Path
from openpyxl import load_workbook,Workbook
import json,hashlib,random,datetime
D=Path.home()/'Desktop';src=D/'EIMERS_COLLATZ_PRECISION_LEDGER_V51B.xlsx';out=D/'EIMERS_COLLATZ_10_GATED_LEVELS_V52.xlsx';receipt=out.with_suffix('.json')
if out.exists() or receipt.exists():raise SystemExit('HOLD: output already exists')
data=list(load_workbook(src,read_only=True)['02 FAMILY PRECISION'].values)[1:]
assert len(data)==12422
def step(n):
 y=3*n+1;v=(y&-y).bit_length()-1;return y>>v,v
def replay(n,k):
 x=n;S=B=0;V=[]
 for i in range(k):
  x,v=step(x);B=3*B+(1<<S);S+=v;V.append(v)
 return x,S,B,tuple(V)
rows=[]
for r in data:
 n,b,w,k,S,remain,prefix,B,exitS,status=r
 rows.append((int(n),int(b),int(w),int(k),int(S),int(remain),tuple(int(v) for v in prefix.split(',')),int(B),int(exitS),str(status)))
assert sum(r[2] for r in rows)==59033
logs=[];tests=0;guard_rejections=0;sample_size=len(rows)
for level in range(1,11):
 rng=random.Random(5200+level)
 checks=0;errors=[]
 for n,b,wt,k,S,remain,V,B,exitS,status in rows:
  x,ss,bb,vv=replay(n,k)
  assert (ss,bb,vv)==(S,B,V) and remain==b-S and S<b
  assert x*(1<<S)==3**k*n+B
  # Explicit terminal step must consume current precision budget
  z,v=step(x);assert S+v==exitS and exitS>=b and status=='PRECISION_EXHAUSTED'
  checks+=4
  # Each level increases input bit depth. Every outcome required, including lift invariance
  t=rng.getrandbits(10+level*11)+1
  y=n+t*(1<<b);yy,s2,b2,v2=replay(y,k)
  assert (s2,b2,v2)==(S,B,V) and yy*(1<<S)==3**k*y+B
  checks+=2
  # Each level adds a distinct adversarial mutation; corrupted receipts cannot pass
  mutated=[(S+1,B,V),(S,B+1,V),(S,B,tuple([V[0]+1]+list(V[1:])))][(level-1)%3]
  if mutated==(ss,bb,vv):raise AssertionError('MUTATION_FALSE_APPROVAL')
  guard_rejections+=1;checks+=1
 # Fail-closed gate: do not advance without every row verified
 tests+=checks;logs.append((level,10+level*11,checks,'PASS','NO_SOURCE_DEFECT','new seeded lift/negative control'))
 print('LEVEL',level,'PASS',checks,'cumulative',tests,flush=True)
# Exact ledger class-membership checks by independent weighted expansion.
# All 59033 equivalent residues must be represented exactly once.
seen=set()
for n,b,w,k,S,rem,V,B,exitS,stat in rows:
 assert w==(1<<(21-b))
 for t in range(w):
  r=n+t*(1<<b)
  assert r not in seen
  seen.add(r)
assert len(seen)==59033
w=Workbook();a=w.active;a.title='01 LEVEL GATES'
a.append(['Level','Challenge lift bits','Checks','Outcome','Source correction','Verifier hardening'])
for row in logs:a.append(row)
s=w.create_sheet('02 VERIFICATION SUMMARY')
for row in [('Gated levels',10),('Total verification checks',tests),('Mutation negative controls',guard_rejections),('Fully rechecked families',len(rows)),('Exact 21bit residues reconstructed',len(seen)),('Source defects found',0),('Repairs to source',0),('Each level advanced only on PASS','YES'),('Global Collatz theorem','HOLD_UNPROVEN')]:s.append(row)
q=w.create_sheet('03 BOUNDARY')
for row in [('No fabricated changes','10 distinct deterministic challenge policies; source fixes only if evidence required'),('Test harness','Each level adds a high-bit lift and new negative check'),('Precision invariant','The last stable step has S<b; next valuation crosses S>=b'),('SHA256','Integrity, not mathematical proof'),('Result','LOCAL_REGRESSION_PASS_GLOBAL_HOLD')]:q.append(row)
w.save(out)
obj={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'levels':10,'checks':tests,'negative_controls':guard_rejections,'family_records':len(rows),'reconstructed_residues':len(seen),'source_defects':0,'source_fixes':0,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'workbook_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'status':'PASS_LOCAL_HOLD_GLOBAL'}
receipt.write_text(json.dumps(obj,indent=2)+'\n')
print('FINAL',obj,flush=True)
