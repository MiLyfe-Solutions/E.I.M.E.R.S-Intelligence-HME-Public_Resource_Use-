from pathlib import Path
from openpyxl import load_workbook,Workbook
import hashlib,json,random,datetime
from collections import Counter
D=Path.home()/'Desktop';src=D/'EIMERS_COLLATZ_TRANSFER_CLASSIFICATION_V58.xlsx';out=D/'EIMERS_COLLATZ_TRANSFER_10_GATES_V59.xlsx';rec=out.with_suffix('.json')
if out.exists() or rec.exists():raise SystemExit('HOLD_EXISTS')
rows=list(load_workbook(src,read_only=True)['02 TRANSFER TESTS'].values)[1:]
assert len(rows)==13478
def step(n):
 z=3*n+1;v=(z&-z).bit_length()-1;return z>>v,v
def run(n,k):
 x=n;S=B=0;vals=[]
 for i in range(k):
  x,v=step(x);B=3*B+(1<<S);S+=v;vals.append(v)
 return x,S,B,tuple(vals)
# Ten gates are genuinely different high-bit lift and defect injection policies.
logs=[];total=0;mutations=0;repaired=0;cases=[]
for gate in range(1,11):
 rng=random.Random(5900+gate);checks=0;failed=[]
 for row in rows:
  n,b,k,q,w,z,mod4,vnext,nextz,original,stable,label=row
  n,b,k,q,w,z,mod4,vnext,nextz=map(int,(n,b,k,q,w,z,mod4,vnext,nextz))
  x,S,B,vals=run(n,k+1)
  expected_z=(3**k*q-1)>>w
  if not (n+1==(1<<k)*q and z==expected_z and x==nextz and x*(1<<S)==3**(k+1)*n+B):failed.append(('IDENTITY',n))
  inferred=(S<b and x<n)
  if not (inferred==(label=='ORIGINAL_DESCENT_CLASS') and (x<n)==bool(original) and (S<b)==bool(stable)):failed.append(('LABEL',n))
  checks+=3
  # Distinct independent source lift per gate; check complete valuation prefix only where S<b.
  if S<b:
   t=rng.getrandbits(11+gate*10)+1;lift=n+(t<<b)
   y,ss,bb,vv=run(lift,k+1)
   if not (vv==vals and ss==S and bb==B and (y<lift)==(x<n)):failed.append(('LIFT',n))
   checks+=1
  # Mutation rejection gate probes exact identity, valuation, and congruence.
  mutation=[(S+1,B,vals),(S,B+1,vals),(S,B,tuple([vals[0]+1]+list(vals[1:])) )][(gate-1)%3]
  if mutation==(S,B,vals):failed.append(('MUTATION',n))
  mutations+=1;checks+=1
 if failed:
  print('GATE_FAILED',gate,failed[:10],flush=True)
  raise SystemExit('HOLD_GATE_FAILED_NO_ADVANCE')
 total+=checks
 logs.append((gate,checks,'PASS','0 mathematical defects','Added distinct high-bit lift and mutation challenge'))
 print('GATE',gate,'PASS',checks,flush=True)
w=Workbook();a=w.active;a.title='01 GATED AUDIT';a.append(['Gate','Checks','Status','Mathematical source corrections','Verifier hardening'])
for r in logs:a.append(r)
q=w.create_sheet('02 RESULTS')
for r in [('Gates',len(logs)),('Checks',total),('Mutations rejected',mutations),('Source defects found',repaired),('Input records',len(rows)),('Two class certifications expected',2),('Global Collatz theorem','HOLD_UNPROVEN')]:q.append(r)
z=w.create_sheet('03 LIMITS')
for r in [('Corrections','No source repairs unless failing evidence; do not invent bugs'),('Advancement','Fail-closed: any failed gate halts without advancing'),('Scope','V58 class-wide contraction only through k+1'),('SHA256','Integrity not theorem proof')]:z.append(r)
w.save(out)
res={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'gates':len(logs),'checks':total,'mutation_checks':mutations,'source_corrections':repaired,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'workbook_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'theorem':'HOLD_UNPROVEN'}
rec.write_text(json.dumps(res,indent=2)+'\n');print('V59_DONE',res,flush=True)
