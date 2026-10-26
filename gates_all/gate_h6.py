import json,hashlib
from pathlib import Path
out=Path('/mnt/data/collatz_h6')
def T(n):return 3*n+1 if n%2 else n//2
def word(n,k):
 p=[]; vals=[n]
 for _ in range(k):
  p.append('O' if n%2 else 'E');n=T(n);vals.append(n)
 return ''.join(p),vals
# affine: 2^e*y = 3^o*x+B; compute rational coefficients as numerator/2^e
# after O: numerator=3*num+2^e; after E: denominator doubles

def coeff(w):
 a,b,e,o=1,0,0,0
 for c in w:
  if c=='O':a*=3;b=3*b+2**e;o+=1
  else:e+=1
 return a,b,e,o
# same target via distinct valid words
mergers=[]
for target in (5,10,13,20,40):
 for k in range(1,9):
  paths=[]
  for mask in range(1<<k):
   w=''.join('O' if mask>>i&1 else 'E' for i in range(k))
   a,b,e,o=coeff(w);v=2**e*target-b
   if v<=0 or v%a:continue
   x=v//a
   got,vals=word(x,k)
   if got==w and vals[-1]==target:paths.append({'source':x,'word':w,'path':vals,'odd':o,'even':e,'B':b})
  if len(paths)>1:mergers.append({'target':target,'steps':k,'paths':paths})
# affine family for word OEEE from 13->5: x=13+16q -> y=5+3q (guards?)
# OEEE valid for x=13 mod 16: 13->40->20->10->5
for q in range(500):
 x=13+16*q;w,v=word(x,4)
 assert w=='OEEE' and v[-1]==5+6*q,(q,w,v)
# valid inverse odd predecessor of y=20m, m=3k+2
for k in range(500):
 x=20*k+13;y=60*k+40
 assert x%2 and T(x)==y
res={'method':'exact exhaustive parity words up to 8 operations for targets 5,10,13,20,40; independent replay of candidate words','merger_groups':len(mergers),'merger_examples':mergers[:12],'family_checks':500,'fixed_target_uniqueness':'For a fixed word and endpoint, affine inversion determines at most one positive source','status':'EXACT_ARITHMETIC_CHECKED; no Lean verification; universal HOLD_UNPROVEN'}
(out/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print('merger groups',len(mergers));print(json.dumps(mergers[:4],indent=2));print('family checks PASS')
