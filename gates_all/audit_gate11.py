#!/usr/bin/env python3
import csv, hashlib
from fractions import Fraction
from pathlib import Path
X0=6544422935497359190781
XS=17725876239305002191858
base=Path(__file__).resolve().parent
front=list(csv.DictReader(open(base/'adaptive_frontier_depth20.csv')))
rows=list(csv.DictReader(open(base/'adaptive_leaf_to_budget_guard.csv')))
summary={r['guard_id']:r for r in csv.DictReader(open(base/'budget_guard_summary.csv'))}
assert len(rows)==35082
assert sum(1 for r in front if r['status']=='DESCENT')==35082
assert sum(1 for r in front if r['status']=='OPEN_SPLIT')==134005
# prefix-free full frontier
seen=set()
for r in sorted(front,key=lambda x:int(x['q_bits'])):
 b=int(r['q_bits']); rr=int(r['q_residue'])%(1<<b)
 for bb in range(b): assert (bb, rr%(1<<bb)) not in seen
 assert (b,rr) not in seen
 seen.add((b,rr))
full_mass=sum((Fraction(1,1<<int(r['q_bits'])) for r in front),Fraction())
assert full_mass==Fraction(3,4)
desc_mass=Fraction()
for i,r in enumerate(rows):
 res=int(r['q_residue']); bits=int(r['q_bits']); word=[int(x) for x in r['post46_word'].split(',') if x]
 A=X0+XS*res; B=XS*(1<<bits)
 for a in word:
  den=1<<a
  assert (3*A+1)%den==0 and (3*B)%den==0
  A=(3*A+1)//den; B=(3*B)//den
  assert A%2==1 and B%2==0
 assert A==int(r['endpoint_base']) and B==int(r['endpoint_slope'])
 assert len(word)==int(r['continuation_steps'])
 assert sum(word)==int(r['valuation_sum'])
 assert int(r['valuation_sum'])>=int(r['threshold'])
 s=summary[r['guard_id']]
 assert int(s['continuation_steps'])==len(word)
 assert int(s['threshold_sum'])==int(r['threshold'])
 desc_mass += Fraction(1,1<<bits)
assert desc_mass==Fraction(652427,1048576)
unresolved=full_mass-desc_mass
assert unresolved==Fraction(134005,1048576)
print('FRONTIER_ROWS=169087')
print('FRONTIER_PREFIX_FREE=PASS')
print('FRONTIER_MASS=3/4')
print('DESCENT_CERTIFICATES=35082')
print('AFFINE_LIFT_REPLAY_ALL_ROWS=PASS')
print('BUDGET_CLASS_MAPPING_ALL_ROWS=PASS')
print('DESCENT_MASS=652427/1048576')
print('UNRESOLVED_MASS=134005/1048576')
print('COMBINED_WITH_GATE4=914571/1048576')
print('GATE11_ARITHMETIC_AUDIT=PASS')
print('UNIVERSAL_COLLATZ=HOLD_UNPROVEN')
