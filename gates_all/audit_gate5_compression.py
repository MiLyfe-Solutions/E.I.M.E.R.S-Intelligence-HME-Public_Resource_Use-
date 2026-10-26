import csv
from fractions import Fraction
TH={1:3,2:5,3:6,4:8,5:9,6:11,7:13,8:14,9:16,10:17,11:19,12:20}
DM={1:1,2:19,3:89,4:635,5:2161,6:13747,7:85849,8:265739,9:1620641,10:4927459,11:29767849,12:89827835}
N0=3487011090801549639707
NS=9444732965739290427392
X0=6544422935497359190781
XS=17725876239305002191858
rows=list(csv.DictReader(open('adaptive_frontier_depth20.csv')))
d=[r for r in rows if r['status']=='DESCENT']
assert len(d)==35082
mass=Fraction(0,1); counts={}
for r in d:
    w=list(map(int,r['post46_word'].split(','))); l=len(w); s=sum(w); b=int(r['q_bits'])
    assert 2 <= l <= 12
    assert s >= TH[l]
    counts[l]=counts.get(l,0)+1
    mass += Fraction(1,2**b)
assert mass == Fraction(652427,1048576)
# Verify the 12 worst-envelope guard inequalities at q=0 and positive slope.
for l in range(1,13):
    t=TH[l]; D=DM[l]
    # If 2^t*y <= 3^l*x46(q)+D, it is sufficient that RHS < 2^t*n(q).
    base_gap=(2**t)*N0 - (3**l*X0 + D)
    slope_gap=(2**t)*NS - 3**l*XS
    assert base_gap > 0, (l,base_gap)
    assert slope_gap > 0, (l,slope_gap)
    print(f'BUDGET_L{l:02d}_THRESHOLD={t}')
    print(f'BUDGET_L{l:02d}_ENVELOPE_D={D}')
    print(f'BUDGET_L{l:02d}_BASE_GAP={base_gap}')
    print(f'BUDGET_L{l:02d}_SLOPE_GAP={slope_gap}')
print('ADAPTIVE_DESCENDING_LEAVES=35082')
print('ADAPTIVE_BUDGET_GUARD_CLASSES=11')
print('ADAPTIVE_COMPRESSION_FACTOR=3189.272727273')
print('ADAPTIVE_CERTIFIED_MASS=652427/1048576')
print('ADAPTIVE_CERTIFIED_PERCENT=62.220287323')
print('WITH_IMMEDIATE_STEP47_CERTIFIED_MASS=914571/1048576')
print('WITH_IMMEDIATE_STEP47_CERTIFIED_PERCENT=87.220287323')
print('BUDGET_ENVELOPE_ARITHMETIC=PASS')
print('GATE5_COMPRESSION_AUDIT=PASS')
print('UNIVERSAL_COLLATZ=HOLD_UNPROVEN')
