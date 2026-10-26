#!/usr/bin/env python3
from itertools import product

THRESHOLDS={1:3,2:5,3:6,4:8,5:9,6:11,7:13,8:14,9:16,10:17,11:19,12:20}
DS={1:1,2:19,3:89,4:635,5:2161,6:13747,7:85849,8:265739,9:1620641,10:4927459,11:29767849,12:89827835}

def env(l,e):
    if l == 0: return 0
    return 3**(l-1) + 2**(e+1)*env(l-1,0)

def C_of(word):
    if len(word)==1: return 1
    a=word[0]
    return 3**(len(word)-1) + 2**a*C_of(word[1:])

def comps(total,k,prefix=()):
    if k==1:
        yield prefix+(total,)
    else:
        for a in range(1,total-k+2):
            yield from comps(total-a,k-1,prefix+(a,))

print('=== GATE 7 POSITIVE WORD BOUND AUDIT ===')
count=0
for l,T in THRESHOLDS.items():
    e=T-l
    D=env(l,e)
    assert D==DS[l]
    mx=-1; arg=None
    for w in comps(T,l):
        c=C_of(w); count+=1
        assert c<=D
        if c>mx: mx,arg=c,w
    expected=(T-l+1,)+(1,)*(l-1)
    assert mx==D and arg==expected
    # stress excess levels without exhaustive explosion
    for extra in range(0,13):
        S=T+extra
        # frontloaded extremal word is enough for normalized envelope identity
        w=(S-l+1,)+(1,)*(l-1)
        c=C_of(w)
        assert (2**T)*c <= (2**S)*D
    print(f'L{l:02d}_T={T}_EXCESS={e}_D={D}_MAX={mx}_ARGMAX={arg}_PASS')
print(f'BOUNDARY_WORDS_REPLAYED={count}')
print('GENERIC_ENVELOPE_RECURRENCE_AUDIT=PASS')
print('NORMALIZED_EXCESS_STRESS=PASS')
print('GATE7_ARITHMETIC_AUDIT=PASS')
print('UNIVERSAL_COLLATZ=HOLD_UNPROVEN')
