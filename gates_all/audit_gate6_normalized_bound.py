#!/usr/bin/env python3
THRESHOLDS={1:3,2:5,3:6,4:8,5:9,6:11,7:13,8:14,9:16,10:17,11:19,12:20}
DS={1:1,2:19,3:89,4:635,5:2161,6:13747,7:85849,8:265739,9:1620641,10:4927459,11:29767849,12:89827835}

def C_of(word):
    C=0; S=0; l=len(word)
    for j,a in enumerate(word):
        C += (3**(l-1-j))*(2**S)
        S += a
    return C,S

def comps(total,k,prefix=()):
    if k==1:
        yield prefix+(total,)
    else:
        for a in range(1,total-k+2):
            yield from comps(total-a,k-1,prefix+(a,))

def add_one(word,k):
    w=list(word); w[k]+=1; return tuple(w)

print('=== GATE 6 NORMALIZED CONSTANT AUDIT ===')
all_boundary=0; mono=0
for l,T in THRESHOLDS.items():
    D=DS[l]; maxC=-1; args=[]; count=0
    boundary=list(comps(T,l))
    for w in boundary:
        C,S=C_of(w); count+=1
        assert C<=D
        if C>maxC: maxC=C; args=[w]
        elif C==maxC: args.append(w)
    expected=(T-l+1,)+(1,)*(l-1)
    assert maxC==D and expected in args
    # Exhaustively verify one-bit normalized monotonicity from every boundary word
    # and every coordinate: 2^T C(w+e_k) <= 2^(T+1) C(w).
    for w in boundary:
        C,S=C_of(w)
        for k in range(l):
            Cp,Sp=C_of(add_one(w,k))
            assert (2**T)*Cp <= (2**(T+1))*C
            mono += 1
    all_boundary += count
    print(f'L{l:02d}_T={T}_D={D}_BOUNDARY_WORDS={count}_MAX={maxC}_EXPECTED_ARGMAX={expected}_PASS')
print(f'BOUNDARY_WORDS_EXHAUSTED={all_boundary}')
print(f'ONE_BIT_MONOTONICITY_CHECKS={mono}')
print('BOUNDARY_MAX_AUDIT=PASS')
print('NORMALIZED_ONE_BIT_MONOTONICITY_AUDIT=PASS')
print('NORMALIZED_CONSTANT_BOUND=EXACT_ARITHMETIC_CHECKED')
print('GENERIC_COMBINATORIAL_LEAN_LEMMA=OPEN')
print('UNIVERSAL_COLLATZ=HOLD_UNPROVEN')
