#!/usr/bin/env python3
from itertools import product


def affine_const(word):
    if not word:
        return 0
    a, *tail = word
    return 3 ** len(tail) + (2 ** a) * affine_const(tail)


def direct_const(word):
    # C = sum_{j=0}^{k-1} 3^(k-1-j) * 2^(sum of valuations before j)
    total = 0
    prefix = 0
    k = len(word)
    for j, a in enumerate(word):
        total += (3 ** (k - 1 - j)) * (2 ** prefix)
        prefix += a
    return total

checks = 0
for k in range(0, 9):
    for word in product(range(1, 7), repeat=k):
        assert affine_const(list(word)) == direct_const(list(word))
        checks += 1

source_word = [1,2,1,1,1,1,2,2,1,2,1,1,2,1,1,1,1,1,1,1,3,1,2,1,1,1,1,1,3,1,1,2,4,3,1,1,2,2,1,1,1,2,3,4,3,2]
target_word = [1,2,1,1,1,1,2,2,1,2,1,1,2,1,1,1,1,1,1,1,3,1,2,1,1,1,1,1,3,1,1,2,4,3,1,1,2,2,1,1,1,2,1,4,5,2]
source_x = 8209377573671194853403
source_z = 7703680527574930143355
target_x = 32720488761612761563163
target_z = 30704909094934814579323

for label, word, x, z in [
    ("SOURCE", source_word, source_x, source_z),
    ("TARGET", target_word, target_x, target_z),
]:
    C = affine_const(word)
    S = sum(word)
    k = len(word)
    assert (2**S) * z == (3**k) * x + C
    print(f"{label}_LENGTH={k}")
    print(f"{label}_SUM={S}")
    print(f"{label}_AFFINE_C={C}")
    print(f"{label}_AFFINE_ENDPOINT_IDENTITY=PASS")

print(f"GENERIC_AFFINE_CONSTANT_STRUCTURAL_CHECKS={checks}")
print("AFFINE_CONSTANT_RECURSION_AUDIT=PASS")
print("WITNESS001_ENDPOINT_AFFINE_REPLAY=PASS")
print("GATE9_ARITHMETIC_AUDIT=PASS")
print("UNIVERSAL_COLLATZ=HOLD_UNPROVEN")
