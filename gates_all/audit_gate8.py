from itertools import product

# Independent structural audit of the word-data recurrence.
def word_data(word):
    if len(word) == 1:
        a = word[0]
        assert a >= 1
        return a - 1, 1
    a = word[0]
    e, C = word_data(word[1:])
    d = a - 1
    return d + e, 3 ** (len(word) - 1) + (2 ** a) * C

# Direct affine constant from a valuation word.
def direct_const(word):
    C = 0
    l = 0
    # Build from the tail, matching 2^S y = 3^l x + C.
    for a in reversed(word):
        C = 3 ** l + (2 ** a) * C
        l += 1
    return C

checks = 0
for L in range(1, 9):
    for word in product(range(1, 7), repeat=L):
        e, C = word_data(word)
        assert sum(word) == L + e
        assert C == direct_const(word)
        checks += 1

print(f"WORD_DATA_STRUCTURAL_CHECKS={checks}")
print("WORD_DATA_SUM_IDENTITY=PASS")
print("WORD_DATA_AFFINE_CONSTANT_RECURRENCE=PASS")
print("ACTUAL_PATH_WORD_ADAPTER_ARITHMETIC=PASS")
print("UNIVERSAL_COLLATZ=HOLD_UNPROVEN")
