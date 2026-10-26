from pathlib import Path
import csv
from fractions import Fraction

base = Path(__file__).resolve().parent
summary = list(csv.DictReader((base / 'budget_guard_summary.csv').open()))
leafs = list(csv.DictReader((base / 'adaptive_leaf_to_budget_guard.csv').open()))

expected = {
    'BUDGET_L02': (2,5,19), 'BUDGET_L03': (3,6,89),
    'BUDGET_L04': (4,8,635), 'BUDGET_L05': (5,9,2161),
    'BUDGET_L06': (6,11,13747), 'BUDGET_L07': (7,13,85849),
    'BUDGET_L08': (8,14,265739), 'BUDGET_L09': (9,16,1620641),
    'BUDGET_L10': (10,17,4927459), 'BUDGET_L11': (11,19,29767849),
    'BUDGET_L12': (12,20,89827835),
}

ok = True
mass = Fraction(0,1)
count = 0
for row in summary:
    gid = row['guard_id']
    if gid not in expected:
        continue
    l,t,d = expected[gid]
    row_ok = (int(row['continuation_steps']) == l and
              int(row['threshold_sum']) == t and
              int(row['worst_envelope_constant']) == d and
              int(row['observed_sum_min']) >= t)
    print(f'{gid}_L={l}_T={t}_D={d}_SUMMARY_MATCH={"PASS" if row_ok else "FAIL"}')
    ok &= row_ok
    mass += Fraction(row['mass'])
    count += int(row['leaf_count'])

leaf_ok = True
for row in leafs:
    gid = row['guard_id']
    if gid not in expected:
        leaf_ok = False
        break
    l,t,_ = expected[gid]
    if int(row['continuation_steps']) != l or int(row['valuation_sum']) < t:
        leaf_ok = False
        break

print(f'ADAPTIVE_DESCENT_LEAF_ROWS={len(leafs)}')
print(f'ADAPTIVE_DESCENT_LEAF_COUNT_SUMMARY={count}')
print(f'ADAPTIVE_LEAF_TO_BUDGET_MATCH={"PASS" if leaf_ok and count == len(leafs) else "FAIL"}')
print(f'ADDITIONAL_CERTIFIED_MASS={mass}')
print(f'ADDITIONAL_CERTIFIED_PERCENT={float(mass)*100:.12f}')
print('IMMEDIATE_GATE4_MASS=1/4')
combined = mass + Fraction(1,4)
print(f'COMBINED_CERTIFIED_MASS={combined}')
print(f'COMBINED_CERTIFIED_PERCENT={float(combined)*100:.12f}')
print('GATE10_ARITHMETIC_AUDIT=' + ('PASS' if ok and leaf_ok and count == len(leafs) and mass == Fraction(652427,1048576) else 'FAIL'))
print('UNIVERSAL_COLLATZ=HOLD_UNPROVEN')
raise SystemExit(0 if ok and leaf_ok and count == len(leafs) and mass == Fraction(652427,1048576) else 1)
