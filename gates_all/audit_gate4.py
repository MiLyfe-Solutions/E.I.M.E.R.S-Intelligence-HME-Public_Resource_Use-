from fractions import Fraction
import csv,json
from pathlib import Path
p=Path(__file__).parent
rows=list(csv.DictReader((p/"adaptive_frontier_depth20.csv").open()))
desc=sum((Fraction(1,2**int(x["q_bits"])) for x in rows if x["status"]=="DESCENT"),Fraction())
un=sum((Fraction(1,2**int(x["q_bits"])) for x in rows if x["status"]!="DESCENT"),Fraction())
imm=Fraction(1,4)
print("IMMEDIATE_STEP47_CERTIFIED_MASS=1/4")
print("IMMEDIATE_STEP47_CERTIFIED_PERCENT=25.0")
print(f"ADAPTIVE_LEAF_COUNT={len(rows)}")
print(f"ADAPTIVE_DESCENDING_LEAF_COUNT={sum(x['status']=='DESCENT' for x in rows)}")
print(f"ADAPTIVE_UNRESOLVED_LEAF_COUNT={sum(x['status']!='DESCENT' for x in rows)}")
print(f"ADAPTIVE_ADDITIONAL_CERTIFIED_MASS={desc}")
print(f"TOTAL_BOUNDED_CERTIFIED_MASS={imm+desc}")
print(f"TOTAL_BOUNDED_CERTIFIED_PERCENT={float((imm+desc)*100):.9f}")
print(f"UNRESOLVED_MASS={un}")
print(f"UNRESOLVED_PERCENT={float(un*100):.9f}")
assert imm+desc+un==1
assert len(rows)==169087
assert sum(x['status']=='DESCENT' for x in rows)==35082
assert desc==Fraction(652427,1048576)
assert un==Fraction(134005,1048576)
print("GATE4_ADAPTIVE_PARTITION_AUDIT=PASS")
print("UNIVERSAL_COLLATZ=HOLD_UNPROVEN")
