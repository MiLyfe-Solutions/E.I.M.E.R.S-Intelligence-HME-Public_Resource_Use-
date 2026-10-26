from pathlib import Path
import json,hashlib,collections
OUT=Path('/mnt/data/collatz_h13'); M=64; CAP=12

def v2(n):
 k=0
 while n%2==0: n//=2;k+=1
 return k

def a(n):return (3*n+1)//(1<<v2(3*n+1))
rows=[];edges=[]; open_nodes=[]; symbolic_replays=0
for r in range(1,M,2):
 v=v2(3*r+1)
 if v>=6:
  # Exceptional branch: precision 6 through 12, preserve all children as disjoint dyadic leaves.
  chain=[]
  for b in range(6,CAP+1):
   residue=next(x for x in range(1,1<<b,2) if (3*x+1)%(1<<b)==0)
   chain.append({'bits':b,'residue':residue,'lower_bound_v':b})
   if b>6:
    sibling=residue^(1<<(b-1))
    assert v2(3*sibling+1)==b-1
  open_nodes.append({'source_r':r,'source_mod':M,'reason':'UNBOUNDED_VALUATION','refinement_chain':chain,'precision_cap':CAP})
  rows.append({'r':r,'status':'OPEN_EXCEPTIONAL','source_mass_numerator':1,'source_mass_denominator':32})
  continue
 base=(3*r+1)//(1<<v); step=3*(M>>v)
 assert step%2==0
 # minimal q modulus to fix image mod64
 qmod=1<<v
 assert step*qmod%M==0 and (qmod==1 or step*(qmod//2)%M!=0)
 destinations=[]
 for qres in range(qmod):
  src=r+M*qres; dest=(base+step*qres)%M
  assert dest%2==1
  for k in (0,1,3):
   q=qres+qmod*k;n=r+M*q
   assert v2(3*n+1)==v and a(n)==base+step*q and a(n)%M==dest
   symbolic_replays+=1
  destinations.append(dest)
  edges.append({'source_residue':r,'source_mod':M,'q_guard':qres,'q_mod':qmod,'source_residue_refined':src,'source_mod_refined':M*qmod,'target_residue_mod64':dest,'endpoint_base':base+step*qres,'endpoint_step_refined':step*qmod,'valuation':v})
 assert len(set(destinations))==qmod # since v <=5, injective mod64
 rows.append({'r':r,'status':'EXACT','valuation':v,'image_base':base,'image_step':step,'q_guard_modulus':qmod,'destination_classes':destinations,'first_step_strict_for_all_q':r>base and M>=step,'first_step_strict_for_q_ge_1':r+M>base+step and M>=step})
assert len(rows)==32 and len(edges)==sum(1<<row['valuation'] for row in rows if row['status']=='EXACT')
# Property grouping: distinct transition evidence, one generic symbolic inequality schema.
strict0=[r['r'] for r in rows if r['status']=='EXACT' and r['first_step_strict_for_all_q']]
strict1=[r['r'] for r in rows if r['status']=='EXACT' and r['first_step_strict_for_q_ge_1']]
# Check exact destination coverage among 31 families, but no guarantee of next certified descent.
destset=set(e['target_residue_mod64'] for e in edges)
allodd=set(range(1,64,2)); missing=sorted(allodd-destset)
# Negative control: unrefined r=1 has multiple destinations.
r1=next(r for r in rows if r['r']==1)
assert len(set(r1['destination_classes']))>1
# Stronger negative control: each refined edge maps into a residue but not necessarily to an exact-valued class.
exceptional_incoming=sum(e['target_residue_mod64']==21 for e in edges)
# Arithmetic consistency: disjoint refined source guards partition each original source family.
assert all(len([e for e in edges if e['source_residue']==r['r']])==r['q_guard_modulus'] for r in rows if r['status']=='EXACT')
res={'input':'H12 mod64 odd partition; independently recomputed','source_odd_classes':32,'uniform_valuation_classes':31,'open_exceptional_classes':1,'exact_guarded_edges':len(edges),'distinct_destination_residues':len(destset),'destination_residues_missing':missing,'edges_into_exceptional_residue_21':exceptional_incoming,'source_classes_strict_descent_all_q':len(strict0),'source_classes_strict_descent_q_ge_1':len(strict1),'strict_all_residues':strict0,'strict_q_ge_1_residues':strict1,'symbolic_replay_samples':symbolic_replays,'discovery_work':'none beyond partition refinement enumeration','rows':rows,'edges':edges,'open_nodes':open_nodes,'status':'EXACT_ARITHMETIC_CHECKED','lean':'NOT_RUN','independent_audit':'NOT_RUN','v185':'NOT_ACCESSED','universal_status':'HOLD_UNPROVEN'}
(OUT/'results.json').write_text(json.dumps(res,indent=2)+'\n')
report=f'''# Gate H13 — Destination closure and guarded escape accounting\n\n## Exact scoped results\n- Parent domain: all **32 odd residues modulo 64**, independently reconstructed from the H12 input specification.\n- **31** uniform first-step valuation families; **one** exceptional class `21 mod 64` remains OPEN.\n- Refined the 31 exact classes into **{len(edges)}** disjoint guarded source subfamilies, each with a **single exact destination residue modulo 64**. Refinement for a valuation-v class requires `q mod 2^v` (source precision 6+v bits).\n- Destination residues reached: **{len(destset)}/32**; missing residues in this *one-step image*, not missing source coverage: {missing}.\n- Guarded edges landing at exceptional residue 21: **{exceptional_incoming}**. Those destinations are recorded, not declared certified successor edges.\n- Exceptional source `21 mod 64` was refined symbolically through precision **{CAP}**; at each depth one continuing exceptional class remains. This is an **open precision obligation**, not a finite partition closure.\n- Strict descent on the first accelerated step for all q>=0: **{len(strict0)}** exact classes; for all q>=1: **{len(strict1)}** exact classes (overlapping). No global progress result.\n- Bounded replay: **{symbolic_replays}** checks on guarded edges (three parameters each). Symbolic exact affine identities justify all q>=0, independent of replay.\n- Negative control: residue 1 mod64 has multiple possible destinations mod64; treating representative q=0 as a universal successor is invalid.\n- A destination residue label is NOT a complete successor certificate. Parameter compatibility and successor valuation guards must be preserved.\n- V185 NOT_ACCESSED; Lean NOT_RUN; independent audit NOT_RUN; universal HOLD_UNPROVEN.\n\n## Proof obligations\n1. Refine exceptional valuation branch as needed for requested destination precision; do not treat a finite cap as closure.\n2. Prove exact successor-family membership with affine parameter transport, not merely destination residue.\n3. Build complete guarded transition coverage with a well-founded rank on every nonterminal branch before making any universal termination claim.\n'''
(OUT/'REPORT.md').write_text(report)
with (OUT/'SHA256SUMS.txt').open('w') as f:
 for p in ('gate_h13.py','results.json','REPORT.md'):
  f.write(hashlib.sha256((OUT/p).read_bytes()).hexdigest()+'  '+p+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ('rows','edges','open_nodes')},indent=2))
