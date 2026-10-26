from openpyxl import load_workbook
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
root=Path.home()/'Desktop'
src=root/'EIMERS_AI_KPI_COLLatz_DEMO_QA_SHADOW.xlsx'
scenarios={
'PROOF':{'grades':['PASS']*20,'proof':['NO']*20,'authority':'YES','expected':'HOLD — PROOF COVERAGE'},
'AUTHORITY':{'grades':['PASS']*20,'proof':['YES']*20,'authority':'NO','expected':'HOLD — AUTHORITY'},
'INCOMPLETE':{'grades':['PASS']*19+[''],'proof':['YES']*20,'authority':'YES','expected':'HOLD — INCOMPLETE'},
'ACCURACY':{'grades':['PASS']*19+['FAIL'],'proof':['YES']*20,'authority':'YES','expected':'HOLD — ACCURACY'},
'DRIFT':{'grades':['PASS']*10+['PASS']*9+['FAIL'],'proof':['YES']*20,'authority':'YES','expected':'HOLD — ACCURACY (precedes drift)'},
'REVIEW':{'grades':['PASS']*20,'proof':['YES']*20,'authority':'YES','expected':'REVIEW — MANUAL GATES'}
}
folder=root/'EIMERS_KPI_GATE_QA_CASES'
folder.mkdir(exist_ok=True)
for name,conf in scenarios.items():
 dst=folder/f'QA_{name}_SHADOW.xlsx'
 if dst.exists():raise FileExistsError(dst)
 w=load_workbook(src);t=w['03 TEST ENGINE'];c=w['01 COMMAND'];g=w['02 GOVERNOR']
 c['D7']='QA-'+name+'-'+datetime.now(timezone.utc).strftime('%Y%m%d')
 c['D21']=20
 for i,row in enumerate(range(7,27)):
  t[f'L{row}']=conf['grades'][i]
  t[f'K{row}']=conf['proof'][i]
  t[f'J{row}']='SYNTHETIC QA FIXTURE — NOT LIVE AI'
  t[f'M{row}']='Controlled synthetic gate scenario '+name
  t[f'N{row}']='QA ONLY — no independent approval'
 g['D24']=conf['authority']
 q=w['11 RUN RECEIPT'];q['B7']=conf['expected'];q['B4']='Synthetic QA gate probe: '+name
 w.calculation.fullCalcOnLoad=True;w.calculation.forceFullCalc=True
 w.save(dst)
 print(name,str(dst),'grades',dict(Counter(conf['grades'])),'authority',conf['authority'],'expected',conf['expected'])
