#!/usr/bin/env python3
"""Audit the complete source closure and strict source policy.

Copyright 2026 Naganori Yamaguchi.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
The underlying generate_manifest.py is adapted unchanged from ProCGroups.
This lexical audit is not an independent proof checker.
"""
from pathlib import Path
import json
import re
import sys
import generate_manifest as gm

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
config = gm.load_json(HERE / 'manifest-config.json')
manifest, report = gm.analyze(ROOT, config)
rows=manifest['moduleRows']
depths=config['depths']
for module,row in rows.items():
    if module in {'Nyll', 'Nyll.All'}: continue
    owner=row['owner']
    clean=gm.mask_noncode((ROOT/row['path']).read_text())
    for line in clean.splitlines():
        match=gm.IMPORT.fullmatch(line)
        if not match: continue
        for target in (match.group(1) or '').split():
            if target not in rows: continue
            if target in {'Nyll', 'Nyll.All'} or depths[rows[target]['owner']]>depths[owner]:
                report['errors'].append({'kind':'reverse-depth-import','module':module,'target':target})

clean=gm.mask_noncode((ROOT/'Nyll/All.lean').read_text())
actual=[m.group(1) for line in clean.splitlines() if (m:=gm.IMPORT.fullmatch(line))]
expected=['Nyll.'+name+'.All' for name in config['orderedLibraries']]
if actual!=expected:
    report['errors'].append({'kind':'root-order','expected':expected,'actual':actual})
report['staticPassed']=not report['errors']
out=ROOT/'tmp/ci-libraries'
out.mkdir(parents=True,exist_ok=True)
(out/'source-audit.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'staticPassed':report['staticPassed'],'moduleCount':report['moduleCount'],
                 'errors':report['errors']},ensure_ascii=False,indent=2))
sys.exit(0 if report['staticPassed'] else 1)
