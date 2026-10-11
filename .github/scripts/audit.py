#!/usr/bin/env python3
"""Audit source closure and record the single explicitly unproved presentation.

Copyright 2026 Naganori Yamaguchi.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
The underlying generate_manifest.py is adapted unchanged from ProCGroups.
This lexical audit is not an independent proof checker.
"""
from pathlib import Path
import importlib.util
import json
import re
import sys
import generate_manifest as gm

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
config = gm.load_json(HERE / 'manifest-config.json')
manifest, report = gm.analyze(ROOT, config)
source = 'Lean4/AnabelianGeometry/GeometricFundamentalGroup/CharZeroPresentation.lean'
spec = importlib.util.spec_from_file_location('diagnostics', HERE / 'check-library-diagnostics.py')
diagnostics = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostics)
allowed = []
if diagnostics.authorized_location(ROOT) is not None:
    clean = gm.mask_noncode((ROOT/source).read_text())
    line = clean[:re.search(r'\bsorry\b', clean).start()].count('\n')+1
    kept=[]
    for finding in report['errors']:
        if (finding.get('kind')=='forbidden-source-token' and finding.get('message')=='sorry'
                and finding.get('path')==source and finding.get('line')==line and not allowed):
            allowed.append({**finding,'declaration':'AnabelianGeometry.GeometricFundamentalGroup.exists_surfacePresentation_charZero','status':'UNPROVED; explicitly authorized on 2026-10-09'})
        else: kept.append(finding)
    report['errors']=kept
    if len(allowed)!=1:
        report['errors'].append({'kind':'exception-audit','message':'Expected exactly one visible unproved presentation'})

rows=manifest['moduleRows']
depths=config['depths']
for module,row in rows.items():
    if module=='All': continue
    owner=row['owner']
    clean=gm.mask_noncode((ROOT/row['path']).read_text())
    for line in clean.splitlines():
        match=gm.IMPORT.fullmatch(line)
        if not match: continue
        for target in (match.group(1) or '').split():
            if target not in rows: continue
            if target=='All' or depths[rows[target]['owner']]>depths[owner]:
                report['errors'].append({'kind':'reverse-depth-import','module':module,'target':target})

clean=gm.mask_noncode((ROOT/'Lean4/All.lean').read_text())
actual=[m.group(1) for line in clean.splitlines() if (m:=gm.IMPORT.fullmatch(line))]
expected=[name+'.All' for name in config['orderedLibraries']]
if actual!=expected:
    report['errors'].append({'kind':'root-order','expected':expected,'actual':actual})
report['authorizedUnproved']=allowed
report['staticPassed']=not report['errors']
out=ROOT/'tmp/ci-libraries'
out.mkdir(parents=True,exist_ok=True)
(out/'source-audit.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'staticPassed':report['staticPassed'],'moduleCount':report['moduleCount'],
                 'authorizedUnproved':allowed,'errors':report['errors']},ensure_ascii=False,indent=2))
sys.exit(0 if report['staticPassed'] else 1)
