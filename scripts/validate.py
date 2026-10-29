#!/usr/bin/env python3
"""Run all three proof-validation gates sequentially; record timestamps and hashes.
Uses the pinned lake environment. Outputs only to --out (plus normal .lake artifacts).
"""
import argparse
import json
import shutil
import subprocess
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo
from audit import ROOT, sources, digest, audit, AXIOM_STAGES, KERNEL_STAGES

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
out = args.out.resolve()
out.mkdir(parents=True, exist_ok=True)
lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
now = lambda: datetime.now(ZoneInfo('America/New_York')).isoformat()
record = {'started_eastern': now(), 'source_sha256': sources(), 'status': 'running'}
STAGES = (
    [('build', ['lake', 'build'])]
    + [(stage, ['lake', 'env', 'lean', path]) for stage, path in AXIOM_STAGES]
    + [(stage, ['lake', 'env', 'leanchecker', '--fresh', module]) for stage, module in KERNEL_STAGES]
)
for stage, cmd in STAGES:
    started = now()
    record['current_stage'] = stage
    record['stage_started_eastern'] = started
    (out / 'validation.json').write_text(json.dumps(record, indent=2) + '\n')
    with (out / f'{stage}.log').open('w') as log:
        result = subprocess.run([lake, *cmd[1:]], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    # Keep machine-specific paths out of the published records.
    log_path = out / f'{stage}.log'
    data = log_path.read_bytes().replace(str(ROOT).encode(), b'<repo>').replace(str(Path.home()).encode(), b'~')
    log_path.write_bytes(data)
    record[stage] = {'command': cmd, 'exit_code': result.returncode,
                     'started_eastern': started, 'completed_eastern': now(),
                     'log_sha256': digest(out / f'{stage}.log')}
    (out / 'validation.json').write_text(json.dumps(record, indent=2) + '\n')
    if result.returncode:
        record['status'] = 'failed'
        (out / 'validation.json').write_text(json.dumps(record, indent=2) + '\n')
        raise SystemExit(result.returncode)
record['completed_eastern'] = now()
record['status'] = 'passed'
record['current_stage'] = 'complete'
assert sources() == record['source_sha256'], 'Sources changed during verification'
(out / 'validation.json').write_text(json.dumps(record, indent=2) + '\n')
report = audit(out)
(out / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
