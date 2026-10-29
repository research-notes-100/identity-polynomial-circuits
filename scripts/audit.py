#!/usr/bin/env python3
"""Audit the final, unconditional theorems and their current validation records.

This checks reproducibility records, not a replacement for running Lean's kernel.
Re-run scripts/validate.py after modifying Lean sources or dependency pins.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOP = {
    'IDMM.main_target', 'IDMM.main_target_almost_every_char',
    'IDMM.main_target_char_zero', 'IDMM.construction_almost_every_char',
    'IDMM.construction_char_zero', 'IDMM.IDBoundF.of_forall_add', 'IDMM.thin_main',
}
# The every-characteristic theorem has its own import closure: Matmul clashes with OAI's Main.
TOP_EVERY_CHAR = {
    'IDMM.id_bound_every_char', 'IDMM.rankAtMost_of_scheme', 'IDMM.uz_exponent_slack',
    'Matmul.RectangularRankBridge.exists_scheme_certificate',
}
# (stage, audit module) pairs that validate.py runs, in order.
AXIOM_STAGES = (('axioms', 'IDMM/FinalAudit.lean'), ('axioms_every_char', 'IDMM/FinalAuditEveryChar.lean'))
KERNEL_STAGES = (('kernel', 'IDMM.FinalAudit'), ('kernel_every_char', 'IDMM.FinalAuditEveryChar'))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    files = [p for folder in ('IDMM', 'PauliCubes', 'OAI', 'Matmul')
             for p in (ROOT / folder).rglob('*.lean')]
    files += [ROOT / f for f in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}


def audit(directory):
    provenance = json.loads((ROOT / 'validation/provenance.json').read_text())
    for f, h in provenance['openai_sha256'].items():
        assert digest(ROOT / f) == h, f'Upstream source changed: {f}'
    for f, h in provenance['matmul_sha256'].items():
        assert digest(ROOT / f) == h, f'Upstream Matmul source changed: {f}'
    for f, rec in provenance['matmul_modified'].items():
        assert digest(ROOT / f) == rec['current_sha256'], f'Ported Matmul file changed again: {f}'
    for folder in ('IDMM', 'PauliCubes', 'Matmul'):
        for f in (ROOT / folder).rglob('*.lean'):
            assert not re.search(r'\b(?:sorry|native_decide)\b|^\s*axiom\s',
                                 f.read_text(), re.M), f'Forbidden shortcut: {f}'
    record = json.loads((directory / 'validation.json').read_text())
    assert record['source_sha256'] == sources(), 'Sources or pins changed since verification'
    stages = ['build'] + [s for s, _ in AXIOM_STAGES] + [s for s, _ in KERNEL_STAGES]
    for stage in stages:
        assert record[stage]['exit_code'] == 0, f'{stage} failed'
        assert digest(directory / f'{stage}.log') == record[stage]['log_sha256'], stage
    for stage, module in KERNEL_STAGES:
        assert record[stage]['command'] == ['lake', 'env', 'leanchecker', '--fresh', module], stage
    assert 'Build completed successfully' in (directory / 'build.log').read_text()
    for (stage, _), top in zip(AXIOM_STAGES, (TOP, TOP_EVERY_CHAR)):
        text = (directory / f'{stage}.log').read_text()
        assert not re.search(r'\berror\b', text), f'{stage}: Lean reported an error'
        rows = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
        assert top <= rows.keys(), f'Missing declarations: {top - rows.keys()}'
        for name, deps in rows.items():
            assert {d.strip() for d in deps.split(',') if d.strip()} <= ALLOWED, name
    return {'status': 'passed', 'unconditional_main_target_proved': True,
            'audited_declarations': sorted(TOP | TOP_EVERY_CHAR), 'allowed_axioms': sorted(ALLOWED),
            'unchanged_OpenAI_modules': len(provenance['openai_sha256']),
            'unchanged_Matmul_files': len(provenance['matmul_sha256']),
            'modified_Matmul_files': sorted(provenance['matmul_modified']),
            'completed_eastern': record['completed_eastern'],
            'scope': 'Current source/pin hashes, complete build, axiom audit, fresh kernel replay.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validation-dir', type=Path, default=ROOT / 'validation/release')
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    result = json.dumps(audit(args.validation_dir.resolve()), indent=2) + '\n'
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(result)
    print(result, end='')
