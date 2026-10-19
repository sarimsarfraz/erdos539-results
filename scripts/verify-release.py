#!/usr/bin/env python3
"""Check the reviewed inventory and receipts; this does not execute Lean."""
from pathlib import Path
import ast
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / 'docs/release-files.json'
IGNORED = {'.git', '.lake', '.cache', 'build-logs', '__pycache__'}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory():
    files = {}
    # Prune runtime directories before descent; a cache may contain many files.
    import os
    for directory, dirs, names in os.walk(ROOT):
        dirs[:] = sorted(d for d in dirs if d not in IGNORED)
        for name in sorted(names):
            path = Path(directory) / name
            relative = path.relative_to(ROOT).as_posix()
            if path == MANIFEST or name == '.DS_Store' or name.endswith('.pyc'):
                continue
            require(not path.is_symlink(), f'Symlink in release tree: {relative}')
            files[relative] = {'sha256': digest(path), 'bytes': path.stat().st_size}
    return files

def verify():
    expected = json.loads(MANIFEST.read_text())
    require(expected['schema_version'] == 1, 'Unsupported manifest schema')
    files = inventory()
    require(set(files) == set(expected['files']), 'Inventory mismatch: missing or unexpected file')
    for name, entry in files.items():
        require(entry == expected['files'][name], f'File hash or size mismatch: {name}')

    receipt = json.loads((ROOT / 'docs/verification.json').read_text())
    require(receipt['toolchain'] == (ROOT / 'lean-toolchain').read_text().strip(), 'Toolchain mismatch')
    require(receipt['manifest_sha256'] == digest(ROOT / 'lake-manifest.json'), 'Dependency pins changed')
    require(0 < receipt['lean_memory_limit_mb'] <= 4096, 'Receipt memory limit exceeds 4096 MB')
    modules = receipt['modules']
    require(len(modules) == 844, 'Unexpected canonical module count; review the release scope')
    module_paths = set()
    for module in modules:
        name = module['module'].replace('.', '/') + '.lean'
        require(module['exit_code'] == 0, f'Failed proof check: {name}')
        require(digest(ROOT / name) == module['sha256'], f'Proof changed after its check: {name}')
        module_paths.add(name)
    references = {name for name in files if name.startswith('vendor-sources/') and name.endswith('.lean')}
    require(len(references) == 5, 'Unexpected number of preserved upstream reference files')
    require({name for name in files if name.endswith('.lean')} == module_paths | references,
            'Lean source outside audited closure or attributed references')
    axioms = receipt['axiom_audit_output']
    require('Axiom audit passed' in axioms and 'sorryAx' not in axioms, 'Missing successful axiom audit')
    require('Allowed: propext, Classical.choice, Quot.sound.' in axioms, 'Axiom policy changed')

    build = json.loads((ROOT / 'docs/RELEASE_BUILD.json').read_text())
    require(build['verification_receipt_sha256'] == digest(ROOT / 'docs/verification.json'),
            'Build record does not match proof receipt')
    paper = (ROOT / 'paper/main.tex').read_text()
    for field, path in [('sha256', 'paper/main.tex'), ('pdf_sha256', 'paper/main.pdf')]:
        require(build['paper'][field] == digest(ROOT / path), f'Paper provenance mismatch: {path}')
    require(r'\author{Sarim Sarfraz}' in paper and r'\author{Wali Ahmed}' in paper, 'Paper authors missing')
    require(r'\author{Wali Ahmed}' + '\n' + r'\address{Columbia University}' in paper,
            'Wali Ahmed affiliation mismatch')
    require((ROOT / 'paper/main.pdf').read_bytes().startswith(b'%PDF-'), 'Invalid paper PDF header')
    for path in (ROOT / 'scripts').glob('*.py'):
        ast.parse(path.read_text(), filename=str(path))
    for name in files:
        if not name.endswith('.md') or name.startswith('vendor-sources/'):
            continue
        for target in re.findall(r'\]\(([^\s)]+)\)', (ROOT / name).read_text()):
            if '://' in target or target.startswith(('#', 'mailto:')):
                continue
            require((ROOT / name).parent.joinpath(target.split('#')[0]).exists(),
                    f'Broken local documentation link: {name}: {target}')

    with tempfile.TemporaryDirectory(prefix='erdos539-certificates-') as tmp:
        work = Path(tmp)
        shutil.copytree(ROOT / 'scripts', work / 'scripts', ignore=shutil.ignore_patterns('__pycache__'))
        shutil.copytree(ROOT / 'data', work / 'data')
        (work / 'Erdos539').mkdir()
        for script in ['generate_pg13_certificate.py', 'generate_pg13_masks.py', 'generate_reflection_certificate.py']:
            result = subprocess.run([sys.executable, str(work / 'scripts' / script)],
                                    cwd=work, capture_output=True, text=True, timeout=120)
            require(result.returncode == 0, f'Certificate generator failed: {script}: {result.stderr}')
        generated = list((work / 'Erdos539').rglob('*.lean'))
        require(len(generated) == 190, 'Unexpected generated certificate count')
        for path in generated:
            name = path.relative_to(work).as_posix()
            require(name in files and digest(path) == files[name]['sha256'],
                    f'Certificate reproduction mismatch: {name}')
    print(json.dumps({'status': 'passed', 'inventory_files': len(files),
                      'proof_sources_matched': len(modules), 'attributed_reference_files': len(references),
                      'finite_certificates_reproduced': len(generated),
                      'lean_executed_by_this_command': False}, indent=2))

if __name__ == '__main__':
    try:
        require(sys.argv[1:] in ([], ['--write-manifest']), 'Usage: verify-release.py [--write-manifest]')
        if sys.argv[1:]:
            MANIFEST.write_text(json.dumps({'schema_version': 1, 'files': inventory()}, indent=2) + '\n')
            print('Updated inventory only. Run the verifier; this operation does not check proofs.')
        else:
            verify()
    except (ValueError, KeyError, OSError, subprocess.TimeoutExpired) as error:
        sys.exit(f'Release integrity check failed: {error}')
