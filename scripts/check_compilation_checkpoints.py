#!/usr/bin/env python3
"""Compile checkpoints sequentially with per-file and total time limits.

Uses existing Dune-built dependencies. Run inside the project's opam environment.
Stops on the first failure/timeout and leaves successful .vo files reusable.
"""
import argparse
import json
import os
import signal
import re
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--timeout', type=float, default=60)
    p.add_argument('--budget', type=float, default=180)
    p.add_argument('files', nargs='*')
    args = p.parse_args()
    if args.timeout <= 0 or args.budget <= 0:
        p.error('timeouts must be positive')
    paths = ([ROOT / f for f in args.files] if args.files else
             [ROOT / 'experiments/compilation/Frontend.v',
              ROOT / 'experiments/compilation/CompilerConfig.v',
              ROOT / 'experiments/compilation/Pipeline.v',
              ROOT / 'theories/Compilation/Allocation.v',
              ROOT / 'theories/Compilation/FastGraph.v',
              ROOT / 'theories/Compilation/FastAllocation.v',
              ROOT / 'theories/Compilation/FastCompiler.v'] +
             sorted((ROOT / '.artifacts/checkpoints').glob('Word[0-9]*.v'),
                    key=lambda path: (path.stem[:8], path.stem[8:] or 'zz')) +
             [ROOT / '.artifacts/checkpoints/WordPipeline.v'] +
             [ROOT / f'experiments/compilation/{name}.v' for name in
              ['Stack', 'RawCalls', 'StackAllocation', 'StackRemoval',
               'StackNames', 'Sections', 'Target', 'Complete', 'ConcreteCertificate']])
    missing = [str(path.relative_to(ROOT)) for path in paths if not path.exists()]
    if missing:
        p.error('Missing checkpoint sources; run generate_compilation_checkpoints.py first: ' + ', '.join(missing[:3]))
    logs = ROOT / '_build/checkpoints'
    logs.mkdir(parents=True, exist_ok=True)
    built = list((ROOT / '_build/default').rglob('*.vo'))
    dependency_time = max((f.stat().st_mtime for f in built), default=0)
    start = time.monotonic()
    report = logs / 'timings.json'
    results = json.loads(report.read_text()) if report.exists() else []
    for path in paths:
        production = path.parent == ROOT / 'theories/Compilation'
        # Invalidate against every local imported checkpoint, including split phases.
        dependency_files = []
        for names in re.findall(r'From InitE\.Compilation Require (?:Import |Export )?([^.]*)\.', path.read_text()):
            for name in names.split():
                for directory in ['_build/default/theories/Compilation', 'experiments/compilation', '.artifacts/checkpoints']:
                    dep = ROOT / directory / (name + '.vo')
                    if dep.exists():
                        dependency_files.append(dep)
        newest = max([path.stat().st_mtime, dependency_time] +
                     [f.stat().st_mtime for f in dependency_files])
        vo = ((ROOT / '_build/default' / path.relative_to(ROOT)).with_suffix('.vo')
              if production else path.with_suffix('.vo'))
        if vo.exists() and vo.stat().st_mtime >= newest:
            continue
        remaining = args.budget - (time.monotonic() - start)
        if remaining <= 0:
            print('Total time budget reached; rerun to resume.', flush=True)
            return 2
        command = ['rocq', 'compile', '-time',
                   '-Q', '_build/default/galette-theories', 'Galette',
                   '-Q', '_build/default/theories', 'InitE',
                   '-Q', 'experiments/compilation', 'InitE.Compilation',
                   '-Q', '.artifacts/checkpoints', 'InitE.Compilation', str(path)]
        if production:
            command = ['dune', 'build', '-j', '1', str(path.relative_to(ROOT).with_suffix('.vo'))]
        before = time.monotonic()
        log = logs / (path.stem + '.log')
        print(f'Checking {path.stem}', flush=True)
        with log.open('w') as out:
            with subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                  start_new_session=True) as proc:
                try:
                    status = proc.wait(timeout=min(args.timeout, remaining))
                except subprocess.TimeoutExpired:
                    # Dune may have spawned Rocq. Stop the entire job, including
                    # children that ignore the first termination signal.
                    try:
                        os.killpg(proc.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        proc.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        pass
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    proc.wait()
                    status = 'timeout'
        seconds = round(time.monotonic() - before, 3)
        results.append({'file': str(path.relative_to(ROOT)), 'seconds': seconds, 'status': status, 'finished_at': time.time()})
        report.write_text(json.dumps(results, indent=2) + '\n')
        print(f'  {status}: {seconds}s ({log.relative_to(ROOT)})', flush=True)
        if status != 0:
            print(log.read_text()[-3000:], flush=True)
            return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
