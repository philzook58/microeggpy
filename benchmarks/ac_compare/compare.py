"""Interleave release binaries on one CPU; preserve every sample as CSV."""
import argparse
import csv
import statistics
import subprocess

p = argparse.ArgumentParser()
p.add_argument('--binary', action='append', required=True, help='label=executable')
p.add_argument('--samples', type=int, default=7)
p.add_argument('--cpu', type=int, default=2)
p.add_argument('--output', required=True)
a = p.parse_args()
binaries = [entry.split('=', 1) for entry in a.binary]
cases = [('atoms', 7), ('atoms', 8), ('variables', 9), ('variables', 10)]
with open(a.output, 'w') as output:
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(['variant', 'leaves', 'n', 'seconds', 'classes', 'nodes'])
    for leaves, n in cases:
        samples = {name: [] for name, _ in binaries}
        for trial in range(-1, a.samples):  # discard one warmup per binary
            order = binaries if trial % 2 else binaries[::-1]
            for name, binary in order:
                engine = 'lambda' if name == 'lambda' else 'thin'
                run = subprocess.run(['taskset', '-c', str(a.cpu), binary, engine, leaves, str(n)],
                                     check=True, capture_output=True, text=True, timeout=60)
                _, _, _, seconds, classes, nodes = run.stdout.strip().split(',')
                if trial >= 0:
                    samples[name].append(float(seconds))
                    writer.writerow([name, leaves, n, seconds, classes, nodes])
                    output.flush()
        for name, values in samples.items():
            median = statistics.median(values)
            mad = statistics.median(abs(value - median) for value in values)
            print(f'{name:12} {leaves:9} AC{n:<2} median={median:.6f}s MAD={mad:.6f}s', flush=True)
