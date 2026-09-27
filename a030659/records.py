"""Load the per-M records written by compute_f.py (plain or gzipped JSON lines)."""
import gzip, json, os

def load_records(path="f_values.jsonl"):
    if not os.path.exists(path) and os.path.exists(path+".gz"):
        with gzip.open(path+".gz","rt") as fh: return [json.loads(l) for l in fh]
    with open(path) as fh: return [json.loads(l) for l in fh]
