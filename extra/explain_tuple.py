#!/usr/bin/env python3
"""Explain datarace MLN tuples using exported domain metadata."""
from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import Dict, List


def load_domain_info(directory: Path) -> Dict[str, Dict[int, str]]:
    """Load per-domain descriptions produced by MLNDataraceAbsDriver."""
    result: Dict[str, Dict[int, str]] = {}
    combined = directory / "dom_info.tsv"
    if combined.exists():
        for line in combined.read_text(encoding="utf-8").splitlines():
            if not line:
                continue
            parts = line.split("\t", 2)
            if len(parts) != 3:
                continue
            dom, idx, desc = parts
            try:
                index = int(idx)
            except ValueError:
                continue
            result.setdefault(dom, {})[index] = desc
        if result:
            return result
    for dom_file in sorted(directory.glob("dom_*.txt")):
        stem = dom_file.stem
        dom = stem.split("_", 1)[1] if "_" in stem else stem
        entries: Dict[int, str] = result.setdefault(dom, {})
        for line in dom_file.read_text(encoding="utf-8").splitlines():
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t", 1)
            if len(parts) != 2:
                parts = line.split(": ", 1)
            if len(parts) != 2:
                continue
            try:
                index = int(parts[0].strip())
            except ValueError:
                continue
            entries[index] = parts[1].strip()
    return result


TUPLE_SCHEMAS: Dict[str, Dict[str, object]] = {
    "PI": {"domains": ["P", "I"], "template": "program point {0} is exactly the invocation quad {1}"},
    "CICM": {"domains": ["C", "I", "C", "M"], "template": "in caller context {0}, invocation {1} may reach method {3} under callee context {2}"},
    "threadStartI": {"domains": ["I"], "template": "invocation {0} calls java.lang.Thread.start()"},
    "MPhead": {"domains": ["M", "P"], "template": "method {0} has entry program point {1}"},
    "threadACM": {"domains": ["AS", "C", "M"], "template": "abstract thread {0} starts in context {1} with root method {2}"},
    "PP": {"domains": ["P", "P"], "template": "program point {0} has control-flow successor {1}"},
    "threadCICM": {"domains": ["C", "I", "C", "M"], "template": "thread-start invocation {1} in context {0} reaches thread root method {3} under context {2}"},
    "MPtail": {"domains": ["M", "P"], "template": "method {0} exits at program point {1}"},
    "EV": {"domains": ["E", "V"], "template": "heap event {0} uses variable {1} as its base reference"},
    "FC": {"domains": ["F", "C"], "template": "static field {0} may refer to object {1}"},
    "MmethArg": {"domains": ["M", "Z", "V"], "template": "method {0} uses variable {2} as argument position {1}"},
    "CFC": {"domains": ["C", "F", "C"], "template": "object {0} refers to object {2} via field {1}"},
    "CVC": {"domains": ["C", "V", "C"], "template": "in context {0}, variable {1} may point to object {2}"},
    "escE": {"domains": ["E"], "template": "heap event {0} is marked as escaping"},
    "PE": {"domains": ["P", "E"], "template": "program point {0} corresponds to heap event {1}"},
    "excludeSameThread": {"domains": ["K"], "template": "exclude-same-thread flag has value {0}"},
    "EF": {"domains": ["E", "F"], "template": "heap event {0} accesses field {1}"},
    "unlockedRaceHext": {"domains": ["AS", "C", "E", "AS", "C", "E"], "template": "unlocked race candidate between ({0}, {1}, {2}) and ({3}, {4}, {5})"},
    "statF": {"domains": ["F"], "template": "field {0} is static"},
    "simplePM_cs": {"domains": ["C", "P", "C", "M"], "template": "call at {1} in context {0} may enter method {3} with callee context {2}"},
    "simplePH_cs": {"domains": ["C", "P", "C", "P"], "template": "call at {1} in context {0} reaches callee entry {3} under context {2}"},
    "simplePT_cs": {"domains": ["C", "P", "C", "P"], "template": "call at {1} in context {0} returns at {3} under context {2}"},
    "threadPM_cs": {"domains": ["C", "P", "C"], "template": "thread start at {1} in context {0} launches thread context {2}"},
    "threadPH_cs": {"domains": ["C", "P", "C", "P"], "template": "thread start at {1} in context {0} enters thread entry {3} under context {2}"},
    "threadAC": {"domains": ["AS", "C"], "template": "abstract thread {0} is runnable in context {1}"},
    "threadACH": {"domains": ["AS", "C", "P"], "template": "abstract thread {0} in context {1} begins at program point {2}"},
    "PathEdge_cs": {"domains": ["C", "P", "AS", "AS", "AS"], "template": "in context {0}, dataflow reaches {1} taking current thread {2} with parallel set {3} to {4}"},
    "SummEdge_cs": {"domains": ["C", "P", "AS", "AS", "AS"], "template": "summary at {1} in context {0} maps ({2}, {3}) to {4}"},
    "mhp_cs": {"domains": ["C", "P", "AS", "AS"], "template": "in context {0} at {1}, thread {2} may run with thread {3}"},
    "escO": {"domains": ["C"], "template": "object {0} escapes its creating thread"},
    "CEC": {"domains": ["C", "E", "C"], "template": "in context {0}, escaping event {1} can access object {2}"},
    "mhe_cs": {"domains": ["C", "E", "AS", "AS"], "template": "in context {0}, event {1} may run in thread {2} while thread {3} is parallel"},
    "statE": {"domains": ["E"], "template": "heap event {0} touches static state"},
    "escapingRaceHext": {"domains": ["AS", "C", "E", "AS", "C", "E"], "template": "escaping race candidate between ({0}, {1}, {2}) and ({3}, {4}, {5})"},
    "parallelRaceHext": {"domains": ["AS", "C", "E", "AS", "C", "E"], "template": "parallel race candidate between ({0}, {1}, {2}) and ({3}, {4}, {5})"},
    "datarace": {"domains": ["AS", "C", "E", "AS", "C", "E"], "template": "confirmed data race between ({0}, {1}, {2}) and ({3}, {4}, {5})"},
    "racePairs_cs": {"domains": ["E", "E"], "template": "data race detected between events {0} and {1}"},
}


TUPLE_PATTERN = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)\s*")


def explain(tuple_text: str, dom_data: Dict[str, Dict[int, str]]) -> str:
    match = TUPLE_PATTERN.fullmatch(tuple_text)
    if not match:
        raise ValueError(f"Malformed tuple: {tuple_text}")
    name = match.group(1)
    schema = TUPLE_SCHEMAS.get(name)
    if schema is None:
        raise KeyError(f"Unknown tuple predicate: {name}")
    args_part = match.group(2).strip()
    raw_args = [] if not args_part else [part.strip() for part in args_part.split(",")]
    domains: List[str] = schema["domains"]  # type: ignore[index]
    if len(raw_args) != len(domains):
        raise ValueError(f"Expected {len(domains)} arguments for {name}")
    resolved: List[str] = []
    for dom_name, arg in zip(domains, raw_args):
        try:
            index = int(arg)
        except ValueError as exc:
            raise ValueError(f"Argument '{arg}' is not an integer") from exc
        desc = dom_data.get(dom_name, {}).get(index)
        if desc is None:
            desc = f"{dom_name}{index}"
        resolved.append(desc)
    template: str = schema["template"]  # type: ignore[assignment]
    return template.format(*resolved)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tuple", help="tuple predicate to explain, e.g. PI(1,2)")
    parser.add_argument("--dir", default=".", help="directory containing dom_info.tsv (default: current directory)")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    directory = Path(args.dir)
    dom_data = load_domain_info(directory)
    if not dom_data:
        raise SystemExit("Domain information is unavailable; run the analysis first and point --dir to its output directory.")
    try:
        message = explain(args.tuple, dom_data)
    except Exception as exc:
        raise SystemExit(str(exc))
    print(message)


if __name__ == "__main__":
    main()
