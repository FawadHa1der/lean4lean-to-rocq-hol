#!/usr/bin/env python3
"""Syntax-only fixture composition: rename table IDs, never logical claims."""
import argparse
import json
from pathlib import Path


def combine(paths):
    out = []
    tops = {'in': 0, 'il': 0, 'ie': -1}
    for path in paths:
        offsets = dict(tops)
        offsets['ie'] += 1
        def name(i):
            return i + offsets['in'] if i else 0
        def level(i):
            return i + offsets['il'] if i else 0
        def expr(i):
            return i + offsets['ie']
        def fields(v, names=(), levels=(), exprs=(), name_lists=(), level_lists=()):
            for key in names:
                v[key] = name(v[key])
            for key in levels:
                v[key] = level(v[key])
            for key in exprs:
                v[key] = expr(v[key])
            for key in name_lists:
                v[key] = list(map(name, v[key]))
            for key in level_lists:
                v[key] = list(map(level, v[key]))
        def header(v):
            fields(v, names=('name',), exprs=('type',), name_lists=('levelParams',))
        for line in path.read_text().splitlines():
            row = json.loads(line)
            tags = set(row) - {'in', 'il', 'ie'}
            if len(tags) != 1:
                raise ValueError('ambiguous record')
            tag = tags.pop()
            v = row[tag]
            if tag == 'meta':
                if not out:
                    out.append(row)
                continue
            if tag in ('str', 'num'):
                fields(v, names=('pre',))
            elif tag == 'succ':
                row[tag] = level(v)
            elif tag in ('max', 'imax'):
                row[tag] = list(map(level, v))
            elif tag == 'param':
                row[tag] = name(v)
            elif tag == 'sort':
                row[tag] = level(v)
            elif tag == 'const':
                fields(v, names=('name',), level_lists=('us',))
            elif tag == 'app':
                fields(v, exprs=('fn', 'arg'))
            elif tag in ('lam', 'forallE', 'letE'):
                fields(v, names=('name',), exprs=('type', 'body') + (('value',) if tag == 'letE' else ()))
            elif tag == 'proj':
                fields(v, names=('typeName',), exprs=('struct',))
            elif tag == 'mdata':
                fields(v, exprs=('expr',))
            elif tag in ('bvar', 'natVal', 'strVal'):
                pass
            elif tag in ('axiom', 'def', 'thm', 'opaque', 'quot'):
                header(v)
                if tag in ('def', 'thm', 'opaque'):
                    fields(v, exprs=('value',), name_lists=('all',))
            elif tag == 'inductive':
                for typ in v['types']:
                    header(typ)
                    fields(typ, name_lists=('all', 'ctors'))
                for ctor in v['ctors']:
                    header(ctor)
                    fields(ctor, names=('induct',))
                for rec in v['recs']:
                    header(rec)
                    fields(rec, name_lists=('all',))
                    for rule in rec['rules']:
                        fields(rule, names=('ctor',), exprs=('rhs',))
            else:
                raise ValueError('unsupported tag: ' + tag)
            for key in tops:
                if key in row:
                    row[key] += offsets[key]
                    tops[key] = max(tops[key], row[key])
            out.append(row)
    return ''.join(json.dumps(row, ensure_ascii=True, separators=(',', ':')) + '\n' for row in out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs', type=Path, nargs='+')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(combine(args.inputs))
