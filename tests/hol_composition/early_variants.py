"""Pinned, test-only early-irrelevance snapshots; no checker authority."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil

import early_observers

SUITE = Path(__file__).resolve().parent
SPEC_SHA256 = '8217d8e8c9aababa4d9833dd292877e623f87be6f5473dfc3322a129cb6abc1d'
OBSERVER_SHA256 = '8c1e16a4888e5546de410c1f14fd3575a225018b18f77dfcf06efc2139a6e6b0'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


SELF_SHA256 = digest(Path(__file__))


def spec(suite=SUITE):
    path = suite / 'early-pins.json'
    if path.is_symlink() or digest(path) != SPEC_SHA256:
        raise ValueError('Early registry/pins changed')
    return json.loads(path.read_text())


def jobs(suite=SUITE):
    return {tag: dict(copy.deepcopy(entry['job']), early_variant=tag)
            for tag, entry in spec(suite)['groups'].items()}


def tree_pins(root):
    """Only the explicit, absolute toolchain link may escape a source snapshot."""
    if root.is_symlink():
        raise ValueError('Snapshot root is a symlink')
    files, links = {}, {}
    for path in sorted(root.rglob('*')):
        relative = str(path.relative_to(root))
        if path.is_symlink():
            target = os.readlink(path)
            if relative != 'toolchain' or not Path(target).is_absolute() or not path.is_dir():
                raise ValueError('Unexpected source symlink: ' + relative)
            links[relative] = {'target': target, 'resolved': str(path.resolve())}
        elif path.is_file():
            files[relative] = digest(path)
        elif not path.is_dir():
            raise ValueError('Nonregular source: ' + relative)
    return {'files': files, 'symlinks': links}


def require_pins(root, expected):
    actual = tree_pins(root)
    if actual != expected:
        raise ValueError('Snapshot drift: ' + str(root))
    return actual


def require_file(root, relative, expected):
    path = root / relative
    if path.is_symlink() or digest(path) != expected:
        raise ValueError('Early source pin mismatch: ' + relative)


def prepare(snapshot, report, tag, job, frozen):
    local_suite = snapshot / 'tests/hol_composition'
    registry = jobs(local_suite)
    if tag not in registry or job != registry[tag]:
        raise ValueError('Unregistered or altered early job')
    if frozen is None:
        raise ValueError('Early jobs require acquisition-time snapshot pins')
    require_pins(snapshot, frozen)
    data = spec(local_suite)
    require_file(local_suite, 'early_variants.py', SELF_SHA256)
    require_file(local_suite, 'early_observers.py', OBSERVER_SHA256)
    require_file(snapshot, 'hol/core.ml', data['production_core_sha256'])
    for relative, pin in data['drivers'].items():
        require_file(snapshot, relative, pin)
    for entry in data['historical_cores'].values():
        require_file(snapshot, entry['path'], entry['sha256'])
    entry = data['groups'][tag]
    variant = entry['variant']
    historical = entry['historical_core_control']
    if historical != (variant != 'candidate'):
        raise ValueError('Historical/production label mismatch')
    source_path = snapshot / ('hol/core.ml' if not historical else data['historical_cores'][variant]['path'])
    require_file(snapshot, str(source_path.relative_to(snapshot)), entry['unmodified_core_sha256'])
    source = source_path.read_text()
    observer = entry['observer_function']
    if observer is not None:
        if observer not in ('observed', 'schedule_observed'):
            raise ValueError('Unknown observer')
        source = getattr(early_observers, observer)(source)
    loaded_pin = hashlib.sha256(source.encode()).hexdigest()
    if loaded_pin != entry['private_tested_loaded_core_sha256']:
        raise ValueError('Observer output does not match tested core')
    derived = report / 'early-snapshots' / tag
    if derived.resolve().is_relative_to(snapshot.resolve()):
        raise ValueError('Derived snapshot must be outside shared snapshot')
    shutil.copytree(snapshot, derived, symlinks=True)
    require_pins(snapshot, frozen)
    require_pins(derived, frozen)
    (derived / 'hol/core.ml').write_text(source)
    prepared = copy.deepcopy(frozen)
    prepared['files']['hol/core.ml'] = loaded_pin
    require_pins(derived, prepared)
    require_pins(snapshot, frozen)
    provenance = {'tag': tag, 'variant': variant,
        'category': 'historical_core_control' if historical else 'candidate_test',
        'observer_function': observer, 'expected_assertions': entry['assertions'],
        'production_core_sha256': data['production_core_sha256'],
        'unmodified_test_core_sha256': entry['unmodified_core_sha256'],
        'loaded_test_core_sha256': loaded_pin,
        'production_snapshot': str(snapshot), 'derived_snapshot': str(derived),
        'shared_pins': frozen, 'derived_pins': prepared,
        'boundary': 'Pinned source snapshots; external toolchain/OS are not hermetic. Historical-core controls are not production-core passes.'}
    path = report / (tag + '.provenance.json')
    with path.open('x') as stream:
        json.dump(provenance, stream, indent=2)
        stream.write('\n')
    return {'base': snapshot, 'derived': derived, 'shared_pins': frozen,
            'derived_pins': prepared, 'entry': entry, 'provenance': provenance,
            'provenance_path': path, 'provenance_sha256': digest(path)}


def check_ready(context):
    require_pins(context['base'], context['shared_pins'])
    require_pins(context['derived'], context['derived_pins'])
    if context['provenance_path'].is_symlink() or digest(context['provenance_path']) != context['provenance_sha256']:
        raise ValueError('Early provenance changed')


def postflight(context):
    result = {'shared_unchanged': False, 'derived_unchanged': False,
              'provenance_unchanged': False, 'errors': []}
    for field, path, expected in (
            ('shared_unchanged', context['base'], context['shared_pins']),
            ('derived_unchanged', context['derived'], context['derived_pins'])):
        try:
            actual = tree_pins(path)
            result[field.replace('_unchanged', '_after_pins')] = actual
            result[field] = actual == expected
        except (OSError, ValueError) as error:
            result['errors'].append(str(error))
    try:
        result['provenance_unchanged'] = (not context['provenance_path'].is_symlink() and
            digest(context['provenance_path']) == context['provenance_sha256'])
    except OSError as error:
        result['errors'].append(str(error))
    result['passed'] = all(result[k] for k in ('shared_unchanged', 'derived_unchanged', 'provenance_unchanged')) and not result['errors']
    return result
