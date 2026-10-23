"""Source/protocol controls only; these do not establish HOL proof correctness."""
import re
from pathlib import Path
import unittest
import run
import helper_contract


class Offline(unittest.TestCase):
    def test_limits_and_separate_registry(self):
        focused = ('general', 'single', 'mutual', 'references', 'authentication',
                   'shape', 'atomicity', 'wrappers')
        self.assertEqual(run.FOCUSED, focused)
        self.assertEqual(run.LIMIT, 180)
        jobs = run.jobs()
        self.assertEqual(list(jobs), list(focused) + ['arena'])
        for phase, job in jobs.items():
            self.assertEqual(job['limit'], 180, phase)
            self.assertEqual(job['source_file'],
                             'safety_arena_tests.ml' if phase == 'arena' else 'safety_tests.ml')
            self.assertEqual(job['options'], {} if phase == 'arena' else {'SAFETY_GROUP': phase})

    def test_exact_protocol(self):
        for phase, job in run.jobs().items():
            marker = ('SAFETY_DEFINITIONS_PASSED ' + phase + ' 7 closed_exact unchanged_axioms rules29_11\n')
            if phase == 'arena':
                marker = ('SAFETY_ARENA_REJECT 140_falseFromUnsafe prefix_checked=2 line=22 exact_closed forbidden_closed retained_loop\n'
                          'SAFETY_ARENA_REJECT 141_falseFromPartial prefix_checked=2 line=22 exact_closed forbidden_closed retained_loop\n'
                          'SAFETY_ARENA_PASSED 17 unchanged_axioms\n')
            marker = '\n'.join(run.LOAD_MARKERS) + '\n' + marker
            self.assertTrue(run.composition.inspect_log(marker, job['markers'])[2])
            for bad in ('', marker + marker, marker + 'Exception: Failure "bad"\n', marker + 'Error: bad\n'):
                self.assertFalse(run.composition.inspect_log(bad, job['markers'])[2])

    def test_assertion_accounting(self):
        text = '# SAFETY_ASSERT general 1 true exact\nSAFETY_ASSERT general 2 false wrong\n'
        self.assertEqual(run.assertions(text, 'general'),
                         [{'index': 1, 'passed': True, 'label': 'exact'},
                          {'index': 2, 'passed': False, 'label': 'wrong'}])
        self.assertEqual(run.assertions('Printf.printf "SAFETY_ASSERT general 1 true quoted"', 'general'), [])

    def test_no_trust_expansion(self):
        for path in run.PRODUCTION:
            if path == 'hol/environment.ml':
                continue
            source = (run.ROOT / path).read_text()
            for forbidden in ('new_axiom', 'new_inductive_definition', 'Obj.magic', 'admit_unsafe', 'axiom_permission ='):
                self.assertNotIn(forbidden, source, path)

    def test_fragment_helper_contract(self):
        helper_contract.require_helper((run.ROOT / 'hol/environment.ml').read_text())

    def test_header_before_placeholder_and_atomic_commit(self):
        text = (run.ROOT / 'hol/safety_admission.ml').read_text()
        body = text[text.index('  let admit_restricted ?'):text.index('  let append_safe ?')]
        self.assertLess(body.index('let headers='), body.index('let frag='))
        self.assertLess(body.index('let bodies='), body.index('let registry='))
        self.assertIn('full s.env registry history trace s.safe_blocks s.safe_trace', body)
        self.assertNotIn('mutable', text)
        self.assertNotIn('with_axioms', text)

    def test_hypothesis_and_view_guards(self):
        text = (run.ROOT / 'hol/safety_admission.ml').read_text()
        self.assertIn('hyp th<>[] || not(aconv(concl th)tm)', text)
        self.assertIn('authenticated s;', text)
        self.assertIn('temporary fragment identity', text)
        self.assertIn('exact(body_term frag r)h', text)
        self.assertIn('canonical_fresh=get(check_fresh s canonical)', text)

    def test_reference_checks_keep_dead_syntax(self):
        text = (run.ROOT / 'hol/safety_syntax.ml').read_text()
        self.assertIn('l4_safety_refs (L4Let n a v b)', text)
        self.assertIn('APPEND (l4_safety_refs v)', text)
        self.assertIn('l4_safety_refs (L4Lam n a b)', text)
        self.assertIn('l4_safety_kind_refs (l4_entry_tag d)', text)

    def test_complete_history_not_filtered_projection(self):
        text = (run.ROOT / 'hol/safety_syntax.ml').read_text()
        self.assertIn('l4_safety_trace policy registry env history', text)
        self.assertIn('l4_name_inventory (MAP l4_mark_name (l4_safety_raw_history history))', text)
        self.assertIn('l4_input_valid policy env (l4_safety_safe_history history)', text)
        self.assertIn('l4_safety_full_old_safe', text)
        self.assertIn('ds = [] /\\ l4_safety_restricted op registry raw', text)

    def test_metadata_and_operation_retained(self):
        text = (run.ROOT / 'frontend/hol_safety_input.ml').read_text()
        self.assertIn('Partial_single', text)
        self.assertIn('Restricted_mutual,List.map(definition memo)ds', text)
        self.assertIn('hint=hint d.Wire.hints;all=List.map Hol_input.name d.Wire.all', text)
        self.assertIn('Hol_input.expr memo d.Wire.value', text)
        self.assertNotIn('expected', text)

    def test_focused_gate_precedes_arena(self):
        text = Path(run.__file__).read_text()
        self.assertIn("for phase in list(FOCUSED) + ['arena']", text)
        self.assertIn("if phase == 'arena' and", text)
        self.assertIn("if not audit['passed']:", text)
        self.assertIn("save(report / 'first-native-failure.json'", text)

    def test_native_controls_cover_required_boundaries(self):
        text = (run.ROOT / 'tests/hol_safety/drivers/safety_tests.ml').read_text()
        for label in ('two member mutually recursive block', 'unused let value not erased',
                      'lambda domain safety', 'mutual header cannot use sibling placeholder',
                      'generated commit independently checks full registry', 'last body failure',
                      'open body theorem rejected', 'standalone partial uses safe prior mode',
                      'conversion unfolds actual unsafe definition', 'unchanged HOL axiom inventory'):
            self.assertIn(label, text)

    def test_separate_interactive_load_phases(self):
        source = (run.ROOT / run.LOAD_PHASE_FILE).read_text()
        events = re.findall(r'(?m)^(set_jrh_lexer|unset_jrh_lexer);;|^needs "([^"]+)";;', source)
        mode = None
        roots = []
        for switch, path in events:
            if switch:
                mode = 'jrh' if switch == 'set_jrh_lexer' else 'ordinary'
            else:
                expected = 'ordinary' if path == 'frontend/hol_check.ml' else 'jrh'
                self.assertEqual(mode, expected, path)
                roots.append(path)
        self.assertEqual(roots, [p for p in run.LOAD_ROOTS if p.endswith('.ml')])
        prefix = source[:source.index('print_endline "SAFETY_LOAD_PHASE transport')]
        self.assertEqual(re.findall(r'(?m)^((?:un)?set_jrh_lexer);;$', prefix),
                         ['set_jrh_lexer', 'unset_jrh_lexer'])
        self.assertIn('Topdirs.dir_load Format.std_formatter "hol_safety_input.cmo";;', prefix)
        adapter = (run.ROOT/'frontend/hol_safety_check.ml').read_text()
        self.assertNotIn('set_jrh_lexer', adapter)
        self.assertIn('needs "hol/safety_admission.ml";;', adapter)
        self.assertIn('needs "frontend/hol_check.ml";;', adapter)
        runner = Path(run.__file__).read_text()
        self.assertIn("(snapshot / 'safety_load_phases.ml').read_text()", runner)
        self.assertNotIn('needs "safety_load_phases.ml"', runner)

    def test_loading_markers_required_not_quoted(self):
        job = run.jobs()['general']
        done = 'SAFETY_DEFINITIONS_PASSED general 20 closed_exact unchanged_axioms rules29_11\n'
        for omitted in run.LOAD_MARKERS:
            log = '\n'.join(m for m in run.LOAD_MARKERS if m != omitted) + '\n' + done
            self.assertFalse(run.composition.inspect_log(log, job['markers'])[2])
        quoted = '\n'.join('print_endline "' + m + '";;' for m in run.LOAD_MARKERS)
        self.assertFalse(run.composition.inspect_log(quoted + '\n' + done, job['markers'])[2])


if __name__ == '__main__':
    unittest.main()
