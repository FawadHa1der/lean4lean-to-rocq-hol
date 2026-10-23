"""Exact reviewed cleanup helper; sole-reaper ownership contract."""
import os
import signal


def cleanup_owned_process(process, allow_group=True):
    """Sole reaper only: the owned unreaped session leader reserves its PID/PGID."""
    errors = []
    actions = []
    unreaped = False
    try:
        unreaped = process.poll() is None
    except Exception as error:
        errors.append('poll: ' + repr(error))
    group_signalled = False
    if unreaped and allow_group:
        # No wait/poll or concurrent reaper may intervene before this signal.
        try:
            os.killpg(process.pid, signal.SIGKILL)
            group_signalled = True
            actions.append('owned_unreaped_group_kill')
        except ProcessLookupError:
            actions.append('owned_group_already_absent')
        except Exception as error:
            errors.append('killpg: ' + repr(error))
    if process.returncode is None:
        if not group_signalled:
            try:
                process.kill()
                actions.append('direct_handle_kill')
            except ProcessLookupError:
                actions.append('direct_handle_already_absent')
            except Exception as error:
                errors.append('kill: ' + repr(error))
        try:
            process.wait(timeout=10)
        except Exception as error:
            errors.append('wait: ' + repr(error))
    if process.stdin is not None and not process.stdin.closed:
        try:
            process.stdin.close()
        except Exception as error:
            errors.append('stdin.close: ' + repr(error))
    presence = {}
    for name, probe in (('pid_absent', os.kill), ('process_group_absent', os.killpg)):
        try:
            probe(process.pid, 0)
            presence[name] = False
        except ProcessLookupError:
            presence[name] = True
        except Exception as error:
            presence[name] = None
            errors.append(name + ': ' + repr(error))
    reaped = process.returncode is not None
    return dict(presence, pid=process.pid, reaped=reaped, actions=actions, errors=errors,
                verified=reaped and all(v is True for v in presence.values()) and not errors)

