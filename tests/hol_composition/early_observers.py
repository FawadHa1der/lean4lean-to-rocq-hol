def observed(source):
    def change(old,new):
        nonlocal source
        if source.count(old)!=1: raise ValueError('observer anchor count: '+old)
        source=source.replace(old,new,1)
    change('  type budget = { mutable remaining : int }',
           '  let test_early_observer = ref (fun (_:string) (_:expr list) (_:expr) (_:expr) -> ())\n  type budget = { mutable remaining : int }')
    for function,tag,args in [('infer_i','infer','e e'),('whnf','whnf','e e')]:
        prefix='  let rec ' if function=='infer_i' else '  and '
        anchor=prefix+function+' st g e =\n'
        change(anchor,anchor+'    (!test_early_observer) "'+tag+'" g '+args+';\n')
    anchor="  and equal_i st g e e' =\n"
    change(anchor,anchor+"    (!test_early_observer) \"equal\" g e e';\n")
    success="      Some(p,guard g e e' p th)"
    if success in source:
        change(success,"      let result=p,guard g e e' p th in\n      (!test_early_observer) \"early-success\" g e e';\n      Some result")
    return source


def schedule_observed(source):
    original=source
    edits=[]
    def change(old,new):
        nonlocal source
        if source.count(old)!=1: raise ValueError('scheduler observer anchor: '+old)
        source=source.replace(old,new,1); edits.append((old,new))
    anchor='  type budget = { mutable remaining : int }'
    change(anchor,'  let test_schedule_expr = ref (fun (_:string) (_:expr) (_:expr) -> ())\n'
        '  let test_schedule_level = ref (fun (_:string) (_:level) (_:level) -> ())\n'
        '  let test_schedule_mark = ref (fun (_:string) -> ())\n'+anchor)
    for prefix,function,tag in [('let rec','infer_i','infer'),('and','whnf','whnf')]:
        anchor='  '+prefix+' '+function+' st g e =\n'
        change(anchor,anchor+'    (!test_schedule_expr) "'+tag+'.enter" e e;\n')
    anchor="  and equal_i st g e e' =\n"
    change(anchor,anchor+'    (!test_schedule_expr) "equal.enter" e e\';\n')
    anchor='  let level_proof st u v =\n'
    change(anchor,anchor+'    (!test_schedule_level) "level.request" u v;\n')
    start="  and early_irrelevance st g e e' =\n"
    if start in source:
        end="\n  and equal_i st g e e' ="
        a=source.index(start); b=source.index(end,a)
        body=source[a:b]; rewritten=body.replace(start,start+'    (!test_schedule_expr) "early.enter" e e\';\n',1)
        for old,new in [
            ('      let p,h = infer_i st g e in\n','      let p,h = infer_i st g e in\n      (!test_schedule_expr) "early.type" e p;\n'),
            ('      let u,hp = infer_sort st g p in\n','      let u,hp = infer_sort st g p in\n      (!test_schedule_level) "early.sort" u Zero;\n'),
            ("      Some(p,guard g e e' p th)","      let result=p,guard g e e' p th in\n      (!test_schedule_mark) \"early.success\"; Some result"),
            ('    with Failure _ | Stop {kind=Proof_failure;_} | Stop {kind=Unsupported;_} -> None',
             '    with Failure _ | Stop {kind=Proof_failure;_} | Stop {kind=Unsupported;_} ->\n      (!test_schedule_mark) "early.fallback"; None')]:
            if rewritten.count(old)!=1: raise ValueError('early observer anchor')
            rewritten=rewritten.replace(old,new,1)
        if '    if (match e with Sort _ | Pi _ -> true | _ -> false) then None else' in rewritten:
            rewritten=rewritten.replace('then None else','then ((!test_schedule_mark) "skip.expression"; None) else',1)
            rewritten=rewritten.replace('| Sort _ -> None','| Sort _ -> (!test_schedule_mark) "skip.inferred-sort"; None',1)
            rewritten=rewritten.replace('| Succ _ -> None','| Succ _ -> (!test_schedule_mark) "skip.successor"; None',1)
        change(body,rewritten)
    restored=source
    for old,new in reversed(edits):
        if restored.count(new)!=1: raise ValueError('observer reversal anchor')
        restored=restored.replace(new,old,1)
    if restored!=original: raise ValueError('observer reversal mismatch')
    return source
