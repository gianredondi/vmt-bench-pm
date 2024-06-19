from pysmt.shortcuts import *
from pysmt.smtlib.parser import SmtLibParser
from collections import namedtuple

TransitionSystem = namedtuple('TransitionSystem',
                              ['statevars', 'init',
                               'trans', 'trans_guard', 'prop', 'index_type'])

def get_ts(opts, file_name):
    parser = SmtLibParser()
    file = open(file_name, 'r')
    script = parser.get_script(file)
    ann = script.annotations

    c_vars = ann.all_annotated_formulae('next')
    vars = set()
    indextp = set()

    for c in c_vars:
        assert len(ann.annotations(c)['next']) == 1
        name = ann.annotations(c)['next'].pop()
        if not c.is_function_application():
            tp = c.get_type()
        else:
            c = c.function_name()
            tp = c.get_type()

        n = Symbol(name, tp)
        vars.add((c, n))

    assert len(ann.all_annotated_formulae('init')) == 1
    init = ann.all_annotated_formulae('init').pop()

    assert len(ann.all_annotated_formulae('action').union(ann.all_annotated_formulae('rule'))) > 0
    trans = ann.all_annotated_formulae('action').union(ann.all_annotated_formulae('rule'))

    assert len(ann.all_annotated_formulae('invar-property')) >= 1
    prop = ann.all_annotated_formulae('invar-property', value = str(opts.vmt_property)).pop()
    return TransitionSystem(vars, init, trans, TRUE(), prop, indextp)

def main(opts):    
    ts = get_ts(opts, opts.vmt_file)
    return ts

if __name__ == '__main__':  
    from argparse import ArgumentParser
    parser = ArgumentParser()
    parser.add_argument('vmt_file', help='VMT file')
    parser.add_argument('vmt_property', type=int, help='VMT property')
    opts = parser.parse_args()
    ts = main(opts)
    for (a, b) in ts.statevars:
        print(a, b)
    print(ts.init.serialize())
    for t in ts.trans:
        print(t.serialize())
    print(ts.prop.serialize())