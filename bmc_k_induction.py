from pysmt.shortcuts import Symbol, Not, And, Or, EqualsOrIff, Implies
from pysmt.shortcuts import is_sat, is_unsat 
from pysmt.typing import BOOL
from vmt2ts import TransitionSystem, get_ts

def at_time(v, t):
    """Builds an SMT variable representing v at time t"""
    return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())

def next_var(v, ts):
    for (a, b) in ts.statevars:
        if a == v:
            return b

class BMCInduction(object):

    def __init__(self, ts : TransitionSystem, solver_name="z3"):
        self.ts = ts
        self.solver = solver_name

    def get_subs(self, i):
        """Builds a map from x to x@i and from x' to x@(i+1), for all x in ts."""
        subs_i = {}
        for v, _ in self.ts.statevars:
            subs_i[v] = at_time(v, i)
            subs_i[next_var(v, self.ts)] = at_time(v, i+1)
        return subs_i

    def get_unrolling(self, k):
        """Unrolling of the transition relation from 0 to k:

        E.g. T(0,1) & T(1,2) & ... & T(k-1,k)
        """
        res = []

        trans = Or([t for t in self.ts.trans])
        for i in range(k+1):
            subs_i = self.get_subs(i)
            res.append(trans.substitute(subs_i))

        return And(res)

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """

        ## TODO: if variables are functions, replace v != w with forall x. v(x) != w(x)
        res = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            for j in range(i+1, k+1):
                state = []
                subs_j = self.get_subs(j)
                for v, _ in self.ts.statevars:
                    v_i = v.substitute(subs_i)
                    v_j = v.substitute(subs_j)
                    state.append(Not(EqualsOrIff(v_i, v_j)))
                res.append(Or(state))
        return And(res)

    def get_k_hypothesis(self, k):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
        res = []
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(self.ts.prop.substitute(subs_i))
        return And(res)

    def get_bmc(self, k):
        """Returns the BMC encoding at step k"""
        init_0 = self.ts.init.substitute(self.get_subs(0))
        prop_k = self.ts.prop.substitute(self.get_subs(k))
        return And(self.get_unrolling(k), init_0, Not(prop_k))

    def get_k_induction(self, k):
        """Returns the K-Induction encoding at step K"""
        subs_k = self.get_subs(k)
        prop_k = self.ts.prop.substitute(subs_k)
        return And(self.get_unrolling(k),
                   self.get_k_hypothesis(self.ts.prop, k),
                   self.get_simple_path(k),
                   Not(prop_k))

    def check_property(self):
        """Interleaves BMC and K-Ind to verify the property."""
        print("Checking property %s..." % self.ts.prop)
        for b in range(100):
            f = self.get_bmc(b)
            print("   [BMC]    Checking bound %d..." % (b+1))
            if is_sat(f, solver_name=self.solver):
                print("--> Bug found at step %d" % (b+1))
                return

            f = self.get_k_induction(self.ts.prop, b)
            print("   [K-IND]  Checking bound %d..." % (b+1))
            if is_unsat(f, solver_name=self.solver):
                print("--> The ts is safe!")
                return

def main(opts):
    ts = get_ts(opts, opts.vmt_file)
    bmc = BMCInduction(ts, opts.solver_name)
    bmc.check_property()

if __name__ == '__main__':  
    from argparse import ArgumentParser
    parser = ArgumentParser()
    parser.add_argument('vmt_file', help='VMT file')
    parser.add_argument('vmt_property', type=int, help='VMT property')
    parser.add_argument('--solver-name', choices=['z3', 'cvc5'], default='z3', help='Solver name (default: z3)')
    opts = parser.parse_args()
    main(opts)
