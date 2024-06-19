from pysmt.shortcuts import Symbol, Not, And, Or, EqualsOrIff, Function
from pysmt.shortcuts import is_sat, is_unsat 
from pysmt.typing import BOOL
from pysmt.walkers import IdentityDagWalker
from vmt2ts import TransitionSystem, get_ts

def at_time(v, t):
    """Builds an variable representing v at time t"""
    return Symbol("%s@%d" % (v.symbol_name(), t), v.symbol_type())

def next_var(v, ts):
    for (a, b) in ts.statevars:
        if a == v:
            return b
        
class SubtituteUF(IdentityDagWalker):
    """ This class is used to substitute constants of function type"""
    def __init__(self):
        IdentityDagWalker.__init__(self)
        self.manager = self.env.formula_manager

    def _get_key(self, formula, **kwargs):
        return formula

    def substitute_all(self, formula, subs):
        f_subs = {}
        for i in subs:
            if i.symbol_type().is_function_type():
                f_subs[i] = subs[i]               
            else:
                formula = formula.substitute({i : subs[i]})
        return self.walk(formula, substitutions=f_subs)
        

    def walk_function(self, formula, args, substitutions):
        if formula.is_function_application():
            f = formula.function_name()
            if f in substitutions:
                new_f = Function(substitutions[f], args)
                return new_f
        
        return formula

subst = SubtituteUF()

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
        trans = And(trans, And([a for a in self.ts.axioms]))
        for i in range(k+1):
            subs_i = self.get_subs(i)
            res.append(subst.substitute_all(trans, subs_i))

        return And(res)

    def get_simple_path(self, k):
        """Simple path constraint for k-induction:
        each time encodes a different state
        """

        ## TODO: if variables are functions, replace v != w with forall x. v(x) != w(x)
        res = []
        state = []
        for i in range(k+1):
            subs_i = self.get_subs(i)
            
            for c, n in self.ts.statevars:
                state.append(subst.substitute_all(Not(EqualsOrIff(c, n)), subs_i))
                
            
            res.append(Or(state))
        return And(res)

    def get_k_hypothesis(self, k):
        """Hypothesis for k-induction: each state up to k-1 fulfills the property"""
        res = []
        for i in range(k):
            subs_i = self.get_subs(i)
            res.append(subst.substitute_all(self.ts.prop, subs_i))
        return And(res)

    def get_bmc(self, k):
        """Returns the BMC encoding at step k"""
        init_0 = subst.substitute_all(self.ts.init, self.get_subs(0))
        prop_k = subst.substitute_all(self.ts.prop, self.get_subs(k))
        return And(self.get_unrolling(k), init_0, Not(prop_k))

    def get_k_induction(self, k):
        """Returns the K-Induction encoding at step K"""
        subs_k = self.get_subs(k)
        prop_k = subst.substitute_all(self.ts.prop, subs_k)
        return And(self.get_unrolling(k),
                   self.get_k_hypothesis(k),
                   #self.get_simple_path(k),
                   Not(prop_k))

    def check_property(self, k):
        """Interleaves BMC and K-Ind to verify the property."""
        print("Checking property %s..." % self.ts.prop)
        for b in range(k):
            f = self.get_bmc(b)
            print(f.serialize())
            print("   [BMC]    Checking bound %d..." % (b+1))
            if is_sat(f, solver_name=self.solver):
                print("--> Bug found at step %d" % (b+1))
                return

            f = self.get_k_induction(b)
            print(f.serialize())
            print("   [K-IND]  Checking bound %d..." % (b+1))
            if is_unsat(f, solver_name=self.solver):
                print("--> The ts is safe!")
                return

def main(opts):
    ts = get_ts(opts, opts.vmt_file)
    bmc = BMCInduction(ts, opts.solver_name)
    bmc.check_property(opts.k)

if __name__ == '__main__':  
    from argparse import ArgumentParser
    parser = ArgumentParser()
    parser.add_argument('vmt_file', help='VMT file')
    parser.add_argument('vmt_property', type=int, help='VMT property')
    parser.add_argument('--solver-name', choices=['z3', 'cvc4'], default='z3', help='Solver name (default: z3)')
    parser.add_argument('--k', type=int, default=100, help='BMC bound (default: 100)')
    opts = parser.parse_args()
    main(opts)
