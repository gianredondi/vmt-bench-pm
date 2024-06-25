from collections import namedtuple

ParametricTransitionSystem = namedtuple(
    'ParametricTransitionSystem',
    ['sorts', 'statevars', 'axioms', 'init', 'trans_rules', 'frozenvars',
     'prop', 'initial_conc_size'])

class Printer:
    def __init__(self, ts):
        self.ts = ts
        
    def print_sorts(self):
        for sort in self.ts.sorts:
            print("(declare-sort " + sort + " 0)")

    def print_variables(self):
        for var, var_next in self.ts.statevars:
            
            if var.get_type().is_function_type():
                ar = var.get_type().param_types
                new_name = var.symbol_name()
                print("(declare-fun " + new_name + " (" + " ".join([str(ar[sort]) for sort in range(len(ar))]) + ") Bool)")    
                next_name = var_next.symbol_name()
                print("(declare-fun " + next_name + " (" + " ".join([str(ar[sort]) for sort in range(len(ar))]) + ") Bool)")
                if var in self.ts.frozenvars:
                    pass
                else:
                    print("(define-fun " + new_name + ".sv" + " (" + " ".join(["(V" + str(i) + " " + str(ar[i]) + ")" for i in range(len(ar))]) 
                        + ") Bool (! (" + new_name + " " + " ".join(["V" + str(i) for i in range(len(ar))]) + ") :next " + next_name + "))")
            else:
                new_name = "_0__" + var.symbol_name()
                print("(declare-const " + new_name + " " + var.sort.symbol_name() + ")")
                next_name = "_1__" + var.symbol_name()
                print("(declare-const " + next_name + " " + var.sort.symbol_name() + ")")            
                print("(define-fun " + new_name + ".sv" + " () " + var.sort.symbol_name() + " (! " + new_name + " :next " + next_name + "))")

    def print_axioms(self):
        axioms = self.ts.axioms
        for i, axiom in enumerate(axioms):
            annotated_axiom_smtlib = f"(! {axiom.simplify().serialize()} :axiom true)"
            print(f"(define-fun axiom_{i} () Bool {annotated_axiom_smtlib})")

    def print_inits(self):
        init = self.ts.init
        print(f"(define-fun init () Bool (! {init.simplify().serialize()} :init true))")

    def print_transitions(self):
        transitions = self.ts.trans_rules
        for i, transition in enumerate(transitions):
            annotated_transition_formula = f"(! {transition.simplify().serialize()} :action true)"
            print(f"(define-fun transition_{i} () Bool {annotated_transition_formula})")

    def print_safety(self):
        safety = self.ts.prop
        print(f"(define-fun safety-prop () Bool (! {safety.simplify().serialize()} :invar-property 0))")

    def print_ts(self):
        self.print_sorts()
        self.print_variables()
        self.print_axioms()
        self.print_inits()
        self.print_transitions()
        self.print_safety()
    