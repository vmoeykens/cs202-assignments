from dataclasses import dataclass
from collections import OrderedDict
from typing import List, Set, Dict, Tuple
import traceback
from rvar_parser import *
import inspect
import sys

from cs202_support.base_ast import AST, print_ast

import cs202_support.x86exp as x86
import cvar

gensym_num = 0
def gensym(x):
    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'

##################################################
# Pass #1: uniquify
##################################################

def uniquify(e: RVarExp) -> RVarExp:
    def uniquify_exp(e: RVarExp, env: Dict[str, str]) -> RVarExp:
        if isinstance(e, Int):
            return e
        elif isinstance(e, Var):
            return Var(env[e.var])
        elif isinstance(e, Let):
            let_var = e.x
            let_rhs = uniquify_exp(e.e1, env)
            unique_let_var = gensym(let_var)
            env = {**env, let_var : unique_let_var}
            let_body = uniquify_exp(e.body, env)
            return Let(unique_let_var, let_rhs, let_body)
        elif isinstance(e, Prim):
            new_args = [uniquify_exp(a, env) for a in e.args]
            return Prim(e.op, new_args)
        else:
            raise Exception('unknown expression', e)
    return uniquify_exp(e, {})

##################################################
# Pass #2: remove-complex-opera*
##################################################

def mk_let(bindings: Dict[str, RVarExp], body: RVarExp):
    result = body
    for var, rhs in reversed(list(bindings.items())):
        result = Let(var, rhs, result)

    return result

def rco(e: RVarExp) -> RVarExp:
    def rco_exp(e: RVarExp) -> RVarExp:
        if isinstance(e, Int):
            return e
        elif isinstance(e, Var):
            return e
        elif isinstance(e, Let):
            e1_p = rco_exp(e.e1)
            body_p = rco_exp(e.body)
            return Let(e.x, e1_p, body_p)
        elif isinstance(e, Prim):
            bindings = {}
            new_args = [rco_atm(a, bindings) for a in e.args]
            p = Prim(e.op, new_args)
            return mk_let(bindings, p)
        else:
            raise Exception('unknown expression', e)

    def rco_atm(e: RVarExp, bindings: Dict[str, RVarExp]) -> RVarExp:
        if isinstance(e, Int):
            return e
        elif isinstance(e, Var):
            return e
        elif isinstance(e, Let):
            bindings[e.x] = rco_exp(e.e1)
            new_var = rco_atm(e.body, bindings)
            return new_var
        elif isinstance(e, Prim):
            new_args = [rco_atm(a, bindings) for a in e.args]
            tmp = gensym('tmp')
            bindings[tmp] = Prim(e.op, new_args)
            return Var(tmp)
        else:
            raise Exception('unknown expression', e)

    return rco_exp(e)

##################################################
# Pass #3: explicate-control
##################################################

def gen_cvar_atm(e: RVarExp) -> cvar.Atm:
    if isinstance(e, Int):
        return cvar.Int(e.val)
    if isinstance(e, Var):
        return cvar.Var(e.var)

def explicate_control(e: RVarExp) -> cvar.Program:
    def ec_tail(e: RVarExp) -> cvar.Tail:
        # in the let case
        if isinstance(e, Int):
            return cvar.Return(cvar.AtmExp(cvar.Int(e.val)))
        elif isinstance(e, Let):
            return ec_assign(e.x, e.e1, ec_tail(e.body))
        elif isinstance(e, Prim):
            tail_args = [gen_cvar_atm(a) for a in e.args]
            return cvar.Return(cvar.Prim(e.op, tail_args))

    def ec_assign(x: str, e: RVarExp, k: cvar.Tail) -> cvar.Tail:
        if isinstance(e, Int):
            assignment = cvar.Assign(x, cvar.AtmExp(cvar.Int(e.val)))
            return cvar.Seq(assignment, k)
        elif isinstance(e, Var):
            assignment = cvar.Assign(x, cvar.AtmExp(cvar.Var(e.var)))
            return cvar.Seq(assignment, k)
        elif isinstance(e, Let):
            assignment = cvar.Assign(e.x, cvar.AtmExp(gen_cvar_atm(e.e1)))
            sequence = cvar.Seq(cvar.Assign(x, cvar.AtmExp(cvar.Var(e.x))),
                                cvar.Return(cvar.AtmExp(cvar.Var(x))))
            return cvar.Seq(assignment, sequence)
        elif isinstance(e, Prim):
            tail_args = [gen_cvar_atm(a) for a in e.args]
            assignment = cvar.Assign(x, cvar.Prim(e.op, tail_args))
            return cvar.Seq(assignment, k)

    return cvar.Program({'start': ec_tail(e)})

##################################################
# Pass #4: select-instructions
##################################################

def select_instructions(p: cvar.Program) -> x86.Program:
    def si_arg(a: cvar.Atm) -> x86.Arg:
        pass

    def si_tail(t: cvar.Tail) -> List[x86.Instr]:
        if isinstance(t, cvar.Return) and isinstance(t.exp, cvar.AtmExp):
            return [x86.Movq(si_arg(t.exp.atm), x86.Reg('rax')), x86.Jmp('conclusion')]


    blocks = p.blocks

    new_blocks = {label: si_tail(block) for label, block in blocks}
    program = x86.Program(new_blocks)

    return program

##################################################
# Pass #6: assign-homes
##################################################
# output of this pass is:
# a tuple where the parts are
# 1. the x86 program
# 2. the number of bytes needed to store variables on the stack
# If I need to store n variables on the stack then this number should be align(8*n)
def assign_homes(program: x86.Program) -> Tuple[x86.Program, int]:
    # YOUR CODE HERE
    pass


##################################################
# Pass #7: patch-instructions
##################################################

def patch_instructions(inputs: Tuple[x86.Program, int]) -> Tuple[x86.Program, int]:
    # YOUR CODE HERE
    pass


##################################################
# Pass #8: print-x86
##################################################

def print_x86(inputs: Tuple[x86.Program, int]) -> str:
    # YOUR CODE HERE
    pass

##################################################
# Compiler definition
##################################################

compiler_passes = {
    'uniquify': uniquify,
    'remove complex opera*': rco,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'assign homes': assign_homes,
    'patch instructions': patch_instructions,
    'print x86': print_x86
}



def run_compiler(s, logging=False):
    current_program = parse_rvar(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print(print_ast(current_program))


    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print(print_ast(current_program))

    return current_program

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())
