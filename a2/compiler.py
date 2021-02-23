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
        if isinstance(e, Int):
            return cvar.Return(cvar.AtmExp(cvar.Int(e.val)))
        elif isinstance(e, Var):
            return cvar.Return(cvar.AtmExp(cvar.Var(e.var)))
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
    def si_atm(a: cvar.Atm) -> x86.Arg:
        if isinstance(a, cvar.Int):
            return x86.Int(a.val)
        elif isinstance(a, cvar.Var):
            return x86.Var(a.var)

    def si_stmt(s: cvar.Stmt) -> List[x86.Instr]:
        if isinstance(s, cvar.Assign):
            if isinstance(s.exp, cvar.Prim):
                return [x86.Movq(si_atm(s.exp.args[0]), x86.Var(s.var)),
                        x86.Addq(si_atm(s.exp.args[1]),
                                 x86.Var(s.var))]
            elif isinstance(s.exp, cvar.AtmExp):
                return [x86.Movq(si_atm(s.exp.atm), x86.Var(s.var))]

    def si_tail(t: cvar.Tail) -> List[x86.Instr]:
        if isinstance(t, cvar.Return) and isinstance(t.exp, cvar.AtmExp):
            return [x86.Movq(si_atm(t.exp.atm), x86.Reg('rax')), x86.Jmp('conclusion')]
        elif isinstance(t, cvar.Return) and isinstance(t.exp, cvar.Prim):
            ret_var = x86.Var(gensym('retvar'))
            return [x86.Movq(si_atm(t.exp.args[0]), ret_var),
                    x86.Addq(si_atm(t.exp.args[1]), ret_var),
                    x86.Movq(ret_var, x86.Reg('rax')), x86.Jmp('conclusion')]
        elif isinstance(t, cvar.Seq):
            return [*si_stmt(t.stmt), *si_tail(t.tail)]

    blocks = p.blocks
    new_blocks = {label: si_tail(blocks[label]) for label in blocks}
    new_program = x86.Program(new_blocks)

    return new_program

##################################################
# Pass #6: assign-homes
##################################################

def align(num_bytes: int) -> int:
    if num_bytes % 16 == 0:
        return num_bytes
    else:
        return num_bytes + (16 - (num_bytes % 16))

def new_stack_location(homes, var):
    len_stack = len(homes) + 1
    new_stack_offset = len_stack * 8
    new_stack_val = x86.Deref(- new_stack_offset, 'rbp')  # produce: -n(%rbp)
    homes[var] = new_stack_val
    return new_stack_val

def assign_homes(program: x86.Program) -> Tuple[x86.Program, int]:
    homes : Dict[str, int] = {}

    def make_stack_location(instructions: List[x86.Instr]) -> List[x86.Instr]:
        new_instructions = []
        for i in instructions:
            if isinstance(i, x86.Addq) or isinstance(i, x86.Movq):
                e1 = i.e1
                e2 = i.e2
                if isinstance(e1, x86.Var):
                    if e1.var in homes:
                        e1 = homes[e1.var]
                    else:
                        e1 = new_stack_location(homes, e1.var)
                if isinstance(e2, x86.Var):
                    if e2.var in homes:
                        e2 = homes[e2.var]
                    else:
                        e2 = new_stack_location(homes, e2.var)
                if isinstance(i, x86.Addq):
                    new_instructions.append(x86.Addq(e1, e2))
                elif isinstance(i, x86.Movq):
                    new_instructions.append(x86.Movq(e1, e2))
            else:
                new_instructions.append(i)
        return new_instructions

    blocks = program.blocks
    new_blocks = {label: make_stack_location(blocks[label]) for label in blocks}
    new_program = x86.Program(new_blocks)
    num_bytes_needed = (len(homes) + 1) * 8
    return (new_program, num_bytes_needed)

##################################################
# Pass #7: patch-instructions
##################################################

def patch_instructions(inputs: Tuple[x86.Program, int]) -> Tuple[x86.Program, int]:
    def fix_double_derefs(instructions: List[x86.Instr]) -> List[x86.Instr]:
        new_instructions = []
        for i in instructions:
            if isinstance(i, x86.Addq) and (isinstance(i.e1, x86.Deref) and isinstance(i.e2, x86.Deref)):
                new_instructions.append(x86.Movq(i.e1, x86.Reg('rax')))
                new_instructions.append(x86.Addq(x86.Reg('rax'), i.e2))
            elif isinstance(i, x86.Movq) and (isinstance(i.e1, x86.Deref) and isinstance(i.e2, x86.Deref)):
                new_instructions.append(x86.Movq(i.e1, x86.Reg('rax')))
                new_instructions.append(x86.Movq(x86.Reg('rax'), i.e2))
            else:
                new_instructions.append(i)
        return new_instructions
    blocks = inputs[0].blocks
    new_blocks = {label: fix_double_derefs(blocks[label]) for label in blocks}
    new_program = x86.Program(new_blocks)
    return (new_program, inputs[1])


##################################################
# Pass #8: print-x86
##################################################

# Boilerplate main section
def make_main(stack_req):
    return x86.Program({
        'main': [
            x86.Pushq(x86.Reg('rbp')),
            x86.Movq(x86.Reg('rsp'), x86.Reg('rbp')),
            x86.Subq(x86.Int(stack_req), x86.Reg('rsp')),
            x86.Jmp('start'),
        ]})

# Boilerplate conclusion section
def make_conclusion(stack_req):
    return x86.Program({
        'conclusion': [
            x86.Movq(x86.Reg('rax'), x86.Reg('rdi')),
            x86.Callq('print_int'),
            x86.Movq(x86.Int(0), x86.Reg('rax')),
            x86.Addq(x86.Int(stack_req), x86.Reg('rsp')),
            x86.Popq(x86.Reg('rbp')),
            x86.Retq(),
        ]
})

def arg_to_x86_string(arg: x86.Arg) -> str:
    """Convert x86exp Arg to x86 string
        Args:
            arg (x86.Arg): x86exp Arg
        Returns:
            String of x86 assembly
    """
    if isinstance(arg, x86.Int):
        return f'${arg.val}'
    elif isinstance(arg, x86.Reg):
        return f'%{arg.val}'
    elif isinstance(arg, x86.Deref):
        return f'{arg.offset}(%{arg.val})'


def instruction_to_x86_string(inst: x86.Instr) -> str:
    """Convert x86ex Instr to x86 string
        Args:
            inst (x86.Instr): x86exp Instr
        Returns:
              String of x86 assembly
    """
    if isinstance(inst, x86.Addq):
        return f'addq {arg_to_x86_string(inst.e1)}, ' \
               f'{arg_to_x86_string(inst.e2)}'
    elif isinstance(inst, x86.Subq):
        return f'subq {arg_to_x86_string(inst.e1)}, ' \
               f'{arg_to_x86_string(inst.e2)}'
    elif isinstance(inst, x86.Movq):
        return f'movq {arg_to_x86_string(inst.e1)}, ' \
               f'{arg_to_x86_string(inst.e2)}'
    elif isinstance(inst, x86.Jmp):
        return f'jmp {inst.label}'
    elif isinstance(inst, x86.Callq):
        return f'callq {inst.label}'
    elif isinstance(inst, x86.Pushq):
        return f'pushq {arg_to_x86_string(inst.e1)}'
    elif isinstance(inst, x86.Popq):
        return f'popq {arg_to_x86_string(inst.e1)}'
    elif isinstance(inst, x86.Retq):
        return f'retq'


def ast_to_x86_string(program: x86.Program) -> str:
    """Iterates through x86exp Program and generates
        x86 assembly string
        Args:
            program (x86.Program): Program to iterate through
        Returns:
            String of x86 assembly block
    """
    output_string = ''
    label = list(program.blocks.keys())[0]
    output_string += f'{label}:\n'
    for instruction in program.blocks[label]:
        output_string += f'   {instruction_to_x86_string(instruction)}\n'
    return output_string

def print_x86(inputs: Tuple[x86.Program, int]) -> str:
    """Generates x86 assembly for this specific assignment"""
    output_string = '   .globl main\n'
    output_string += ast_to_x86_string(make_main(inputs[1]))
    output_string += ast_to_x86_string(inputs[0])
    output_string += ast_to_x86_string(make_conclusion(inputs[1]))

    return output_string

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
