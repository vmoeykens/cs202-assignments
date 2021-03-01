from dataclasses import dataclass
from collections import OrderedDict, defaultdict
from typing import List, Set, Dict, Tuple, DefaultDict
import itertools
import traceback
from rvar_parser import *
import inspect
import sys

from cs202_support.base_ast import AST, print_ast

import cs202_support.x86exp as x86
import cvar
import constants

gensym_num = 0


def gensym(x):
    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


##################################################
# uniquify
##################################################

def uniquify(e: RVarExp) -> RVarExp:
    """
    Makes the program's variable names unique
    :param e: The RVar program to uniquify
    :return: An RVar program with unique names
    """
    def uniquify_exp(e: RVarExp, env: Dict[str, str]) -> RVarExp:
        if isinstance(e, Int):
            return e
        elif isinstance(e, Var):
            return Var(env[e.var])
        elif isinstance(e, Let):
            new_e1 = uniquify_exp(e.e1, env)
            new_x = gensym(e.x)
            new_env = {**env, e.x: new_x}
            new_body = uniquify_exp(e.body, new_env)
            return Let(new_x, new_e1, new_body)
        elif isinstance(e, Prim):
            new_args = [uniquify_exp(arg, env) for arg in e.args]
            return Prim(e.op, new_args)
        else:
            raise Exception('uniquify', e)

    return uniquify_exp(e, {})


##################################################
# remove-complex-opera*
##################################################

def mk_let(bindings: Dict[str, RVarExp], body: RVarExp):
    """
    Builds a Let expression from a list of bindings and a body.
    :param bindings: A list of bindings from variables (str) to their expressions (RVarExp)
    :param body: The body of the innermost Let expression
    :return: A Let expression implementing the bindings in "bindings"
    """
    result = body
    for var, rhs in reversed(list(bindings.items())):
        result = Let(var, rhs, result)

    return result


def rco(e: RVarExp) -> RVarExp:
    """
    Removes complex operands. After this pass, the program will be in A-Normal Form (the arguments to Prim
    operations will be atomic).
    :param e: An RVar expression
    :return: An RVar expression in A-Normal Form
    """
    def rco_atm(e: RVarExp, bindings: Dict[str, RVarExp]) -> RVarExp:
        if isinstance(e, Int):
            return e
        elif isinstance(e, Var):
            return e
        elif isinstance(e, Let):
            new_e1 = rco_exp(e.e1)
            bindings[e.x] = new_e1
            v = rco_atm(e.body, bindings)
            return v
        elif isinstance(e, Prim):
            new_args = [rco_atm(arg, bindings) for arg in e.args]

            new_v = gensym('tmp')
            bindings[new_v] = Prim(e.op, new_args)
            return Var(new_v)
        else:
            raise Exception('rco_atm', e)

    def rco_exp(e: RVarExp) -> RVarExp:
        if isinstance(e, Int):
            return e
        elif isinstance(e, Var):
            return e
        elif isinstance(e, Let):
            new_e1 = rco_exp(e.e1)
            new_body = rco_exp(e.body)
            return Let(e.x, new_e1, new_body)
        elif isinstance(e, Prim):
            bindings = {}
            new_args = [rco_atm(arg, bindings) for arg in e.args]

            return mk_let(bindings, Prim(e.op, new_args))
        else:
            raise Exception('rco_exp', e)

    return rco_exp(e)


##################################################
# explicate-control
##################################################

def explicate_control(e: RVarExp) -> cvar.Program:
    """
    Transforms an RVar Expression into a CVar program.
    :param e: An RVar Expression
    :return: A CVar Program
    """
    def ec_atm(e: RVarExp) -> cvar.Atm:
        if isinstance(e, Int):
            return cvar.Int(e.val)
        elif isinstance(e, Var):
            return cvar.Var(e.var)

    def ec_exp(e: RVarExp) -> cvar.Exp:
        if isinstance(e, Prim):
            return cvar.Prim(e.op, [ec_atm(a) for a in e.args])
        else:
            return cvar.AtmExp(ec_atm(e))

    def ec_assign(x: str, e: RVarExp, k: cvar.Tail) -> cvar.Tail:
        if isinstance(e, (Int, Var, Prim)):
            return cvar.Seq(cvar.Assign(x, ec_exp(e)), k)
        elif isinstance(e, Let):
            return ec_assign(e.x, e.e1, ec_assign(x, e.body, k))
        else:
            raise Exception('ec_assign', e)

    def ec_tail(e: RVarExp) -> cvar.Tail:
        if isinstance(e, (Int, Var, Prim)):
            return cvar.Return(ec_exp(e))
        elif isinstance(e, Let):
            return ec_assign(e.x, e.e1, ec_tail(e.body))
        else:
            raise Exception('ec_tail', e)

    return cvar.Program({'start': ec_tail(e)})


##################################################
# select-instructions
##################################################

def select_instructions(p: cvar.Program) -> x86.Program:
    """
    Transforms a CVar program into a pseudo-x86 assembly program.
    :param p: a CVar program
    :return: a pseudo-x86 program
    """
    def si_atm(a: cvar.Atm) -> x86.Arg:
        if isinstance(a, cvar.Int):
            return x86.Int(a.val)
        elif isinstance(a, cvar.Var):
            return x86.Var(a.var)
        else:
            raise Exception('si_atm', a)

    def si_stmt(e: cvar.Stmt) -> List[x86.Instr]:
        if isinstance(e, cvar.Assign):
            if isinstance(e.exp, cvar.AtmExp):
                return [ x86.Movq(si_atm(e.exp.atm), x86.Var(e.var)) ]
            elif isinstance(e.exp, cvar.Prim):
                if e.exp.op == '+':
                    a1, a2 = e.exp.args
                    return [ x86.Movq(si_atm(a1), x86.Var(e.var)),
                             x86.Addq(si_atm(a2), x86.Var(e.var)) ]
            raise Exception('si_stmt Assign', e)
        else:
            raise Exception('si_stmt', e)

    def si_tail(e: cvar.Tail) -> List[x86.Instr]:
        if isinstance(e, cvar.Return):
            new_var = gensym('retvar')
            instrs = si_stmt(cvar.Assign(new_var, e.exp))

            return instrs + \
                [ x86.Movq(x86.Var(new_var), x86.Reg('rax')),
                  x86.Jmp('conclusion') ]
        elif isinstance(e, cvar.Seq):
            return si_stmt(e.stmt) + si_tail(e.tail)
        else:
            raise Exception('si_tail', e)

    return x86.Program({label: si_tail(block) for (label,block) in p.blocks.items()})


##################################################
# uncover-live
##################################################

def uncover_live(program: x86.Program) -> Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]:
    """
    Performs liveness analysis. Returns the input program, plus live-after sets for its blocks.
    :param program: a pseudo-x86 assembly program
    :return: A tuple. The first element is the same as the input program. The second element is a dict of
    live-after sets. This dict maps each label in the program to a list of live-after sets for that label.
    The live-after sets are in the same order as the label's instructions.
    """

    def ul_block(instrs: List[x86.Instr]) -> List[Set[x86.Var]]:
        # Computes a list of live-after sets for the instructions in one block of the oram

        # process instructions in reverse order
        for instruction in reversed(instrs):
            # you will need the "previous life-after set"
            pass
        pass

    pass


##################################################
# build-interference
##################################################

class InterferenceGraph:
    """
    A class to represent an interference graph: an undirected graph where nodes are x86.Arg objects and an edge
    between two nodes indicates that the two nodes cannot share the same locations.
    """
    graph: DefaultDict[x86.Arg, Set[x86.Arg]]

    def __init__(self):
        self.graph = defaultdict(lambda: set())

    def add_edge(self, a: x86.Arg, b: x86.Arg):
        if a != b:
            self.graph[a].add(b)
            self.graph[b].add(a)

    def neighbors(self, a: x86.Arg) -> Set[x86.Arg]:
        if a in self.graph:
            return self.graph[a]
        else:
            return set()

    def __str__(self):
        pairs = set()
        for k in self.graph.keys():
            new_pairs = set((k, v) for v in self.graph[k])
            pairs = pairs.union(new_pairs)

        for a, b in list(pairs):
            if (b, a) in pairs:
                pairs.remove((a, b))

        strings = [print_ast(a) + ' -- ' + print_ast(b) for a, b in pairs]
        return 'InterferenceGraph{\n ' + ',\n '.join(strings) + '\n}'



def build_interference(inputs: Tuple[x86.Program, Dict[str, List[Set[x86.Var]]]]) -> \
        Tuple[x86.Program, InterferenceGraph]:
    """
    Build the interference graph.
    :param inputs: A Tuple. The first element is a pseudo-x86 program. The second element is the dict of live-after
    sets produced by the uncover-live pass.
    :return: A Tuple. The first element is the same as the input program. The second is a completed interference graph.
    """

    pass


##################################################
# allocate-registers
##################################################

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]


def allocate_registers(inputs: Tuple[x86.Program, InterferenceGraph]) -> \
        Tuple[x86.Program, int]:
    """
    Assigns homes to variables in the input program. Allocates registers and stack locations as needed, based on
    a graph-coloring register allocation algorithm.
    :param inputs: A Tuple. The first element is the pseudo-x86 program. The second element is the completed
    interference graph.
    :return: A Tuple. The first element is an x86 program (with no variable references). The second element is
    the number of bytes needed in stack locations.
    """

    ## Functions for listing the variables in the program
    def vars_arg(a: x86.Arg) -> Set[x86.Var]:
        pass

    def vars_instr(e: x86.Instr) -> Set[x86.Var]:
        pass

    ## Functions for graph coloring
    def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:
        pass

    # Functions for allocating registers
    def make_stack_loc(offset):
        return x86.Deref(-(offset * 8), 'rbp')

    # Defines the set of registers to use
    register_locations = [x86.Reg(r) for r in constants.caller_saved_registers + constants.callee_saved_registers]

    # Functions for replacing variables with their homes
    homes: Dict[str, x86.Arg] = {}

    def ah_arg(a: x86.Arg) -> x86.Arg:
        pass

    def ah_instr(e: x86.Instr) -> x86.Instr:
        pass

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        pass

    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))

    # Main body of the pass
    pass


##################################################
# patch-instructions
##################################################

def patch_instructions(inputs: Tuple[x86.Program, int]) -> Tuple[x86.Program, int]:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param inputs: A Tuple. The first element is an x86 program. The second element is the stack space in bytes.
    :return: A Tuple. The first element is the patched x86 program. The second element is the stack space in bytes.
    """
    def pi_instr(e: x86.Instr) -> List[x86.Instr]:
        if isinstance(e, x86.Movq) and \
           isinstance(e.e1, x86.Deref) and \
           isinstance(e.e2, x86.Deref):
            return [x86.Movq(e.e1, x86.Reg('rax')),
                    x86.Movq(x86.Reg('rax'), e.e2)]
        elif isinstance(e, x86.Addq) and \
           isinstance(e.e1, x86.Deref) and \
           isinstance(e.e2, x86.Deref):
            return [x86.Movq(e.e1, x86.Reg('rax')),
                    x86.Addq(x86.Reg('rax'), e.e2)]
        elif isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.Movq, x86.Addq)):
            return [e]
        else:
            raise Exception('pi_instr', e)

    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instrs = [pi_instr(i) for i in instrs]
        flattened = [val for sublist in new_instrs for val in sublist]
        return flattened

    program, stack_size = inputs
    blocks = program.blocks
    new_blocks = {label: pi_block(block) for label, block in blocks.items()}
    return (x86.Program(new_blocks), stack_size)


##################################################
# print-x86
##################################################

def print_x86(inputs: Tuple[x86.Program, int]) -> str:
    """
    Prints an x86 program to a string.
    :param inputs: A Tuple. The first element is the x86 program. The second element is the stack space in bytes.
    :return: A string, ready for gcc.
    """

    def print_arg(a: x86.Arg) -> str:
        if isinstance(a, x86.Int):
            return f'${a.val}'
        elif isinstance(a, x86.Reg):
            return f'%{a.val}'
        elif isinstance(a, x86.Var):
            return f'#{a.var}'
        elif isinstance(a, x86.Deref):
            return f'{a.offset}(%{a.val})'
        else:
            raise Exception('print_arg', a)

    def print_instr(e: x86.Instr) -> str:
        if isinstance(e, x86.Movq):
            return f'movq {print_arg(e.e1)}, {print_arg(e.e2)}'
        elif isinstance(e, x86.Addq):
            return f'addq {print_arg(e.e1)}, {print_arg(e.e2)}'
        elif isinstance(e, x86.Callq):
            return f'callq {e.label}'
        elif isinstance(e, x86.Retq):
            return f'retq'
        elif isinstance(e, x86.Jmp):
            return f'jmp {e.label}'
        else:
            raise Exception('print_instr', e)

    def print_block(label: str, instrs: List[x86.Instr]) -> str:
        name = f'{label}:\n'
        instr_strs = '\n'.join(['  ' + print_instr(i) for i in instrs])
        return name + instr_strs

    program, stack_size = inputs
    blocks = program.blocks
    block_instrs = '\n'.join([print_block(label, block) for label, block in blocks.items()])

    program = f"""
      .globl main
    main:
      pushq %rbp
      movq %rsp, %rbp
      subq ${stack_size}, %rsp
      jmp start
    {block_instrs}
    conclusion:
      movq %rax, %rdi
      callq print_int
      movq $0, %rax
      addq ${stack_size}, %rsp
      popq %rbp
      retq
    """

    return program

##################################################
# Compiler definition
##################################################

compiler_passes = {
    'uniquify': uniquify,
    'remove complex opera*': rco,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'uncover live': uncover_live,
    'build interference': build_interference,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'print x86': print_x86
}


def run_compiler(s, logging=False):
    """
    Run the compiler on an input program.
    :param s: An RVar program, as a string.
    :param logging: Whether or not to print out debugging information.
    :return: An x86 program, as a string
    """
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
