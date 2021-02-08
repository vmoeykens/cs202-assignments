from dataclasses import dataclass
from collections import OrderedDict
from typing import List, Set, Dict, Tuple
from r0_parser import *
import sys

from cs202_support.base_ast import AST, print_ast

import cs202_support.x86exp as x86

gensym_num = 0
def gensym(x):
    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'

##################################################
# Pass #1: select-instructions
##################################################

def select_instructions(e: R0Exp) -> x86.Program:
    return x86.Program({
         'start': [
           x86.Movq(
            x86.Int(e.val),
            x86.Reg('rax')),
           x86.Jmp('conclusion')
          ]
})
    
##################################################
# Pass #2: print-x86
##################################################


# Boilerplate main section
main = x86.Program({
        'main': [
            x86.Pushq(x86.Reg('rbp')),
            x86.Movq(x86.Reg('rsp'), x86.Reg('rbp')),
            x86.Jmp('start'),
        ]})

# Boilerplate conclusion section
conclusion = x86.Program({
        'conclusion': [
            x86.Movq(x86.Reg('rax'), x86.Reg('rdi')),
            x86.Callq('print_int'),
            x86.Movq(x86.Int(0), x86.Reg('rax')),
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


def print_x86(program: x86.Program) -> str:
    """Generates x86 assembly for this specific assignment"""
    output_string = '   .globl main\n'
    output_string += ast_to_x86_string(main)
    output_string += ast_to_x86_string(program)
    output_string += ast_to_x86_string(conclusion)

    return output_string

##################################################
# Compiler definition
##################################################

compiler_passes = {
    'select instructions': select_instructions,
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

            except Exception as e:
                print('Error during compilation:', e)
