#!/usr/bin/env python3

import sys
import re

DECLARE_CONST = "(declare-const V{} Int)"

'''
This function reads from STDIN and returns the unsolved kenken puzzle 
'''
def read_puzzle():
    input_str = sys.stdin.read()
    puzzle = re.sub("[\n\r]", "", input_str)
    return puzzle

def add_mathsat_logic(assertions):
    assertions.append("(set-logic UFNIA)")
    assertions.append("(set-option :produce-models true)")
    assertions.append("(set-option :produce-assignments true)")
    
    for i in range(0, 49):
        assertions.append(DECLARE_CONST.format(i))
    return assertions

def create_assertions(puzzle):
    assertions = add_mathsat_logic([])
    print(assertions)

if __name__ == "__main__":
    puzzle = read_puzzle()
    create_assertions(puzzle)
    
