#!/usr/bin/env python3

import sys
import re
from itertools import permutations

DECLARE_CONST = "(declare-const V{} Int)"
ASSERT_VALUE_RANGE = "(assert (and (> V{} 0) (< V{} 8)))"


'''
This function reads from STDIN and returns the unsolved kenken puzzle 
'''
def read_puzzle():
    input_str = sys.stdin.read()
    puzzle = re.sub("[\r]", "", input_str).split("\n")[1:] # remove first line
    puzzle = re.sub("\n", ",", "\n".join(puzzle))[:-1] # remove last comma
    return puzzle

def add_mathsat_logic(smt2_lines):
    smt2_lines.append("(set-logic UFNIA)")
    smt2_lines.append("(set-option :produce-models true)")
    smt2_lines.append("(set-option :produce-assignments true)")
    
    for i in range(0, 49):
        smt2_lines.append(DECLARE_CONST.format(i))

    # extra for-loop makes the output more readable
    for i in range(0, 49):
        smt2_lines.append(ASSERT_VALUE_RANGE.format(i, i))

    return smt2_lines

def add_distinct_col_row_assertions(smt2_lines):
    # add distinct value assertions for each row
    smt2_lines.append("(assert (distinct V0 V1 V2 V3 V4 V5 V6))")
    smt2_lines.append("(assert (distinct V7 V8 V9 V10 V11 V12 V13))")
    smt2_lines.append("(assert (distinct V14 V15 V16 V17 V18 V19 V20))")
    smt2_lines.append("(assert (distinct V21 V22 V23 V24 V25 V26 V27))")
    smt2_lines.append("(assert (distinct V28 V29 V30 V31 V32 V33 V34))")
    smt2_lines.append("(assert (distinct V35 V36 V37 V38 V39 V40 V41))")
    smt2_lines.append("(assert (distinct V42 V43 V44 V45 V46 V47 V48))")

    # add distinct value assertions for each column
    smt2_lines.append("(assert (distinct V0 V7 V14 V21 V28 V35 V42))")
    smt2_lines.append("(assert (distinct V1 V8 V15 V22 V29 V36 V43))")
    smt2_lines.append("(assert (distinct V2 V9 V16 V23 V30 V37 V44))")
    smt2_lines.append("(assert (distinct V3 V10 V17 V24 V31 V38 V45))")
    smt2_lines.append("(assert (distinct V4 V11 V18 V25 V32 V39 V46))")
    smt2_lines.append("(assert (distinct V5 V12 V19 V26 V33 V40 V47))")
    smt2_lines.append("(assert (distinct V6 V13 V20 V27 V34 V41 V48))")

    return smt2_lines

def add_region_assertions(smt2_lines, puzzle):
    cells = puzzle.split(",")
    regions = []
    cell_num = 0

    # create array of regions
    for cell in cells:
        if "." in cell:
            region_num, region_operation = cell.split(".") # split r10.3+ into r10 and 3+
            region = [region_operation, "V{}".format(cell_num)]
            regions.append(region)

        else:
            region_num = int(cell[1:])

            # this will catch an error where there is a region with no total value
            try :
                regions[region_num - 1].append("V{}".format(cell_num))    
            except:
                sys.exit(1)

        cell_num += 1

    # add assertions for each region
    for region in regions:
        operation = re.split(r"(\D)", region[0], maxsplit=1) # split 3+ into 3 and +
        if len(operation) > 1:
            total, operator = operation[0], operation[1]
        else:
            total, operator = operation[0], None

        if operator == None:
            smt2_lines.append("(assert (= {} {}))".format(total, region[1]))
        if operator in ["+", "*"]:
            smt2_lines.append("(assert (= {} ({} {})))".format(total, operator, " ".join(region[1:])))
        if operator in ["-", "/"]:
            perms = permutations(region[1:]) # get all permutations of the region values
            or_statements = ""
            for perm in perms:
                or_statements += "(= {} ({} {}))".format(total, operator, " ".join(perm))

            smt2_lines.append("(assert (or {}))".format(or_statements))
    
    return smt2_lines

def add_final_lines(smt2_lines):
    smt2_lines.append("(check-sat)")
    smt2_lines.append("(get-value (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 V16 V17 V18 V19 V20 V21 V22 V23 V24 V25 V26 V27 V28 V29 V30 V31 V32 V33 V34 V35 V36 V37 V38 V39 V40 V41 V42 V43 V44 V45 V46 V47 V48))")
    smt2_lines.append("(exit)")
    return smt2_lines

# Write to STDOUT
def print_smt2_lines(smt2_lines):
    for smt2_line in smt2_lines:
        print(smt2_line)

def create_smt2_lines(puzzle):
    smt2_lines = add_mathsat_logic([])
    smt2_lines = add_distinct_col_row_assertions(smt2_lines)
    smt2_lines = add_region_assertions(smt2_lines, puzzle)
    smt2_lines = add_final_lines(smt2_lines)

    return smt2_lines

if __name__ == "__main__":
    puzzle = read_puzzle()
    smt2_lines = create_smt2_lines(puzzle)
    print_smt2_lines(smt2_lines)
    
