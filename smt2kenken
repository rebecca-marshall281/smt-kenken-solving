#!/usr/bin/env python3
import sys

def get_solution():
    # get input from stdin and split text by lines
    # if line doesn't contain v it's not a variable so get rid of the line
    sys_in = sys.stdin.read()
    inputt = sys_in.splitlines()
    inputt = [string for string in inputt if "V" in string]
 
    # append all output to this variable
    output = ""

    # loop through input and append variable number
    for line in inputt:
        var = ""
        var_num = ""
                
        result = line.replace("(", "")
        result = result.replace(")", "")
        with_empty_strings = result.split(" ")
        var_num_list = [string for string in with_empty_strings if string != ""]
        output += var_num_list[1]
    
    # print the output
    print(output)

if __name__ == "__main__":
    sudoku = get_solution()

