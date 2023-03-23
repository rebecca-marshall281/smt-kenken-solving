#!/usr/bin/env python3

import matplotlib.pyplot as plt
import argparse
import sys

colors = ['white', 'red', 'green', 'blue', 'yellow', 'orange', 'purple', 'pink', 'brown', 'gray']

def parse_kenken(input_file):
    regions = [[0]*7 for i in range(7)]
    operands = [[None]*7 for i in range(7)]

    with open(input_file, 'r') as f:
        for i, line in enumerate(f):
            if line.startswith('#'):
                continue
            cells = line.split(',')
            for j, cell in enumerate(cells):
                try:
                    region, operand = cell.split('.')
                    regions[i-1][j] = float(region.strip('r'))
                    operands[i-1][j] = operand
                except ValueError:
                    regions[i-1][j] = float(cell.strip('r'))
    
    return regions, operands

def parse_solution(solution_file):
    solution = []
    row=[]

    with open(solution_file, 'r') as f:
        for i, line in enumerate(f):
            if line.startswith('#'):
                continue
            line = line.strip('\n')
            print("Got line: {}".format(line))
            assert len(line) == 49
            for i, c in enumerate(line):
                row.append(int(c))
                if (i+1) % 7 == 0:
                    print("Starting new row after: {}".format(row))
                    solution.append(row)
                    print("Current solution: {}".format(solution))
                    row = []
            break
    
    return solution

def parse_args(args):
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="Input puzzle file to be displayed")
    parser.add_argument("solution", help="Solution to the puzzle")
    p_args = parser.parse_args(args)
    return p_args

if __name__ == '__main__':
    args = parse_args(sys.argv[1:])

    regions, operands = parse_kenken(args.input)
    kenken = parse_solution(args.solution)

    # Define the figure and axis
    fig, ax = plt.subplots()

    # Plot the Kenken numbers
    for i in range(7):
        for j in range(7):
            ax.text(j + 0.5, i + 0.5, str(kenken[6-i][j]), ha='center', va='center')
            if operands[6-i][j] != None:
                ax.text(j+0.05, i+0.95, str(operands[6-i][j]), ha='left', va='top', size=8)

    # Plot the grid
    for i in range(10):
        linewidth = 1
        ax.axhline(i, lw=linewidth, color='k')
        ax.axvline(i, lw=linewidth, color='k')

    # Set the axis limits and remove the ticks
    ax.set_title("Kenken Puzzle #<Test>")
    ax.set_xlim(0, 7)
    ax.set_ylim(0, 7)
    ax.set_xticks([])
    ax.set_yticks([])

    # Show the plot
    ax.imshow(regions, cmap="tab20", origin="upper", extent=[0, 7, 0, 7])
    plt.show()
