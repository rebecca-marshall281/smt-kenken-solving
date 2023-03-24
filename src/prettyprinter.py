#!/usr/bin/env python3

from matplotlib.colors import ListedColormap
import matplotlib.pyplot as plt
import argparse
import sys
import re


# Define the custom colors
colours = [
    '#E0BBE4CC', # lavender
    '#E9967ACC', # dark salmon
    '#E8E8E8CC', # very light grey
    '#957DADCC', # medium purple
    '#D291E4CC', # bright purple
    '#FEC8D8CC', # pastel pink
    '#FFDFD3CC', # pastel orange
    '#FFF2D5CC', # pale orange
    '#B7E4C7CC', # mint
    '#7FB3D5CC', # sky blue
    '#DCE2F1CC', # light grey-blue
    '#B8D7FACC', # light blue
    '#FEEAE6CC', # light peach
    '#F7C5D1CC', # light rose
    '#F4A6AACC', # light salmon
    '#F8B195CC', # light coral
    '#F7DBA7CC', # light gold
    '#D1F2A5CC', # light green
    '#A2DED0CC', # light teal
    '#D3D3D3CC', # light grey
    '#E6D4A3CC', # light khaki
    '#EFECCA99', # pale yellow
    '#FFF8E6CC', # pale beige
    '#FFE5D9CC', # pale peach
    '#FFD7B5CC', # pale apricot
    '#FFB7B2CC', # pale coral
    '#FF9AA2CC', # pale pink
    '#DD7596CC', # pale raspberry
    '#CA6680CC', # pale magenta
    '#F5F5F5CC', # very light grey
    '#9F5F80CC', # pale plum
    '#5C5C5CCC', # pale grey
    '#8E8D8ACC', # pale grey-blue
    '#BCB8B1CC', # light grey
    '#FFC0CBCC', # pink
    '#FFE4E1CC', # misty rose
    '#FFEBCDCC', # blanched almond
    '#E6E6FACC', # light steel blue
    '#B0C4DECC', # light steel blue
    '#D8BFD8CC', # thistle
    '#FFF0F5CC', # lavender blush
    '#FFA07ACC', # salmon
    '#FFDAB9CC', # peach puff
]


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
            #print("Got line: {}".format(line))
            assert len(line) == 49
            for i, c in enumerate(line):
                row.append(int(c))
                if (i+1) % 7 == 0:
                    #print("Starting new row after: {}".format(row))
                    solution.append(row)
                    #print("Current solution: {}".format(solution))
                    row = []
            break
    
    return solution

def parse_args(args):
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="Input puzzle file to be displayed")
    parser.add_argument("solution", help="Solution to the puzzle")
    parser.add_argument("-o", "--output", help="Output file to save the image to")
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

    # Get puzzle number
    puzzle_num = re.findall(r"\d+", args.input)[0]

    # Set the axis limits and remove the ticks
    ax.set_title("Kenken Puzzle #{}".format(puzzle_num))
    ax.set_xlim(0, 7)
    ax.set_ylim(0, 7)
    ax.set_xticks([])
    ax.set_yticks([])

    # Create a colormap for the regions
    cmap = ListedColormap(colours)

    # Save the figure
    ax.imshow(regions, cmap=cmap, origin="upper", extent=[0, 7, 0, 7])
    fig.savefig(args.output)
