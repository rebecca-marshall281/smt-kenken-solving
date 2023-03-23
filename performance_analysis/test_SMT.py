#!/usr/bin/env python3

import os
import shutil
import sys
import json
import argparse
import re


# copy file to this folder
def copy_file(src_path, dst_path="."):
    try:
        shutil.copy(src_path, dst_path)
    except IOError as e:
        print(f"Unable to copy file. {e}")

# delete file
def delete_file(file_path):
    try:
        os.remove(file_path)
    except OSError as e:
        print(f"Error: {file_path} : {e.strerror}")

def delete_folder(folder_path):
    shutil.rmtree(folder_path)


def run_kenken2smt(puzzle, i):
    output_file = "puzzle_{}.smt".format(i)

    # Run kenken2smt
    os.system(f"./kenken2smt < {puzzle} > {output_file}")


def run_mathsat(i, output_folder_path): 
    input_file = "puzzle_{}.smt".format(i)
    
    # check if the mathsat input file exists
    if (not os.path.exists(input_file)):
        print("Mathsat input file does not exist: ", input_file)
        return
    
    output_file = os.path.join(output_folder_path, "model_{}.smt".format(i))

    # Run the minisat command and capture the output in a file
    os.system(f"mathsat -stats < {input_file} > {output_file}")

    # Delete input file
    delete_file(input_file)


def create_output_folder(new_dir):
    if not os.path.exists(new_dir):
        os.makedirs(new_dir)


# Run all puzzles with kenken2smt and mathsat
def process_puzzles(folder_path, output_folder, kenken2smt_path):    
    create_output_folder(output_folder)
    
    if not os.path.exists("kenken2smt"):
        copy_file(kenken2smt_path)
    
    for root, dirs, files in os.walk(folder_path):
        if not dirs: # if there are no subfolders
            print("Processing puzzles in: ", root , "...")
            output_sub_folders = root.replace(folder_path, "") # remove the input folder name from the path
            puzzle_output_folder = os.path.join(output_folder, output_sub_folders)
            create_output_folder(puzzle_output_folder)
            for file_name in files:
                if file_name.endswith('.txt') and "solution" not in file_name:
                    puzzle_number = re.findall('\d+', file_name)[0]
                    puzzle_file_path = os.path.join(root, file_name)
                    run_kenken2smt(puzzle_file_path, puzzle_number)
                    run_mathsat(puzzle_number, puzzle_output_folder)

# Parse output file to get statistics
def get_statistics(output_folder):

    for root, dirs, files in os.walk(output_folder):
        if not dirs: # if there are no subfolders
            puzzle_output_folder = root
            print("Getting statistics for: ", puzzle_output_folder, "...")
            stats_list = []
            
            for file_name in files:
                if file_name.endswith('.smt'):
                    file_path = os.path.join(puzzle_output_folder, file_name)
                    with open(file_path, "r") as file:
                        stat_content = file.read()
                        stats = parse_statistics(stat_content)
                        if stats == {}:
                            print("No statistics found for: ", file_path)
                        else:
                            stats_list.append(stats)

            get_worst_and_average_case(stats_list, puzzle_output_folder)

# Parse the statistics from the output file
def parse_statistics(statistics_str):
    stats = {}
    for line in statistics_str.split('\n'):
        if ':' in line:
            line = line.replace(':', '')
            key, value = line.split()
            key = key.strip()
            value = float(value.strip())
            stats[key] = value
    return stats

# Get the worst and average case statistics
def get_worst_and_average_case(stats_list, output_folder):
    worst_case = {}
    average_case = {}
    for stat in stats_list:
        for key, value in stat.items():
            if key not in worst_case:
                worst_case[key] = value
            else:
                if value > worst_case[key]:
                    worst_case[key] = value

            if key not in average_case:
                average_case[key] = value
            else:
                average_case[key] += value

    for key, value in average_case.items():
        average_case[key] = value / len(stats_list)

    output_path = os.path.join(output_folder, "worst_and_average_case.txt")
    with open(output_path, 'w') as f:
        f.write("Worst case: ")
        f.write(json.dumps(worst_case))
        f.write('\n')
        f.write("Average case: ")
        f.write(json.dumps(average_case))

                
def parse_args(args):
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="Input folder with puzzle files")
    parser.add_argument("-k", "--kenken2smt", help="Path to kenken2smt executable")
    parser.add_argument("-o", "--output", help="output folder for stats and report file", default="test_output/")
    p_args = parser.parse_args(args)
    return p_args

if __name__ == '__main__':
    args = parse_args(sys.argv[1:])

    process_puzzles(args.input, args.output, args.kenken2smt)
    #get_statistics(args.output)
    
