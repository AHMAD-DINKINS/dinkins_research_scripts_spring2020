import subprocess
import sys
import re
import os
import time
import argparse
import collections
import pprint
import csv
import json
import time
import shutil
import io
import platform
from test import Test
from xml.etree import ElementTree as ET

# CONSTANTS #
WINDOWS = "Windows"

# Returns the absolute path to a file or directory
def get_abs_path(path: "str")-> "str":
    return os.path.abspath(path)

# rename contract_test to test_file
#NOTE consider if we parse PUT names then for safety check, the xml parsing will have to consider that pex will output
# of each test in seperate .cs files
# Method that handles setting up pex, rebuilding the solution and running pex
def run(test_file: "str", solution: "str", assembly: "str")-> "None":
    # Replace all [PexMethod]
    #pex_replacement(test_file)
    # Build solution
    #build(solution)
    # Get the contracts
    #contracts = get_contracts(test_file) # gets puts
    # Run pex
    #run_pex(solution, contracts, assembly) # puts as contracts
    pass


# Method to set up pex config
def pex_replacement(test_file: "str")-> "None":
    abs_path_to_test_file = get_abs_path(test_file)
    # What you wish to replace
    to_replace = "[PexMethod]"
    # What you wish to replace with
    replacement = "[PexMethod(MaxRuns=100)]"
    # Reads the file
    file = open(abs_path_to_test_file, 'r')
    lines = file.readlines()
    file.close()
    # Performs replacement
    text = "".join(lines)
    text = text.replace(to_replace, replacement)
    # Writes chaages to the contract test
    file = open(abs_path_to_test_file, 'w')
    file.write(text)
    file.close()


# Builds the solution
def build(solution: "str")-> "None":
    build_command = get_msbuild_command(solution)
    build_output = run_command(build_command)


# Gets the build command to run
def get_msbuild_command(solution: "str")-> "str":
    abs_path_to_solution = get_abs_path(solution)
    abs_path_to_msbuild = get_abs_path("c:\WINDOWS\Microsoft.NET\Framework\\v4.0.30319\MSBuild.exe")
    return f"{abs_path_to_msbuild} {abs_path_to_solution} /t:rebuild"


# Get the contracts and stores them as keys in a set
def get_contracts(test_file: "str")-> "set":
    abs_path_to_test = get_abs_path(test_file)

    file = open(abs_path_to_test)
    lines = file.readlines()
    file.close()

    contracts = set()

    for line in lines:
        if "PUT_" in line:
            slice_index = line.index("PUT_")
            contract = line[slice_index:]
            slice_index = contract.index('(')
            contract = contract[:slice_index]
            contracts.add(contract)

    return contracts


# Runs pex on each contract and returns a list of generated tests
def run_pex(assembly: "str", contract: "str")-> "list": # puts as parameter
    # The absolute path to the dll
    abs_path_to_assembly = get_abs_path(assembly)
    # Get the problem information for pex
    (problem_name, test_namespace, test_class) = get_problem_information(assembly)
    # For each contract, run pex
    pex_command = get_pex_command(abs_path_to_assembly, contract, test_namespace, test_class)
    # Store the pex output for that contract
    pex_output = run_command(pex_command)
    # Parse and store each generated test in a list
    # Assumes root directory is named root
    (path_to_tests, path_to_report) = get_path_to_xml_report(abs_path_to_assembly, problem_name)
    parse_report(contract, path_to_report)
    tests = collect_tests(contract, path_to_tests)
    return tests


# Returns the path to the directory that contains the XmlReport pex generated
def get_path_to_xml_report(path_to_assembly: "str", problem_name: "str")-> "str":
    delimiter = "\\" if platform.system() is WINDOWS else '/'
    root_dir = delimiter + "root"
    slice_index = path_to_assembly.rindex(delimiter)
    path_to_root_dir = path_to_assembly[:slice_index] + root_dir
    dirs = os.listdir(path_to_root_dir)
    # Makes sure pex geneerated an xml report
    assert("XmlReport" in " ".join(dirs))
    path_to_tests = f"{path_to_root_dir + delimiter}XmlReport{delimiter}tests{delimiter + problem_name + delimiter}Test{delimiter}"
    path_to_report = f"{path_to_root_dir + delimiter}XmlReport{delimiter}report.per"
    return (path_to_tests, path_to_report)


# Parses the xml report file generated by pex and prints the results to stdout
def parse_report(contract: "str", report: "str")-> "None":
    # Information to print to stdout
    number_of_tests_generated = int()
    number_of_passing_tests = int()
    # API call to parse xml into tree
    tree = ET.parse(report)
    # Query the tree for generated tests and see the result
    for test in tree.findall(".//generatedTest"):
            # check for TermFailure exception
            name = test.get("name")
            if name.find("TermDestruction") != -1:
                continue
                
            status = test.get("status")
            statuses_to_ignore = ("assumptionviolation", "minimizationrequest", "pathboundsexceeded")
            if status not in statuses_to_ignore:
                number_of_tests_generated += 1
                if status == "normaltermination":
                    number_of_passing_tests += 1
                
            # singlePoint = ()
            # for value in test.xpath('./value'):
            #     if re.match("^\$.*", value.xpath('./@name')[0]):
            #         val = str(value.xpath('string()'))
            #         val = self.ReplaceIntMinAndMax(val)
            #         val = self.ReplaceTrueAndFalse(val)
            #         singlePoint = singlePoint + (val,)
            
            # if len(singlePoint) < len(precisFeatureList):
            #     continue
    print(f"{contract}:")
    print(f"\tNumber of tests generated: {number_of_tests_generated}")
    print(f"\tNumber of passing tests: {number_of_passing_tests}")
    print(f"\tNumber of failing tests: {number_of_tests_generated - number_of_passing_tests}\n")


# Parses the tests files and stores them in a list
def collect_tests(contract: "str", path_to_tests: "str")-> "list":
    tests = list()
    slice_index = contract.index("Contract")
    name_of_PUT = contract[:slice_index]
    for test in os.listdir(path_to_tests):
        if not name_of_PUT in test:
            continue
        # Get the absolute path to the test
        path_to_current_test = path_to_tests + test
        # Read the test
        file = io.open(path_to_current_test, encoding="utf-16")
        lines = "".join(file.readlines())
        file.close()
        # Parse test
        new_tests = lines.split("[Test]")[1:]
        for idx in range(0, len(new_tests) - 1):
            new_tests[idx] = new_tests[idx].replace("\n\n        ", "")
        new_tests[len(new_tests) - 1] = new_tests[len(new_tests) - 1].replace("\n    }\n}\n", "")
        for idx in range(0, len(new_tests)):
            new_tests[idx] = Test(new_tests[idx])
        tests.extend(new_tests)
    return tests



# Gets the information that pex needs to run
def get_problem_information(solution: "str")-> "tuple":
    abs_path_to_solution = get_abs_path(solution)
    delimiter = "\\" if platform.system() is WINDOWS else '/'
    contracts_subjects = f"{delimiter}ContractsSubjects{delimiter}"
    slice_index = abs_path_to_solution.index(contracts_subjects)
    problem_name = abs_path_to_solution[slice_index+len(contracts_subjects):]
    slice_index = problem_name.index(delimiter)
    problem_name = problem_name[:slice_index]
    return (problem_name, f"{problem_name}.Test", f"{problem_name}ContractTest")


# Returns the command to run pex with
def get_pex_command(testDll: "str", testMethod: "str", testNamespace: "str", testClass: "str"):
        arguments = ['/nor']
        abs_path_to_pex = get_abs_path("c:\Program Files\Microsoft Pex\\bin\pex.exe") # Might not work on systems other than windows...
        cmd = [abs_path_to_pex, testDll , f"/membernamefilter:M:{testMethod}!", f"/methodnamefilter:{testMethod}!", f"/namespacefilter:{testNamespace}!", f"/typefilter:{testClass}!"]
        cmd.extend(["/ro:root", "/rn:XmlReport", "/rl:Xml"])
        cmd.extend(arguments)
        
        return cmd


# Runs the passed in command
def run_command(args):
    try:
        executionOutput = ""
        executionRun = subprocess.Popen(args, stdout = subprocess.PIPE, stderr = subprocess.PIPE)
        for line in executionRun.stdout:
            executionOutput += os.linesep + str(line.rstrip())
        executionRun.stdout.close()
        return executionOutput
    except OSError as e:
        print('OSError > ', e.errno)
        print('OSError > ', e.strerror)
        print('OSError > ', e.filename)       
        raise OSError
    except:
        print('Error > ', sys.exc_info()[0])
        raise OSError


# Main Method
if __name__ == "__main__":
    # Create the argument parser
    parser = argparse.ArgumentParser()
    # Argument that collects the contract test, the solution, and the test dll
    parser.add_argument("-run", type=str, nargs=3, required=True)
    # Produces a namespace that maps 'run' to a list filled with the arguments
    args = parser.parse_args()
    # Get the list of arguments
    to_run = args.run
    assert(len(to_run) == 3)
    # The contrat test
    test_file = to_run[0]
    # The solution
    solution = to_run[1]
    # The assembly file
    assembly = to_run[2]
    # Set upn pex methods within the contract test and run pex
    #run(test_file, solution, assembly) # puts as parameter
    # The contracts pex will generate tests for
    # NOTE: A single contract will be the input
    stack_contracts = ["PUT_PushContract"]
    arrlist_contracts = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_InsertContract', 'PUT_SetContract', 'PUT_GetContract',
                 'PUT_ContainsContract', 'PUT_IndexOfContract', 'PUT_LastIndexOfContract', 'PUT_CountContract']
    # Runs pex and stores the generated tests
    tests = run_pex(assembly, stack_contracts[0])

    for test in tests:
        print(test)




    