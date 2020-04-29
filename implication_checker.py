import argparse
import os
from precis_feature import PrecisFeature
from problem import Problem
from typing import List, Tuple, Type
from z3 import *

def getBaseFeatures(problem, PUTName):
    
    AllOberverTypes = os.getcwd()
    AllOberverTypes = AllOberverTypes+"\\typesOM_Class.txt"
    putObeserverTypes = os.getcwd()
    putObeserverTypes = putObeserverTypes +"\\typesOM_PUT.txt"

    problem.ExtractObserversInClass(AllOberverTypes, "daikonClass")
    problem.ExtractObserversInPUT(PUTName, putObeserverTypes,"daikonMethod")
    allFeatures: Tuple[PrecisFeature] = problem.ReadObserversFromFile(AllOberverTypes)
    putBaseFeatures: Tuple[PrecisFeature] = problem.ReadObserversFromFile(putObeserverTypes)
    #print(allFeatures)
    #print(putBaseFeatures)

    return (allFeatures, putBaseFeatures)

def get_problem(problem_name):
    sln = os.path.abspath(f'../DaikonContractsSubjects/{problem_name}/{problem_name}.sln')
    projectName = f'{problem_name}Test'
    testDebugFolder = f'../DaikonContractsSubjects/{problem_name}/{problem_name}Test/bin/Debug/'
    testDll = testDebugFolder + f'{problem_name}Test.dll'
    testFileName = f'{problem_name}ContractTest.cs'
    testNamepace = f'{problem_name}.Test'
    testClass = f'{problem_name}ContractTest'
    daikonTestFilePath = f"../DaikonContractsSubjects/{problem_name}/{problem_name}Test/{problem_name}DaikonContract.cs"

    arrayListPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_InsertContract', 'PUT_SetContract',
                     'PUT_GetContract', 'PUT_ContainsContract', 'PUT_IndexOfContract', 'PUT_LastIndexOfContract', 'PUT_CountContract']

    binaryHeapPUTs = ['PUT_AddContract', 'PUT_MinimumContract', 'PUT_RemoveMinimumContract', 'PUT_RemoveAtContract',
                     'PUT_IndexOfContract', 'PUT_UpdateContract', 'PUT_MinimumUpdateContract']
    
    dictionaryPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_GetContract', 'PUT_SetContract', 'PUT_ContainsKeyContract', 'PUT_ContainsValueContract', 'PUT_CountContract']
    
    hashSetPUTs = ['PUT_AddContract', 'PUT_RemoveContract', 'PUT_CountContract', 'PUT_ContainsContract']

    queuePUTs = ['PUT_EnqueueContract', 'PUT_DequeueContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract']

    stackPUTs = ['PUT_PushContract', 'PUT_PopContract', 'PUT_PeekContract', 'PUT_CountContract', 'PUT_ContainsContract']

    uGraphPUTS = ['PUT_AddVertexContract', 'PUT_RemoveVertexContract','PUT_ClearAdjacentEdgesContract','PUT_ContainsEdgeContract', 'PUT_RemoveVertexContract',
                    'PUT_ContainsEdgeIntContract', 'PUT_AdjacentEdgeContract', 'PUT_IsVerticesEmptyContract', 'PUT_VertexCountContract', 'PUT_ContainsVertexContract',
                    'PUT_AddEdgeContract', 'PUT_RemoveEdgeContract', 'PUT_IsEdgesEmptyContract', 'PUT_EdgeCountContract', 'PUT_AdjacentDegreeContract',
                    'PUT_IsAdjacentEdgesEmptyContract']

    puts_map = {"ArrayList": arrayListPUTs, "BinaryHeap": binaryHeapPUTs, "Dictionary": dictionaryPUTs, "HashSet": hashSetPUTs, "Queue": queuePUTs,
                "Stack": stackPUTs, "UndirectedGraph": uGraphPUTS}

    PUTs = puts_map[problem_name]

    p = Problem(sln, projectName, testDebugFolder, testDll,
                 testFileName, testNamepace, testClass, daikonTestFilePath, PUTs)
    

    return p


def get_name(line):
    #Problem: ArrayListTest
    colon = line.index(":") + 1
    test = line.index("Test")
    return line[colon:test].strip()


def get_smts(lines):
    idx = 0
    smts = {}
    current_contract = ""
    while idx < len(lines):
        if "PUT_" in lines[idx]:
            current_contract = lines[idx].strip()
        if "smt" in lines[idx]:
            colon = lines[idx].index(':') + 1
            smt = lines[idx][colon:].strip()
            smts[current_contract] = smt
        idx += 1
    return smts

def evaluate(implication):
    solver = Solver()
    solver.add(implication)
    check = solver.check()
    return check

def implication_check(precis_inspection, daikon_inspection):
    #Extract the daikon and precis smt from inspection files
    abs_path_to_precis_inspection = os.path.abspath(precis_inspection)
    abs_path_to_daikon_inspection = os.path.abspath(daikon_inspection)

    precis = open(abs_path_to_precis_inspection, 'r')
    precis_lines = precis.readlines()
    precis.close()

    daikon = open(abs_path_to_daikon_inspection, 'r')
    daikon_lines = daikon.readlines()
    daikon.close()

    precis_smts = get_smts(precis_lines)
    daikon_smts = get_smts(daikon_lines)

    #assert same problem
    assert(precis_lines[0] == daikon_lines[0])

    name = get_name(precis_lines[0])
    problem = get_problem(name)

    evaluations = {}
    for PUT in problem.puts:
        allBaseFeat, putBaseFeat = getBaseFeatures(problem, PUT)
        declMap = { f.varName : f.varZ3 for f in putBaseFeat}

        if PUT in precis_smts and not PUT in daikon_smts:
            continue
        elif not PUT in precis_smts and PUT in daikon_smts:
            continue
        precis_formula = parse_smt2_string("(assert "+ precis_smts[PUT]+")", decls=declMap)[0]
        daikon_formula = parse_smt2_string("(assert "+ daikon_smts[PUT]+")", decls=declMap)[0]

        # precis_formula = And([c.varZ3 for c in precisExpr])
        # daikon_formula = And([c.varZ3 for c in daikonExpr])
        # implication = Not(Implies(daikon_formula[0], precis_formula[0]))

        # daikon && !precis is sat
        implication = And(daikon_formula, Not(precis_formula))
        first_eval = evaluate(implication)
        # precis && !daikon is unsat
        implication = And(precis_formula, Not(daikon_formula))
        second_eval = evaluate(implication)

        # -1 = unsat, 1 = sat, 0 = unknown
        if first_eval.r == 1 and second_eval.r == -1:
            evaluations["Precis"] = [PUT] if not "Precis" in evaluations else evaluations["Precis"] + [PUT]
        elif first_eval.r == -1 and second_eval.r == 1:
            evaluations["Daikon"] = [PUT] if not "Daikon" in evaluations else evaluations["Daikon"] + [PUT]
        elif first_eval.r == -1 and second_eval.r == -1:
            evaluations["Equivalent"] = [PUT] if not "Equivalent" in evaluations else evaluations["Equivalent"] + [PUT]
        else:
            print(f"\nCannot determine {name} {PUT} because !(daikon && !precis) was {first_eval} and precis && !daikon was {second_eval}\n")

    return evaluations, name


def precisSimplify(postcondition):
        
        
        set_option(max_args = 10000000, max_lines = 1000000, max_depth = 10000000, max_visited = 1000000)
        set_option(html_mode=False)
        set_fpa_pretty(flag=False)

        #intVars = [ Int(var) for var in intVariables]
        #boolVars = [ Bool(var) for var in boolVariables]

        #declareInts = "\n".join([ "(declare-const " + var + " Int)" for var in intVariables ])
        #declareBools = "\n".join([ "(declare-const " + var + " Bool)" for var in boolVariables ])
        #stringToParse = "\n".join([declareInts,  declareBools, "( assert " + precondition + ")"])

        #logger = logging.getLogger("Framework.z3Simplify")

        # logger.info("############ z3 program")
        # logger.info("############ " + stringToParse)

        #expr = parse_smt2_string(strinagToParse)

        g = Goal()
        g.add(postcondition)
        
        # works = Repeat(Then(
        #     OrElse(Tactic('ctx-solver-simplify'), Tactic('skip')),
        #     OrElse(Tactic('unit-subsume-simplify'),Tactic('skip')),
        #     # OrElse(Tactic('propagate-ineqs'),Tactic('skip')),
        #     # OrElse(Tactic('purify-arith'),Tactic('skip')),
        #       OrElse(Tactic('ctx-simplify'),Tactic('skip')),
        #       OrElse(Tactic('dom-simplify'),Tactic('skip')),
        #     # OrElse(Tactic('propagate-values'),Tactic('skip')),
        #     OrElse(Tactic('simplify'), Tactic('skip')),
        #     #region
        #     # OrElse(Tactic('aig'),Tactic('skip')),
        #     # OrElse(Tactic('degree-shift'),Tactic('skip')),
        #     # OrElse(Tactic('factor'),Tactic('skip')),
        #     # OrElse(Tactic('lia2pb'),Tactic('skip')),
        #     # OrElse(Tactic('recover-01'),Tactic('skip')),
        #     #must to remove ite
        #     # OrElse(Tactic('elim-term-ite'), Tactic('skip')),
        #     # OrElse(Tactic('smt'), Tactic('skip')),
        #     # OrElse(Tactic('injectivity'),Tactic('skip')),
        #     # OrElse(Tactic('snf'),Tactic('skip')),
        #     # OrElse(Tactic('reduce-args'),Tactic('skip')),
        #     # OrElse(Tactic('elim-and'),Tactic('skip')),
        #     # OrElse(Tactic('symmetry-reduce'),Tactic('skip')),
        #     # OrElse(Tactic('macro-finder'),Tactic('skip')),
        #     # OrElse(Tactic('quasi-macros'),Tactic('skip')),
        #     #Repeat(OrElse(Tactic('cofactor-term-ite'), Tactic('skip'))),
        #     Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))),   
        # ))
        
        works = Repeat(Then( 
        #Repeat(OrElse(Tactic('split-clause'),Tactic('skip'))),
                OrElse(Tactic('ctx-solver-simplify'),Tactic('skip')),
                OrElse(Tactic('unit-subsume-simplify'),Tactic('skip')),
                OrElse(Tactic('propagate-ineqs'),Tactic('skip')),
                OrElse(Tactic('purify-arith'),Tactic('skip')),
                OrElse(Tactic('ctx-simplify'),Tactic('skip')),
                OrElse(Tactic('dom-simplify'),Tactic('skip')),
                OrElse(Tactic('propagate-values'),Tactic('skip')),
                OrElse(Tactic('simplify'),Tactic('skip')),
                OrElse(Tactic('aig'),Tactic('skip')),
                OrElse(Tactic('degree-shift'),Tactic('skip')),
                OrElse(Tactic('factor'),Tactic('skip')),
                OrElse(Tactic('lia2pb'),Tactic('skip')),
                OrElse(Tactic('recover-01'),Tactic('skip')),
                OrElse(Tactic('elim-term-ite'),Tactic('skip')), #must to remove ite
                OrElse(Tactic('injectivity'),Tactic('skip')),
                OrElse(Tactic('snf'),Tactic('skip')),
                OrElse(Tactic('reduce-args'),Tactic('skip')),
                OrElse(Tactic('elim-and'),Tactic('skip')),
                OrElse(Tactic('symmetry-reduce'),Tactic('skip')),
                OrElse(Tactic('macro-finder'),Tactic('skip')),
                OrElse(Tactic('quasi-macros'),Tactic('skip')),
                Repeat(OrElse(Tactic('split-clause'),Tactic('skip')))))
        
        result = works(g)
        #result = works1(g)
        # split_all =

        # print str(result)
        # result = [[ "d1", "d2", "d3"], #= conjunct && conjunct
        #           [ "d4", "d5", "d6"]]

        # remove empty subgoals and check if resultant list is empty.
        result = filter(None, result)
        if not result:
            print("there is an error in the custom simplify Z3")
            sys.exit(-9)
        
        # return result
        results = list(result)
        completeConjunct = []
        for i in range(0,len(results)):
            conjunction = results[i]
            completeDisjunct = []
            for literal in conjunction:
                #if i >= 1 and  literal in result[i-1]:
                #    continue
                completeDisjunct.append(literal)

            completeConjunct.append(simplify(And(completeDisjunct)))

        simplifiedPrecondition = Or(completeConjunct)
        return simplifiedPrecondition

if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("--precis", "-p", type=str, nargs=1, required=True)
    parser.add_argument("--daikon", "-d", type=str, nargs=1, required=True)
    args = parser.parse_args()

    precis = args.precis[0]
    daikon = args.daikon[0]

    (evaluations, problem_name) = implication_check(precis, daikon)
    tools = ["Precis", "Daikon", "Equivalent"]
    
    smt_file = open(f"{problem_name}_smt_check.txt", 'w')
    for tool in tools:
        if tool not in evaluations:
            evaluations[tool] = []
        num_puts = len(evaluations[tool])
        print(f"\nTool: {tool}\n\tNumber of Contracts: {num_puts}\n\t{evaluations[tool]}")
        smt_file.write(f"\nTool: {tool}\n\tNumber of Contracts: {num_puts}\n\t{evaluations[tool]}")
    smt_file.close()