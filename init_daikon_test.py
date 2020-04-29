import os
import re
import sys

def deleteExistingTest(file):
    f = f"C:\\Users\\Synthesis\\Research\\LearningContracts\\DaikonContractsSubjects\\{file}\\{file}Test\\{file}DaikonContract.cs"

    test = open(f, 'r')
    lines = test.readlines()
    test.close()

    test = open(f, 'w')
    idx = 0
    new_line = False
    while idx < len(lines):
        if "[Test]" in lines[idx]:
            while idx < len(lines) and len(re.findall(r"^\s+}\n$", lines[idx])) == 0:
                idx += 1
            if not new_line:
                test.write("\n")
                new_line = True
        else:
            test.write(lines[idx])
        idx += 1
    test.close()


if __name__ == "__main__":
    subject = sys.argv[1]
    deleteExistingTest(subject)