import argparse
import os
import re


#NOTE: parse observer methods from PUT
# input is name of PUT
# parse PUT to get names of observers
# return a list of strings, client will find out type 

# Returns a tuple containg the features within the test file
def collect_global_features(test_file: "str")-> "tuple":
    abs_path_to_test = os.path.abspath(test_file)

    file = open(abs_path_to_test)
    lines = file.readlines()
    file.close()

    features = list()
    line_idx = 0
    while line_idx < len(lines) and not "/* Observer Methods START */" in lines[line_idx]:
        line_idx += 1

    while line_idx < len(lines) and not "/* Observer Methods END */" in lines[line_idx]:
        if not is_comment(lines[line_idx]):
            feature = extract_feature_definition(lines[line_idx])
            if not feature == "":
                features.append(feature)
        line_idx += 1

    return features


# Returns the features that are defined globally within the method
def collect_features(test_file: "str", put: "str")-> list:
    abs_path_to_test = os.path.abspath(test_file)

    file = open(abs_path_to_test)
    lines = file.readlines()
    file.close()

    local_features = list()
    global_features = list()
    line_idx = 0
    while line_idx < len(lines) and not put in lines[line_idx]:
        line_idx += 1
    
    while line_idx < len(lines) and not "PexObserve" in lines[line_idx]:
        if not is_comment(lines[line_idx]):
            local_feature = extract_feature_definition(lines[line_idx])
            global_feature = extract_feature_assignment(lines[line_idx])
            if not local_feature == "":
                local_features.append(local_feature)
            if not global_feature == "":
                global_features.append(global_feature)  
        line_idx += 1
    
    return local_features, global_features

# Returns true if the string is a comment
# NOTE: Nee to fix multi line comment
def is_comment(line: "str")-> "bool":
    return len(re.findall(r"(?:\s*)(?://|/\*)", line)) > 0


# Returne the feature stored in line
def extract_feature_definition(line: "str")-> "str":
    match = re.match(r"\s*(?P<type>int|bool) (?P<feature>\D*) =", line)
    return (match.group("feature"), match.group("type")) if not match is None else ""


# Returns the feature stored in line
def extract_feature_assignment(line: "str")-> "str":
    match = re.match(r"\s*(?P<feature>(?:Old|New)\D*) =", line)
    return match.group("feature") if not match is None else ""


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("--test-files", type=str, nargs=argparse.ONE_OR_MORE, required=True)

    args = parser.parse_args()

    test = args.test_files[0]

    put = "PUT_IndexOfContract"

    features = collect_global_features(test)
    (local_features, global_features) = collect_features(test, put)
    print(features)
    print(local_features)
    print(global_features)