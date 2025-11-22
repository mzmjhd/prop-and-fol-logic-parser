
MAX_CONSTANTS = 10



# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    #proposition
    if fmla in ['p','q','r','s']:
        return 6 #It's a proposition
    #atom
    elif len(fmla) == 6 and fmla[0] in ['P', 'Q', 'R', 'S'] and fmla[1] == '(' \
         and fmla[2] in ['x','y','z','w'] and fmla[3] == ',' \
         and fmla[4] in ['x','y','z','w'] and fmla[5] == ')':
        return 1  # 'an atom'
    #negation (both prop and FOL)
    elif fmla[0] == '~':
        sub_formula_type = parse(fmla[1:])
        if sub_formula_type >= 6:
            return 7 #negation of prop
        elif 1 <= sub_formula_type <= 5:
            return 2 #negation of FOL
        else: return 0
    #bin fmla (both prop and FOL)
    elif (fmla[0] == '(') and (fmla[-1] == ')'):
        index = mainConIndex(fmla)
        if index != -1:
            #split into lhs and rhs
            left = lhs(fmla)
            right = rhs(fmla)

            # Recursively parse both sides
            lhs_type = parse(left)
            rhs_type = parse(right)

            # Check if both sides are valid and of the same logic type
            if lhs_type != 0 and rhs_type != 0:
                is_prop_lhs = lhs_type >= 6
                is_prop_rhs = rhs_type >= 6
                if is_prop_lhs and is_prop_rhs:
                    return 8  # 'a binary connective propositional formula'
                elif not is_prop_lhs and not is_prop_rhs:
                    return 5  # 'a binary connective first order formula'
        return 0 # If parsing fails at any point, it's not a formula
    #existential or universal FOL
    elif (len(fmla) > 2) and (fmla[0] in ['A', 'E']) and (fmla[1] in ['x', 'y', 'z', 'w']):
        #the part after the quantifier and variable must be a valid FOL formula
        sub_formula_type = parse(fmla[2:])
        if sub_formula_type != 0 and sub_formula_type < 6:
            return 3 if fmla[0] == 'A' else 4  # universal or existential
        else:
            return 0

    return 0

#method to find main connective
def mainConIndex(fmla):
    #a prop formula must be at least 4 characters in length and start/end with ()
    if (len(fmla) < 4) or (fmla[0] != '(') or (fmla[-1] != ')'):
        return -1
    stack = 0
    #Loop through fmla
    #Start at i=1, and end before last ), minus if (, plus if ), main connective at stack=0 
    for i in range(1, len(fmla)-1):
        char = fmla[i]

        if char == '(':
            stack += 1
        elif char == ')':
            stack -= 1

        elif stack == 0:
            if fmla[i:i+2] in ['->', '\/'] or char == '&':
                return i
    return -1

# Return the LHS of a binary connective formula
def lhs(fmla):
    if fmla.startswith('~'):
        fmla = fmla[1:]
    index = mainConIndex(fmla)
    if index != -1:
        return fmla[1:index]
    return ''

# Return the connective symbol of a binary connective formula
def con(fmla):
    index = mainConIndex(fmla)
    if index != -1:
        if fmla[index:index+2] == '->':
            return '->'
        elif fmla[index:index+2] == '\/':
            return '\/'
        else:
            return fmla[index]
    return ''

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    if fmla.startswith('~'):
        fmla = fmla[1:]
    index = mainConIndex(fmla)
    if index != -1:
        connective = con(fmla)
        # The RHS starts after the connective
        start_of_rhs = index + len(connective)
        return fmla[start_of_rhs:-1]
    return ''


# You may choose to represent a theory as a set or a list
def theory(fmla):
    #sets for fast lookups and no duplicates
    return {fmla}

_next_constant_index = 0

#helper function to generate a new constant
def generate_new_constant():
    global _next_constant_index
    const = f'c{_next_constant_index}' #c1, c2, c3, ...
    _next_constant_index += 1
    return const

#helper function to extract unique constants from a branch
def get_constants_from_branch(branch_formulas):
    all_text = "".join(branch_formulas)
    found_consts = set()
    for i, char in enumerate(all_text):
        if char == 'c':
            constNum = ""
            j = i + 1 #checks the imm next character for a number
            while j < len(all_text) and all_text[j].isdigit():
                constNum += all_text[j]
                j += 1
            if constNum:
                found_consts.add(f'c{constNum}')
    return found_consts

#helper function to substitute free variables with a term
def substitute(fmla, var, term):
    return fmla.replace(var, term)

# --- Branch Rules ---

def apply_alpha_rule(fmla, branch_formulas): #fmla = formula to expand, branch_formulas = the formula popped from the queue
    formulas = branch_formulas - {fmla} #this is the set of fmla that we will return to add into the queue
    # print("branch_formula:", branch_formulas)
    # print("formula to branch:", fmla)
    print("This is an alpha rule:", formulas, "fmla to work on:",fmla)
    if con(fmla) == '&': # (A & B)
        formulas.add(lhs(fmla))
        formulas.add(rhs(fmla))

    sub_fmla = fmla[1:] #It's a negation!
    if fmla.startswith('~(') and con(sub_fmla) == '\/': # ~(A V B)
        formulas.add(f'~{lhs(fmla)}')
        formulas.add(f'~{rhs(fmla)}')
    elif fmla.startswith('~(') and con(sub_fmla) == '->': # ~(A -> B)
        formulas.add(lhs(fmla))
        formulas.add(f'~{rhs(fmla)}')
        
    return [formulas]

def apply_beta_rule(fmla, branch_formulas):
    base_formulas = branch_formulas - {fmla}
    branch1, branch2 = set(base_formulas), set(base_formulas)
    print("this is a beta rule:",base_formulas, "fmla to work on:",fmla)
    if con(fmla) == '\/': # (A V B)
        branch1.add(lhs(fmla))
        branch2.add(rhs(fmla))
    elif con(fmla) == '->': # (A -> B)
        branch1.add(f'~{lhs(fmla)}')
        branch2.add(rhs(fmla))
    sub_fmla = fmla[1:]
    if fmla.startswith('~(') and con(sub_fmla) == '&': # ~(A & B)
        branch1.add(f'~{lhs(fmla)}')
        branch2.add(f'~{rhs(fmla)}')
    print("result of beta op:", branch1, branch2)
    return [branch1, branch2]

def apply_delta_rule(fmla, branch_formulas, branch_new_constants):
    formulas = branch_formulas - {fmla}
    new_const = generate_new_constant()
    print("this is a delta rule:", formulas, "fmla to work on:", fmla)
    
    var = fmla[1] # e.g., 'x' from 'ExP(x,y)'
    sub_fmla = fmla[2:]
    
    if fmla.startswith('E'): # ExF(x)
        formulas.add(substitute(sub_fmla, var, new_const))
    sub_fmla = fmla[3:]
    if fmla.startswith('~A'): # ~AxF(x)
        formulas.add(f'~{substitute(sub_fmla, var, new_const)}')
        
    return [(formulas, branch_new_constants | {new_const})]

def apply_gamma_rule(fmla, branch_formulas):
    # We don't tick the fmla after a gamma rule so no branch_formulas-{fmla}
    print("this is a gamma rule:",branch_formulas,"fmla:",fmla)
    
    constants_on_branch = get_constants_from_branch(branch_formulas)

    if not constants_on_branch:
        return [branch_formulas]
        
    var = fmla[1]
    sub_fmla = fmla[2:]

    if fmla.startswith('A'): # AxF(x)
        for c in constants_on_branch:
            branch_formulas.add(substitute(sub_fmla, var, c))
    sub_fmla = fmla[3:]
    if fmla.startswith('~E'): # ~ExF(x)
        for c in constants_on_branch:
            branch_formulas.add(f'~{substitute(sub_fmla, var, c)}')
            
    return [branch_formulas]

#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    global _next_constant_index
    _next_constant_index = 0
    
    # The queue will store tuples of: (set_of_formulas, set_of_new_constants)
    queue = [(set(branch), set()) for branch in tableau]
    print("original queue:",queue) #delete
    
    processed_branches = set()
    undetermined_branch_found = False #if MAX_CONSTANT reached, set to true

    while queue:
        branch_formulas, branch_new_constants = queue.pop(0)

        #Add this state of the branch to the processed_branch and skip if we've already processed this branch
        current_state = (frozenset(branch_formulas), frozenset(branch_new_constants))
        if current_state in processed_branches:
            continue
        processed_branches.add(current_state)

        # 1. Check for contradictions
        has_contradiction = False
        literals = {f for f in branch_formulas if parse(f) in [1, 2, 6, 7]}
        for lit in literals:
            if lit.startswith('~') and lit[1:] in literals:
                has_contradiction = True
                break
            elif f'~{lit}' in literals:
                has_contradiction = True
                break
        if has_contradiction:
            continue

        # 2. Check for constant limit
        if len(branch_new_constants) > MAX_CONSTANTS:
            undetermined_branch_found = True
            continue

        # 3. Find a formula to expand
        formula_to_expand = None
        for fmla in branch_formulas:
            # Fair schedule of operations: alpha, beta, delta, gamma
            if con(fmla) in ['&', '\/', '->']: #alpha or beta rule
                formula_to_expand = fmla
                break
        if not formula_to_expand:
            for fmla in branch_formulas:
                if parse(fmla) in [4, 2] and fmla.startswith(('E','~A')): #delta rule
                    formula_to_expand = fmla
                    break
        # Pick any remaining non-literal if the prioritized ones are not found
        if not formula_to_expand:
            for fmla in branch_formulas:
                 if parse(fmla) not in [0, 1, 6]: # if not an atom or literal
                    #it might still be a negation of a proposition or atom
                    if parse(fmla[1:]) in [1,6]:
                        break
                    formula_to_expand = fmla
                    break
        
        # If no formula was found, the branch is fully expanded and open
        if not formula_to_expand:
            return 1 # SATISFIABLE
        
        #no need to filter for if parse = 0 because the function below calling sat already does that.

        # 4. Apply rules and enqueue new branches
        new_branches = []
        p_type = parse(formula_to_expand)
        print("fmla to expand:",formula_to_expand,"p_type:",p_type, "con", con(formula_to_expand))
        
        # Alpha rules
        if (con(formula_to_expand) == '&') or \
           (formula_to_expand.startswith('~') and con(formula_to_expand[1:]) in ['\/','->']):
            new_formulas = apply_alpha_rule(formula_to_expand, branch_formulas)
            for f in new_formulas:
                new_branches.append((f, branch_new_constants))

        # Beta rules
        elif (con(formula_to_expand) in ['\/', '->']) or \
             (formula_to_expand.startswith('~') and con(formula_to_expand[1:]) == '&'):
            new_formulas_list = apply_beta_rule(formula_to_expand, branch_formulas)
            for f in new_formulas_list:
                new_branches.append((f, branch_new_constants))       

        # Delta rules
        elif formula_to_expand.startswith('~A' or 'E'):
            # Pass and receive the set of new constants for this branch
            new_branches.extend(apply_delta_rule(formula_to_expand, branch_formulas, branch_new_constants))

        # Gamma rules
        elif formula_to_expand.startswith('~E' or 'A'):
            new_formulas = apply_gamma_rule(formula_to_expand, branch_formulas)
            for f in new_formulas:
                new_branches.append((f, branch_new_constants))

        #if it's a negation (of a negation..) of a proposition or atom
        elif p_type in [2,7] and con(formula_to_expand) =='':
            sub_fmla = formula_to_expand[1:]
            if parse(sub_fmla) != 6:
                new_branches = [({sub_fmla},branch_new_constants)]
            else: new_branches = [({formula_to_expand},branch_new_constants)]
            
        # Enqueue all newly generated branches
        print("new branches to add to queue:", new_branches)
        for br_f, br_c in new_branches:
            queue.append((br_f, br_c))
        
        print("queue result:",queue) #delete this later
            
    # If the queue is empty, check if we bailed on any branch
    if undetermined_branch_found:
        return 2 # MAYBE SATISFIABLE

    return 0 # NOT SATISFIABLE

#------------------------------------------------------------------------------------------------------------------------------:
#                                            DO NOT MODIFY THE CODE BELOW THIS LINE!                                           :
#------------------------------------------------------------------------------------------------------------------------------:

f = open('testCase.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
