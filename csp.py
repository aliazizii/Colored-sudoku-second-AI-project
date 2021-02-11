import itertools
from typing import Generic, TypeVar, Dict, List, Optional
from abc import ABC, abstractmethod
from termcolor import colored
import copy
import time
import random

color_dict = {'r': 'red', 'b': 'blue', 'p': 'magenta', 'g': 'green', 'y': 'yellow', 'c': 'cyan', 'w': 'white'}
colorful_print = False
V = TypeVar('V')
D = TypeVar('D')

class Variable:
    def __init__(self, x: int, y: int):
        self.x = x
        self.y = y
    def __str__(self):
        return str(self.x) + "," + str(self.y)
    def __repr__(self):
        return str(self.x) + "," + str(self.y)
    def __eq__(self, other):
        return self.x == other.x and self.y == other.y
    def __hash__(self):
        return hash((self.x, self.y))

class Domain:
    def __init__(self, number: int, color: str):
        self.number = number
        self.color = color
    def __str__(self):
        return str(self.number) + self.color
    def __repr__(self):
        return str(self.number) + self.color

def color_forward_checking(vs: List[Variable], ds: Dict[V, List[D]], c):
    for v in vs:
        for i, element in enumerate(ds[v]):
            if element.color == c:
                ds[v][i] = -2
        while ds[v].count(-2) > 0:
            ds[v].remove(-2)

def color_priority_forward_checking(vs: List[Variable], ds: Dict[V, List[D]], value: Domain):
    for v in vs:
        for i, element in enumerate(ds[v]):
            flag1 = color_priority[element.color] < color_priority[value.color] and int(element.number) > int(value.number)
            flag2 = color_priority[element.color] > color_priority[value.color] and int(element.number) < int(value.number)
            if flag1 or flag2:
                ds[v][i] = -3
        while ds[v].count(-3) > 0:
            ds[v].remove(-3)


def number_forward_checking(vs: List[Variable], ds: Dict[V, List[D]], num):
    for v in vs:
        for i, element in enumerate(ds[v]):
            if int(element.number) == int(num):
                ds[v][i] = -1
        while ds[v].count(-1) > 0:
            ds[v].remove(-1)

# Base class for all constraints
class Constraint(Generic[V, D], ABC):
    # The variables that the constraint is between
    def __init__(self, variables: List[V]) -> None:
        self.variables = variables
    # Must be overridden by subclasses
    @abstractmethod
    def satisfied(self, assignment: Dict[V, D]) -> bool:
        ...

class CSP(Generic[V, D]):
    def __init__(self, variables: List[V], domains: Dict[V, List[D]]) -> None:
        self.variables: List[V] = variables # variables to be constrained
        self.domains: Dict[V, List[D]] = domains # domain of each variable
        self.constraints: Dict[V, List[Constraint[V, D]]] = {}
        for variable in self.variables:
            self.constraints[variable] = []
            if variable not in self.domains:
                raise LookupError("Every variable should have a domain assigned to it.")

    def add_constraint(self, constraint: Constraint[V, D]) -> None:
        for variable in constraint.variables:
            if variable not in self.variables:
                raise LookupError("Variable in constraint not in CSP")
            else:
                self.constraints[variable].append(constraint)

    # Check if the value assignment is consistent by checking all constraints
    # for the given variable against it
    def consistent(self, variable: V, assignment: Dict[V, D]) -> bool:
        for constraint in self.constraints[variable]:
            if not constraint.satisfied(assignment):
                return False
        return True

    def minimum_remaining_values(self, unassigned: List[Variable], local_domain: Dict[V, List[D]]):
        unassigned.sort(key=lambda x: len(local_domain[x]))
        domain_len = []
        for v in unassigned:
            domain_len.append(len(local_domain[v]))
        c = domain_len.count(domain_len[0])
        return unassigned[:c]

    def degree(self, l: List[Variable]):
        l.sort(key=lambda x: len(self.constraints[x]), reverse=True)
        return l[0]

    def select(self, vs: List[Variable], ds: Dict[V, List[D]]):
        l = self.minimum_remaining_values(vs, ds)
        return self.degree(l)

    def is_failure(self, ds: Dict[V, List[D]]):
        keys = ds.keys()
        for v in keys:
            if len(ds[v]) == 0:
                return True
        return False

    def backtracking_search(self, ds: Dict[V, List[D]], assignment: Dict[V, D] = {}) -> Optional[Dict[V, D]]:
        # assignment is complete if every variable is assigned (our base case)
        if len(assignment) == len(self.variables):
            return assignment
        # get all variables in the CSP but not in the assignment
        unassigned: List[V] = [v for v in self.variables if v not in assignment]
        # get the every possible domain value of the first unassigned variable

        first: V = self.select(unassigned, ds)
        l = ds[first]
        shuffled = sorted(l, key=lambda k: random.random())

        for value in ds[first]:
            local_assignment = assignment.copy()

            local_assignment[first] = value
            # if we're still consistent, we recurse (continue)

            if self.consistent(first, local_assignment):
                local_domains = copy.deepcopy(ds)
                l2 = number_neighbors_dict[first]
                l1 = color_neighbors_dict[first]
                color_forward_checking(l1, local_domains, value.color)
                number_forward_checking(l2, local_domains, value.number)
                color_priority_forward_checking(l1, local_domains, value)

                if not self.is_failure(local_domains):
                    result: Optional[Dict[V, D]] = self.backtracking_search(local_domains, local_assignment)
                    # if we didn't find the result, we will end up backtracking
                    if result is not None:
                        return result
        return None

class different_color_constraint(Constraint[Variable, Variable]):
    def __init__(self, v1: Variable, v2: Variable) :
        super().__init__([v1, v2])
        self.v1 = v1
        self.v2 = v2
    def satisfied(self, assignment: Dict[V, D]) -> bool:
        if self.v1 not in assignment or self.v2 not in assignment:
            return True
        return assignment[self.v1].color != assignment[self.v2].color

class different_number_constraint(Constraint[Variable, Variable]):
    def __init__(self, v1: Variable, v2: Variable) :
        super().__init__([v1, v2])
        self.v1 = v1
        self.v2 = v2
    def satisfied(self, assignment: Dict[Variable, Domain]) -> bool:
        if self.v1 not in assignment or self.v2 not in assignment:
            return True
        x1 = int(assignment[self.v1].number)
        x2 = int(assignment[self.v2].number)
        return x1 != x2

color_priority = {}
class color_priority_constraint(Constraint[Variable, Variable]):
    def __init__(self, v1: Variable, v2: Variable) :
        super().__init__([v1, v2])
        self.v1 = v1
        self.v2 = v2
    def satisfied(self, assignment: Dict[V, D]) -> bool:
        if self.v1 not in assignment or self.v2 not in assignment:
            return True
        x1 = int(assignment[self.v1].number)
        x2 = int(assignment[self.v2].number)
        if x1 > x2:
            return color_priority[assignment[self.v1].color] > color_priority[assignment[self.v2].color]
        if x1 < x2:
            return color_priority[assignment[self.v1].color] < color_priority[assignment[self.v2].color]

def read_input():
    f = open("testcase.txt", "r")
    global m, n
    m, n = map(int, f.readline().split())
    nums = []
    for i in range(n):
        nums.append(int(i+1))
    global colors
    colors = f.readline().split()
    for i, c in enumerate(colors):
        color_priority[c] = len(colors) - i
    global initialization, domains, variables
    initialization = {}
    domains = {}
    variables = []
    for i in range(n):
        temp = f.readline().split()
        for j in range(n):
            v = Variable(i, j)
            variables.append(v)
            if temp[j][0] == '*' and temp[j][1] == '#':
                l = list(itertools.product(nums, colors))
                doms = []
                for p ,q in l:
                    d = Domain(p, q)
                    doms.append(d)
                domains[v] = doms
            elif temp[j][0] == '*' and temp[j][1] != '#':
                c = [temp[j][1]]
                l = list(itertools.product(nums, c))
                doms = []
                for p, q in l:
                    d = Domain(p, q)
                    doms.append(d)
                domains[v] = doms
            elif temp[j][0] != '*' and temp[j][-1] == '#':
                temp_list = ([temp[j][:-1]])
                strings = [str(integer) for integer in temp_list]
                a_string = "".join(strings)
                nn = int(a_string)
                l = list(itertools.product([nn], colors))
                doms = []
                for p, q in l:
                    d = Domain(p, q)
                    doms.append(d)
                domains[v] = doms
            else:
                d = Domain(temp[j][:-1], temp[j][-1])
                doms = [d]
                domains[v] = doms
                initialization[v] = d
number_neighbors_dict = {}
def number_neighbors(vs: List[Variable]):
    for v1 in vs:
        l = []
        for v2 in vs:
            if (v1.x == v2.x and v1.y != v2.y) or (v1.x != v2.x and v1.y == v2.y):
                l.append(v2)
        number_neighbors_dict[v1] = l

color_neighbors_dict = {}
def color_neighbors(vs: List[Variable]):
    for v1 in vs:
        l = []
        for v2 in vs:
            diff1 = abs(v1.x - v2.x)
            diff2 = abs(v1.y - v2.y)
            if (diff1 == 1 and diff2 == 0) or (diff2 == 1 and diff1 == 0):
                l.append(v2)
        color_neighbors_dict[v1] = l

def is_neighbor(v1: Variable, v2: Variable):
    diff1 = abs(v1.x - v2.x)
    diff2 = abs(v1.y - v2.y)
    return (diff1 == 1 and diff2 == 0) or (diff2 == 1 and diff1 == 0)

def get_res(assignment_dict: Dict[Variable, Variable]):
    res = []
    for v in variables :
        res.append(assignment_dict[v])
    return res

def print_res(l:List[Domain]):
    print(colored('Colored', 'blue'), colored('Sudoku', 'red'))
    print("\n")
    temp = 0
    for i in range(len(l)):
        if colorful_print:
            c = l[i].color
            color = color_dict[c]
            print(colored(l[i], color), end=" ")
        else:
            print(l[i], end=" ")
        temp += 1
        if temp == n:
            temp = 0
            print("\n")

def main():
    read_input()
    csp = CSP(variables, domains)
    number_neighbors(variables)
    color_neighbors(variables)

    for i in range(len(variables)):
        for j in range(i, len(variables)):
            if variables[i].x == variables[j].x and variables[i].y != variables[j].y:
                csp.add_constraint(different_number_constraint(variables[i], variables[j]))
            if variables[i].x != variables[j].x and variables[i].y == variables[j].y:
                csp.add_constraint(different_number_constraint(variables[i], variables[j]))

    for i in range(len(variables)):
        for j in range(i, len(variables)):
            if is_neighbor(variables[i], variables[j]):
                csp.add_constraint(different_color_constraint(variables[i], variables[j]))
                csp.add_constraint(color_priority_constraint(variables[i], variables[j]))

    s = csp.backtracking_search(domains, initialization)
    if s != None:
        res = get_res(s)
        print_res(res)
    else:
        print(colored('There is no solution for this problem', 'cyan'), colored(":(", 'red'))

if __name__ == '__main__':
    start_time = time.time()
    main()
    end_time = time.time()
    print("--- %s minutes and %s seconds ---" % (int((end_time - start_time) // 60), float((end_time - start_time) % 60)))