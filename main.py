from collections import OrderedDict
import networkx as nx
import matplotlib.pyplot as plt

class ASTNode:
    def __init__(self, type, value=None):
        self.type = type
        self.value = type
        self.children = []

    def add_child(self, child):
        self.children.append(child)

# AST building function
def build_ast(grammar, symbol, remaining_input):
    node = ASTNode(symbol)
    productions = grammar.get(symbol, [])

    for production in productions:
        current_node = node
        current_input = remaining_input

        for symbol in production:
            if symbol.isupper():  # Non-terminal
                child_node, consumed_input = build_ast(grammar, symbol, current_input)
                current_node.children.append(child_node)
                current_node = child_node
                current_input = consumed_input
            else:  # Terminal
                if current_input.startswith(symbol):
                    current_node.children.append(ASTNode(symbol, symbol))
                    current_input = current_input[len(symbol):]
                else:
                    # Error handling, symbol in input does not match grammar
                    break

        # If we successfully matched a production, return the AST and the remaining input
        else:
            return node, current_input

    # If no production matches, return the partial AST and the remaining input
    return node, remaining_input

# AST visualization function
def visualize_ast(root):
    graph = nx.DiGraph()
    visualize_ast_recursive(graph, None, root)
    pos = nx.spring_layout(graph)
    labels = {node: data['label'] for node, data in graph.nodes(data=True)}
    nx.draw(graph, pos, labels=labels, with_labels=True, node_size=3000, node_color="skyblue")
    plt.title("Abstract Syntax Tree (AST)")
    plt.show()

# Recursive AST visualization function
def visualize_ast_recursive(graph, parent_name, node, depth=1):
    if isinstance(node, ASTNode):
        node_name = f"{node.type}_{id(node)}"
        graph.add_node(node_name, label=node.value)
    elif isinstance(node, tuple):
        node_name = f"{node[0]}_{id(node)}"
        label = node[1] if len(node) > 1 else None
        graph.add_node(node_name, label=label)
    else:
        node_name = f"unknown_{id(node)}"
        graph.add_node(node_name, label=str(node))

    if parent_name is not None:
        graph.add_edge(parent_name, node_name)

    if isinstance(node, (ASTNode, tuple)) and hasattr(node, 'children'):
        for child in node.children if isinstance(node, ASTNode) else node[2]:
            visualize_ast_recursive(graph, node_name, child, depth + 1)

    return graph

def isterminal(char):
    if char.isupper() or char == "e":
        return False
    else:
        return True


def insert(grammar, lhs, rhs):
    if lhs in grammar and rhs not in grammar[lhs] and grammar[lhs] != "null":
        grammar[lhs].append(rhs)
    elif lhs not in grammar or grammar[lhs] == "null":
        grammar[lhs] = [rhs]
    return grammar


def find_epsilon_nonterminals(grammar):
    epsilon_nonterminals = set()
    for lhs, rhs_list in grammar.items():
        for rhs in rhs_list:
            if "e" in rhs:
                epsilon_nonterminals.add(lhs)
    while True:
        prev_epsilon_nonterminals = set(epsilon_nonterminals)
        for lhs, rhs_list in grammar.items():
            for rhs in rhs_list:
                if all(nonterminal in epsilon_nonterminals for nonterminal in rhs):
                    epsilon_nonterminals.add(lhs)
        if prev_epsilon_nonterminals == epsilon_nonterminals:
            break
    return epsilon_nonterminals


def first(lhs, grammar, grammar_first):
    rhs = grammar[lhs]
    for i in rhs:
        k = 0
        flag = 0
        current = []
        confirm = 0
        flog = 0
        if lhs in grammar and "e" in grammar_first[lhs]:
            flog = 1
        while 1:
            check = []
            if k >= len(i):
                if len(current) == 0 or flag == 1 or confirm == k or flog == 1:
                    grammar_first = insert(grammar_first, lhs, "e")
                break
            if i[k].isupper():
                if grammar_first[i[k]] == "null":
                    grammar_first = first(i[k], grammar, grammar_first)
                # print("state ", lhs, "i ", i, "k, ", k, grammar_first[i[k]])
                for j in grammar_first[i[k]]:
                    grammar_first = insert(grammar_first, lhs, j)
                    check.append(j)
            else:
                grammar_first = insert(grammar_first, lhs, i[k])
                check.append(i[k])
            if i[k] == "e":
                flag = 1
            current.extend(check)
            if "e" not in check:
                if flog == 1:
                    grammar_first = insert(grammar_first, lhs, "e")
                break
            else:
                confirm += 1
                k += 1
                grammar_first[lhs].remove("e")
    return grammar_first


def rec_follow(k, next_i, grammar_follow, i, grammar, start, grammar_first, lhs):
    if len(k) == next_i:
        if grammar_follow[i] == "null":
            grammar_follow = follow(i, grammar, grammar_follow, start)
        for q in grammar_follow[i]:
            grammar_follow = insert(grammar_follow, lhs, q)
    else:
        if k[next_i].isupper():
            for q in grammar_first[k[next_i]]:
                if q == "e":
                    grammar_follow = rec_follow(k, next_i + 1, grammar_follow, i, grammar, start, grammar_first, lhs)
                else:
                    grammar_follow = insert(grammar_follow, lhs, q)
        else:
            grammar_follow = insert(grammar_follow, lhs, k[next_i])

    return grammar_follow


def follow(lhs, grammar, grammar_follow, start):
    for i in grammar:
        j = grammar[i]
        for k in j:
            if lhs in k:
                next_i = k.index(lhs) + 1
                grammar_follow = rec_follow(k, next_i, grammar_follow, i, grammar, start, grammar_first, lhs)
    if lhs == start:
        grammar_follow = insert(grammar_follow, lhs, "$")
    return grammar_follow


def show_dict(dictionary):
    for key in dictionary.keys():
        print(key + "  :  ", end="")
        for item in dictionary[key]:
            if item == "e":
                print("Epsilon, ", end="")
            else:
                print(item + ", ", end="")
        print("\b\b")


def get_rule(non_terminal, terminal, grammar, grammar_first):
    for rhs in grammar[non_terminal]:
        # print(rhs)
        for rule in rhs:
            if rule == terminal:
                string = non_terminal + "-" + rhs
                return string

            elif rule.isupper() and terminal in grammar_first[rule]:
                string = non_terminal + "-" + rhs
                return string


def generate_parse_table(terminals, non_terminals, grammar, grammar_first, grammar_follow):
    parse_table = [[""] * len(terminals) for i in range(len(non_terminals))]

    for non_terminal in non_terminals:
        for terminal in terminals:
            # print(terminal)
            # print(grammar_first[non_terminal])
            if terminal in grammar_first[non_terminal]:
                rule = get_rule(non_terminal, terminal, grammar, grammar_first)
                # print(rule)

            elif "e" in grammar_first[non_terminal] and terminal in grammar_follow[non_terminal]:
                rule = non_terminal + "-e"

            elif terminal in grammar_follow[non_terminal]:
                rule = "Sync"

            else:
                rule = ""

            parse_table[non_terminals.index(non_terminal)][terminals.index(terminal)] = rule

    return parse_table


def display_parse_table(parse_table, terminal, non_terminal):
    print("\t\t\t\t", end="")
    for terminal in terminals:
        print(terminal + "\t\t", end="")
    print("\n")

    for non_terminal in non_terminals:
        print("\t\t" + non_terminal + "\t\t", end="")
        for terminal in terminals:
            print(parse_table[non_terminals.index(non_terminal)][terminals.index(terminal)] + "\t\t", end="")
        print("\n")


def parse(expr, parse_table, terminals, non_terminals):
    stack = ["$"]
    stack.insert(0, non_terminals[0])

    print("\t\t\tMatched\t\t\tStack\t\t\tInput\t\t\tAction\n")
    print("\t\t\t-\t\t\t", end="")
    for i in stack:
        print(i, end="")
    print("\t\t\t", end="")
    print(expr + "\t\t\t", end="")
    print("-")

    matched = "-"
    while True:
        action = "-"

        if stack[0] == expr[0] and stack[0] == "$":
            break

        elif stack[0] == expr[0]:
            if matched == "-":
                matched = expr[0]
            else:
                matched = matched + expr[0]
            action = "Matched " + expr[0]
            expr = expr[1:]
            stack.pop(0)

        else:
            action = parse_table[non_terminals.index(stack[0])][terminals.index(expr[0])]
            stack.pop(0)
            i = 0
            for item in action[2:]:
                if item != "e":
                    stack.insert(i, item)
                i += 1

        print("\t\t\t" + matched + "\t\t\t", end="")
        for i in stack:
            print(i, end="")
        print("\t\t\t", end="")
        print(expr + "\t\t\t", end="")
        print(action)


grammar = OrderedDict()
grammar_first = OrderedDict()
grammar_follow = OrderedDict()

f = open('grammar.txt')
for i in f:
    i = i.replace("\n", "")
    lhs = ""
    rhs = ""
    flag = 1
    for j in i:
        if j == "-":
            flag = (flag + 1) % 2
            continue
        if flag == 1:
            lhs += j
        else:
            rhs += j
    grammar = insert(grammar, lhs, rhs)
    grammar_first[lhs] = "null"
    grammar_follow[lhs] = "null"

print("Grammar\n")
show_dict(grammar)

epsilon_nonterminals = find_epsilon_nonterminals(grammar)
print("\nEpsilon Non-terminals:", epsilon_nonterminals)

for lhs in grammar:
    if grammar_first[lhs] == "null":
        grammar_first = first(lhs, grammar, grammar_first)

print("\nFirst\n")
show_dict(grammar_first)

start = list(grammar.keys())[0]
for lhs in grammar:
    if grammar_follow[lhs] == "null":
        grammar_follow = follow(lhs, grammar, grammar_follow, start)

print("\n")
print("Follow\n")
show_dict(grammar_follow)

non_terminals = list(grammar.keys())
terminals = []

for i in grammar:
    for rule in grammar[i]:
        for char in rule:

            if isterminal(char) and char not in terminals:
                terminals.append(char)

terminals.append("$")

# print(non_terminals)
# print(terminals)

print("\n\t\t\t\t\t\t\tParse Table\n")
parse_table = generate_parse_table(terminals, non_terminals, grammar, grammar_first, grammar_follow)
display_parse_table(parse_table, terminals, non_terminals)

# expr = input("Enter the expression ending with $ : ")
expr = "a+a*a$"

print("\t\t\t\t\t\t\tParsing Expression\n")
parse(expr, parse_table, terminals, non_terminals)
ast_root, remaining_input = build_ast(grammar, start, expr)

visualize_ast(ast_root)
