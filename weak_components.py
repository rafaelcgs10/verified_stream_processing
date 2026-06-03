#!/usr/bin/env python3


def weak_components(graph):
    labels = {}
    for node in graph:
        labels[node] = node

    for node in graph:
        assert labels[node] in reachable(graph, node)

    changed = True
    while changed:
        changed = False

        for node in graph:
            smallest = labels[node]

            for neighbor in graph[node]:
                if labels[neighbor] < smallest:
                    smallest = labels[neighbor]

            if smallest < labels[node]:
                labels[node] = smallest
                changed = True

        for node in graph:
            assert labels[node] in reachable(graph, node)

    return components_from_labels(labels)


def components_from_labels(labels):
    components = {}
    for node in labels:
        label = labels[node]

        if label not in components:
            components[label] = []

        components[label].append(node)

    return components

def reachable(graph, node):
    nodes = [node]

    for node in nodes:
        new_nodes = [n for n in graph[node] if n not in nodes]
        nodes.extend(new_nodes)

    return nodes
    

def main():
    graph = {
        1: [2],
        2: [1, 3],
        3: [2],
        4: [5],
        5: [4],
        6: [7, 8],
        7: [6, 8],
        8: [6, 7],
        9: [],
    }

    components = weak_components(graph)

    for label in sorted(components):
        print("component", label, ":", sorted(components[label]))

if __name__ == "__main__":
    main()
