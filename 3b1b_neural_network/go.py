#!/usr/bin/env python

default_weight = .5

TESTING = True
if TESTING:
    layer0_size = 3
    layer1_size = 3
    layer2_size = 3
    layer3_size = 3
else:
    layer0_size = 10
    layer1_size = 10
    layer2_size = 10
    layer3_size = 10

import math
import random

def sigmoid(x):
    return 1 / (1+math.e ** (-x))

class Thing:
    def __init__(self, layer, index):
        self.layer = layer
        self.index = index

    def dot_id(self):
        return f'n_{self.layer}_{self.index}'
    def dot_label(self):
        return f'{self.layer}-{self.index}'
    def dot_extra_attributes(self):
        return ''

class Pixel(Thing):
    def __init__(self, layer, index, initial_value):
        super().__init__(layer, index)

        self.activation = random.random()
        self.connections = []

    def calculate_activation(self):
        print(f'// {self} calculate my activation to: {self.activation}')
        return self.activation

    def dot_label(self):
        return str(self.activation)

    def dot_extra_attributes(self):
        return 'shape="rectangle"'

    def __str__(self):
        return f'pixel_{self.layer}_{self.index}'

class Neuron(Thing):
    def __init__(self, layer, index):
        super().__init__(layer, index)

        self.connections = []
        self.weights = []
        self.activation = 0
        self.bias = 0

    def calculate_activation(self):
        result = 0
        for i in range(len(self.connections)):
            result = result + self.weights[i] * self.connections[i].activation
        result = result + self.bias

        # squishify
        result = sigmoid(result)

        # cache and return the result
        self.activation = result

        print(f'// {self} calculate my activation to: {self.activation}')

        return result

    def dot_label(self):
        return str(round(self.activation, 2))

    def __str__(self):
        return f'neuron_{self.layer}_{self.index}'

def generate_random_weights(n):
    result = []
    for i in range(n):
        result.append(random.random())
    return result

def setup_neural_network():
    layer0 = []
    for i in range(layer1_size):
        n = Pixel(0, i, .5)
        layer0.append(n)

    layer1 = []
    for i in range(layer1_size):
        n = Neuron(1, i)
        n.connections = layer0
        n.weights = generate_random_weights(len(layer0))
        layer1.append(n)

    layer2 = []
    for i in range(layer2_size):
        n = Neuron(2, i)
        n.connections = layer1
        n.weights = generate_random_weights(len(layer1))
        layer2.append(n)

    layer3 = []
    for i in range(layer3_size):
        n = Neuron(3, i)
        n.connections = layer2
        n.weights = generate_random_weights(len(layer2))
        layer3.append(n)

    return [layer0, layer1, layer2, layer3]

def draw_neural_network(network):
    print('digraph whatever')
    print('{')
    print('\trankdir="RL"')

    allnodes = []
    for layer in network:
        allnodes = allnodes + layer
    for n in allnodes:
        print(f'\t{n.dot_id()} [label="{n.dot_label()}"{n.dot_extra_attributes()}];')

    for source in allnodes:
        for i in range(len(source.connections)):
            dest = source.connections[i]
            weight = source.weights[i]
            print(f'\t{source.dot_id()} -> {dest.dot_id()} [label="{round(weight, 2)}"];')

    print('}')

def evaluate_neural_network(network):
    # heavy calculation
    for layer in network:
        for node in layer:
            node.calculate_activation()

    # which has greatest activation?
    last_layer = network[len(network)-1]

    record = 0
    record_holder = None
    for neuron in last_layer:
        if neuron.activation > record:
            record = neuron.activation
            record_holder = neuron

    return record_holder.index

nn = setup_neural_network()
result = evaluate_neural_network(nn)
print(f'// result: {result}')

if TESTING:
    draw_neural_network(nn)
