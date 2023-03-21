import random

epsilon_max = 1
epsilon_min = .01

def get_action(q_table, state, progress):
    global epsilon_max, epsilon_min

    epsilon = epsilon_max - progress*(epsilon_max - epsilon_min)

    if random.random() < epsilon:
        options = list(q_table[state])
        result = random.choice(options)
        print(f'choosing random from {options} returns {result}')
    else:
        action_value_pairs = sorted(q_table[state], key=lambda k:q_table[state][k], reverse=True)
        result = action_value_pairs[0]
        print(f'best action/value pairs: {action_value_pairs} returns {result}')

    return result
