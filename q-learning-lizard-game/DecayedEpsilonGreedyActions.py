import random

epsilon_max = 1
epsilon_min = .01

def get_action(q_table, state, progress):
    global exploration_rate, epislon_floor

    actions = q_table[state].keys()

    epsilon = epsilon_max - progress*(epsilon_max - epsilon_min)

    if random.random() < epsilon:
        result = random.choice(list(q_table[state]))
        print('choosing random from {action_value_pairs} returns {result}')
    else:
        action_value_pairs = sorted(q_table[state], key=lambda k:q_table[state][k], reverse=True)
        result = action_value_pairs[0]
        print('best action/value pairs: {action_value_pairs} returns {result}')

    return result
