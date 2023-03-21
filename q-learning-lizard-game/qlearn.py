#!/usr/bin/env python

import re
import sys
import pprint
import importlib

num_episodes = 1000
max_steps_per_episode = 100

learning_rate = .7 # "alpha", how quickly adopts new q-value (factor of weighted sum)
discount_rate = .99 # "gamma", importance of future rewards (0 means only consider current rewards)

LOG = True

if __name__ == '__main__':
    # dynamically load game
    module_name = 'LizardGame'
    for arg in sys.argv[1:]:
        if arg.endswith('Game'):
            module_name = arg
    module = importlib.import_module(module_name)
    class_ref = getattr(module, 'Game')
    game = class_ref()

    # dynamically load action selection policy
    module_name = 'ManualActions'
    for arg in sys.argv[1:]:
        if arg.endswith('Actions'):
            module_name = arg
    action_select_module = importlib.import_module(module_name)

    # setup Q-learning
    states_possible = game.states()
    state_init = states_possible[0]

    q_table = {s: {a:0 for a in game.actions(s)} for s in game.states()}
    sa_pairs = sorted([(s,a) for s in q_table for a in q_table[s]])
    pprint.pprint(q_table)

    # start log
    fp_log = None
    if LOG:
        fp_log = open('./log.csv', 'w')
        fp_log.write(','.join([f'{p[0][0]}-{p[0][1]}-{p[1]}' for p in sa_pairs]) + '\n')

    for episode in range(num_episodes):
        state = state_init

        print(f'---- episode {episode} start ----')
        pprint.pprint(q_table)
        print(game.draw(state))
        if LOG:
            fp_log.write(','.join([str(q_table[s][a]) for (s, a) in sa_pairs]) + '\n')

        for step in range(max_steps_per_episode):
            print('---- getting action ----')
            progress = episode / num_episodes
            action = action_select_module.get_action(q_table, state, progress)

            if action == 'q':
                sys.exit(0)
            if not action in game.actions(state):
                print('INVALID ACTION')
                continue

            q_current = q_table[state].get(action, 0)

            state_next = game.transition(state, action)
            reward = game.reward(state_next)

            q_new = reward + discount_rate * max(q_table[state_next].values())

            update = (1-learning_rate)*q_current + learning_rate*q_new
            q_table[state][action] = update

            print(f'   action: {action} moves agent {state} -> {state_next} for reward {reward}')
            print(f'q_current: {q_current}')
            print(f'    q_new: {q_new}')
            print(f'  updated: {update}')

            pprint.pprint(q_table)

            print(game.draw(state_next))
            if LOG:
                fp_log.write(','.join([str(q_table[s][a]) for (s, a) in sa_pairs]) + '\n')

            if game.ends(state_next):
                print('ENDING EPISODE')
                break

            state = state_next

