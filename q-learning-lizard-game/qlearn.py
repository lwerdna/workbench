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
#LOG = False

if __name__ == '__main__':
    # dynamically load game
    module_name = 'LizardGame'
    for arg in sys.argv[1:]:
        if arg.endswith('Game'):
            module_name = arg
    module = importlib.import_module(module_name)
    Game = getattr(module, 'Game')
    game = Game()

    # dynamically load action selection policy
    module_name = 'ManualActions'
    for arg in sys.argv[1:]:
        if arg.endswith('Actions'):
            module_name = arg
    action_select_module = importlib.import_module(module_name)

    # setup Q-learning
    q_table = {s: {a:0 for a in game.actions(s)} for s in game.states()}
    sa_pairs = sorted([(s,a) for s in q_table for a in q_table[s]])

    # start log
    fp_log = None
    if LOG:
        fp_log = open('./log.csv', 'w')
        fp_log.write(','.join([f'{p[0][0]}-{p[0][1]}-{p[1]}' for p in sa_pairs]) + '\n')
        fp_log.write(','.join([str(round(q_table[s][a], 2)) for (s, a) in sa_pairs]) + '\n')

    for episode in range(num_episodes):
        game = Game()

        print(f'---- episode {episode} start ----')
        pprint.pprint(q_table)
        print(game)

        for step in range(max_steps_per_episode):
            state = game.state

            print('---- getting action ----')
            progress = episode / num_episodes
            action = action_select_module.get_action(q_table, state, progress)

            if action == 'q':
                sys.exit(0)
            if not action in game.actions():
                print('INVALID ACTION')
                continue

            (state_next, reward) = game.transition(action)

            # calculate Bellman
            q_current = q_table[state].get(action, 0)

            values = q_table[state_next].values()
            q_future = max(values) if values else 0

            q_new = reward + discount_rate * q_future
            update = (1-learning_rate)*q_current + learning_rate*q_new
            q_table[state][action] = update

            # output
            print(f'   action: {action} moves agent {state} -> {state_next} for reward {reward}')
            print(f'q_current: {q_current}')
            print(f'    q_new: {q_new}')
            print(f'  updated: {update}')

            pprint.pprint(q_table)

            print(game)
            if LOG:
                fp_log.write(','.join([str(round(q_table[s][a], 2)) for (s, a) in sa_pairs]) + '\n')

            if game.ends():
                print('ENDING EPISODE')
                break

    # print best path
    print('---- result ----')
    game = Game()
    state = game.state
    while not game.ends():
        aq_pairs = q_table[state]

        Q = max(aq_pairs.values())
        action = [a for a in aq_pairs if aq_pairs[a] == Q][0]
        print(f'at state {state} the best action is {action} with Q-value {Q}')
        (state, reward) = game.transition(action)
