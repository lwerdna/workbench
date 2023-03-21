#!/usr/bin/env python

import re
import sys
import pprint

num_episodes = 10000
max_steps_per_episode = 100

learning_rate = .7 # "alpha", how quickly adopts new q-value (factor of weighted sum)
discount_rate = .99 # "gamma", importance of future rewards (0 means only consider current rewards)

exploration_rate = 1 # "epsilon"
max_exploration_rate = 1
min_exploration_rate = .01
exploration_decay_rate = .01

#    +------------------+------------------+------------------+
# 2  |       crickets(1)|                  |                  |
#    +------------------+------------------+------------------+
# 1  |                  |              bird|                  |
#    +------------------+------------------+------------------+
# 0  |            lizard|                  |       crickets(5)|
#    +------------------+------------------+------------------+
#              0                  1                  2
class Game():
    def __init__(self):
        pass

    # return possible states, the first is the start state
    def states(self):
        return [(x,y) for x in range(3) for y in range(3)]

    def actions(self, state):
        return {(0,0): {'right', 'up'},
                (0,1): {'right', 'up', 'down'},
                (0,2): {'right', 'down'},
                (1,0): {'right', 'left', 'up'},
                (1,1): {'left', 'right', 'up', 'down'},
                (1,2): {'left', 'right', 'down'},
                (2,0): {'left', 'up'},
                (2,1): {'left', 'up', 'down'},
                (2,2): {'left', 'down'}}[state]

    def reward(self, state):
        lookup = {(2,0): 10, (1,1): -10, (0,2): 2}
        return lookup.get(state, -1)

    def transition(self, state, action):
        dx, dy = {'left':(-1, 0), 'right':(1,0), 'up':(0,1), 'down':(0,-1)}[action]

        result = (state[0]+dx, state[1]+dy)

        # assume caller used only legal actions
        assert result[0] >= 0 and result[0] < 3 and result[1] >= 0 and result[1] < 3

        return result

    def ends(self, state):
        return state == (1,1) or state == (2,0) # position of bird or the 10 crickets

    def draw(self, state):
        lines = []
        lines.append('+------------------+------------------+------------------+')
        for y in range(3-1, 0-1, -1): # height-1, height-2, ..., 0
            tokens = []
            for x in range(0, 3): # 0, 1, ..., width-1
                contents = []
                if (x,y)==(0,2): contents.append('crickets(1)')
                if (x,y)==(1,1): contents.append('bird')
                if (x,y)==(2,0): contents.append('crickets(5)')
                if (x,y)==state: contents.append('lizard')
                tokens.append(','.join(contents).rjust(18))
            lines.append('|' + '|'.join(tokens) + '|')
            lines.append('+------------------+------------------+------------------+')
        return '\n'.join(lines)

def get_action_from_user():
    import getch

    ch0 = getch.getch()
    if ord(ch0) == 27: # ESC \x1B
        ch1 = getch.getch()
        if ch1 == '[':
            ch2 = getch.getch()
            if ch2 == 'A': return 'up'
            if ch2 == 'B': return 'down'
            if ch2 == 'C': return 'right'
            if ch2 == 'D': return 'left'
    else:
        return ch0

if __name__ == '__main__':
    game = Game()

    states_possible = game.states()
    state_init = states_possible[0]

    q_table = {s: {a:0 for a in game.actions(s)} for s in game.states()}
    pprint.pprint(q_table)

    for episode in range(num_episodes):
        state = state_init

        print(f'---- episode {episode} start ----')
        pprint.pprint(q_table)
        print(game.draw(state))

        for step in range(max_steps_per_episode):
            print('---- getting action ----')
            action = get_action_from_user()

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

            if game.ends(state_next):
                print('ENDING EPISODE')
                break

            state = state_next

