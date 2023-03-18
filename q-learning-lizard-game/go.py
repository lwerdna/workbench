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

class Game():
    def __init__(self):
        self.dimensions = (3, 3)

        # Cartesian view
        self.cells = {  (2,0): 'crickets(5)',
                        (1,1): 'bird',
                        (0,2): 'crickets(1)'
                    }

        self.lizard_loc = (0, 0)

    def move(self, move):
        dx, dy = 0, 0
        match move:
            case 'left':
                dx = -1
            case 'right':
                dx = 1
            case 'up':
                dy = 1
            case 'down':
                dy = -1

        new_loc = (self.lizard_loc[0]+dx, self.lizard_loc[1]+dy)

        if new_loc[0] >= 0 and new_loc[0] < 3 and \
           new_loc[1] >= 0 and new_loc[1] < 3:
            self.lizard_loc = new_loc 

    def reward(self, position=None):
        if position == None:
            position = self.lizard_loc

        if position in self.cells:
            item = self.cells[position]

            if item == 'bird':
                return -10
            elif m := re.match(r'^crickets\((\d+)\)$', item):
                crickets_n = int(m.group(1))
                return 2 * crickets_n
            else:
                assert False, f'unknown item: {item}'
        else:
            return -1
            
    def state(self):
        return str(self.lizard_loc) 

    def __str__(self):
        return 'lizard at: ' + self.state() + ' which rewards ' + str(self.reward())

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
    states_n = game.dimensions[0] * game.dimensions[1]

    q_table = {(x,y): {'left':0, 'right':0, 'up':0, 'down':0} for x in range(game.dimensions[0]) for y in range(game.dimensions[1])}

    for episode in range(num_episodes):
        g = Game()

        print(f'---- episode {episode} start ----')
        pprint.pprint(q_table)
        print(g)

        for step in range(max_steps_per_episode):
            print('---- getting move ----')
            action = get_action_from_user()
            if not action in ['left', 'right', 'up', 'down']:
                sys.exit(-1)

            q_current = q_table[g.lizard_loc][action]

            position_current = g.lizard_loc
            g.move(action)
            reward = g.reward()

            q_new = reward + discount_rate * max(q_table[g.lizard_loc].values())

            update = (1-learning_rate)*q_current + learning_rate*q_new
            q_table[position_current][action] = update

            print(f'   action: {action} moves agent {position_current} -> {g.lizard_loc} for reward {reward}')
            print(f'q_current: {q_current}')
            print(f'    q_new: {q_new}')
            print(f'  updated: {update}')

            pprint.pprint(q_table)
            print(g)

            if abs(reward) >= 10:
                print('EXITING EPISODE')
                break

