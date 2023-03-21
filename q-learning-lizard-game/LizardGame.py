#!/usr/bin/env python

# From this video "Exploration vs. Exploitation - Learning the Optimal
# Reinforcement Learning Policy"
# https://www.youtube.com/watch?v=mo96Nqlo1L8

# The game is called the "lizard game" from this video [1] and has a simple 3x3
# grid where the agent (a lizard) starts in the bottom left and moves about,
# trying to maximize rewards:
# 
#    +------------------+------------------+------------------+
# 2  |       crickets(1)|                  |                  |
#    +------------------+------------------+------------------+
# 1  |                  |              bird|                  |
#    +------------------+------------------+------------------+
# 0  |            lizard|                  |       crickets(5)|
#    +------------------+------------------+------------------+
#              0                  1                  2
# 
# The rewards are simple:
# 
#     moving into an empty spot yields -1
#     moving into crickets(1) yields +2
#     moving into crickets(5) yields +10 and terminates the episode
#     moving into bird yields -10 and terminates the episode
# 
# The actions are left, right, up, down.

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

