#!/usr/bin/env python

# From this video "Exploration vs. Exploitation - Learning the Optimal
# Reinforcement Learning Policy"
# https://www.youtube.com/watch?v=mo96Nqlo1L8

# The game is called the "lizard game" from this video [1] and has a simple 3x3
# grid where the agent (a lizard) starts in the bottom left and moves about,
# trying to maximize rewards:
#
#    +------------------+------------------+------------------+
# 2  |        1 cricket |                  |                  |
#    +------------------+------------------+------------------+
# 1  |                  |             bird |                  |
#    +------------------+------------------+------------------+
# 0  |           lizard |                  |       5 crickets |
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
        # *GAME* state (the actual game state, the "territory", not the Q-learning state)
        self.environment = {(0,0): None,
                            (0,1): None,
                            (0,2): 'C', # 1 cricket
                            (1,0): None,
                            (1,1): 'B', # 1 bird
                            (1,2): None,
                            (2,0): 'CCCCC', # 5 crickets
                            (2,1): None,
                            (2,2): None}

        # *AGENT* state (the simplified, abstracted game state, the "map", the vertices of the MDP graph)
        self.state = (0,0)

    # return possible agent states (state vertices in the MDP)
    def states(self):
        return set([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)])

    # return possible agent actions from a given agent state (outgoing edges in the MDP)
    def actions(self, state=None):
        if state == None:
            state = self.state

        return {(0,0): {'right', 'up'},
                (0,1): {'right', 'up', 'down'},
                (0,2): {'right', 'down'},
                (1,0): {'right', 'left', 'up'},
                (1,1): set(),
                (1,2): {'left', 'right', 'down'},
                (2,0): set(),
                (2,1): {'left', 'up', 'down'},
                (2,2): {'left', 'down'}}[state]

    # returns (state, reward) pair
    def transition(self, action):
        # calculate the destination
        assert action in self.actions()
        dx, dy = {'left':(-1, 0), 'right':(1,0), 'up':(0,1), 'down':(0,-1)}[action]
        destination = (self.state[0]+dx, self.state[1]+dy)

        # calculate the reward
        match self.environment[destination]:
            case 'B': reward = -10
            case 'C': reward = 2
            case 'CCCCC': reward = 10
            case _: reward = -1

        # consume the cricket
        if destination == (0,2):
            self.environment[(0,2)] = None

        # save new agent state
        self.state = destination

        return (self.state, reward)

    def ends(self):
        return self.state == (1,1) or self.state == (2,0) # position of bird or the 10 crickets

    def __str__(self):
        lines = []
        lines.append('+------------------+------------------+------------------+')
        for y in range(3-1, 0-1, -1): # height-1, height-2, ..., 0
            tokens = []
            for x in range(0, 3): # 0, 1, ..., width-1
                contents = []
                position = (x,y)
                if self.environment[position] == 'C': contents.append('crickets(1)')
                if self.environment[position] == 'B': contents.append('bird')
                if self.environment[position] == 'CCCCC': contents.append('crickets(5)')
                if position == self.state: contents.append('lizard')
                tokens.append(','.join(contents).rjust(18))
            lines.append('|' + '|'.join(tokens) + '|')
            lines.append('+------------------+------------------+------------------+')
        return '\n'.join(lines)

