#!/usr/bin/env python

import sys
import random

import gymnasium as gym

class QLearner():
    def __init__(self, alpha, gamma, states_n, actions_n):
        self.states_n = states_n
        self.actions_n = actions_n
        self.alpha = alpha # learning rate
        self.gamma = gamma # future discount
        self.reset()

    def update(self, state, action, reward, state_next):
        q_current = self.qtable[state][action]

        values = self.qtable[state_next]
        q_future = max(values)

        q_new = reward + self.gamma * q_future

        result = (1-self.alpha)*q_current + self.alpha*q_new
        self.qtable[state][action] = result

        if 0:
            print('')
            print(f'   action: {action}, state transition {state} -> {state_next} rewards {reward}')
            print(f'q_current: {q_current} (for this transition)')
            print(f' q_future: max({list(values)}) = {q_future}')
            print(f'    q_new: {reward} + {self.gamma}*{q_future} = {q_new}')
            print(f'   result: ({1-self.alpha}*{q_current} + {self.alpha}*{q_new} = {result}')
            print('')

        return result

    def reset(self):
        self.qtable = [[0.0] * self.actions_n for i in range(self.states_n)]

    def __str__(self):
        lines = []

        for row in self.qtable:
            svalues = [str(round(v, 4)).rjust(7) for v in row]
            line = ','.join(svalues)
            lines.append(line)

        return '\n'.join(lines)

class DecayedEpsilonGreedy():
    def __init__(self, epsilon_min, epsilon_max):
        self.epsilon_min = epsilon_min
        self.epsilon_max = epsilon_max

    def choose_action(self, qtable, state, progress):
        # reminder: 0,1,2,3 is left,down,right,up
        epsilon = self.epsilon_max - progress*(self.epsilon_max - self.epsilon_min)

        actions = list(range(len(qtable[0])))

        if random.random() < epsilon:
            result = random.choice(actions)
            print(f'choosing random action returns {result}')
        else:
            qbest = max(qtable[state])
            actions = [i for (i,q) in enumerate(qtable[state]) if q==qbest]
            result = random.choice(actions)
            print(f'choosing best action from {actions} which have q={qbest} returns {result}')

        return result

if __name__ == '__main__':
    ql = QLearner(.7, .99, 16, 4)
    deg = DecayedEpsilonGreedy(.01, 1)

    env = gym.make('FrozenLake-v1', map_name="4x4", is_slippery=False, render_mode='human')

    # convert an observation to a state id (here they're 1:1)
    def obs_to_state(obs):
        assert type(obs)==int and obs >= 0 and obs <= 15, breakpoint()
        return obs

    observation, info = env.reset()
    state = obs_to_state(observation)

    max_steps = 10000
    for step in range(max_steps):
        print('')
        print('--- step ---')
        action = deg.choose_action(ql.qtable, state, step / max_steps)

        observation, reward, terminated, truncated, info = env.step(action)
        state_next = obs_to_state(observation)
    
        ql.update(state, action, reward, state_next)
        print(ql)

        lookup = ['left', 'down', 'right', 'up']
        print(f'{state} --{lookup[action]}--> {state_next} is rewarded {reward}')
        print(f'terminated: {terminated}')
        print(f'truncated: {truncated}')
        print(info)

        # terminated means terminal state reached (eg: agent has died, agent has reached goal)
        # truncated means the max steps per episode has been reached
        if terminated or truncated:
            observation, info = env.reset()
            state = obs_to_state(observation)
        else:
            state = state_next

    env.close()
