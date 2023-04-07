#!/usr/bin/env python

import sys
import random

import gymnasium as gym

states = list(range(37)) # 0, 1, ..., 36
# actions: 0, 1, 2, 3
action_names = ['up', 'right', 'down', 'left']

class SARSALearner():
    def __init__(self, alpha=None, gamma=None, states=None, actions=None, behavior_policy=None):
        self.states = states

        self.actions = actions
        self.alpha = alpha # learning rate AKA step size
        self.gamma = gamma # future discount

        self.behavior_policy = behavior_policy

        self.reset()

    def update(self, state, action, reward, state_next=None):
        q_current = self.qtable[state][action]

        # estimate future reward by seeing what action we'd take next
        action_value_function = lambda state,action: self.qtable[state][action]
        action_next = self.behavior_policy.choose_action(state, self.actions, action_value_function)

        q_future = self.qtable[state_next][action_next]

        q_new = q_current + self.alpha * (reward + self.gamma * q_future - q_current)
        self.qtable[state][action] = q_new

        if 0:
            print('')
            print(f'     action: {action}, state transition {state} -> {state_next} rewards {reward}')
            print(f'  q_current: {q_current} (for this transition)')
            print(f'   q_future: qtable[{self.state_next}][{self.action_next}] = {q_future}')
            print(f' discounted: {self.gamma}*{q_future} = {self.gamma * q_future}')
            print(f'      q_new: {q_new}')
            print('')

        return (state_next, action_next)

    def reset(self):
        self.qtable = [[0.0] * len(self.actions) for i in range(len(self.states))]

    def __str__(self):
        lines = []

        for i,row in enumerate(self.qtable):
            svalues = [str(round(v, 4)).rjust(7) for v in row]
            line = (str(i)+':').rjust(4) + ','.join(svalues)
            lines.append(line)

        return '\n'.join(lines)

# epsilon is the probability a random action will be taken
class EpsilonGreedy():
    def __init__(self, epsilon):
        self.epsilon = epsilon

    def choose_action(self, state, actions, action_value_function):
        if random.random() < self.epsilon:
            print(f'choose_action() returning randomly from {actions}')
            result = random.choice(actions)
            print(f'choice=RANDOM action returns {result} ({action_names[result]})')
        else:
            print(f'choose_action() choosing best q_pi(s,a) {actions}')
            values = { a:action_value_function(state, a) for a in actions }
            ranked = sorted(values, key=lambda a:values[a], reverse=True)
            result = ranked[0]
            print(f'choice=BEST from {actions} with q={round(values[result], 2)} returns {result} ({action_names[result]})')

        return result

if __name__ == '__main__':
    behavior_policy = EpsilonGreedy(epsilon=.1)
    slearner = SARSALearner(alpha=.5, gamma=.99, states=states, actions=[0,1,2,3], behavior_policy=behavior_policy)

    env = gym.make('CliffWalking-v0', render_mode='human')

    # convert an observation to a state id (here they're 1:1)
    def obs_to_state(obs):
        return obs

    observation, info = env.reset()
    state = obs_to_state(observation)

    max_steps = 500

    # initial conditions
    action = 0 # up

    for step in range(max_steps):
        print('')
        print('---- STEP ----')

        observation, reward, terminated, truncated, info = env.step(action)
        state_next = obs_to_state(observation)

        print(f'{state} --{action_names[action]}--> {state_next} is rewarded {reward}')
        print(f'terminated: {terminated}')
        print(f'truncated: {truncated}')
        print(info)

        # terminated means terminal state reached (eg: agent has died, agent has reached goal)
        # truncated means the max steps per episode has been reached
        if terminated or truncated:
            observation, info = env.reset()
            print('---- EPISODE END ----')
            state, action = obs_to_state(observation), 0
        else:
            _, action_next = slearner.update(state, action, reward, state_next)
            print(slearner)
            state, action = state_next, action_next

    env.close()
