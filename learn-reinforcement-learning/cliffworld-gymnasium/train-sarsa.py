#!/usr/bin/env python

import sys
import random

import gymnasium as gym

#  0  1  2  3  4  5  6  7  8  9 10 11
# 12 13 14 15 16 17 18 19 20 21 22 23
# 24 25 26 27 28 29 30 31 32 33 34 35
# 36
states = [   0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,
            12,13,14,15,16,17,18,19,20,21,22,23,
            24,25,26,27,28,29,30,31,32,33,34,35,
            36 ]
# actions: 0, 1, 2, 3
action_names = ['up', 'right', 'down', 'left']

VERBOSE = False

def debug_print(message):
    global VERBOSE
    if VERBOSE:
        print(message)

class SARSALearner():
    def __init__(self, alpha=None, gamma=None, states=None, actions=None):
        self.states = states
        self.actions = actions

        self.alpha = alpha # learning rate AKA step size
        self.gamma = gamma # future discount

        self.reset()

    def update(self, state, action, reward, state_next=None, action_next=None):
        q_current = self.qtable[state][action]

        # estimate future reward by seeing what action we'd take next
        if state_next != None and action_next != None:
            q_future = self.qtable[state_next][action_next]
        else:
            q_future = 0

        q_new = q_current + self.alpha * (reward + self.gamma * q_future - q_current)
        self.qtable[state][action] = q_new

        if 1:
            debug_print('')
            debug_print(f'     action: {action}, state transition {state} -> {state_next} rewards {reward}')
            debug_print(f'  q_current: {q_current} (for this transition)')
            if q_future:
                debug_print(f'   q_future: qtable[{state_next}][{action_next}] = {q_future}')
            else:
                debug_print(f'   q_future: {q_future}')
            debug_print(f' discounted: {self.gamma}*{q_future} = {self.gamma * q_future}')
            debug_print(f'      q_new: {q_new}')
            debug_print('')

    def reset(self):
        self.qtable = { s:[0.0]*len(self.actions) for s in self.states }

    def __str__(self):
        lines = []

        for state in sorted(self.states):
            svalues = [str(round(v, 2)).rjust(7) for v in self.qtable[state]]
            line = (str(state)+':').rjust(4) + ','.join(svalues)
            lines.append(line)

        return '\n'.join(lines)

class Manual():
    def __init__(self):
        pass

    def choose_action(self, state, actions, action_value_function):
        import getch
        ch0 = getch.getch()
        if ord(ch0) == 27: # ESC \x1B
            ch1 = getch.getch()
            if ch1 == '[':
                ch2 = getch.getch()
                if ch2 == 'A': return 0
                if ch2 == 'B': return 2
                if ch2 == 'C': return 1
                if ch2 == 'D': return 3
        else:
            return ch0

# epsilon is the probability a random action will be taken
class EpsilonGreedy():
    def __init__(self, epsilon):
        self.epsilon = epsilon

    def choose_action(self, state, actions, action_value_function):
        if random.random() < self.epsilon:
            debug_print(f'choose_action() returning randomly from {actions}')
            result = random.choice(actions)
            debug_print(f'choice=RANDOM action returns {result} ({action_names[result]})')
        else:
            debug_print(f'choose_action() choosing best q_pi(s,a) {actions}')
            returns = {a:action_value_function(state, a) for a in actions}
            best_q = max(returns.values())
            result = random.choice([a for a in returns if returns[a] == best_q])
            debug_print(f'choice=BEST from {state}: {returns} is {result} ({action_names[result]})')

        return result

if __name__ == '__main__':
    if '--verbose' in sys.argv[1:]:
        VERBOSE = True

    if '--manual' in sys.argv[1:]:
        behavior_policy = Manual()
    else:
        behavior_policy = EpsilonGreedy(epsilon=.1)

    actions = [0,1,2,3]
    slearner = SARSALearner(alpha=.5, gamma=.99, states=states, actions=actions)

    if '--manual' in sys.argv[1:] or '--human' in sys.argv[1:]:
        env = gym.make('CliffWalking-v0', render_mode='human')
    else:
        env = gym.make('CliffWalking-v0')

    # convert an observation to a state id (here they're 1:1)
    def obs_to_state(obs):
        return obs

    episode_i, step_i = 0, 0

    action_value_function = lambda state,action: slearner.qtable[state][action]

    rewards_per_episode = []

    for episode_i in range(500):
        observation, info = env.reset()
        rewards_total = 0

        state = obs_to_state(observation)
        action = behavior_policy.choose_action(state, actions, action_value_function)

        for step_i in range(999999):
            debug_print('')
            debug_print(f'---- EPISODE {episode_i}, STEP {step_i} ----')
            observation, reward, terminated, truncated, info = env.step(action)
            rewards_total += reward
            state_next = obs_to_state(observation)

            debug_print(f'{state} --{action_names[action]}--> {state_next} is rewarded {reward}')
            debug_print(f'terminated: {terminated}')
            debug_print(f'truncated: {truncated}')
            debug_print(info)

            # terminated means terminal state reached (eg: agent has died, agent has reached goal)
            # truncated means the max steps per episode has been reached
            if terminated or truncated:
                debug_print('---- EPISODE END ----')
                slearner.update(state, action, reward)
                break

            action_next = behavior_policy.choose_action(state, actions, action_value_function)
            slearner.update(state, action, reward, state_next, action_next)

            debug_print(slearner)
            state, action = state_next, action_next

        rewards_per_episode.append(rewards_total)

    import json
    result = {
        'rewards_per_episode': rewards_per_episode,
        'qtable': slearner.qtable
    }
    print(json.dumps(result, indent=4))

    env.close()
