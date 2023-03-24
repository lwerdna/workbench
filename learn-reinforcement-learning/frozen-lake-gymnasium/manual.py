#!/usr/bin/env python

# manual (human controlled) interaction
# keys must be given to focused console

import getch

import gymnasium as gym

def get_action():
    ch0 = getch.getch()
    if ord(ch0) == 27: # ESC \x1B
        ch1 = getch.getch()
        if ch1 == '[':
            ch2 = getch.getch()
            if ch2 == 'A': return 3 # up
            if ch2 == 'B': return 1 # 'down'
            if ch2 == 'C': return 2 # 'right'
            if ch2 == 'D': return 0 # left
    else:
        return ch0

if __name__ == '__main__':
    env = gym.make('FrozenLake-v1', desc=None, map_name="4x4", is_slippery=False, render_mode='human')

    observation, info = env.reset()

    while 1:
        action = get_action()

        observation, reward, terminated, truncated, info = env.step(action)

        print('--')
        print(f'action: {action}')
        print(observation)
        print(reward)
        print(terminated)
        print(truncated)
        print(info)

        # terminated means terminal state reached (eg: agent has died, agent has reached goal)
        # truncated means the max steps per episode has been reached
        if terminated or truncated:
            observation, info = env.reset()

    env.close()
