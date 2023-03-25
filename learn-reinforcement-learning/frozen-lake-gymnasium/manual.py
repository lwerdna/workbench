#!/usr/bin/env python

# manual (human controlled) interaction
# keys must be given to focused console

import getch

import gymnasium as gym

# try to hook pygame pump
import pygame
action_queue = []
def pump_detour():
    global action_queue

    #print(f'pump_detour() enters')

    for event in pygame.event.get():

        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_UP:
                action = 3
            elif event.key == pygame.K_LEFT:
                action = 0
            elif event.key == pygame.K_RIGHT:
                action = 2
            elif event.key == pygame.K_DOWN:
                action = 1
            else:
                breakpoint()
                raise Exception('only supported keys: left, right, up, down')

            action_queue.append(action)

        elif event.type == pygame.KEYUP:
            action = None

    #print(f'pump_detour() leaves with action_queue: {action_queue}')

pygame.event.pump = pump_detour

if __name__ == '__main__':
    env = gym.make('FrozenLake-v1', desc=None, map_name="4x4", is_slippery=False, render_mode='human')

    observation, info = env.reset()

    while 1:
        while not action_queue:
            env.render()

        action = action_queue.pop(0)

        observation, reward, terminated, truncated, info = env.step(action)

        print('--')
        print(f'action: {action}')
        print(f'observation: {observation}')
        print(f'reward: {reward}')
        print(f'terminated: {terminated}')
        print(f'truncated: {truncated}')
        print(f'info: {info}')

        # terminated means terminal state reached (eg: agent has died, agent has reached goal)
        # truncated means the max steps per episode has been reached
        if terminated or truncated:
            observation, info = env.reset()

    env.close()
