#!/usr/bin/env python

import os, sys
import termios, tty, select

import gymnasium as gym
env = gym.make("LunarLander-v2", render_mode="human")


# env.action_space: Discrete(4) so actions {0, 1, 2, 3}
#  0: do nothing
#  1: fire left orientation engine
#  2: fire main engine
#  3: fire right orientation engine
# env.observation_space

# try to hook pygame pump
import pygame
action = 0
pump_old = pygame.event.pump
def pump_new():
    global pump_old, action
    for event in pygame.event.get():
        if event.type == pygame.KEYDOWN:
            keys_pressed = pygame.key.get_pressed()

            action = 0
            if keys_pressed[pygame.K_UP]:
                action = 2
            elif keys_pressed[pygame.K_LEFT]:
                action = 1
            elif keys_pressed[pygame.K_RIGHT]:
                action = 3
            else:
                raise Exception('only supported keys: left, right, up')

            print(f'set action={action}') 

        elif event.type == pygame.KEYUP:
            action = 0
pygame.event.pump = pump_new

#
observation, info = env.reset()

while(True):
    #print(f'sending action: {action}')
    observation, reward, terminated, truncated, info = env.step(action)

    if terminated or truncated:
        observation, info = env.reset()

env.close()
