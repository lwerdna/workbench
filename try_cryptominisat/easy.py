#!/usr/bin/env python

from cms5_wrapper import solve_english, solve_english_all

# Alice will be happy if weather is good, her favorite team wins, or John Doe is elected
# Bob will be happy if gloomy day, if when team x loses, or if John Doe is elected
# Carl will be happy if sunny day, if team x wins, or if John Doe loses the election
#
# Is there an assignment of events that might appease all three?
# 
proposition = '(sunny_day | team_x_wins | john_doe_elected) & ' + \
  			'(~sunny_day | ~team_x_wins | john_doe_elected) & ' + \
  			'(sunny_day | team_x_wins | ~john_doe_elected)'

#print(solve_english(proposition))

for solution in solve_english_all(proposition):
	print('solution: ', solution)

