#!/usr/bin/env python

import os
import re
import sys

from bs4 import BeautifulSoup

if __name__ == '__main__':
    data = {}

    html_doc = open('List_of_countries_and_dependencies_by_population.html').read()
    soup = BeautifulSoup(html_doc, 'html.parser')

    table = soup.find(class_='wikitable sortable')
    for row in table.find_all('tr'):
        cells = row.find_all('td')
        if not cells:
            continue

        #print(f'{len(cells)} cells: ' + '|'.join([c.text.strip() for c in cells]))
        offset = 1 if len(cells) == 7 else 0
        name = cells[offset+0].text.strip()
        population = int(cells[offset+1].text.strip().replace(',', ''))
        if name == 'World':
            continue

        data[name] = population

    world_pop = sum(data.values())
    
    total_prob = 0
    for name, population in data.items():
        probability = (population/world_pop)*((population-1)/world_pop)
        total_prob += probability
        print(f'"{name}" population={population} chance={probability*100:.06f}%')

    print('total countries:', len(data))
    print('world population:', world_pop)
    print('probability of two randomly selected earthlings being from the same country:', total_prob)

    print('[' + ','.join([str(x) for x in data.values()]) + ']')


