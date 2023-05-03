#!/usr/bin/env python

import matplotlib
import matplotlib.pyplot as plt
plt.style.use('seaborn-whitegrid')

if __name__ == '__main__':
    data = []

    for line in open('./helens-preferences.dat').readlines():
        miles, games, icecream, label = line.strip().split('\t')
        data.append((float(miles), float(games), float(icecream), label))

    # https://matplotlib.org/stable/api/markers_api.html
    # https://matplotlib.org/stable/tutorials/colors/colors.html

    # games vs. icecream
    fig, ax = plt.subplots(1)
    ax.set_xlabel('Percentage of Time Spent Playing Video Games')
    ax.set_ylabel('Liters of Ice Cream Consumed Per Week')

    for (label, color) in (('didntLike','r'), ('smallDoses','b'), ('largeDoses', 'g')):
        x = [row[1] for row in data if row[3]==label]
        y = [row[2] for row in data if row[3]==label]
        ax.scatter(x, y, c=color, marker='.')

    plt.savefig('games-icecream.svg')
    plt.savefig('games-icecream.png')
    plt.close(fig)

    # games vs. miles
    fig, ax = plt.subplots(1)
    ax.set_xlabel('Percentage of Time Spent Playing Video Games')
    ax.set_ylabel('Frequent Flyer Miles')

    for (label, color) in (('didntLike','r'), ('smallDoses','b'), ('largeDoses', 'g')):
        x = [row[0] for row in data if row[3]==label]
        y = [row[1] for row in data if row[3]==label]
        ax.scatter(x, y, c=color, marker='.')

    plt.savefig('miles-games.svg')
    plt.savefig('miles-games.png')
    plt.close(fig)

    # games vs. icecream
    fig, ax = plt.subplots(1)
    ax.set_xlabel('Frequent Flyer Miles')
    ax.set_ylabel('Liters of Ice Cream Consumed Per Week')

    for (label, color) in (('didntLike','r'), ('smallDoses','b'), ('largeDoses', 'g')):
        x = [row[0] for row in data if row[3]==label]
        y = [row[2] for row in data if row[3]==label]
        ax.scatter(x, y, c=color, marker='.')

    plt.savefig('miles-icecream.svg')
    plt.savefig('miles-icecream.png')
    plt.close(fig)

    # 3d plot!
    fig = plt.figure()
    ax = fig.add_subplot(projection='3d')
    ax.set_xlabel('Frequent Flyer Miles')
    ax.set_ylabel('Percentage of Time Spent Playing Video Games')
    ax.set_zlabel('Liters of Ice Cream Consumed Per Week')

    for (label, color) in (('didntLike','r'), ('smallDoses','b'), ('largeDoses', 'g')):
        x = [row[0] for row in data if row[3]==label]
        y = [row[1] for row in data if row[3]==label]
        z = [row[2] for row in data if row[3]==label]
        ax.scatter(x, y, z, c=color, marker='.')

    #plt.show()
    plt.savefig('miles-games-icecream.svg')
    plt.savefig('miles-games-icecream.png')
    plt.close(fig)

