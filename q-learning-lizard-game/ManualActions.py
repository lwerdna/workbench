# gets action from the user

def get_action(q_table, state):
    import getch

    print(f'available actions: ' + str(list(q_table[state].keys())))

    ch0 = getch.getch()
    if ord(ch0) == 27: # ESC \x1B
        ch1 = getch.getch()
        if ch1 == '[':
            ch2 = getch.getch()
            if ch2 == 'A': return 'up'
            if ch2 == 'B': return 'down'
            if ch2 == 'C': return 'right'
            if ch2 == 'D': return 'left'
    else:
        return ch0
