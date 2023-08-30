#!/usr/bin/env python3

import os, sys

from pprint import pprint

class Trie:
    def __init__(self, root=True):
        self.children = {} # dict from char -> Trie

    # returns: void
    def insert(self, word: str) -> None:
        if not word:
            self.children['\0'] = None
            return

        char = word[0]
        if not char in self.children:
            self.children[char] = Trie()
        self.children[char].insert(word[1:])

    # returns: bool
    def search(self, word: str) -> bool:
        if not word:
            return '\0' in self.children

        char = word[0]
        return char in self.children and self.children[char].search(word[1:])

    # returns: bool
    def startsWith(self, prefix: str) -> bool:
        if not prefix:
            return True

        char = prefix[0]
        return char in self.children and self.children[char].startsWith(prefix[1:])

    def __contains__(self, item):
        return item in self.children  

    def str_re(self, depth):
        indent = '  '*depth

        result = ''
        for char in self.children:
            if char == '\0':
                result += f'{indent}<end>\n'
            else:
                result += f"{indent}'{char}'\n"
                result += self.children[char].str_re(depth+1)

        return result

    def __str__(self):
        return self.str_re(0)

trie = Trie()
trie.insert("apple")
assert trie.search("apple")
assert not trie.search("app")
assert trie.startsWith("app")
trie.insert("app");
print(trie)
assert trie.search("app");
