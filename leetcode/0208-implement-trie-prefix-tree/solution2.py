#!/usr/bin/env python

class Node:
    def __init__(self):
        self.children = {}
        self.terminal = False

class Trie(object):
    def __init__(self):
        self.root = Node()

    # returns (node, remaining string)
    def seek(self, word):
        current = self.root

        while word:
            if not word[0] in current.children:
                break

            current = current.children[word[0]]
            word = word[1:]

        return (current, word)

    def insert(self, word):
        node, word = self.seek(word)

        while word:
            node.children[word[0]] = Node()
            node = node.children[word[0]]
            word = word[1:]

        node.terminal = True

    def search(self, word):
        node, word = self.seek(word)
        return word == '' and node.terminal

    def startsWith(self, prefix):
        node, word = self.seek(prefix)
        return word == ''

if __name__ == '__main__':
    trie = Trie()
    trie.insert("apple")

    assert trie.search("apple") == True #// return True
    assert trie.search("app") == False #     // return False
    assert trie.startsWith("app") == True #// return True
    trie.insert("app")
    assert trie.search("app") == True #     // return True
