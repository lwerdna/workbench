#!/usr/bin/env python

# There is no arbitrary value associated with the string keys.
# The value is just whether or not the string is in the trie or not.

class Node(object):
    def __init__(self):
        self.children = [None]*26
        self.is_word = False

    def __getitem__(self, char):
        idx = ord(char) - ord('a')
        return self.children[idx]

    def __setitem__(self, char, value):
        idx = ord(char) - ord('a')
        self.children[idx] = value

class Trie(object):
    def __init__(self):
        self.root = Node()

    def insert(self, word):
        node = self.root
        for c in word:
            if not node[c]:
                node[c] = Node()
            node = node[c]
        node.is_word = True

    def seek(self, word):
        node = self.root
        for c in word:
            if node[c] == None:
                return None
            node = node[c]
        return node

    def search(self, word):
        node = self.seek(word)
        return node and node.is_word

    def startsWith(self, prefix):
        node = self.seek(prefix)
        return bool(node)

if __name__ == '__main__':
    trie = Trie()
    trie.insert("apple")
    
    assert trie.search("apple") == True #// return True
    assert trie.search("app") == False #     // return False
    assert trie.startsWith("app") == True #// return True
    trie.insert("app")
    assert trie.search("app") == True #     // return True
