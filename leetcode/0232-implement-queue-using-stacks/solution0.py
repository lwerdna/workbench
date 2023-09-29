class MyQueue:
    def __init__(self):
        self.a = True
        self.stack_a = []
        self.stack_b = []

    def mode_a(self):
        if not self.a:
            while self.stack_b:
                self.stack_a.append(self.stack_b.pop())
            self.a = True

    def mode_b(self):
        if self.a:
            while self.stack_a:
                self.stack_b.append(self.stack_a.pop())
            self.a = False

    def push(self, x: int) -> None:
        self.mode_a()
        self.stack_a.append(x)

    def pop(self) -> int:
        self.mode_b()
        return self.stack_b.pop()

    def peek(self) -> int:
        self.mode_b()
        return self.stack_b[-1]

    def empty(self) -> bool:
        return len(self.stack_a) == len(self.stack_b) == 0

if __name__ == '__main__':
    # Your MyQueue object will be instantiated and called as such:
    obj = MyQueue()
    obj.push(1)
    obj.push(2)
    obj.push(3)
    obj.push(4)
    print(obj.peek())
    print(obj.pop())
    print(obj.pop())
    obj.push(5)
    obj.push(6)
    print(obj.pop())
    print(obj.pop())
    print(obj.pop())
    print(obj.pop())

