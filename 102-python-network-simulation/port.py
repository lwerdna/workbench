import threading

class Port:
    def __init__(self):
        self.destination = None # python reference to another port
        self.queue = [] # queue of received data (frames, packets, etc.)
        self.lock = threading.Lock() # mutex on the queue
    
    def send(self, data):
        if not self.destination:
            return

        with self.destination.lock:
            self.destination.queue.append(data)

    def receive(self):
        with self.lock:
            if len(self.queue) == 0:
                return None
            else:
                return self.queue.pop(0)

    def connected(self):
        return self.destination != None
