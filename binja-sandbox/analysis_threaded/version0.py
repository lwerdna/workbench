#!/usr/bin/env python3

import time
import threading
 
def worker(workList, result):
    batch = set()
    
    while True:
        func = workList.get()
        if func == None:
            break

        for instr in func.mlil.instructions:
            batch.add(instr.operation)

    result.update(batch)

# class to manage the work in a thread-safe way
class WorkList:
    def __init__(self, work):
        self.work = work
        self.lock = threading.Lock()

    def empty(self):
        with self.lock:
            return len(self.work) == 0

    def get(self):
        with self.lock:
            if len(self.work) == 0:
                return None
            return self.work.pop()

    def __str__(self):
        return f'work: {self.work}'

# class to collect results in a thread-safe way
class Result:
    def __init__(self):
        self.bag = set()
        self.lock = threading.Lock()

    def update(self, addition):
        with self.lock:
            self.bag = self.bag.union(addition)

    def __str__(self):
        #return f'{len(self.bag)} unique operations'
        return '-'.join(sorted(o.name[5:] for o in self.bag))

def experimentA(bv):
    workList = WorkList(list(bv.functions))
    result = Result()

    t0 = time.perf_counter()
    worker(workList, result)
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')

def experimentB(bv, n_threads=12):
    workList = WorkList(list(bv.functions))
    result = Result()

    threads = [threading.Thread(target=worker, args=(workList, result)) for i in range(n_threads)]
    t0 = time.perf_counter()
    print('starting')
    [t.start() for t in threads]
    print('joining')
    [t.join() for t in threads]
    print('done')
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')
