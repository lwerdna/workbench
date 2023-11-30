#!/usr/bin/env python3

import time
import threading

import binaryninja
 
def worker(thread_id, work_gen, result):
    batch = set()
    
    while True:
        func = work_gen.get()
        if func == None:
            break

        if type(func) == binaryninja.function.Function:
            func = func.mlil # this initiates the analysis

        for instr in func.instructions:
            batch.add(instr.operation)

    result.update(batch)

# class to manage the work in a thread-safe way
class WorkGen:
    def __init__(self, generator):
        self.generator = generator
        self.lock = threading.Lock()

    def get(self):
        with self.lock:
            return next(self.generator, None)

# class to collect results in a thread-safe way
class Result:
    def __init__(self):
        self.bag = set()
        self.lock = threading.Lock()

    def update(self, addition):
        with self.lock:
            self.bag = self.bag.union(addition)

    def __str__(self):
        return '-'.join(sorted(o.name[5:] for o in self.bag))

def experimentA(bv):
    workGen = WorkGen((f for f in bv.functions))
    result = Result()

    t0 = time.perf_counter()
    worker(0, workGen, result)
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')

def experimentB(bv, n_threads=12):
    workGen = WorkGen((f for f in bv.functions))
    result = Result()

    threads = [threading.Thread(target=worker, args=(i, workGen, result)) for i in range(n_threads)]
    t0 = time.perf_counter()
    print('starting')
    [t.start() for t in threads]
    print('joining')
    [t.join() for t in threads]
    print('done')
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')

def experimentC(bv):
    workGen = WorkGen((f for f in bv.mlil_functions(12)))
    result = Result()

    t0 = time.perf_counter()
    worker(0, workGen, result)
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')
