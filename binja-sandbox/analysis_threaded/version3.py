#!/usr/bin/env python3

import time
import threading

import binaryninja

G_DO_WORK = False

def worker(thread_id, work_gen, result):
    global G_DO_WORK
    
    print(f'thread {thread_id} here!')
    
    blocks_seen = 0
    functions_seen = 0
    functions_skipped = 0
    
    while True:
        if (func := work_gen.get()) == None:
            break

        functions_seen += 1

        if type(func) == binaryninja.function.Function:
            try:
                func = func.mlil # this initiates the analysis
            except:
                functions_skipped += 1
                continue

        if G_DO_WORK:
            for instr in func.instructions:
                pass

            blocks_seen += len(func.basic_blocks)

    print(f'thread {thread_id} reports {functions_seen} functions')
    result.update(blocks_seen, functions_seen, functions_skipped)

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
        self.blocks_seen = 0
        self.functions_seen = 0
        self.functions_skipped = 0
        self.lock = threading.Lock()

    def update(self, blocks_seen, functions_seen, functions_skipped):
        with self.lock:
            self.blocks_seen += blocks_seen
            self.functions_seen += functions_seen
            self.functions_skipped += functions_skipped

    def __str__(self):
        return f'{self.blocks_seen} total basic blocks across {self.functions_seen} functions ({self.functions_skipped} skipped)'

def experimentA(bv):
    workGen = WorkGen((f for f in bv.functions))
    result = Result()

    t0 = time.perf_counter()
    worker(0, workGen, result)
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')

def experimentB(bv, n_threads=11):
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
    workGen = WorkGen((f for f in bv.mlil_functions()))
    result = Result()

    t0 = time.perf_counter()
    worker(0, workGen, result)
    t1 = time.perf_counter()
    print(result)
    print(f'{t1-t0} seconds')

