import angr

# THE PROJECT
# has options...
# backend - which backend to use, as either a class or name (elf, pe, mach-o, cgc, etc.)
# base_addr - a base address to use
# entry_point - an entry point to use
# arch - the name of an architecture to use
proj = angr.Project('/Users/andrewl/repos/vector35/pace/testbins/tests')
proj.hook(addr, hook) # hook is a SimProcedure instance
proj.is_hooked
proj.unhook
proj.hooked_by

# THE LOADER
loader = proj.loader
loader.all_objects
loader.shared_objects
loader.all_elf_objects
loader.all_pe_objects
loader.find_object_containing(0x400000)
loader.extern_object # special
loader.kernel_object
loader.main_object

# OBJECT
obj = loader.main_object
obj.entry
obj.min_addr
obj.max_addr
obj.segments
obj.find_segment_containing(obj.entry)
obj.find_section_containing(obj.entry)
obj.linked_base
obj.mapped_base
obj.relocs
obj.imports
obj.plt['strcmp'] # returns: 0x400550
obj.reverse_plt[0x400550] # returns: 'strcmp'

# SYMBOLS
sym = loader.find_symbol('strcmp')
sym.name # 'strcmp'
sym.owner # <ELF Object libc-2.23.so, maps [0x1000000:0x13c999f]>
sym.rebased_addr
sym.linked_addr
sym.relative_addr
sym.is_import
sym.is_export

# STATE
state = proj.factory.blank_state()
state = proj.factory.entry_state() # ready at the main binary's entrypoint
state = proj.factory.full_init_state() # ready at pre-entrypoint (initializers, shared lib constructors, etc.)
state = proj.factory.call_state() # ready to execute a given function
state.mem
state.regs

# SOLVER
solver = state.solver

# bit vector, value
one = solver.BVV(1, 64) # 64 bit wide vector with value 1
hundred = solver.BVV(100, 64) # ...with value 100

# bit vector, symbolic
x = state.solver.BVS("x", 64)

