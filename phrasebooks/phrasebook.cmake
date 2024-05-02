# minimum three commands are:
cmake_minimum_required(VERSION 3.9 FATAL_ERROR)
project(MyProject)
# one of:
add_library(MyProject DYNAMIC ${SOURCES})
add_library(MyProject STATIC ${SOURCES})
add_library(MyProject OBJECT a.c b.c)
add_executable(hello MyProject.c)

# tell one project to compile another

# tell one project to link to another
target_link_libraries(linking_project PUBLIC linked_project)

# say to include a directory (this generates something like: -Ipath/to/include0 -Ipath/to/include1)
target_include_directories(MyProject PUBLIC
							path/to/include0
							path/to/include1
						)

# say to define something (probably generates something like: -DMyOption)
add_compile_definitions(MyOption)


# clear junk out with
rm -rf CMakeCache.txt CMakeFiles
