cmake_minimum_required(VERSION 2.6)
project(gratgen)

set(CMAKE_CXX_FLAGS "-Wall -Wextra -Weffc++ -Wpedantic -Wzero-as-null-pointer-constant -Werror -std=c++11 -m32 -I/home/lammich/include")
set(CMAKE_CXX_FLAGS_DEBUG "-ggdb3 -DDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-ggdb3 -O3")

link_directories(/home/lammich/lib)
# link_libraries(profiler)
add_executable(gratgen main.cpp)

install(TARGETS gratgen RUNTIME DESTINATION bin)
