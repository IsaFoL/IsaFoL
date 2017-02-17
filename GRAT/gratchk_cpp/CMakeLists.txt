cmake_minimum_required(VERSION 2.6)
project(gratchk)


set(CMAKE_CXX_FLAGS "-Wall -Wextra -Weffc++ -Wpedantic -Wzero-as-null-pointer-constant  -Werror -std=c++11")
set(CMAKE_CXX_FLAGS_DEBUG "-ggdb3 -DDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

add_executable(gratchk main.cpp)

install(TARGETS gratchk RUNTIME DESTINATION bin)
