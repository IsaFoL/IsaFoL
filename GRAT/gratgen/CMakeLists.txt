cmake_minimum_required(VERSION 2.6)
project(gratgen)

if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  message(STATUS "Setting build type to 'Release' as none was specified.")
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Choose the type of build." FORCE)
  # Set the possible values of build type for cmake-gui
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "Release"
    "MinSizeRel" "RelWithDebInfo")
endif()

find_package(Boost REQUIRED COMPONENTS timer)

include_directories(${Boost_INCLUDE_DIRS})

set(CMAKE_CXX_FLAGS "-Wall -Wextra -Weffc++ -Wpedantic -Wzero-as-null-pointer-constant -std=c++11")

set(CMAKE_CXX_FLAGS_DEBUG "-ggdb3 -DDEBUG -O0")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-ggdb3 -O3 -DNDEBUG -DWITH_PROFILING")

set(CMAKE_INSTALL_PREFIX "$ENV{HOME}")

# link_directories(/home/lammich/lib)
link_libraries(pthread)


if (CMAKE_BUILD_TYPE STREQUAL "RelWithDebInfo")
  include_directories("~/include")
  link_directories(~/lib)
  link_libraries(profiler)
endif()



add_executable(gratgen gratgen.cpp)

add_executable(lrat_grat_cnv lrat_grat_cnv.cpp)

install(TARGETS gratgen RUNTIME DESTINATION bin)


option(BUILD_DOCUMENTATION "Use Doxygen to create the HTML based API documentation" OFF)
if(BUILD_DOCUMENTATION)
  FIND_PACKAGE(Doxygen)
  if (NOT DOXYGEN_FOUND)
    message(FATAL_ERROR
      "Doxygen is needed to build the documentation. Please install it correctly")
  endif()

  add_custom_target (doc ALL
                     ${DOXYGEN_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile
                     WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                     )

endif()

