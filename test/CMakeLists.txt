add_subdirectory (googletest)

include_directories(
  ${canary_SOURCE_DIR}/test/googletest/include
  ${canary_SOURCE_DIR}/include)

link_directories (${canary_BINARY_DIR}/lib)

set (EXECUTABLE_OUTPUT_PATH ${canary_BINARY_DIR}/test)
add_definitions(-DGTEST_HAS_RTTI=0)

add_executable(AliasTest AliasTest.cpp)
target_link_libraries(AliasTest LLVMAsmParser LLVMCore LLVMSupport gtest_main)