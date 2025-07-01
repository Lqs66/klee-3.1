#!/bin/bash

# Test script for split mode functionality
echo "======================================"
echo "KLEE Split Mode Functionality Tests"
echo "======================================"

TEST_DIR="$(dirname "$0")"
cd "$TEST_DIR"

echo ""
echo "Available test programs:"
echo "- simple_test.c: Basic recursive functions"  
echo "- comprehensive_test.c: Complex control flow"
echo ""

# Test 1: Basic split mode enablement
echo "Test 1: Enable split mode with basic options"
echo "Description: Enables split mode without additional constraints"
echo "Command: klee --enable-split simple_test.bc"
echo "Expected: Split mode initialization messages, normal execution"
echo ""

# Test 2: Split mode with call depth limit  
echo "Test 2: Enable split mode with max call depth"
echo "Description: Limits recursive function calls to prevent deep recursion"
echo "Command: klee --enable-split --max-call-depth=5 comprehensive_test.bc"
echo "Expected: Execution terminates when call depth exceeds 5"
echo ""

# Test 3: Split mode with target basic blocks
echo "Test 3: Enable split mode with target basic blocks file"
echo "Description: Tracks coverage of specific basic blocks from file"
echo "Command: klee --enable-split --target-basic-blocks=target_blocks.txt simple_test.bc"
echo "Expected: Coverage tracking messages as blocks are visited"
echo ""

# Test 4: Split mode with coverage threshold
echo "Test 4: Enable split mode with coverage threshold"
echo "Description: Stops execution when target coverage percentage is reached"
echo "Command: klee --enable-split --coverage=50 --target-basic-blocks=target_blocks.txt comprehensive_test.bc"
echo "Expected: Execution halts when 50% coverage is achieved"
echo ""

# Test 5: Combined options
echo "Test 5: Enable split mode with all options"
echo "Description: Uses all split mode features together"
echo "Command: klee --enable-split --max-call-depth=3 --target-basic-blocks=target_blocks.txt --coverage=70 comprehensive_test.bc"
echo "Expected: Execution controlled by depth limit AND coverage threshold"
echo ""

# Test 6: Edge cases
echo "Test 6: Edge cases and error handling"
echo "Description: Tests invalid configurations and edge cases"
echo "Commands:"
echo "  klee --enable-split --coverage=150 simple_test.bc  # Invalid coverage"
echo "  klee --enable-split --target-basic-blocks=nonexistent.txt simple_test.bc  # Missing file"
echo "Expected: Warning messages and graceful fallback behavior"
echo ""

echo "======================================"
echo "Compilation and Execution Instructions"
echo "======================================"
echo ""
echo "To run these tests, first compile the test programs to LLVM bitcode:"
echo ""
echo "# Compile test programs"
echo "clang -emit-llvm -c -g -O0 -I/path/to/klee/include simple_test.c -o simple_test.bc"
echo "clang -emit-llvm -c -g -O0 -I/path/to/klee/include comprehensive_test.c -o comprehensive_test.bc"
echo ""
echo "# Run individual tests"
echo "klee --enable-split simple_test.bc"
echo "klee --enable-split --max-call-depth=5 comprehensive_test.bc"
echo "klee --enable-split --target-basic-blocks=target_blocks.txt --coverage=60 comprehensive_test.bc"
echo ""
echo "Note: Adjust include paths and klee binary location as needed for your installation."