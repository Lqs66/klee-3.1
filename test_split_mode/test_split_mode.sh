#!/bin/bash

# Test script for split mode functionality
echo "Testing KLEE split mode functionality..."

# Test 1: Basic split mode enablement
echo "Test 1: Enable split mode with basic options"
echo "Command: klee --enable-split simple_test.bc"

# Test 2: Split mode with call depth limit  
echo "Test 2: Enable split mode with max call depth"
echo "Command: klee --enable-split --max-call-depth=5 simple_test.bc"

# Test 3: Split mode with target basic blocks
echo "Test 3: Enable split mode with target basic blocks file"
echo "Command: klee --enable-split --target-basic-blocks=target_blocks.txt simple_test.bc"

# Test 4: Split mode with coverage threshold
echo "Test 4: Enable split mode with coverage threshold"
echo "Command: klee --enable-split --coverage=80 --target-basic-blocks=target_blocks.txt simple_test.bc"

# Test 5: Combined options
echo "Test 5: Enable split mode with all options"
echo "Command: klee --enable-split --max-call-depth=3 --target-basic-blocks=target_blocks.txt --coverage=70 simple_test.bc"

echo ""
echo "Note: These tests demonstrate the command-line interface."
echo "To run actual tests, first compile simple_test.c to LLVM bitcode:"
echo "clang -emit-llvm -c -g simple_test.c -o simple_test.bc"
echo "Then run the klee commands above."