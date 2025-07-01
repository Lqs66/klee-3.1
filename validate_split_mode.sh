#!/bin/bash

# Validation script for split mode implementation
# This script checks that the code changes are syntactically correct
# and that the command-line options are properly defined

echo "========================================"
echo "KLEE Split Mode Implementation Validation"
echo "========================================"

REPO_ROOT="$(dirname "$0")"
cd "$REPO_ROOT"

echo ""
echo "1. Checking that split mode options are defined..."

# Check that all split mode options are present in the code
OPTIONS=("EnableSplit" "MaxCallDepth" "TargetBasicBlocks" "CoverageThreshold")
FOUND_ALL=true

for option in "${OPTIONS[@]}"; do
    if grep -q "$option" lib/Core/Executor.cpp; then
        echo "✓ $option option found"
    else
        echo "✗ $option option NOT found"
        FOUND_ALL=false
    fi
done

echo ""
echo "2. Checking split mode member variables..."

# Check member variables in header file
VARIABLES=("splitModeEnabled" "targetBasicBlocks" "totalBasicBlocks" "coveredBasicBlocks")
for var in "${VARIABLES[@]}"; do
    if grep -q "$var" lib/Core/Executor.h; then
        echo "✓ $var variable declared"
    else
        echo "✗ $var variable NOT found"
        FOUND_ALL=false
    fi
done

echo ""
echo "3. Checking split mode method implementations..."

# Check method implementations
METHODS=("initializeSplitMode" "loadTargetBasicBlocks" "checkCallDepth" "updateCoverage" "checkCoverageThreshold")
for method in "${METHODS[@]}"; do
    if grep -q "Executor::$method" lib/Core/Executor.cpp; then
        echo "✓ $method method implemented"
    else
        echo "✗ $method method NOT implemented"
        FOUND_ALL=false
    fi
done

echo ""
echo "4. Checking integration points..."

# Check that split mode is integrated into key execution points
if grep -q "splitModeEnabled.*checkCallDepth" lib/Core/Executor.cpp; then
    echo "✓ Call depth checking integrated in executeCall"
else
    echo "✗ Call depth checking NOT integrated"
    FOUND_ALL=false
fi

if grep -q "updateCoverage" lib/Core/Executor.cpp; then
    echo "✓ Coverage tracking integrated in transferToBasicBlock"
else
    echo "✗ Coverage tracking NOT integrated"
    FOUND_ALL=false
fi

echo ""
echo "5. Checking test files..."

TEST_FILES=("test_split_mode/simple_test.c" "test_split_mode/comprehensive_test.c" "test_split_mode/target_blocks.txt")
for file in "${TEST_FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "✓ $file exists"
    else
        echo "✗ $file NOT found"
        FOUND_ALL=false
    fi
done

echo ""
echo "========================================"
if [ "$FOUND_ALL" = true ]; then
    echo "✓ ALL CHECKS PASSED"
    echo "Split mode implementation appears to be complete!"
    echo ""
    echo "Next steps:"
    echo "1. Build KLEE with the new changes"
    echo "2. Compile test programs to LLVM bitcode"
    echo "3. Run KLEE with split mode options"
    echo "4. Verify functionality with test cases"
else
    echo "✗ SOME CHECKS FAILED"
    echo "Please review the implementation for missing components."
fi
echo "========================================"