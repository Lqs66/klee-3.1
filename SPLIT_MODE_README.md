# KLEE Split Mode Documentation

## Overview

The Split Mode functionality in KLEE provides targeted code analysis with the following capabilities:

1. **Controlled exploration depth** - Limit function call depth to prevent excessive recursion
2. **Target-specific coverage** - Track coverage of specific basic blocks
3. **Coverage-based termination** - Stop execution when target coverage threshold is reached
4. **Enhanced analysis control** - Fine-tune symbolic execution for specific analysis goals

## Command Line Options

### `--enable-split`
Enables split mode for targeted code analysis.
- Type: Boolean flag
- Default: false
- Usage: `klee --enable-split program.bc`

### `--max-call-depth=N`
Sets the maximum function call depth for exploration.
- Type: Unsigned integer
- Default: 0 (no limit)
- Usage: `klee --enable-split --max-call-depth=10 program.bc`

### `--target-basic-blocks=FILE`
Specifies the path to a file containing target basic block identifiers.
- Type: String (file path)
- Default: empty (no target file)
- Usage: `klee --enable-split --target-basic-blocks=targets.txt program.bc`

### `--coverage=PERCENT`
Sets the target coverage percentage (0-100).
- Type: Float
- Default: 100.0
- Usage: `klee --enable-split --coverage=80.0 program.bc`

## Target Basic Blocks File Format

The target basic blocks file should contain one basic block identifier per line:

```
# Comments start with #
main_entry
function_loop
error_handling_block
# Empty lines are ignored
```

## Example Usage

### Basic Split Mode
```bash
klee --enable-split program.bc
```

### Limited Call Depth
```bash
klee --enable-split --max-call-depth=5 program.bc
```

### Target Coverage Analysis
```bash
klee --enable-split \
     --target-basic-blocks=important_blocks.txt \
     --coverage=75.0 \
     program.bc
```

### Combined Configuration
```bash
klee --enable-split \
     --max-call-depth=3 \
     --target-basic-blocks=targets.txt \
     --coverage=85.0 \
     program.bc
```

## Implementation Details

When split mode is enabled:

1. **Call Depth Tracking**: Each function call increments the stack depth, and execution is terminated if the maximum depth is exceeded.

2. **Basic Block Coverage**: As execution transfers between basic blocks, the coverage is updated if target blocks are specified.

3. **Coverage Monitoring**: When the coverage threshold is reached, execution is halted with an appropriate message.

4. **Integration**: Split mode integrates with existing KLEE infrastructure without disrupting normal operation when disabled.

## Testing

See the `test_split_mode/` directory for example programs and test scripts demonstrating split mode functionality.