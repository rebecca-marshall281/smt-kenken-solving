# smt-kenken-solving

## Project 2 - CSC322 Spring 2023

### Authors


| Name               | V#               |
| ----------------   | ---------------- |
| Eduardo Szeckir    | V00921126        |
| Rebecca Marshall   | V00911412        |
| Emma Dewit         | V00906515        |
| Sylvain Taghaoussi | V00896706        |

## To Execute
The files under root are the compiled files. To run the program, execute the following command:

```bash
./kenken2smt <kenken-puzzle.txt >puzzle.smt
mathsat <puzzle.smt >model.smt
./smt2kenken <model.smt >solution.smt
```

## To Compile
To make the program executable on Unix systems, needed for the lab:

1. Make sure the following line is at the top of the `.py` file:

```python
#!/usr/bin/env python3
```

2. Copy the file into the root directory of the project:

```bash
cp hello.py ./../hello
```

3. Run the following command to make file executable:

```bash
chmod +x hello
```

4. Run the program with the following command:

```bash
./hello
```

## Common Errors
```bash
-bash: ./hello: Permission denied
```

To fix error, run the following command:
```bash
chmod +x hello
```

## Performance Analysis

