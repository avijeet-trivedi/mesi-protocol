#!/usr/bin/python3

import random

def generate_mesi_test_vectors(num_valid_commands, num_idle_commands=50, num_of_cores=4, xlen=6, cl=8):
    commands = [0, 1]  # Read (0) and Write (1)
    
    def generate_core_file(filename, num_commands):
        with open(filename, "w") as f:
            for _ in range(num_commands):
                command = random.choice(commands)  # Choose Read or Write
                address = random.randint(0, 2**xlen - 1)  # Address
                data = random.randint(0, 2**cl - 1) if command == 1 else 0  # Data only for writes
                f.write(f"{command} {address} {data}\n")
            
            # Append idle commands
            for _ in range(num_idle_commands):
                f.write("2 0 0\n")
    
    for core in range(num_of_cores):
        # Generate a file for each core
        generate_core_file(f"inputs_{core}.txt", num_valid_commands)
    
random.seed(43)
generate_mesi_test_vectors(num_valid_commands=1000000, num_idle_commands=50, num_of_cores=4, xlen=6, cl=8)