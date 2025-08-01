"""
FileUtils module for Dafny YAML reader
"""

import os
import sys

def ReadAllLines(path):
    """
    Read all lines from a file and return them as a list of strings.
    
    Args:
        path (str): The file path to read
        
    Returns:
        list: List of strings, each representing a line from the file
    """
    try:
        print(f"ReadAllLines called with path: {path}")
        
        if not os.path.exists(path):
            print(f"Error: File {path} does not exist")
            return []
            
        with open(path, 'r', encoding='utf-8') as file:
            lines = file.readlines()
            
        # Remove trailing newlines
        lines = [line.rstrip('\n') for line in lines]
        
        print(f"Read {len(lines)} lines from file")
        return lines
        
    except Exception as ex:
        print(f"Error reading file: {ex}", file=sys.stderr)
        return []

def WriteLine(s):
    """
    Write a string to stdout.
    
    Args:
        s (str): The string to write
    """
    print(s) 