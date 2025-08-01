import sys
import YamlToDafnyTranslator

def main():
    # Get command line arguments
    args = sys.argv[1:]  # Skip the script name
    
    # Convert to Dafny sequence format
    dafny_args = YamlToDafnyTranslator._dafny.Seq.FromArray(args)
    
    # Call the Dafny Main method
    YamlToDafnyTranslator.default__.Main(dafny_args)

if __name__ == "__main__":
    main() 