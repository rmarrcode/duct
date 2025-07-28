using System;

namespace YamlToDafnyTranslator
{
    class Program
    {
        static void Main(string[] args)
        {
            // Convert string arguments to Dafny sequences
            var dafnyArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args);
            
            // Call the main method with external function implementations
            YamlToDafnyTranslator.__default._Main(dafnyArgs);
        }
    }
} 