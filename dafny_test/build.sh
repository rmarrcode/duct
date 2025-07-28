#!/bin/bash

# Run dafny build
dafny build --target:cs Demo1.dfy Demo.cs

# Fix the target framework in the generated csproj file
if [ -f "Demo1.csproj" ]; then
    sed -i '' 's/<TargetFramework>net8.0<\/TargetFramework>/<TargetFramework>net6.0<\/TargetFramework>/g' Demo1.csproj
    echo "Fixed target framework in Demo1.csproj"
    
    # Try building again with the fixed project file
    dotnet build Demo1.csproj
else
    echo "Demo1.csproj not found"
fi 