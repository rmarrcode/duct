import os
import ast
from typing import Dict, Tuple, Set, List, Optional
import tiktoken

def count_tokens_for_gpt4o(text: str) -> int:
    """Count tokens for GPT-4o using tiktoken"""
    try:
        # Use the cl100k_base encoding which is used by GPT-4o
        encoding = tiktoken.get_encoding("cl100k_base")
        tokens = encoding.encode(text)
        return len(tokens)
    except Exception as e:
        print(f"Error counting tokens: {e}")
        return 0

def find_django_files(directory: str) -> List[str]:
    """Perform DFS to find all Python files in Django project"""
    django_files = []
    priority_files = []

    for root, dirs, files in os.walk(directory):
        # Skip common directories that don't contain Django code
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['node_modules', '__pycache__', 'venv', 'env', '.git']]
        
        for file in files:
            if file == 'views.py':
                priority_files.append(os.path.join(root, file))
            elif file.endswith('.py'):
                file_path = os.path.join(root, file)
                django_files.append(file_path)

    return priority_files + django_files

import os
import ast
from typing import Dict, Tuple, Set, List, Optional

def _find_module_file(from_file: str, module_fullname: str) -> Optional[str]:
    parts = module_fullname.split(".")
    cur = os.path.dirname(from_file)
    while True:
        candidate_dir = os.path.join(cur, parts[0])
        if os.path.isdir(candidate_dir):
            candidate_file = os.path.join(cur, *parts) + ".py"
            if os.path.isfile(candidate_file):
                return candidate_file
            pkg_init = os.path.join(cur, *parts, "__init__.py")
            if os.path.isfile(pkg_init):
                return pkg_init
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    return None

def _parse_file(file_path: str) -> Tuple[ast.Module, str]:
    with open(file_path, "r", encoding="utf-8") as f:
        src = f.read()
    return ast.parse(src), src

def _collect_functions(module_ast: ast.Module) -> Dict[str, ast.FunctionDef]:
    funcs: Dict[str, ast.FunctionDef] = {}
    for node in module_ast.body:
        if isinstance(node, ast.FunctionDef):
            funcs[node.name] = node
    return funcs

def _collect_imported_names(module_ast: ast.Module) -> Dict[str, Tuple[str, str]]:
    mapping: Dict[str, Tuple[str, str]] = {}
    for node in module_ast.body:
        if isinstance(node, ast.ImportFrom) and node.module:
            mod = node.module
            for alias in node.names:
                local_name = alias.asname or alias.name
                mapping[local_name] = (mod, alias.name)
    return mapping

def _called_names_in_function(func: ast.FunctionDef) -> Set[str]:
    called: Set[str] = set()
    for node in ast.walk(func):
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Name):
                called.add(f.id)
    return called

def _unparse_func(func: ast.FunctionDef) -> str:
    return ast.unparse(func)

def expand_function_with_imports_recursive(file_path: str, function_name: str) -> str:
    try:
        module_ast, _ = _parse_file(file_path)
        funcs = _collect_functions(module_ast)
        imports = _collect_imported_names(module_ast)

        if function_name not in funcs:
            return f"Function '{function_name}' not found in {file_path}"

        target_func = funcs[function_name]
        to_resolve: List[Tuple[str, str, str]] = []
        seen_funcs: Set[Tuple[str, str]] = set()

        for name in _called_names_in_function(target_func):
            if name in imports:
                mod, orig = imports[name]
                to_resolve.append((mod, orig, file_path))

        expanded: Dict[str, Dict[str, Dict[str, str]]] = {}

        while to_resolve:
            mod, orig_name, from_file = to_resolve.pop()
            key = (mod, orig_name)
            if key in seen_funcs:
                continue
            seen_funcs.add(key)

            mod_file = _find_module_file(from_file, mod)
            if not mod_file:
                continue

            mod_ast, _ = _parse_file(mod_file)
            mod_funcs = _collect_functions(mod_ast)
            mod_imports = _collect_imported_names(mod_ast)

            if orig_name not in mod_funcs:
                continue

            func_node = mod_funcs[orig_name]
            func_src = _unparse_func(func_node)

            if mod not in expanded:
                expanded[mod] = {"file": mod_file, "funcs": {}}
            expanded[mod]["funcs"][orig_name] = func_src

            for name in _called_names_in_function(func_node):
                if name in mod_imports:
                    sub_mod, sub_orig = mod_imports[name]
                    sub_key = (sub_mod, sub_orig)
                    if sub_key not in seen_funcs:
                        to_resolve.append((sub_mod, sub_orig, mod_file))

        out: List[str] = []
        
        # Add all function implementations first
        for mod in sorted(expanded.keys()):
            for fname in sorted(expanded[mod]["funcs"].keys()):
                out.append(expanded[mod]["funcs"][fname])
                out.append("")
        
        # Add main function
        out.append(_unparse_func(target_func))

        return "\n".join(out)

    except Exception as e:
        return f"Error expanding function: {e}"

def python_file_to_string(file_path: str) -> str:
    """
    Read a Python file and return its contents as a string.
    
    Args:
        file_path (str): Path to the Python file
        
    Returns:
        str: Contents of the file as a string, or empty string if error occurs
        
    Raises:
        FileNotFoundError: If the file doesn't exist
        UnicodeDecodeError: If the file can't be decoded as UTF-8
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as file:
            content = file.read()
            return content
    except FileNotFoundError:
        print(f"Error: File '{file_path}' not found")
        return ""
    except UnicodeDecodeError as e:
        print(f"Error: Unable to decode file '{file_path}' as UTF-8: {e}")
        return ""
    except PermissionError:
        print(f"Error: Permission denied reading file '{file_path}'")
        return ""
    except Exception as e:
        print(f"Unexpected error reading file '{file_path}': {e}")
        return ""