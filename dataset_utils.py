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

def _collect_functions_and_methods(module_ast: ast.Module) -> Dict[str, ast.FunctionDef]:
    """Collect both standalone functions and class methods"""
    funcs: Dict[str, ast.FunctionDef] = {}
    
    for node in module_ast.body:
        if isinstance(node, ast.FunctionDef):
            funcs[node.name] = node
        elif isinstance(node, ast.ClassDef):
            # Add class methods
            for class_node in node.body:
                if isinstance(class_node, ast.FunctionDef):
                    # Use class_name.method_name as key
                    method_key = f"{node.name}.{class_node.name}"
                    funcs[method_key] = class_node
    
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

def _var_class_bindings(func: ast.FunctionDef, imports: Dict[str, Tuple[str, str]]) -> Dict[str, Tuple[str, str]]:
    """Map local variable names to (module, class_name) when assigned from imported classes."""
    bindings: Dict[str, Tuple[str, str]] = {}
    for node in ast.walk(func):
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
            callee = node.value.func
            if isinstance(callee, ast.Name) and callee.id in imports:
                mod, orig = imports[callee.id]
                for t in node.targets:
                    if isinstance(t, ast.Name):
                        bindings[t.id] = (mod, orig)
    return bindings

def _method_calls(func: ast.FunctionDef) -> List[Tuple[str, str]]:
    """Return (var_name, method_name) for calls like var.method(...)."""
    calls: List[Tuple[str, str]] = []
    for node in ast.walk(func):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
            calls.append((node.func.value.id, node.func.attr))
    return calls

def _str_calls(func: ast.FunctionDef) -> List[str]:
    """Return variable names used in str(var) calls."""
    vars_used: List[str] = []
    for node in ast.walk(func):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "str":
            if node.args and isinstance(node.args[0], ast.Name):
                vars_used.append(node.args[0].id)
    return vars_used

def _unparse_func(func: ast.FunctionDef) -> str:
    return ast.unparse(func)



def expand_function_with_imports_recursive(file_path: str, function_name: str) -> str:
    try:
        module_ast, _ = _parse_file(file_path)
        funcs = _collect_functions_and_methods(module_ast)
        imports = _collect_imported_names(module_ast)

        # First try to find the exact function name
        if function_name not in funcs:
            # If not found, try to find it as a method in any class
            for key in funcs.keys():
                if key.endswith(f".{function_name}"):
                    function_name = key
                    break
            else:
                return f"Function '{function_name}' not found in {file_path}"

        target_func = funcs[function_name]
        to_resolve: List[Tuple[str, str, str]] = []
        seen_funcs: Set[Tuple[str, str]] = set()

        # Regular imported function calls
        for name in _called_names_in_function(target_func):
            if name in imports:
                mod, orig = imports[name]
                to_resolve.append((mod, orig, file_path))

        # Resolve instance method calls and str(var)
        bindings = _var_class_bindings(target_func, imports)
        for var, method in _method_calls(target_func):
            if var in bindings:
                mod, cls = bindings[var]
                to_resolve.append((mod, f"{cls}.{method}", file_path))
        for var in _str_calls(target_func):
            if var in bindings:
                mod, cls = bindings[var]
                to_resolve.append((mod, f"{cls}.__str__", file_path))

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
            mod_funcs = _collect_functions_and_methods(mod_ast)
            mod_imports = _collect_imported_names(mod_ast)

            if orig_name not in mod_funcs:
                continue

            func_node = mod_funcs[orig_name]
            func_src = _unparse_func(func_node)

            if mod not in expanded:
                expanded[mod] = {"file": mod_file, "funcs": {}}
            expanded[mod]["funcs"][orig_name] = func_src

            # Recurse within resolved function/method
            for name in _called_names_in_function(func_node):
                if name in mod_imports:
                    sub_mod, sub_orig = mod_imports[name]
                    if (sub_mod, sub_orig) not in seen_funcs:
                        to_resolve.append((sub_mod, sub_orig, mod_file))

        out: List[str] = []
        for mod in sorted(expanded.keys()):
            for fname in sorted(expanded[mod]["funcs"].keys()):
                out.append(expanded[mod]["funcs"][fname])
                out.append("")
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