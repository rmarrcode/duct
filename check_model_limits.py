import os
from groq import Groq
import tiktoken

# Configuration
API_KEY = "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"
DJANGO_PROJECT_PATH = "/Users/ryanmarr/Documents/saleor"

# Groq client setup
client = Groq(api_key=API_KEY)

def get_model_limits():
    """Get current model limits from Groq"""
    models = {
        "llama-4-scout-17b-16e-instruct": {
            "max_tokens": 32768,
            "max_input_tokens": 32768,
            "max_output_tokens": 4096
        },
        "deepseek-r1-distill-llama-70b": {
            "max_tokens": 32768,
            "max_input_tokens": 32768,
            "max_output_tokens": 4096
        },
        "mixtral-8x7b-32768": {
            "max_tokens": 32768,
            "max_input_tokens": 32768,
            "max_output_tokens": 4096
        },
        "llama-4-2024-04-09": {
            "max_tokens": 32768,
            "max_input_tokens": 32768,
            "max_output_tokens": 4096
        }
    }
    return models

def count_tokens(text: str, model: str = "cl100k_base") -> int:
    """Count tokens in text using tiktoken"""
    try:
        encoding = tiktoken.get_encoding(model)
        return len(encoding.encode(text))
    except:
        # Fallback: rough estimation (1 token ≈ 4 characters)
        return len(text) // 4

def calculate_request_size(prompt: str, model: str) -> dict:
    """Calculate the size of a request for a given model"""
    models = get_model_limits()
    model_info = models.get(model, {})
    
    # Count tokens in prompt
    prompt_tokens = count_tokens(prompt)
    
    # Calculate total request size
    total_tokens = prompt_tokens + model_info.get("max_output_tokens", 4096)
    
    return {
        "prompt_tokens": prompt_tokens,
        "max_output_tokens": model_info.get("max_output_tokens", 4096),
        "total_tokens": total_tokens,
        "max_tokens": model_info.get("max_tokens", 32768),
        "within_limit": total_tokens <= model_info.get("max_tokens", 32768),
        "available_tokens": model_info.get("max_tokens", 32768) - total_tokens
    }

def find_optimal_content_size(file_path: str, model: str, max_content_chars: int = 3000) -> int:
    """Find optimal content size that fits within model limits"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Start with a small size and increase
        for size in [1000, 2000, 3000, 4000, 5000, 6000, 8000, 10000]:
            content_preview = content[:size]
            
            prompt = f"""
            Analyze this Python file and identify all Django REST API functions or classes.
            
            File: {file_path}
            
            Look for:
            1. Functions that handle HTTP methods (GET, POST, PUT, DELETE, PATCH)
            2. Functions that process requests and return responses
            3. Any other REST API endpoints
            
            File content (first {size} chars):
            {content_preview}
            
            IMPORTANT: Return ONLY valid JSON with this exact structure:
            {{
                "apis": [
                    {{
                        "name": "function_or_class_name",
                        "http_method": "GET|POST|PUT|DELETE|PATCH|UNKNOWN",
                        "description": "Brief description of what this API does",
                        "content_django": "actual function and implementation",
                        "content_dafny": "Based on the django function, create a Dafny function specification with preconditions and postconditions"
                    }}
                ]
            }}
            
            If no REST APIs are found, return: {{"apis": []}}
            Do not include any text before or after the JSON.
            """
            
            request_info = calculate_request_size(prompt, model)
            
            if not request_info["within_limit"]:
                return size - 1000  # Return previous size that worked
            
        return max_content_chars  # If all sizes work, return max
        
    except Exception as e:
        print(f"Error analyzing {file_path}: {e}")
        return 2000  # Default safe size

def main():
    """Main function to analyze model limits and file sizes"""
    print("=== GROQ MODEL LIMITS ===")
    models = get_model_limits()
    
    for model_name, limits in models.items():
        print(f"\n📊 Model: {model_name}")
        print(f"   Max Tokens: {limits['max_tokens']:,}")
        print(f"   Max Input Tokens: {limits['max_input_tokens']:,}")
        print(f"   Max Output Tokens: {limits['max_output_tokens']:,}")
    
    print("\n=== TESTING FILE SIZES ===")
    
    # Test with a sample file
    django_files = []
    for root, dirs, files in os.walk(DJANGO_PROJECT_PATH):
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['node_modules', '__pycache__', 'venv', 'env', '.git']]
        for file in files:
            if file.endswith('.py'):
                file_path = os.path.join(root, file)
                django_files.append(file_path)
                if len(django_files) >= 5:  # Test first 5 files
                    break
        if len(django_files) >= 5:
            break
    
    for file_path in django_files:
        print(f"\n📁 Testing: {os.path.basename(file_path)}")
        
        for model_name in models.keys():
            optimal_size = find_optimal_content_size(file_path, model_name)
            print(f"   {model_name}: {optimal_size:,} chars optimal")
    
    print("\n=== RECOMMENDATIONS ===")
    print("1. Use content preview of 2000-3000 characters for most files")
    print("2. For large files, limit to 2000 characters to be safe")
    print("3. Consider using smaller models for large files")
    print("4. Implement retry logic with smaller content sizes")

if __name__ == "__main__":
    main() 