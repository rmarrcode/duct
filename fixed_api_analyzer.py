import os
from groq import Groq
import re
from typing import List, Dict, Any
import yaml
from tqdm import tqdm
import json

# Configuration
API_KEY = "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"
DJANGO_PROJECT_PATH = "/Users/ryanmarr/Documents/saleor"
MODEL_NAME = "meta-llama/llama-4-scout-17b-16e-instruct"
MAX_TOKENS = 4096  # Increased from 2048
TEMPERATURE = 0.1
TOP_P = 1
STREAM = False

# Groq client setup
client = Groq(api_key=API_KEY)

def find_django_files(directory: str) -> List[str]:
    """Perform DFS to find all Python files in Django project"""
    django_files = []
    
    for root, dirs, files in os.walk(directory):
        # Skip common directories that don't contain Django code
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['node_modules', '__pycache__', 'venv', 'env', '.git']]
        
        for file in files:
            if file.endswith('.py'):
                file_path = os.path.join(root, file)
                django_files.append(file_path)
    
    return django_files

def extract_json_from_response(response: str) -> str:
    """Extract valid JSON from Groq response with better error handling"""
    # Try multiple approaches to extract JSON
    
    # First, try to find complete JSON object with balanced braces
    start_idx = response.find('{')
    if start_idx == -1:
        return None
    
    # Count braces to find the matching closing brace
    brace_count = 0
    end_idx = start_idx
    
    for i, char in enumerate(response[start_idx:], start_idx):
        if char == '{':
            brace_count += 1
        elif char == '}':
            brace_count -= 1
            if brace_count == 0:
                end_idx = i + 1
                break
    
    if brace_count == 0:
        json_str = response[start_idx:end_idx]
        # Validate that it's valid JSON
        try:
            json.loads(json_str)
            return json_str
        except json.JSONDecodeError:
            pass
    
    # If the above fails, try regex approach
    json_match = re.search(r'\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}', response, re.DOTALL)
    if json_match:
        json_str = json_match.group(0)
        try:
            json.loads(json_str)
            return json_str
        except json.JSONDecodeError:
            pass
    
    return None

def extract_rest_apis_from_file_with_groq(file_path: str) -> List[Dict[str, Any]]:
    """Use Groq to analyze file content and find REST APIs"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()  
        
        # Skip files that don't contain common Django/API keywords
        if not any(keyword in content.lower() for keyword in ['api', 'view', 'rest', 'http', 'request', 'response', 'serializer']):
            return []
        
        # Limit content to first 3000 chars to avoid token limits
        content_preview = content[:3000]
        
        prompt = f"""
        Analyze this Python file and identify all Django REST API functions or classes.
        
        File: {file_path}
        
        Look for:
        1. Functions that handle HTTP methods (GET, POST, PUT, DELETE, PATCH)
        2. Functions that process requests and return responses
        3. Any other REST API endpoints
        
        File content (first 3000 chars):
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
        
        try:
            completion = client.chat.completions.create(
                model=MODEL_NAME,
                messages=[
                    {
                        "role": "user",
                        "content": prompt
                    }
                ],
                temperature=TEMPERATURE,
                max_tokens=MAX_TOKENS,
                top_p=TOP_P,
                stream=STREAM
            )
            
            response = completion.choices[0].message.content.strip()
            
            # Extract JSON using improved method
            json_str = extract_json_from_response(response)
            
            if json_str:
                try:
                    result = json.loads(json_str)
                    return result.get('apis', [])
                except json.JSONDecodeError as e:
                    print(f"Failed to parse JSON from response for {file_path}")
                    print(f"JSON string: {json_str[:200]}...")
                    print(f"Error: {e}")
                    return []
            else:
                print(f"No valid JSON found in response for {file_path}")
                print(f"Response preview: {response[:200]}...")
                return []
                
        except Exception as e:
            print(f"Error calling Groq API for {file_path}: {e}")
            return []
            
    except Exception as e:
        print(f"Error reading file {file_path}: {e}")
        return []

def main():
    """Main execution function"""
    print(f"Analyzing Django project at: {DJANGO_PROJECT_PATH}")
    
    # Find all Python files
    django_files = find_django_files(DJANGO_PROJECT_PATH)
    print(f"Found {len(django_files)} Python files")
    
    # Extract REST APIs
    all_apis = []
    for file_path in tqdm(django_files, desc="Analyzing files"):
        apis = extract_rest_apis_from_file_with_groq(file_path)
        if apis:  # Only extend if we found APIs
            all_apis.extend(apis)
            
    print(f"Total APIs found: {len(all_apis)}")
    
    # Save results to file
    with open('api_analysis.json', 'w') as f:
        json.dump(all_apis, f, indent=2)
        
    print(f"Results saved to api_analysis.json")

if __name__ == "__main__":
    main() 