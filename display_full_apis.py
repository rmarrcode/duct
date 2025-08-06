import json
from typing import List, Dict, Any

def display_full_api_info(apis: List[Dict[str, Any]]):
    """Display complete API information with full Django code and Dafny specs"""
    
    print("=" * 100)
    print("COMPLETE DJANGO REST API ANALYSIS")
    print("=" * 100)
    print(f"Total APIs found: {len(apis)}")
    print()
    
    # Group by file path
    files = {}
    for api in apis:
        file_path = api.get('file_path', 'Unknown')
        if file_path not in files:
            files[file_path] = []
        files[file_path].append(api)
    
    # Display by file
    for file_path, file_apis in files.items():
        print(f"📁 FILE: {file_path}")
        print("=" * 100)
        print(f"APIs found: {len(file_apis)}")
        print()
        
        for i, api in enumerate(file_apis, 1):
            print(f"🔗 API #{i}: {api.get('name', 'Unknown')}")
            print(f"   Method: {api.get('http_method', 'UNKNOWN')}")
            print(f"   Description: {api.get('description', 'No description')}")
            print()
            
            print("📝 DJANGO CODE:")
            print("-" * 50)
            django_code = api.get('content_django', 'No Django code available')
            print(django_code)
            print()
            
            print("🔬 DAFNY SPECIFICATION:")
            print("-" * 50)
            dafny_spec = api.get('content_dafny', 'No Dafny specification available')
            print(dafny_spec)
            print()
            
            print("─" * 100)
            print()
    
    # Summary statistics
    print("=" * 100)
    print("SUMMARY STATISTICS")
    print("=" * 100)
    
    # HTTP method distribution
    methods = {}
    for api in apis:
        method = api.get('http_method', 'UNKNOWN')
        methods[method] = methods.get(method, 0) + 1
    
    print("HTTP Methods:")
    for method, count in sorted(methods.items()):
        print(f"  {method}: {count}")
    
    print()
    print(f"Files analyzed: {len(files)}")
    print(f"Total APIs: {len(apis)}")

def display_api_details(apis: List[Dict[str, Any]]):
    """Display detailed view of each API with full code"""
    
    for i, api in enumerate(apis, 1):
        print(f"\n{'='*120}")
        print(f"API #{i}: {api.get('name', 'Unknown')}")
        print(f"{'='*120}")
        
        print(f"📂 File: {api.get('file_path', 'Unknown')}")
        print(f"🔗 Method: {api.get('http_method', 'UNKNOWN')}")
        print(f"📝 Description: {api.get('description', 'No description')}")
        print()
        
        print("🐍 DJANGO IMPLEMENTATION:")
        print("─" * 60)
        django_code = api.get('content_django', 'No Django code available')
        # Split into lines and number them
        django_lines = django_code.split('\n')
        for j, line in enumerate(django_lines, 1):
            print(f"{j:3d}: {line}")
        print()
        
        print("🔬 DAFNY SPECIFICATION:")
        print("─" * 60)
        dafny_spec = api.get('content_dafny', 'No Dafny specification available')
        # Split into lines and number them
        dafny_lines = dafny_spec.split('\n')
        for j, line in enumerate(dafny_lines, 1):
            print(f"{j:3d}: {line}")
        print()

# Example usage with your data
if __name__ == "__main__":
    # Your API data
    apis = [
        {
            'name': 'GraphQLView.as_view',
            'http_method': 'POST',
            'description': 'Handles GraphQL API requests',
            'content_django': "from django.views.decorators.csrf import csrf_exempt\nfrom .graphql.views import GraphQLView\n\nre_path(r'^graphql/$', csrf_exempt(GraphQLView.as_view(backend=backend, schema=schema)), name='api')",
            'content_dafny': '// Dafny function specification\nfunction GraphQLView_as_view(backend: object, schema: object, request: object) returns (response: object)\n  requires backend != null && schema != null && request != null;\n  ensures response != null;\n',
            'file_path': '/Users/ryanmarr/Documents/saleor/saleor/urls.py'
        },
        {
            'name': 'digital_product',
            'http_method': 'GET',
            'description': 'Handles digital product downloads',
            'content_django': "from .product.views import digital_product\n\nre_path(r'^digital-download/(?P<token>[0-9A-Za-z_\\-]+)/$', digital_product, name='digital-product')",
            'content_dafny': '// Dafny function specification\nfunction digital_product(token: string) returns (response: object)\n  requires token != null;\n  ensures response != null;\n',
            'file_path': '/Users/ryanmarr/Documents/saleor/saleor/urls.py'
        },
        {
            'name': 'handle_plugin_per_channel_webhook',
            'http_method': 'POST',
            'description': 'Handles plugin per-channel webhooks',
            'content_django': "from .plugins.views import handle_plugin_per_channel_webhook\n\nre_path(r'^plugins/channel/(?P<channel_slug>[.0-9A-Za-z_\\-]+)/(?P<plugin_id>[.0-9A-Za-z_\\-]+)/', handle_plugin_per_channel_webhook, name='plugins-per-channel')",
            'content_dafny': '// Dafny function specification\nfunction handle_plugin_per_channel_webhook(channel_slug: string, plugin_id: string, request: object) returns (response: object)\n  requires channel_slug != null && plugin_id != null && request != null;\n  ensures response != null;\n',
            'file_path': '/Users/ryanmarr/Documents/saleor/saleor/urls.py'
        },
        {
            'name': 'handle_global_plugin_webhook',
            'http_method': 'POST',
            'description': 'Handles global plugin webhooks',
            'content_django': "from .plugins.views import handle_global_plugin_webhook\n\nre_path(r'^plugins/global/(?P<plugin_id>[.0-9A-Za-z_\\-]+)/', handle_global_plugin_webhook, name='plugins-global')",
            'content_dafny': '// Dafny function specification\nfunction handle_global_plugin_webhook(plugin_id: string, request: object) returns (response: object)\n  requires plugin_id != null && request != null;\n  ensures response != null;\n',
            'file_path': '/Users/ryanmarr/Documents/saleor/saleor/urls.py'
        }
    ]
    
    # Display detailed view
    display_api_details(apis)
    
    print("\n" + "="*100 + "\n")
    
    # Display organized view
    display_full_api_info(apis) 