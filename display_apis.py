import json
from typing import List, Dict, Any

def display_api_info(apis: List[Dict[str, Any]]):
    """Display API information in a clear, organized format"""
    
    print("=" * 80)
    print("DJANGO REST API ANALYSIS RESULTS")
    print("=" * 80)
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
        print("-" * 60)
        print(f"APIs found: {len(file_apis)}")
        print()
        
        for i, api in enumerate(file_apis, 1):
            print(f"  {i}. {api.get('name', 'Unknown')}")
            print(f"     Method: {api.get('http_method', 'UNKNOWN')}")
            print(f"     Description: {api.get('description', 'No description')}")
            print(f"     Django Code: {api.get('content_django', 'No code')[:100]}...")
            print(f"     Dafny Spec: {api.get('content_dafny', 'No spec')[:100]}...")
            print()
        
        print()
    
    # Summary statistics
    print("=" * 80)
    print("SUMMARY STATISTICS")
    print("=" * 80)
    
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

def display_api_table(apis: List[Dict[str, Any]]):
    """Display APIs in a table format"""
    
    print("=" * 120)
    print("API DETAILS TABLE")
    print("=" * 120)
    
    # Table header
    print(f"{'#':<3} {'Name':<30} {'Method':<8} {'File':<50}")
    print("-" * 120)
    
    for i, api in enumerate(apis, 1):
        name = api.get('name', 'Unknown')[:28] + ".." if len(api.get('name', '')) > 30 else api.get('name', 'Unknown')
        method = api.get('http_method', 'UNKNOWN')
        file_path = api.get('file_path', 'Unknown').split('/')[-1]  # Just filename
        
        print(f"{i:<3} {name:<30} {method:<8} {file_path:<50}")
    
    print("-" * 120)

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
    
    # Display in organized format
    display_api_info(apis)
    print("\n" + "="*80 + "\n")
    display_api_table(apis) 