# Minimal change to add file path to API information
# In your extract_rest_apis_from_file_with_groq function, change this:

# OLD CODE:
# try:
#     result = json.loads(json_str)
#     print(f"result: {result}")
#     return result.get('apis', [])

# NEW CODE:
# try:
#     result = json.loads(json_str)
#     print(f"result: {result}")
#     apis = result.get('apis', [])
#     # Add file path to each API entry
#     for api in apis:
#         api['file_path'] = file_path
#     return apis

# This change will add the 'file_path' field to each API dictionary returned by the function 