#!/usr/bin/env python3
"""
Django Model Extractor

This script extracts all Django models from a project and converts them to YAML format.
Can be run from any directory by setting the appropriate environment variables.

Usage:
    python extract_models.py [project_path] [output_file]

Examples:
    python extract_models.py /path/to/django/project models.yml
    python extract_models.py /Users/ryanmarr/Documents/saleor saleor_schema.yml
"""

import os
import sys
import yaml
import argparse
from pathlib import Path


def setup_django(project_path, settings_module=None):
    """
    Setup Django environment for external scripts
    
    Args:
        project_path (str): Path to the Django project
        settings_module (str): Django settings module (e.g., 'saleor.settings')
    """
    # Add project to Python path
    if project_path not in sys.path:
        sys.path.insert(0, project_path)
    
    # Set Django settings module
    if settings_module:
        os.environ.setdefault('DJANGO_SETTINGS_MODULE', settings_module)
    else:
        # Try to auto-detect settings module
        project_name = Path(project_path).name
        possible_settings = [
            f'{project_name}.settings',
            'settings',
            'config.settings'
        ]
        
        for setting in possible_settings:
            try:
                os.environ.setdefault('DJANGO_SETTINGS_MODULE', setting)
                break
            except:
                continue
    
    # Import and setup Django
    import django
    django.setup()
    
    return True


def django_type_to_yaml_type(field):
    """
    Convert Django field type to YAML type
    
    Args:
        field: Django model field
        
    Returns:
        str: YAML type
    """
    field_type = type(field).__name__
    
    type_mapping = {
        'AutoField': 'int',
        'BigAutoField': 'int',
        'IntegerField': 'int',
        'BigIntegerField': 'int',
        'PositiveIntegerField': 'int',
        'SmallIntegerField': 'int',
        'CharField': 'string',
        'TextField': 'string',
        'EmailField': 'string',
        'URLField': 'string',
        'SlugField': 'string',
        'DateTimeField': 'string',
        'DateField': 'string',
        'TimeField': 'string',
        'BooleanField': 'boolean',
        'NullBooleanField': 'boolean',
        'DecimalField': 'decimal',
        'FloatField': 'decimal',
        'BinaryField': 'binary',
        'JSONField': 'json',
        'UUIDField': 'string',
        'FileField': 'string',
        'ImageField': 'string',
        'ForeignKey': 'int',
        'OneToOneField': 'int',
        'ManyToManyField': 'int',
    }
    
    return type_mapping.get(field_type, 'string')


def extract_models_to_yaml():
    """
    Extract all Django models to YAML format
    
    Returns:
        list: List of table definitions
    """
    from django.apps import apps
    
    tables = []
    
    for app_config in apps.get_app_configs():
        app_name = app_config.label
        
        # Skip Django built-in apps we don't need
        skip_apps = ['admin', 'sessions', 'messages', 'staticfiles', 'contenttypes']
        if app_name in skip_apps:
            continue
            
        for model in app_config.get_models():
            # Skip proxy models and abstract models
            if model._meta.proxy or model._meta.abstract:
                continue
                
            table = {
                'name': model._meta.db_table,
                'columns': []
            }
            
            # Add primary key
            pk_field = model._meta.pk
            if pk_field:
                table['columns'].append({
                    'name': pk_field.column,
                    'type': django_type_to_yaml_type(pk_field)
                })
            
            # Add regular fields
            for field in model._meta.fields:
                if field != pk_field:  # Skip primary key as it's already added
                    table['columns'].append({
                        'name': field.column,
                        'type': django_type_to_yaml_type(field)
                    })
            
            # Add many-to-many fields (they create junction tables)
            for field in model._meta.many_to_many:
                # Create junction table
                junction_table_name = field.m2m_column_name() if hasattr(field, 'm2m_column_name') else f'{model._meta.db_table}_{field.name}'
                
                junction_table = {
                    'name': junction_table_name,
                    'columns': [
                        {'name': 'id', 'type': 'int'},
                        {'name': f'{model._meta.db_table}_id', 'type': 'int'},
                        {'name': f'{field.related_model._meta.db_table}_id', 'type': 'int'}
                    ]
                }
                tables.append(junction_table)
            
            tables.append(table)
    
    return tables


def main():
    """Main function"""
    parser = argparse.ArgumentParser(description='Extract Django models to YAML format')
    parser.add_argument('project_path', help='Path to Django project')
    parser.add_argument('output_file', help='Output YAML file')
    parser.add_argument('--settings', help='Django settings module (e.g., saleor.settings)')
    
    args = parser.parse_args()
    
    # Validate project path
    project_path = os.path.abspath(args.project_path)
    if not os.path.exists(project_path):
        print(f"Error: Project path '{project_path}' does not exist")
        sys.exit(1)
    
    try:
        # Setup Django
        print(f"Setting up Django for project: {project_path}")
        setup_django(project_path, args.settings)
        
        # Extract models
        print("Extracting models...")
        tables = extract_models_to_yaml()
        
        # Write to YAML file
        output_file = args.output_file
        with open(output_file, 'w') as f:
            yaml.dump(tables, f, default_flow_style=False, sort_keys=False)
        
        print(f"Successfully generated schema with {len(tables)} tables in '{output_file}'")
        
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main() 