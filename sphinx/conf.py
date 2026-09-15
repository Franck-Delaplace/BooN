# Configuration file for the Sphinx documentation builder.
 
import os
import sys
#sys.path.insert(0, os.path.abspath('C:\\Users\\franck.delaplace\\OneDrive - Universite Evry Val d\'Essonne\\BooN'))
sys.path.insert(0, os.path.abspath('..'))  #relative path

project = 'BooN'
copyright = '2024, Franck Delaplace'
author = 'Franck Delaplace'
release = '1.05'

# -- General configuration -------------------------------
# linkcode_url = '{{ repo }}/blob/master/{{ object }}#L{{ lineno }}'   #Git Hub theme

extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.napoleon',
    'sphinx_rtd_theme',
    'sphinx.ext.viewcode',
    'sphinx.ext.githubpages',
]

# Autodoc settings: include members and mock heavy optional dependencies
autodoc_default_options = {
    'members': True,
    'undoc-members': True,
    'show-inheritance': True,
}

# Mock imports so Sphinx can import the project even if heavy deps are missing
autodoc_mock_imports = [
    'z3', 'netgraph', 'networkx', 'pulp', 'sympy', 'libsbml', 'tqdm', 'matplotlib', 'pulp', 'libsbml', 'numpy', 'PyQt5', 'tabulate'
]

# Use both class and __init__ docstrings when documenting classes
autoclass_content = 'both'
 
templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']
html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']

# autodoc_param_description = [
#     'param',
#     'type',
#     'return',
#     'rtype'
#     'default'
# ]
