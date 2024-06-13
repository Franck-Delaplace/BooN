# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information
import os
import sys
sys.path.insert(0, os.path.abspath('C:\\Users\\franck.delaplace\\OneDrive - Universite Evry Val d\'Essonne\\BooN'))


project = 'BooN'
copyright = '2024, Franck Delaplace'
author = 'Franck Delaplace'
release = '1.03'

# -- General configuration -------------------------------
# --------------------

# linkcode_url = '{{ repo }}/blob/master/{{ object }}#L{{ lineno }}'   #Git Hub theme

extensions = [
                'sphinx.ext.autodoc',
                'sphinx_rtd_theme',
                'sphinx.ext.githubpages',
               # 'sphinx.ext.napoleon',
               ]

templates_path = ['_templates']
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

autodoc_param_description = [
    'param',
    'type',
    'return',
    'rtype'
    'default'
]


html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']

