import importlib, traceback, importlib.machinery, importlib.util, sys, os
try:
    path = os.path.join(os.getcwd(), 'boonify.py')
    loader = importlib.machinery.SourceFileLoader('boonify', path)
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    print('IMPORT OK')
except Exception:
    traceback.print_exc()