"""Install the pin-only observer before a freshly spawned Python worker imports the suite."""
import builtins
import os
import sys

mode=os.environ.get("BR5_PIN_WORKER")
if mode and any("multiprocessing.spawn import spawn_main" in s for s in sys.orig_argv):
    if mode=="operands":
        import operands
        builtins._br5_compare=operands.compare
        builtins._br5_capture=operands.capture
        sys.meta_path.insert(0,operands.Finder())
        if operands.monitor.get_tool(operands.tool) is None:
            operands.monitor.use_tool_id(operands.tool,'pinned test code')
            operands.monitor.register_callback(operands.tool,operands.monitor.events.PY_START,operands.entry)
            operands.monitor.set_events(operands.tool,operands.monitor.events.PY_START)
    elif mode=="fields":
        import field_uses
        builtins._br5_lookup=field_uses.lookup
        builtins._br5_namespace=field_uses.namespace
        builtins._br5_field=field_uses.read
        builtins._br5_member=field_uses.member
        builtins._br5_arity=field_uses.arity
        sys.meta_path.insert(0,field_uses.Finder())
    elif mode=="dispatch":
        import dispatch_uses
        dispatch_uses.install()
        sys.meta_path.insert(0,dispatch_uses.Finder())
    elif mode=="prefixes":
        import prefixes
        prefixes.install()
        sys.meta_path.insert(0,prefixes.Finder())
    elif mode=="passive":
        import passive_ops
        passive_ops.install()
        sys.meta_path.insert(0,passive_ops.Finder())
