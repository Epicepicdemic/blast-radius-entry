import os

if "BR_TRACES" in os.environ:
    import probe
    probe.start()

if "CENSUS_CHILD_OUT" in os.environ:
    # A process started by a census test (spawned pool worker or subprocess).
    import census_plugin
    census_plugin.child_process(os.environ["CENSUS_CHILD_OUT"])
