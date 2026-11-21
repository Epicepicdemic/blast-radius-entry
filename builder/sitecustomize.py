import os

if "BR_TRACES" in os.environ:
    import probe
    probe.start()
