import sys

sys.path.append("/usr/share/python3/")
sys.path.append("/usr/local/share/python3/")

import RRegistry as RR
import RSupport as RS

import kernel_globals as g

print("Created handle! Trying to connect")

# Connect to default path.
status = g.rsupport.connect()
if status != RS.RSupportStatus_Ok:
    print("Error while connecting: " + RS.rsupport_status_msg(status))

# After connecting, options can be set.
g.rsupport.service()

# The frequency should be regulated automatically.
g.rsupport.setOption(RS.RSupportOption_AutoFrequency, True)
# After each loop, the movement state should be
# forwarded to the hardware and the Arduino.
g.rsupport.setOption(RS.RSupportOption_AutoMovementBurst, True)

# Receive the registry instance.
registry = g.rsupport.registry()
g.registry = registry

# Subscribe to inputs.
g.rsupport.subscribe(RR.Type_Int16, RR.Int16_MVMT_STEER_DIRECTION)
g.rsupport.subscribe(RR.Type_Int16, RR.Int16_MVMT_FORWARD_VELOCITY)

# Run the kernel code.
import kernel_code
