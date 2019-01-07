import RRegistry as RR
import RSupport as RS
import kernel_globals as g
from numpy import interp
import math
rsupport = g.rsupport
registry = g.registry
# RVERIFY_BEGIN

d_fl = 33
d_fr = 33
d_rl = 31
d_rr = 31

G = 30

# Start loop.
while(True):
    # Service the Regulation Kernel for newest updates and synchronisation.
    rsupport.service()

    # Get the needed variables from the local copy of the registry.
    # The properties of these variables can be looked up in the wiki.
    steer_direction = registry.getInt16(RR.Int16_MVMT_STEER_DIRECTION)
    vel = registry.getInt16(RR.Int16_MVMT_FORWARD_VELOCITY)

    forward_velocity = interp(vel, [-32768, 32767], [-255, 255])
    # forward_velocity = registry.getInt16(RR.Int16_MVMT_FORWARD_VELOCITY) / 128

    # Set simple motor speeds.
    motor_fl = int(forward_velocity)
    motor_fr = int(forward_velocity)
    motor_rl = int(forward_velocity)
    motor_rr = int(forward_velocity)

    if forward_velocity < -180:
        steer_direction = steer_direction * 0.7

    if forward_velocity > 180:
        steer_direction = steer_direction * 0.7

    # Calculate Wheel Positions
    # =========================

    # Calculate Steering Angle Beta

    # beta = math.pi / 2 - (interp(shifted_steer_direction, [0, 32767 + 32768], [0, math.pi / 13 * 3 + math.pi / 13 * 3]) - math.pi / 13 * 3)
    # beta = math.pi / 2 - interp(steer_direction, [-32768, 32767], [- math.pi / 13 * 3, math.pi / 13 * 3])
    beta_sub = (interp(steer_direction, [-32768, 32767], [-72, 72])) / 100
    beta = (math.pi / 2) - beta_sub

    # A
    A = math.tan(beta) * G

    # Angles.
    beta_fl = math.atan((A + d_fl) / G)
    beta_fr = math.atan((A - d_fr) / G)

    # The rear has to be inverted.
    beta_rl = -math.atan((A + d_rl) / G)
    beta_rr = -math.atan((A - d_rr) / G)

    # Servo-Outputs
    multiplicators_1 = (beta_fl * 2) / math.pi
    multiplicators_2 = (beta_fr * 2) / math.pi
    multiplicators_3 = (beta_rl * 2) / math.pi
    multiplicators_4 = (beta_rr * 2) / math.pi

    if steer_direction >= 0:
        values_1 = 128 + (1 - multiplicators_1) * 128
        values_2 = 128 + (1 - multiplicators_2) * 128
        values_3 = 128 - (1 + multiplicators_3) * 128
        values_4 = 128 - (1 + multiplicators_4) * 128
    else:
        values_1 = 128 - (1 + multiplicators_1) * 128
        values_2 = 128 - (1 + multiplicators_2) * 128
        values_3 = 128 + (1 - multiplicators_3) * 128
        values_4 = 128 + (1 - multiplicators_4) * 128

    # Assign the calculated variables into the registry.
    registry.setInt16(RR.Int16_MVMT_MOTOR_PWM_FL, int(motor_fl))
    registry.setInt16(RR.Int16_MVMT_MOTOR_PWM_FR, int(motor_fr))
    registry.setInt16(RR.Int16_MVMT_MOTOR_PWM_RL, int(motor_rl))
    registry.setInt16(RR.Int16_MVMT_MOTOR_PWM_RR, int(motor_rr))

    registry.setUint8(RR.Uint8_MVMT_SERVO_FL_POSITION, int(values_1))
    registry.setUint8(RR.Uint8_MVMT_SERVO_FR_POSITION, int(values_2))
    registry.setUint8(RR.Uint8_MVMT_SERVO_RL_POSITION, int(values_3))
    registry.setUint8(RR.Uint8_MVMT_SERVO_RR_POSITION, int(values_4))
