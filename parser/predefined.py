logic = """
(set-logic QF_UFNIRA)
"""

internals = """
(declare-fun _forward_velocity_ () Int)
(declare-fun _steer_direction_ () Int)
(assert (>= _forward_velocity_ (- 32768)))
(assert (<= _forward_velocity_ 32767))

(assert (or 
    (and (>= _steer_direction_ (- 32768)) (<= _steer_direction_ (- 10)))
    (and (>= _steer_direction_ 10) (<= _steer_direction_ 32767))))

(declare-fun _motor_fl_ () Int)
(declare-fun _motor_fr_ () Int)
(declare-fun _motor_rl_ () Int)
(declare-fun _motor_rr_ () Int)
(declare-fun _servo_fl_ () Int)
(declare-fun _servo_fr_ () Int)
(declare-fun _servo_rl_ () Int)
(declare-fun _servo_rr_ () Int)

;; Formula taken from https://gamedev.stackexchange.com/a/33445
(define-fun mapReal ((x Real) (min Real) (max Real) (outMin Real) (outMax Real)) Real 
    (+ (* (/ (- x min) (- max min)) (- outMax outMin)) outMin))
 
(define-fun mapInt ((x Int) (min Int) (max Int) (outMin Int) (outMax Int)) Int 
    (+ (* (div (- x min) (- max min)) (- outMax outMin)) outMin))

(declare-fun pi () Real)
(assert (= pi 3.14159265359))
"""

# Every check case must be wrapped inside an (assert (not ... )) block to check against it.
checkCases = [
    {
        'name': 'Motor FL Minimum -255',
        'expression': '(>= _motor_fl_ (- 255))'
    },
    {
        'name': 'Motor FL Maximum 255',
        'expression': '(<= _motor_fl_ 255)'
    },
    {
        'name': 'Motor FR Minimum -255',
        'expression': '(>= _motor_fr_ (- 255))'
    },
    {
        'name': 'Motor FR Maximum 255',
        'expression': '(<= _motor_fr_ 255)'
    },
    {
        'name': 'Motor RL Minimum -255',
        'expression': '(>= _motor_rl_ (- 255))'
    },
    {
        'name': 'Motor RL Maximum 255',
        'expression': '(<= _motor_rl_ 255)'
    },
    {
        'name': 'Motor RR Minimum -255',
        'expression': '(>= _motor_rr_ (- 255))'
    },
    {
        'name': 'Motor RR Maximum 255',
        'expression': '(<= _motor_rr_ 255)'
    },
    {
        'name': 'Servo FL Minimum',
        'expression': '(>= _servo_fl_ 0)'
    },
    {
        'name': 'Servo FL Maximum',
        'expression': '(<= _servo_fl_ 255)'
    },
    {
        'name': 'Servo FR Minimum',
        'expression': '(>= _servo_fr_ 0)'
    },
    {
        'name': 'Servo FR Maximum',
        'expression': '(<= _servo_fr_ 255)'
    },
    {
        'name': 'Servo RL Minimum',
        'expression': '(>= _servo_rl_ 0)'
    },
    {
        'name': 'Servo RL Maximum',
        'expression': '(<= _servo_rl_ 255)'
    },
    {
        'name': 'Servo RR Minimum',
        'expression': '(>= _servo_rr_ 0)'
    },
    {
        'name': 'Servo RR Maximum',
        'expression': '(<= _servo_rr_ 255)'
    },
    {
        'name': 'Servos FL and FR standing like /\\ must mean, motors FL and FR must go in opposite directions.',
        'expression': '(=> (and (> _servo_fl_ 128) (< _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (<= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (>= _motor_fr_ 0))))'
    },
    {
        # This rule includes small space for very small mistakes.
        'name': 'Servos FL and FR standing like \\/ must never happen.',
        'expression': '(and (=> (<= _servo_fl_ 125) (<= _servo_fr_ 128)) (=> (>= _servo_fr_ 130) (>= _servo_fl_ 125)))'
    },
    {
        # This rule includes small space for very small mistakes.
        'name': 'Servos RL and RR standing like /\\ must never happen.',
        'expression': '(and (=> (>= _servo_rl_ 130) (>= _servo_rr_ 128)) (=> (<= _servo_rr_ 125) (<= _servo_rl_ 128)))'
    },
    {
        'name': 'Servos RL and RR standing like \\/ must mean, motors RL and RR must go in opposite directions.',
        'expression': '(=> (and (< _servo_rl_ 128) (> _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (<= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (>= _motor_rr_ 0))))'
    },
    {
        'name': 'Servos FL and FR standing like // must mean, motors FL and FR go in same direction.',
        'expression': '(=> (and (> _servo_fl_ 128) (> _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (>= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (<= _motor_fr_ 0))))'
    },
    {
        'name': 'Servos RL and RR standing like // must mean, motors RL and RR go in same direction.',
        'expression': '(=> (and (> _servo_rl_ 128) (> _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (>= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (<= _motor_rr_ 0))))'
    },
    {
        'name': 'Servos FL and FR standing like \\\\ must mean, motors FL and FR go in same direction.',
        'expression': '(=> (and (< _servo_fl_ 128) (< _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (>= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (<= _motor_fr_ 0))))'
    },
    {
        'name': 'Servos RL and RR standing like \\\\ must mean, motors RL and RR go in same direction.',
        'expression': '(=> (and (< _servo_rl_ 128) (< _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (>= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (<= _motor_rr_ 0))))'
    }
]

check_sat = """
(check-sat)
"""

get_model = """
(get-model)
"""
