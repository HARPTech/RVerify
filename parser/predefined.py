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

checks = """
(assert (not (and

(>= _motor_fl_ (- 255))
(<= _motor_fl_ 255)
(>= _motor_fr_ (- 255))
(<= _motor_fr_ 255)
(>= _motor_rl_ (- 255))
(<= _motor_rl_ 255)
(>= _motor_rr_ (- 255))
(<= _motor_rr_ 255)

(=> (or (> _steer_direction_ 1) (< _steer_direction_ (- 1)))
    (and
     (>= _servo_fl_ 0)
     (<= _servo_fl_ 255)
     (>= _servo_fr_ 0)
     (<= _servo_fr_ 255)
     (>= _servo_rl_ 0)
     (<= _servo_rl_ 255)
     (>= _servo_rr_ 0)
     (<= _servo_rr_ 255)
     ))

;; Combined Properties
;; -------------------

(=> (and (> _servo_fl_ 128) (< _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (<= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (>= _motor_fr_ 0))))
(=> (and (> _servo_fr_ 128) (< _servo_fl_ 128)) (or (and (>= _motor_fl_ 0) (<= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (>= _motor_fr_ 0))))
(=> (and (> _servo_rl_ 128) (< _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (<= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (>= _motor_rr_ 0))))
(=> (and (> _servo_rr_ 128) (< _servo_rl_ 128)) (or (and (>= _motor_rl_ 0) (<= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (>= _motor_rr_ 0))))
(=> (and (> _servo_fl_ 128) (> _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (>= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (<= _motor_fr_ 0))))
(=> (and (> _servo_rl_ 128) (> _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (>= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (<= _motor_rr_ 0))))

)))
"""

check_sat = """
(check-sat)
"""

get_model = """
(get-model)
"""
