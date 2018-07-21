(set-logic AUFNIRA)

;; Formula taken from https://gamedev.stackexchange.com/a/33445
(define-fun mapReal ((x Real) (min Real) (max Real) (outMin Real) (outMax Real)) Real 
    (+ (* (/ (- x min) (- max min)) (- outMax outMin)) outMin))

(declare-fun _forward_velocity_ () Int)
(assert (>= _forward_velocity_ -32768))
(assert (<= _forward_velocity_ 32767))

(declare-fun _motor_fl_ () Int)
(assert (= _motor_fl_ (to_int (mapReal (to_real _forward_velocity_) (- 32768.0) 32767.0 (- 255.0) 255.0))))

(echo "Check if mapReal itself is satisfiable.")

(check-sat)
(get-model)

(echo "Check if negations of expected values are satisfiable.")
(assert (not (and
    (>= _motor_fl_ -255)
    (<= _motor_fl_ 255)
)))

(check-sat)
(get-model)
(echo "If unsat, mapReal works as expected.")