;; This file tries to implement the same logic as the standard initialisation
;; code, with the addition of using bitvectors instead of integers and floats instead of reals.
;; The problem with this code is the time it takes to compute a result:
;; Just validating this setup takes as long as an entire check with
;; RVerify using Real and Int sorts. The added
;; precision (it is guaranteed to work with all possible bit-assignments) gives no additional benefit over
;; the Int-inputs and Real numbers in RVerify, because all possible assignments are already covered using
;; the Integer logic.

;; Logic
(set-logic QF_FPBV)

;; Input Variables
(declare-fun _forward_velocity_bv_ () (_ BitVec 64))
(declare-fun _steer_direction_bv_ () (_ BitVec 64))
(declare-fun _forward_velocity_ () Float64)
(declare-fun _steer_direction_ () Float64)

(assert 
  (and 
    (bvsge _forward_velocity_bv_ (bvneg (_ bv32768 64)))
    (bvslt _forward_velocity_bv_ (_ bv32767 64))
))

(assert (and
  (or 
    (and (bvsge _steer_direction_bv_ (bvneg (_ bv32768 64))) (bvslt _steer_direction_bv_ (bvneg (_ bv10 64))))
    (and (bvsge _steer_direction_bv_ (_ bv10 64)) (bvslt _steer_direction_bv_ (_ bv32767 64))))
))

;; Conversion to IEEE Floating Point Numbers
;; -----------------------------------------
;; Rounding Mode is always RTN (Round To Null), like the default in Python.
;; Floating Poing Numbers used are Float64: which is a synonym for (_ FloatingPoint 11 53).
(assert (= _forward_velocity_ ((_ to_fp 11 53) RTN _forward_velocity_bv_)))
(assert (= _steer_direction_ ((_ to_fp 11 53) RTN _steer_direction_bv_)))

;; Output Variables
;; ----------------
;; Motor Speed (m) Range: -255 <= m <= 255
;; Servo (s) Range: 0 <= s <= 255
;; The ranges are checked on assignments at the end too.

(declare-fun _motor_fl_bv_ () (_ BitVec 9))
(declare-fun _motor_fr_bv_ () (_ BitVec 9))
(declare-fun _motor_rl_bv_ () (_ BitVec 9))
(declare-fun _motor_rr_bv_ () (_ BitVec 9))
(declare-fun _servo_fl_bv_ () (_ BitVec 8))
(declare-fun _servo_fr_bv_ () (_ BitVec 8))
(declare-fun _servo_rl_bv_ () (_ BitVec 8))
(declare-fun _servo_rr_bv_ () (_ BitVec 8))

(declare-fun _motor_fl_ () Float64)
(declare-fun _motor_fr_ () Float64)
(declare-fun _motor_rl_ () Float64)
(declare-fun _motor_rr_ () Float64)
(declare-fun _servo_fl_ () Float64)
(declare-fun _servo_fr_ () Float64)
(declare-fun _servo_rl_ () Float64)
(declare-fun _servo_rr_ () Float64)

(assert (and
	 (= _motor_fl_bv_ ((_ fp.to_sbv 9) RTN _motor_fl_))
	 (= _motor_fr_bv_ ((_ fp.to_sbv 9) RTN _motor_fr_))
	 (= _motor_rl_bv_ ((_ fp.to_sbv 9) RTN _motor_rl_))
	 (= _motor_rr_bv_ ((_ fp.to_sbv 9) RTN _motor_rr_))
	 (= _servo_fl_bv_ ((_ fp.to_sbv 8) RTN _servo_fl_))
	 (= _servo_fr_bv_ ((_ fp.to_sbv 8) RTN _servo_fr_))
	 (= _servo_rl_bv_ ((_ fp.to_sbv 8) RTN _servo_rl_))
	 (= _servo_rr_bv_ ((_ fp.to_sbv 8) RTN _servo_rr_))
	 ))

;; Utility Function
(define-fun mapReal ((x Float64) (min Float64) (max Float64) (outMin Float64) (outMax Float64)) Float64
    (fp.add (fp.mul RTN (fp.div RTN (fp.neg x min) (fp.neg max min)) (fp.neg outMax outMin)) outMin))
 
;; Check SAT
(check-sat)
