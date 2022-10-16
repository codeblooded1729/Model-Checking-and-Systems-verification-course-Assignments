(define-fun T ((x0 Bool) (x1 Bool) (x2 Bool) (y0 Bool) (y1 Bool) (y2 Bool))
     (Bool)
     (or (and (= x2 false) (= y0 false) (= y1 x0) (= y2 x1))
	     (and (= x2 true) (= y2 true) (= y1 x2) (= y0 x1)))
)
(define-fun T2 ((x0 Bool) (x1 Bool) (x2 Bool) (y0 Bool) (y1 Bool) (y2 Bool))
     (Bool)
     (exists ((z0 Bool) (z1 Bool) (z2 Bool))
       (and (T x0 x1 x2 z0 z1 z2) (T z0 z1 z2 y0 y1 y2))))
(define-fun T3 ((x0 Bool) (x1 Bool) (x2 Bool) (y0 Bool) (y1 Bool) (y2 Bool))
     (Bool)
     (exists ((z0 Bool) (z1 Bool) (z2 Bool))
       (and (T2 x0 x1 x2 z0 z1 z2) (T z0 z1 z2 y0 y1 y2))))

(declare-const a0 Bool)
(declare-const a1 Bool)
(declare-const a2 Bool)    
(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Bool)

(assert (T3 a0 a1 a2 b0 b1 b2)) 
(check-sat)
(get-model)

;gives b0=false, b1=false, b2=false. That is , x=0

(assert (not (and (not b0)(not b1) (not b2))))
(check-sat)
(get-model)

;gives b0=true, b1=true, b2=true. That is , x=7

(assert (not (and b0 b1 b2)))
(check-sat)
(get-model)

;gives b0=false, b1=true, b2=true. That is , x=3

(assert (not (and (not b0) b1 b2)))
(check-sat)

;gives unsat

;so all states reachable after 3 iterations are x=0,3,7