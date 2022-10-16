(declare-const Myshkin Bool)
(declare-const Ulyanov Bool)
(declare-const Lomonosov Bool)
(assert (= Myshkin (and (not Ulyanov) Lomonosov)))
(assert (= Ulyanov (=> (not Myshkin)(not Lomonosov))))
(assert (= Lomonosov (and Lomonosov (or (not Ulyanov) (not Myshkin)))))
(check-sat)
(get-model)

;We get that Ulyanov is true and rest are false. So Ulyanov is not guilty, and Myshkin and Lomonosov are guilty.