#[test]
fn poly_simp() {
    test_cases! {
        definitions = "
            (declare-fun k () Int)
            (declare-fun n () Int)
            (declare-fun a () Int)
            (declare-fun x () Real)
            (declare-fun y () Real)
        ",
        "Simple working examples" {
            "(step t1 (cl (= (+ (* 2 k) (* 1 n)) (+ n (* k 2)))) :rule poly_simp)": true,
            "(step t1 (cl (=
                (+ (* 2.0 y) (* 1.0 x))
                (+ x (* y 2.0))
            )) :rule poly_simp)": true,
        }
        "Coefficient cancellation" {
            "(step t1 (cl (=
                (+ (* 2.0 x) (* (- 2.0) x) y)
                (* y 1.0)
            )) :rule poly_simp)": true,
            "(step t1 (cl (= (+ 2 (- 1) (- 1)) 0)) :rule poly_simp)": true,
            "(step t1 (cl (= (* 0.0 x) 0.0)) :rule poly_simp)": true,
        }
        "Failing examples" {
            "(step t1 (cl (= (+ k k) (+ k 0))) :rule poly_simp)": false,
            "(step t1 (cl (= (* 2.0 x) (+ 2.0 x))) :rule poly_simp)": false,
        }
        "Regression" {
            "(step t1 (cl (= (- a (* 2 2)) (+ a (* -1 (* 2 2))) )) :rule poly_simp)": true,
            "(step t1 (cl (= (* 0 (div 0 0)) 0)) :rule poly_simp)": true,
        }
    }
}

#[test]
fn poly_simp_ff() {
    test_cases! {
        definitions = "
            (declare-fun x () (_ FiniteField 5))
            (declare-fun y () (_ FiniteField 5))
        ",
        "Finite field normalization" {
            "(step t1 (cl (= (ff.add x y) (ff.add y x))) :rule poly_simp)": true,
            "(step t1 (cl (= (ff.neg #f1m5) (ff.mul #f4m5 #f1m5))) :rule poly_simp)": true,
            "(step t1 (cl (= (ff.add #f0m5 #f1m5 #f2m5 #f3m5) #f1m5)) :rule poly_simp)": true,
            "(step t1 (cl (= (ff.neg x) (ff.mul #f4m5 x))) :rule poly_simp)": true,
            "(step t1 (cl (= (ff.add x x x) (ff.mul #f3m5 x))) :rule poly_simp)": true,
        }
        "Failing examples" {
            "(step t1 (cl (= (ff.add x y) x)) :rule poly_simp)": false,
            "(step t1 (cl (= (ff.add #f1m5 #f1m5) #f1m5)) :rule poly_simp)": false,
        }
    }
}

#[test]
fn poly_simp_rel_ff() {
    test_cases! {
        definitions = "
            (declare-fun x1 () (_ FiniteField 5))
            (declare-fun x2 () (_ FiniteField 5))
            (declare-fun y1 () (_ FiniteField 5))
            (declare-fun y2 () (_ FiniteField 5))
        ",
        "Finite field equality" {
            "(assume h1 (= (ff.mul #f1m5 (ff.add x1 (ff.neg x2)))
                           (ff.mul #f1m5 (ff.add y1 (ff.neg y2)))))
             (step t1 (cl (= (= x1 x2) (= y1 y2))) :rule poly_simp_rel :premises (h1))": true,

            "(assume h1 (= (ff.mul #f2m5 (ff.add x1 (ff.neg x2)))
                           (ff.mul #f3m5 (ff.add y1 (ff.neg y2)))))
             (step t1 (cl (= (= x1 x2) (= y1 y2))) :rule poly_simp_rel :premises (h1))": true,
        }
        "Failing examples" {
            "(assume h1 (= (ff.mul #f0m5 (ff.add x1 (ff.neg x2)))
                           (ff.mul #f1m5 (ff.add y1 (ff.neg y2)))))
             (step t1 (cl (= (= x1 x2) (= y1 y2))) :rule poly_simp_rel :premises (h1))": false,
        }
    }
}
