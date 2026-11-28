(in-package "ACL2")
(set-guard-checking :none)

(defun c3-mv-nth-sample (index values)
  (list index values (mv-nth index values)))

(assign c3-mv-nth-samples
  (list (c3-mv-nth-sample 0 '(:first :second))
        (c3-mv-nth-sample 1 '(:first :second))
        (c3-mv-nth-sample 2 '(:first :second))
        (c3-mv-nth-sample (expt 2 80) '(:first :second))
        (c3-mv-nth-sample -3 '(:first :second))
        (c3-mv-nth-sample 1/2 '(:first :second))
        (c3-mv-nth-sample #C(1 2) '(:first :second))
        (c3-mv-nth-sample :bad '(:first :second))
        (c3-mv-nth-sample nil '(:first :second))
        (c3-mv-nth-sample '(1) '(:first :second))
        (c3-mv-nth-sample 0 '(:first . :tail))
        (c3-mv-nth-sample 1 '(:first . :tail))
        (c3-mv-nth-sample 1 '(:first :second . :tail))
        (c3-mv-nth-sample 2 '(:first :second . :tail))
        (c3-mv-nth-sample 0 :tail) (c3-mv-nth-sample 3 "abc")
        (c3-mv-nth-sample 0 nil) (c3-mv-nth-sample 1 '(t nil))))

(defun c3-eql-sample (x y) (list x y (eql x y)))

(assign c3-eql-samples
  (list (c3-eql-sample (cons 1 :tail) (cons (+ 0 1) :tail))
        (c3-eql-sample '(1 . :tail) '(1 . :other))
        (c3-eql-sample "acl2" (coerce '(#\a #\c #\l #\2) 'string))
        (c3-eql-sample "acl2" "ACL2")
        (c3-eql-sample 'acl2::c3-same :c3-same)
        (c3-eql-sample :same :same)
        (c3-eql-sample 2/4 1/2)
        (c3-eql-sample #C(2 -1) #C(2 -1))
        (c3-eql-sample #\A #\a)
        (c3-eql-sample nil 0)))

(defun c3-not-sample (x) (list x (not x)))

(assign c3-not-samples
  (list (c3-not-sample nil) (c3-not-sample t) (c3-not-sample 0)
        (c3-not-sample #C(1 2)) (c3-not-sample "") (c3-not-sample #\a)
        (c3-not-sample :nil) (c3-not-sample '(nil))))
