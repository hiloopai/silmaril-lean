(component
  (import "r" (type $r (sub resource)))
  (type $b (borrow $r))
  (import "v" (value $v (type $b)))
  (instance (export "v" (value $v))))
