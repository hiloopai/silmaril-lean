(module (func))
(assert_invalid (module (func (result i32))) "type mismatch")
