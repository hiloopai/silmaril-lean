(in-package "ACL2")

(defun defstobj-world-rows (name world)
  (let ((prop (c3-property name 'stobj world)))
    (loop for fn in (list* (access stobj-property prop :recognizer)
                          (access stobj-property prop :creator)
                          (access stobj-property prop :names))
          when (function-symbolp fn world)
          collect (defstobj-logical-row fn world))))

(defun export-defstobj-schema (output)
  (let ((world (w *the-live-state*)))
    (with-open-file (out output :direction :output :if-exists :error :external-format :utf-8)
      (c3-json-term
       (list (get-event 'sil-toy world) (defstobj-world-rows 'sil-toy world)
             (get-event 'sil-shelves world) (defstobj-world-rows 'sil-shelves world)
             (loop for name in '(shelves-create shelves-valid shelves-bad-order shelves-bad-capacity
                                  shelves-bad-cell shelves-read-items shelves-write-items
                                  shelves-read-mark shelves-write-mark shelves-read-reserve
                                  shelves-write-reserve)
                   collect (list name (c3-property name 'theorem world))))
       out)
      (terpri out))))
