(in-package "ACL2")

(defstobj sil-shelves
  (shelf-items :type (array integer (2)) :initially 4)
  (shelf-mark :type integer :initially -9)
  (shelf-reserve :type (array integer (1)) :initially -3))

(defthm shelves-create (equal (create-sil-shelves) '((4 4) -9 (-3))) :rule-classes nil)
(defthm shelves-valid (equal (sil-shelvesp '((4 5) -9 (8))) t) :rule-classes nil)
(defthm shelves-bad-order (equal (sil-shelvesp '(-9 (4 5) (8))) nil) :rule-classes nil)
(defthm shelves-bad-capacity (equal (sil-shelvesp '((4 5) -9 (8 9))) nil) :rule-classes nil)
(defthm shelves-bad-cell (equal (sil-shelvesp '((4 5) -9 (8 . 9))) nil) :rule-classes nil)
(defthm shelves-read-items (equal (shelf-itemsi 1 '((4 5) -9 (8))) 5) :rule-classes nil)
(defthm shelves-write-items
  (equal (update-shelf-itemsi 1 11 '((4 5) -9 (8))) '((4 11) -9 (8))) :rule-classes nil)
(defthm shelves-read-mark (equal (shelf-mark '((4 5) -9 (8))) -9) :rule-classes nil)
(defthm shelves-write-mark
  (equal (update-shelf-mark 11 '((4 5) -9 (8))) '((4 5) 11 (8))) :rule-classes nil)
(defthm shelves-read-reserve (equal (shelf-reservei -1 '((4 5) -9 (8))) 8) :rule-classes nil)
(defthm shelves-write-reserve
  (equal (update-shelf-reservei 2 11 '((4 5) -9 (8))) '((4 5) -9 (8 nil 11))) :rule-classes nil)
