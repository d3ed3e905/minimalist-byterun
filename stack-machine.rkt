#lang racket
(require "opcodes.rkt")
(provide make-stack-machine)
(provide run-stack-machine)
(provide get-stack)
(provide get-varnames)
(provide get-consts)
(provide get-names)
(provide get-code)
(provide get-IC)
(provide empty-stack)
(provide make-stack)
(provide push)
(provide pop)
(provide top)


;; Implementare stiva
(define empty-stack '())
(define (make-stack) '())

(define (push element stack) (cons element stack))
(define (top stack) (car stack))
(define (pop stack) (cdr stack))

;; Implementare mașini stivă.
;; Definire make-stack-machine; primeste cele 4 segmente de date
;; Stivă pentru execuție și counter pentru a indica instructiunea.
(define (make-stack-machine stack co-varnames co-consts co-names co-code IC)
  (list stack co-varnames co-consts co-names co-code IC))

;; Funcțiile `get-varnames`, `get-consts`, `get-names`,
;; `get-code`, `get-stack`, `get-IC` primesc o mașina stivă și întorc
;; componenta respectivă

;; ex:
;; > (get-varnames (make-stack-machine empty-stack 'dummy-co-varnames (hash) (hash) (list) 0))
;; 'dummy-co-varnames
(define (get-varnames stack-machine) (cadr stack-machine))

;; ex:
;; > (get-consts (make-stack-machine empty-stack (hash) 'dummy-co-consts (hash) (list) 0))
;; 'dummy-co-consts
(define (get-consts stack-machine) (caddr stack-machine))

;; ex:
;; > (get-names (make-stack-machine empty-stack (hash) (hash) 'dummy-co-names (list) 0))
;; 'dummy-co-names
(define (get-names stack-machine) (cadddr stack-machine))

;; ex:
;; > (get-code (make-stack-machine empty-stack (hash) (hash) (hash) 'dummy-co-code 0))
;; dummy-co-code
(define (get-code stack-machine) (cadr (cdddr stack-machine)))

;; Întoarce stiva de execuție.
;; ex:
;; > (get-code (make-stack-machine 'dummy-exec-stack (hash) (hash) (hash) (list) 0))
;; dummy-exec-stack
(define (get-stack stack-machine) (car stack-machine))

;; Întoarce instruction counterul.
;; ex:
;; > (get-code (make-stack-machine empty-stack (hash) (hash) (hash) (list) 0))
;; 0
(define (get-IC stack-machine) (last stack-machine))


(define symbols (list 'STACK 'CO-VARNAMES 'CO-CONSTS 'CO-NAMES 'CO-CODE 'INSTRUCTION-COUNTER))

;; Funcția get-symbol-index gasește index-ul simbolului in listă.
(define (get-symbol-index symbol)
  (let loop [(i 0)
             (L symbols)]
    (if (equal? symbol (car L))
        i
        (loop (add1 i) (cdr L)))))

;; Funcția update-stack-machine intoarce o noua mașina stivă
;; înlocuind componenta corespondentă simbolului cu item-ul dat în paremetri.
;; > (get-varnames (update-stack-machine "new-varnames" 'CO-VARNAMES stack-machine))
;; "new-varnames"
;; > (get-varnames (update-stack-machine "new-names" 'CO-NAMES stack-machine))
;; "new-names"
(define (update-stack-machine item symbol stack-machine)
  (reverse (let loop [(n (get-symbol-index symbol))
                      (i 0) ; contor pentru pozitie
                      (st-m stack-machine)
                      (result null)]
             (cond [(null? st-m) result]
                   [(= n i) (loop n (add1 i) (cdr st-m) (cons item result))]
                   [else (loop n (add1 i) (cdr st-m) (cons (car st-m) result))]))))

;; Funcția push-exec-stack primește o masină stivă și o valoare
;; și intoarce o noua mașina unde valoarea este pusă pe stiva de execuție
(define (push-exec-stack value stack-machine)
  (update-stack-machine (cons value (get-stack stack-machine))
                        'STACK
                        stack-machine))

;;  Funcția pop-exec-stack primește o masină stivă
;;  și intoarce o noua mașina aplicând pop pe stiva de execuție.
(define (pop-exec-stack stack-machine)
  (update-stack-machine (cdr (get-stack stack-machine))
                        'STACK
                        stack-machine))

;; Funcția run-stack-machine execută operații pană epuizează co-code.
(define (run-stack-machine stack-machine)
  (let* [(op-list (get-code stack-machine))
         (op-listLen (length op-list))
         (IC (get-IC stack-machine))
         ; f-update = functie care face update la IC din stack-machine
         (f-update (lambda (st-m x)
                     (update-stack-machine x 'INSTRUCTION-COUNTER st-m)))]
    (let ((opname (car (list-ref op-list IC)))
          (param (cdr (list-ref op-list IC))))
      (cond
        [(equal? opname 'RETURN_VALUE) stack-machine]

        [(equal? 'LOAD_CONST opname) (run-stack-machine (f-update (push-exec-stack (hash-ref (get-consts stack-machine) param) stack-machine) (add1 IC)))]
                
        [(equal? 'STORE_FAST opname) (let ((tos (top (get-stack stack-machine))))
                                       (run-stack-machine (f-update (pop-exec-stack (update-stack-machine (hash-set (get-varnames stack-machine) param tos)
                                                                                                          'CO-VARNAMES
                                                                                                          stack-machine)) (add1 IC))))]
                
        [(equal? 'LOAD_FAST opname) (run-stack-machine (f-update (push-exec-stack (hash-ref (get-varnames stack-machine) param) stack-machine) (add1 IC)))]
                
        [(equal? 'POP_JUMP_IF_FALSE opname) (let ((tos (top (get-stack stack-machine))))
                                              (run-stack-machine (f-update (pop-exec-stack stack-machine) (if (equal? tos #f)
                                                                                                              (quotient param 2)
                                                                                                              (add1 IC)))))]
                
        [(equal? 'JUMP_ABSOLUTE opname) (run-stack-machine (f-update stack-machine (quotient param 2)))]
                
        [(equal? 'FOR_ITER opname) (let* [(st (get-stack stack-machine))
                                          (tos (top st))
                                          (next cdr)
                                          (current car)]
                                     (cond
                                       [(equal? tos null) (run-stack-machine (f-update (pop-exec-stack stack-machine) (+ IC (quotient param 2) 1)))]
                                       [(list? (next tos)) (run-stack-machine (f-update (push-exec-stack (current tos)
                                                                                                         (push-exec-stack (next tos) (pop-exec-stack stack-machine)))
                                                                                        (add1 IC)))]))]
                
        [(equal? 'LOAD_GLOBAL opname) (run-stack-machine (f-update (push-exec-stack (hash-ref (get-names stack-machine) param) stack-machine) (add1 IC)))]
                
        [(equal? 'POP_TOP opname) (run-stack-machine (f-update (pop-exec-stack stack-machine) (add1 IC)))]
                
        [(equal? 'CALL_FUNCTION opname) (if (= 1 param)
                                            (let* [(st (get-stack stack-machine))
                                                   (arg (top st))
                                                   (f (get-function (top (pop st))))]
                                              (run-stack-machine (f-update (push-exec-stack (f arg) (pop-exec-stack (pop-exec-stack stack-machine))) (add1 IC))))
                                            (let* [(st (get-stack stack-machine))
                                                   (argL (take st param))
                                                   (f (get-function (list-ref st param)))]
                                              (run-stack-machine (f-update (push-exec-stack (f argL)
                                                                                            (let loop ((st-m stack-machine)
                                                                                                       (n param))
                                                                                              (if (< n 0)
                                                                                                  st-m
                                                                                                  (loop (pop-exec-stack st-m) (sub1 n)))))
                                                                           (add1 IC)))))]
                
        [(list? (member opname '(BINARY_ADD BINARY_SUBTRACT BINARY_MODULO INPLACE_ADD INPLACE_SUBTRACT INPLACE_MODULO COMPARE_OP)))
         (let* [(stack (get-stack stack-machine))
                (tos (top stack))
                (tos1 (top (cdr stack)))]
           (run-stack-machine (f-update (push-exec-stack (cond [(list? (member opname '(BINARY_ADD INPLACE_ADD))) (+ tos1 tos)]
                                                               [(list? (member opname '(BINARY_SUBTRACT INPLACE_SUBTRACT))) (- tos1 tos)]
                                                               [(list? (member opname '(BINARY_MODULO INPLACE_MODULO))) (modulo tos1 tos)]
                                                               [(equal? 'COMPARE_OP opname) ((get-cmpop param) tos1 tos)])
                                                         (pop-exec-stack (pop-exec-stack stack-machine)))
                                        (add1 IC))))]
                
        [(list? (member opname '(GET_ITER SETUP_LOOP POP_BLOCK))) (run-stack-machine (f-update stack-machine (add1 IC)))]))))
