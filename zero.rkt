#lang racket

(define-syntax-rule (define-tracing (name args ...) body ...)
  (define (name args ...)
    (println (list 'name args ...))
    body ...))

; ($add-stx-tx trigger-name (literals pattern value) ...)

(define (and* vals)
  (or (empty? vals)
      (and (car vals)
           (and* (cdr vals)))))

(define (compile-vars pattern)
  (cond [(list? pattern) (append* (map compile-vars pattern))]
        [(pair? pattern) (append (compile-vars (car pattern)) (compile-vars (cdr pattern)))]
        [(symbol? pattern) (list pattern)]
        [else empty]))

(define (match-exec procs param1 values)
  (if (empty? procs) #t
      (and ((car procs) param1 (car values))
           (match-exec (cdr procs) param1 (cdr values)))))
(define (cpattern-seq cpatterns)
  (lambda (vals stx)
    (and (list? stx) (= (length stx) (length cpatterns))
         (match-exec cpatterns vals stx))))
(define (cpattern-seq-tail cpatterns ctail)
  (lambda (vals stx)
    (and (list? stx) (>= (length stx) (length cpatterns))
         (match-exec cpatterns vals (take stx (length cpatterns)))
         (ctail vals (drop stx (length cpatterns))))))

(define (isolate-vals cpattern stx)
  (let ((new-vals (make-hash)))
    (and (cpattern new-vals stx)
         new-vals)))
(define (isolate-combine-lists a b)
  (map cons a b))
(define (isolate->list var-list hash)
  (if (= (hash-count hash) (length var-list))
      (map (lambda (var) (hash-ref hash var)) var-list)
      (error "hash did not provide proper set of variables!")))
(define (list->isolate var-list val-list)
  (make-hash (map cons var-list val-list)))
(define (isolate-merge possible-var-list isolates)
  (list->isolate possible-var-list (foldr isolate-combine-lists (map (const empty) possible-var-list) (map (curry isolate->list possible-var-list) isolates))))
(define (vals-from! target source)
  (and* (hash-map source (curry val-try-set! target))))
(define (cpattern-variate possible-vars cpattern)
  (lambda (vals stx)
    (vals-from! vals (isolate-merge (set->list possible-vars) (map (curry isolate-vals cpattern) stx)))))

(define (val-try-set! vals name value)
  (if (hash-has-key? vals name)
      (equal? (hash-ref vals name) value)
      (begin
        (hash-set! vals name value)
        #t)))
(define (cpattern-vardef variable)
  (lambda (vals stx)
    (val-try-set! vals variable stx)))
(define (cpattern-exact exact)
  (lambda (vals stx)
    (equal? stx exact)))

(define (compile-get-used-vars pattern allowed)
  (cond [(list? pattern) (foldl set-union (set) (map (lambda (ptn) (compile-get-used-vars ptn allowed)) pattern))]
        [(set-member? allowed pattern) (set pattern)]
        [else (set)]))

(define (compile-pattern pattern vars)
  (cond [(and (pair? pattern) (eq? (last pattern) '...))
         (cpattern-seq-tail (map (lambda (p) (compile-pattern p vars)) (drop-right pattern 2))
                            (cpattern-variate (compile-get-used-vars (car (take-right pattern 2)) vars) (compile-pattern (car (take-right pattern 2)) vars)))]
        [(and (pair? pattern) (member '... pattern))
         (error "'...' continuations only allowed at the end of a list")]
        [(pair? pattern)
         (cpattern-seq (map (lambda (p) (compile-pattern p vars)) pattern))]
        [(eq? pattern '...)
         (error "'...' continuations invalid in use location")]
        [(set-member? vars pattern)
         (cpattern-vardef pattern)]
        [else (cpattern-exact pattern)]))

(define (template-append a b)
  (lambda (vars)
    (append (a vars) (b vars))))
(define (template-cons a b)
  (lambda (vars)
    (cons (a vars) (b vars))))
(define (template-empty)
  (lambda (vars)
    empty))
(define (template-lookup name)
  (lambda (vars)
    (hash-ref vars name)))
(define (template-raw value)
  (lambda (vars)
    value))
(define (template-variate base)
  (lambda (vars)
    (let ((lookup (symbol->string (base vars))))
      (if (hash-has-key? vars lookup)
          (hash-ref vars lookup)
          (let ((generated (gensym lookup)))
            (hash-set! vars lookup generated)
            generated)))))

(define (template-repeat-unpack template unpack-vars)
  (lambda (vars)
    (let ((lens (map (lambda (var) (length (hash-ref vars var))) unpack-vars)))
      (unless (= 1 (set-count (list->set lens)))
        (error "mismatched unpack lengths: ~s!" lens))
      (map (lambda (i)
             (let ((subvars (hash-copy vars)))
               (for ((unpack-var unpack-vars))
                 (hash-set! subvars unpack-var (list-ref (hash-ref subvars unpack-var) i)))
               (template subvars)))
           (range (set-first lens))))))

(define (compile-template-used-vars template vars)
  (cond [(pair? template)
         (append (compile-template-used-vars (car template) vars)
                 (compile-template-used-vars (cdr template) vars))]
        [(set-member? vars template)
         (list template)]
        [else empty]))
(define (compile-template template vars)
  (cond [(and (pair? template) (set-member? vars (car template)) (pair? (cdr template)) (eq? (cadr template) '...))
         (template-append (template-repeat-unpack (template-lookup (car template))
                                                  (list (car template)))
                          (compile-template (cddr template) vars))]
        [(and (pair? template) (pair? (cdr template)) (eq? (cadr template) '...) (not (eq? (car template) '...)))
         (template-append (template-repeat-unpack (compile-template (car template) vars)
                                                  (compile-template-used-vars (car template) vars))
                          (compile-template (cddr template) vars))]
        [(and (pair? template) (pair? (cdr template)) (pair? (cadr template)) (pair? (cdadr template)) (eq? (caadr template) '...) (not (eq? (cadadr template) '...)))
         (template-append (template-repeat-unpack (compile-template (car template) vars)
                                                  (cdadr template))
                          (compile-template (cddr template) vars))]
        [(and (pair? template) (pair? (cdr template)) (eq? (car template) '...) (eq? (cadr template) '...) (null? (cddr template)))
         (template-raw '...)]
        [(and (pair? template) (pair? (cdr template)) (eq? (car template) '$variate) (symbol? (cadr template)) (null? (cddr template)))
         (template-variate (if (set-member? vars (cadr template))
                               (template-lookup (cadr template))
                               (template-raw (cadr template))))]
        [(pair? template)
         (template-cons (compile-template (car template) vars) (compile-template (cdr template) vars))]
        [(empty? template)
         (template-empty)]
        [(eq? template '...)
         (error "unexpected ...")]
        [(set-member? vars template)
         (template-lookup template)]
        [else
         (template-raw template)]))

(define (compile-variant kpt)
  (unless (= (length kpt) 3)
    (error "bad number of arguments to compile-variant: ~s!" kpt))
  (apply (lambda (keep pattern template)
           (let* ((vars (set-subtract (list->set (compile-vars pattern)) (list->set (cons '... keep))))
                  (ptn (compile-pattern pattern vars))
                  (tpl (compile-template template vars)))
             (lambda (stx)
               (let ((vars (make-hash)))
                 (when (ptn vars stx)
                   ;(println (list 'result-vars vars))
                   (tpl vars))))))
         kpt))

(define (try-variants variants stx allow-none)
  (if (empty? variants)
      (unless allow-none
        (error "no variant matched" stx))
      (let ((res ((car variants) stx)))
        (if (void? res)
            (try-variants (cdr variants) stx allow-none)
            res))))

(define (context)
  (define txes (make-hash))
  (define (add-tx name tx)
    (hash-set! txes name (cons tx (hash-ref txes name empty))))
  (define (get-tx name)
    (let ((gotten (hash-ref txes name empty)))
      (if (empty? gotten) empty
          (car gotten))))
  (define (del-tx name)
    (let ((gotten (hash-ref txes name)))
      (if (empty? (cdr gotten))
          (hash-remove! txes name)
          (hash-set! txes name (cdr gotten)))))
  
  (define ($add-stx-tx stx allow-none)
    (unless (and allow-none (not (pair? stx)))
      (let ((trigger-name (cadr stx))
            (variants (map compile-variant (cddr stx))))
        (add-tx trigger-name (curry try-variants variants))
        '$void)))
  (add-tx '$add-stx-tx $add-stx-tx)
  (define ($del-stx-tx stx allow-none)
    (unless (and allow-none (not (pair? stx)))
      (let ((name (cadr stx)))
        (del-tx name)
        '$void)))
  (add-tx '$del-stx-tx $del-stx-tx)
  (define ($if-symbol stx allow-none)
    (unless (and allow-none (not (pair? stx)))
      (let ((name (cadr stx)) (sym (caddr stx)) (else (cadddr stx)))
        (if (symbol? name)
            sym
            else))))
  (add-tx '$if-symbol $if-symbol)
  
  (define (process-until-no-change stx)
    (let ((updated (process stx)))
      (if (equal? updated stx)
          updated
          (process-until-no-change updated))))
  (define tracing #f)
  (define (process stx)
    (if (not (pair? stx))
        (let ((tx (get-tx stx)))
          (if (null? tx)
              stx
              (let ((rep (tx stx #t)))
                (if (void? rep)
                    stx
                    rep))))
        (begin
          (when tracing
            (println (list 'process stx)))
          (if (list? (car stx))
              (let ((replacement (process-until-no-change (car stx))))
                (if (list? replacement)
                    (cons replacement
                          (map process (cdr stx)))
                    (process (cons replacement
                                   (cdr stx)))))
              (let ((tx (get-tx (car stx))))
                (if (null? tx)
                    (if (list? stx)
                        (map process stx)
                        stx)
                    (let ((processed (tx stx #f)))
                      (if (equal? processed stx)
                          (if (list? stx)
                              (map process stx)
                              stx)
                          (process processed)))))))))
  (define (top-level-process stx tracing-opt)
    (set! tracing tracing-opt)
    (let ((result (process-until-no-change (list '$postphase
                                                 (process-until-no-change (cons 'unit stx))))))
      result))
  top-level-process)

(define test-context (context))

(define code
  '{
    ($add-stx-tx defsyntax*
                 {(defsyntax*)
                  (defsyntax* name (keep ...) [(pattern ...) template] ...)
                  ($add-stx-tx name ((name keep ...) (name pattern ...) template) {... pattern template})})
    
    (defsyntax* defsyntax ()
      [((name pattern ...) template)
       (defsyntax* name (name)
         [(pattern ...)
          template])]
      [(name value)
       ($add-stx-tx name
                    {(name) name value}
                    {(name) (name rest {... ...}) (value rest {... ...})})])
    
    (defsyntax (substitute name value body)
      ($meta-seq ($meta-seq ($add-stx-tx name
                                         {(name) name value}
                                         {(name) (name rest {... ...}) (value rest {... ...})})
                            body)
                 ($del-stx-tx name)))
    
    (defsyntax* $meta-seq ($void)
      [($void x)
       x]
      [(x $void)
       x]
      [(x y)
       ($meta-seq x y)])
    
    (defsyntax* unit (define $void)
      [((define name value))
       (unit value)]
      [((define name value) rest ...)
       (unit
         (let ((name value))
           rest ...))]
      [($void rest ...)
       (unit rest ...)]
      [(rest ...)
       (unit rest ...)])
    
    (defsyntax* list ()
      [()
       empty]
      [(x rest ...)
       ($cons x (list rest ...))])
    
    (defsyntax (cons a b)
      ($cons a b))
    
    (defsyntax (car x)
      ($car x))
    
    (defsyntax (cdr x)
      ($cdr x))
    
    (defsyntax (unless cond body ...)
      (if cond
          (void)
          (begin
            body ...)))
    
    (defsyntax (when cond body ...)
      (if cond
          (begin
            body ...)
          (void)))
    
    (defsyntax* and ()
      [(x)
       x]
      [(x rest ...)
       ($and x (and rest ...))])
    
    (defsyntax (if cond true false)
      ($if cond true false))

    (defsyntax (void)
      $const-void)

    ; mirrored below in compiler
    (defsyntax $TAG_false 0)
    (defsyntax $TAG_true 1)
    (defsyntax $TAG_null 2)
    (defsyntax $TAG_void 3)
    (defsyntax $TAG_integer 4)
    (defsyntax $TAG_symbol 5)
    (defsyntax $TAG_string 6)

    (defsyntax (null? x)
      ($v= ($tag x) $TAG_null))
    (defsyntax (integer? x)
      ($v= ($tag x) $TAG_integer))
    (defsyntax (not x)
      ($v= ($tag x) $TAG_false))
    (defsyntax (error x)
      ($throw x))
    (defsyntax empty
      ($datum ()))

    (defsyntax* $cons ($datum)
      [(($datum x) ($datum (rest ...)))
       ($datum (x rest ...))]
      [(a b)
       ($cons a b)])
    
    (defsyntax* $postfill ($seq $lambda $apply $cons $car $cdr $datum $and $if $tag $v= $throw $lookup list $const-void)
      [(($seq a b))
       ($seq ($postfill a) ($postfill b))]
      [(($lambda args body))
       ($lambda args ($postfill body))]
      [(($apply a b))
       ($apply ($postfill a) ($postfill b))]
      [(($cons ($datum x) ($datum (data ...))))
       ($datum (x data ...))]
      [(($cons a b))
       ($cons ($postfill a) ($postfill b))]
      [(($car x))
       ($car ($postfill x))]
      [(($cdr x))
       ($cdr ($postfill x))]
      [(($datum x))
       ($datum x)]
      [(($and x y))
       ($and ($postfill x) ($postfill y))]
      [(($if cond t f))
       ($if ($postfill cond) ($postfill t) ($postfill f))]
      [(($tag x))
       ($tag ($postfill x))]
      [(($v= x y))
       ($v= ($postfill x) ($postfill y))]
      [(($throw x))
       ($throw ($postfill x))]
      [(($lookup x))
       ($lookup x)]
      [((list))
       ($datum ())]
      [((list x rest ...))
       ($postfill ($cons x (list rest ...)))]
      [((f arg ...))
       ($apply ($postfill f) ($postfill (list arg ...)))]
      [($const-void)
       $const-void]
      [(x)
       ($if-symbol x ($lookup x) ($datum x))])
    
    (defsyntax* $postphase (unit)
      [((unit))
       $void]
      [((unit x))
       ($postfill x)]
      [((unit x rest ...))
       ($seq ($postfill x)
             ($postphase (unit rest ...)))])
    
    (defsyntax* begin (define $void)
      [((define name value))
       (syntax-error "cannot end a block with a define statement! there must be a returned value!")]
      [((define name value) rest ...)
       (let ((name value))
         rest ...)]
      [($void)
       (syntax-error "the final element in a block reduced to $void!")]
      [($void rest ...)
       (begin rest ...)]
      [(x)
       x]
      [(head rest ...)
       ($seq head (begin rest ...))])
    
    (defsyntax* substitute-lookup ()
      [(args () body)
       body]
      [(args (x rest ...) body)
       (substitute x (car args)
                   (substitute-lookup (cdr args) (rest ...)
                                      body))])
    
    (defsyntax* arglen-eq ()
      [(() args)
       (null? args)]
      [((x rest ...) args)
       (and (not (null? args)) (arglen-eq (rest ...) (cdr args)))])
    
    (defsyntax (lambda-one (arg ...) body)
      ($lambda ($variate args)
               (begin
                 (unless (arglen-eq (arg ...) ($variate args))
                   (error "wrong number of arguments"))
                 (substitute-lookup ($variate args) (arg ...)
                                    body))))
    
    (defsyntax (lambda (arg ...) body ...)
      (lambda-one (arg ...) (begin body ...)))
    
    (defsyntax (let ((name value) ...)
                 body ...)
      ((lambda (name ...)
         body ...)
       value ...))
    
    (defsyntax (defun (name arg ...) body ...)
      (define name (lambda (arg ...) body ...)))
    })

(define body
  '{
    (defun (sq x)
      (* x x))
    (sq 7)
    })

(define $TAG_false 0)
(define $TAG_true 1)
(define $TAG_null 2)
(define $TAG_void 3)
(define $TAG_integer 4)
(define $TAG_symbol 5)
(define $TAG_string 6)
(define $TAG_lambda 7)
(define $TAG_pair 8)

(define (get-stack-in x)
  (case x
    [(const datum integer get-context get-ssa fake-global) 0]
    [(dup not to-boolean-tagged get-car get-cdr tag untag set-tag tag-eq assert-fixed tag-check put-ssa pop put-context) 1]
    [(put-slot equal make-pair swap math) 2]
    [(label panic-fixed gotoif gotodyn goto panic) (void)]
    [(const-ssa reach-ssa) (void)] ; transient
    [else (error "no stack req for:" x)]))
(define (get-stack-out x)
  (case x
    [(dup swap) 2]
    [(not to-boolean-tagged get-car get-cdr tag untag set-tag tag-eq const make-pair datum integer get-context get-ssa fake-global equal math) 1]
    [(assert-fixed put-slot tag-check put-ssa pop put-context) 0]
    [(label panic-fixed gotoif gotodyn goto panic) (void)]
    [(const-ssa reach-ssa) (void)] ; transient
    [else (error "no stack prod for:" x)]))
(define (can-traverse? x)
  (and (not (void? (get-stack-in x)))
       (not (void? (get-stack-out x)))))
(define (not-contextual? x)
  (and (can-traverse? x)
       (not (member x '(get-context put-context)))))

(define (optimize-once seq labels-used)
  (match seq
    [(list-rest (list 'integer value) (list 'to-boolean-tagged) rest)
     (if (= value 0)
         (list* (list 'const $TAG_false 0) rest)
         (list* (list 'const $TAG_true value) rest))]
    [(list-rest (list 'const tag value) (list 'to-boolean-tagged) rest)
     (if (= tag $TAG_false)
         (list* (list 'const $TAG_false 0) rest)
         (list* (list 'const $TAG_true value) rest))]
    [(list-rest (list 'integer value) (list 'not) rest)
     (if (= value 0)
         (list* (list 'const $TAG_true 1) rest)
         (list* (list 'const $TAG_false 0) rest))]
    [(list-rest (list 'const tag _) (list 'not) rest)
     (if (= tag $TAG_false)
         (list* (list 'const $TAG_true 1) rest)
         (list* (list 'const $TAG_false 0) rest))]
    [(list-rest (list 'to-boolean-tagged) (list 'tag) rest)
     rest]
    [(list-rest (list 'to-boolean-tagged) (list 'dup) rest)
     (list* (list 'dup) (list 'to-boolean-tagged) (list 'swap) (list 'to-boolean-tagged) rest)]
    [(list-rest (and orig (cons (or 'tag 'equal 'tag-eq) _)) (list 'set-tag n) (list 'const n value) (list 'equal) rest)
     (list* orig (list 'integer value) (list 'equal) rest)]
    [(list-rest (list 'integer 0) (list 'equal) rest)
     (list* (list 'not) rest)]
    [(list-rest (list 'to-boolean-tagged) (list 'not) rest)
     (list* (list 'not) rest)]
    [(list-rest (list 'const tag1 value1) (list 'const tag2 value2) (list 'make-pair tag-out) rest)
     (list* (list 'const tag-out (list tag1 value1 tag2 value2)) rest)]
    [(list-rest (list 'tag) (list 'integer n) (list 'equal) rest)
     (list* (list 'tag-eq n) rest)]
    [(list-rest (and orig (cons (or 'panic 'panic-fixed 'goto) _)) (cons (not 'label) _) rest)
     (list* orig rest)]
    [(list-rest (and orig (cons (or 'const) _)) (list 'pop) rest)
     rest]
    [(list-rest (list 'const tag value) (list 'dup) rest)
     (list* (list 'const tag value) (list 'const tag value) rest)]
    [(list-rest (list 'const tag value) (list 'tag) rest)
     (list* (list 'integer tag) rest)]
    [(list-rest (list 'const tag value) (list 'untag) rest)
     (list* (list 'integer value) rest)]
    [(list-rest (list 'const tag value) (list 'tag-eq n) rest)
     (if (= tag n)
         (list* (list 'integer 1) rest)
         (list* (list 'integer 0) rest))]
    [(list-rest (list 'const tag value) (list 'tag-check (not tag) message) rest)
     (list* (list 'panic-fixed message) rest)]
    [(list-rest (list 'const tag value) (list 'tag-check tag message) rest)
     rest]
    [(list-rest (list 'const tag value) (list 'assert-fixed message) rest)
     (if (= tag $TAG_false)
         (list* (list 'panic-fixed message) rest)
         rest)]
    [(list-rest (list 'const tag (list tag1 value1 tag2 value2)) (list 'get-car) rest)
     (list* (list 'const tag1 value1) rest)]
    [(list-rest (list 'const tag (list tag1 value1 tag2 value2)) (list 'get-cdr) rest)
     (list* (list 'const tag2 value2) rest)]
    [(list-rest (list 'const tag1 value1) (list 'const tag2 value2) (list 'equal) rest)
     (if (and (equal? tag1 tag2) (equal? value1 value2))
         (list* (list 'integer 1) rest)
         (list* (list 'integer 0) rest))]
    [(list-rest (list 'integer value) (list 'integer value) (list 'equal) rest)
     (list* (list 'integer 1) rest)]
    [(list-rest (list 'integer value) (list 'set-tag tag) rest)
     (list* (list 'const tag value) rest)]
    [(list-rest (list 'integer value) (list 'gotoif target) rest)
     (if (= value 0)
         rest
         (list* (list 'goto target) rest))]
    [(list-rest (list 'const tag value) (list 'gotoif target) rest)
     (if (= tag $TAG_false)
         rest
         (list* (list 'goto target) rest))]
    [(list-rest (list 'label (? (lambda (name) (not (set-member? labels-used name))) name)) rest)
     rest] ; unused label
    [(list-rest (list (or 'goto 'gotoif) label) (list 'label label) rest)
     (list* (list 'label label) rest)]
    [(list-rest (list 'integer (? symbol? ptr)) (list 'gotodyn) rest)
     (list* (list 'goto ptr) rest)]
    [(list-rest (list 'datum (and message (? string?))) (list 'panic) rest)
     (list* (list 'panic-fixed message) rest)]
    [(list-rest (list 'gotoif skip) (list 'panic-fixed message) (list 'label skip) rest)
     (list* (list 'assert-fixed message) (list 'label skip) rest)]
    [(list-rest (list 'tag-eq tagno) (list 'assert-fixed message) rest)
     (list* (list 'tag-check tagno message) rest)]
    [(list-rest (and orig (cons (? can-traverse? name) _)) (list 'reach-ssa ssa index-old) rest)
     (let* ((out (get-stack-out name))
            (in (get-stack-in name))
            (index (- (+ index-old in) out)))
       (if (< index-old out)
           (if (= out 1)
               (list* orig (list 'put-ssa ssa) rest)
               (if (eq? name 'dup) ; these require special handling
                   (list* (list 'reach-ssa ssa 0) (list 'get-ssa ssa) rest)
                   (error "provides multiple outputs but has no special handling:" name)))
           (list* (list 'reach-ssa ssa index) orig rest)))]
    [(list-rest (list 'const-ssa tag value ssa) (list 'get-ssa ssa) rest)
     (displayln "const assist")
     (list* (list 'const tag value) (list 'const-ssa tag value ssa) rest)]
    [(list-rest (list 'const-ssa tag value ssa) (and orig (cons (not 'const-ssa) _)) rest)
     (if (can-traverse? (car orig))
         (list* orig (list 'const-ssa tag value ssa) rest)
         (list* orig rest))]
    [(list (list 'const-ssa tag value ssa))
     (displayln "const die")
     (list)]
    [(list-rest (list 'const tag value) (list 'put-ssa ssa) rest)
     (displayln "const create")
     (list* (list 'const-ssa tag value ssa) rest)]
    [(list-rest (list 'get-ssa ssa1) (list 'put-ssa ssa2) (list 'get-ssa ssa2) rest)
     (displayln "coalesce")
     (list* (list 'get-ssa ssa1) (list 'get-ssa ssa1) (list 'put-ssa ssa2) rest)]
    [(list-rest (list 'get-ssa ssa1) (list 'put-ssa ssa2) (and orig (cons (and name (not 'get-ssa)) _)) rest)
     (if (can-traverse? name)
         (begin
           (println (list 'traverse orig))
           (list* orig (list 'get-ssa ssa1) (list 'put-ssa ssa2) rest))
         (list* orig rest))]
    [(list-rest (list 'dup) (list 'put-ssa ssa) rest)
     (list* (list 'put-ssa ssa) (list 'get-ssa ssa) rest)]
    [(list-rest (list 'swap) rest)
     (let ((ssa (gensym "ssa")))
       (displayln "decompose swap")
       (list* (list 'reach-ssa ssa 1) (list 'get-ssa ssa) rest))]
    [(list-rest (list 'put-context) (list 'get-context) rest)
     (list* (list 'dup) (list 'put-context) rest)]
    [(list-rest (list 'const tag value) (list 'put-context) (and orig (cons (or (? not-contextual?) 'gotoif) _)) ... (list 'get-context) rest)
     (append (list (list 'const tag value) (list 'put-context))
             orig
             (list (list 'const tag value))
             rest)]
    [(list-rest (list 'put-context) (and orig (cons (? not-contextual?) _)) ... (list 'put-context) rest)
     (append (list (list 'pop))
             orig
             (list (list 'put-context))
             rest)]
    [(list-rest (list 'const tag value) (list 'put-context) (and orig (cons (? not-contextual?) _)) rest)
     (list* orig (list 'const tag value) (list 'put-context) rest)]
    [(list-rest (list 'integer (? symbol? ptr))
                (and orig (cons (or 'const 'integer) _))
                (list 'put-context)
                (list 'gotodyn)
                rest)
     (list* orig (list 'put-context) (list 'goto ptr) rest)]
    [(list-rest (and cond (cons (or 'integer 'const) _))
                (and orig (cons (or 'const 'integer) _))
                (list 'put-context)
                (list 'gotoif ptr)
                rest)
     (if (if (eq? (car cond) 'integer)
             (= (cadr cond) 0)
             (= (cadr cond) $TAG_false))
         (list* orig (list 'put-context) rest)
         (list* orig (list 'put-context) (list 'goto ptr) rest))]
    
    ['() empty]
    [(cons head tail) (cons head (optimize-once tail labels-used))]))
(define (optimize-once-splitting seq)
  (match seq
    [(list-rest (and cexpr (cons 'const _))
                (list 'put-context)
                (and o1 (list 'label lambda)) ; the same lambda as above
                (and o2 (cons (not 'label) _)) ...
                (and o3 (list 'get-context)) ; heuristic to detect if this is helpful
                (and o4 (cons (not 'label) _)) ...
                (and o5 (list 'label next))
                rest)
     (let ((specified (gensym "specified")))
       (display "FORKING CODE: ")
       (displayln (hash-count optimization-steps))
       (append (list cexpr (list 'put-context)) ; creates TWO copies
               o2
               (list o3)
               o4
               (list (list 'goto next) o1)
               o2
               (list o3)
               o4
               (list o5)
               rest))]
    ['() empty]
    [(cons head tail) (cons head (optimize-once-splitting tail))]))
(define optimization-steps (make-hash))
(define (get-label-refs x)
  (match x
    [(list (or 'goto 'gotoif) label) (list label)]
    [(list 'const tag (? symbol? ptr)) (list ptr)]
    [(list 'const tag (list tag1 value1 tag2 value2))
     (append (get-label-refs (list 'const tag1 value1))
             (get-label-refs (list 'const tag2 value2)))]
    [(list 'const-ssa tag value ssa)
     (get-label-refs (list 'const tag value))]
    [(list 'integer (? symbol? ptr)) (list ptr)]
    [else empty]))
(define (optimize seq nth [reordered-last #f])
  (when (hash-has-key? optimization-steps nth)
    (error "OOPS"))
  (hash-set! optimization-steps nth seq)
  (let* ((known (list->set (append* (map get-label-refs seq))))
         (new (optimize-once seq known)))
    (if (equal? seq new)
        (let ((new2 (optimize-once-splitting new)))
          (if (equal? new new2)
              (if reordered-last
                  new2
                  (optimize (reorder new2) (+ nth 1) #t))
              (optimize new2 (+ nth 1))))
        (optimize new (+ nth 1)))))

(define (split-list should-split-after? main-seq)
  (define (split-list-i seq)
    (if (empty? seq)
        (values empty empty)
        (let ((split (should-split-after? seq)))
          (let-values (((current-list more-lists) (split-list-i (cdr seq))))
            (if split
                (values (list (car seq)) (cons current-list more-lists))
                (values (cons (car seq) current-list) more-lists))))))
  (let-values (((cur more) (split-list-i main-seq)))
    (let ((combined (cons cur more)))
      (if (empty? (car (take-right combined 1)))
          (drop-right combined 1)
          combined))))

(define (split-point? seq)
  (match seq
    [(list-rest (list 'goto target) (list 'label label) _)
     #t]
    [(list-rest (list 'gotodyn) (list 'label label) _)
     #t]
    [_
     #f]))

(define (recut seq) ; make sure that no labels are implicitly entered
  (if (or (empty? seq) (empty? (cdr seq))) seq
      (if (and (not (eq? (caar seq) 'goto)) (not (eq? (caar seq) 'gotodyn)) (eq? (caadr seq) 'label))
          (list* (car seq)
                 (list 'goto (cadadr seq))
                 (cadr seq)
                 (recut (cddr seq)))
          (cons (car seq) (recut (cdr seq))))))
(define (rejoin seq) ; the reverse of that
  (if (or (empty? seq) (empty? (cdr seq))) seq
      (if (and (eq? (caar seq) 'goto) (eq? (caadr seq) 'label) (eq? (cadar seq) (cadadr seq)))
          (cons (cadr seq)
                (rejoin (cddr seq)))
          (cons (car seq)
                (rejoin (cdr seq))))))
(define (reorder seq)
  (let* ((seq (recut seq))
         (sublists (split-list split-point? seq))
         (sources (map (lambda (x) (and (eq? (caar x) 'label) (cadar x))) sublists))
         (targets (map (lambda (x) (and (eq? (car x) 'goto) (cadr x))) (map last sublists)))
         (chunks (make-hash (map cons sources sublists)))
         (source->target (make-immutable-hash (map cons sources targets)))
         (target->source (make-immutable-hash (map cons targets sources))))
    (unless (eq? (car sources) #f)
      (error "first chunk should not start with a label!"))
    (unless (= (length sources) (hash-count source->target))
      (error "duplicate labels!"))
    ;(println (list 'reorder source->target target->source))
    (define (rip-chain start)
      (let ((chunk (hash-ref chunks start))
            (next (hash-ref source->target start #f)))
        (hash-remove! chunks start)
        (append chunk
                (if (and next (hash-has-key? chunks next))
                    (rip-chain next)
                    empty))))
    (define (pretraverse start seen)
      (if (eq? start #f)
          start
          (let ((prev (hash-ref target->source start #f)))
            (if (and prev (hash-has-key? chunks prev))
                (if (member prev seen)
                    prev
                    (pretraverse prev (cons prev seen)))
                start))))
    (let ((combined (rip-chain #f)))
      (let loop ()
        (when (not (hash-empty? chunks))
          (set! combined (append combined
                                 (rip-chain (pretraverse (hash-iterate-key chunks (hash-iterate-first chunks)) '()))))
          (loop)))
      (unless (= (length seq) (length combined))
        (error "lost something, somewhere, somehow:" (length seq) (length combined)))
      (rejoin combined))))

(define (ix . xes)
  (list xes))
(define (assert-is-tag tag message)
  (let ((skip (gensym "label")))
    (append (ix 'dup)
            (ix 'tag)
            (ix 'integer tag)
            (ix 'equal)
            (ix 'gotoif skip)
            (ix 'datum message)
            (ix 'panic)
            (ix 'label skip))))
(define (compile-top block)
  (define all-output empty)
  (define (compile-lambda var block)
    ; TODO: closures!
    (let ((data (compile-block block var)) (name (gensym "lambda")))
      (set! all-output (append all-output
                               (ix 'label name)  ; (...) ARGUMENT RETURN-ADDRESS
                               (ix 'swap)        ; (...) RETURN-ADDRESS ARGUMENT
                               (ix 'get-context) ; (...) RETURN-ADDRESS ARGUMENT OLD-CONTEXT
                               (ix 'swap)        ; (...) RETURN-ADDRESS OLD-CONTEXT ARGUMENT
                               (ix 'put-context) ; (...) RETURN-ADDRESS OLD-CONTEXT
                               data              ; (...) RETURN-ADDRESS OLD-CONTEXT RETURN-VALUE
                               (ix 'swap)        ; (...) RETURN-ADDRESS RETURN-VALUE OLD-CONTEXT
                               (ix 'put-context) ; (...) RETURN-ADDRESS RETURN-VALUE
                               (ix 'swap)        ; (...) RETURN-VALUE RETURN-ADDRESS
                               (ix 'gotodyn)     ; (...) RETURN-VALUE (and we're at the old address)
                               ))
      name))
  (define (compile-block block argname)
    (match block
      [(list '$seq first second) (append (compile-block first argname)
                                         (ix 'pop)
                                         (compile-block second argname))]
      [(list '$lambda name body) (ix 'const $TAG_lambda (compile-lambda name body))]
      [(list '$apply name args) (let ((ret (gensym "label")))
                                  (append (compile-block name argname)
                                          (compile-block args argname)
                                          (ix 'swap)
                                          (assert-is-tag $TAG_lambda "not a lambda!")
                                          (ix 'integer ret)
                                          (ix 'swap)
                                          (ix 'untag)
                                          (ix 'gotodyn)
                                          (ix 'label ret)))]
      [(list '$cons a b) (append (compile-block a argname)
                                 (compile-block b argname)
                                 (ix 'make-pair $TAG_pair))]
      [(list '$car x) (append (compile-block x argname)
                              (assert-is-tag $TAG_pair "not a pair!")
                              (ix 'get-car))]
      [(list '$cdr x) (append (compile-block x argname)
                              (assert-is-tag $TAG_pair "not a pair!")
                              (ix 'get-cdr))]
      [(list '$datum x) (cond ((integer? x) (ix 'const $TAG_integer x))
                              ((empty? x) (ix 'const $TAG_null 0))
                              ((pair? x) (append (compile-block (list '$datum (car x)) argname)
                                                 (compile-block (list '$datum (cdr x)) argname)
                                                 (ix 'make-pair 8)))
                              (else (ix 'datum x)))]
      ['$const-void (ix 'const $TAG_void 0)]
      [(list '$and a b) (let ((ondone (gensym "label")))
                          (append (compile-block a argname)
                                  (ix 'dup)
                                  (ix 'not)
                                  (ix 'gotoif ondone) ; if the first argument is false, then return it directly.
                                  (ix 'pop) ; if first argument is true, then ignore it and return the second argument.
                                  (compile-block b argname)
                                  (ix 'label ondone)))]
      [(list '$if c t f) (let ((iftrue (gensym "label")) (ondone (gensym "label")))
                           (append (compile-block c argname)
                                   (ix 'gotoif iftrue)
                                   (compile-block f argname)
                                   (ix 'goto ondone)
                                   (ix 'label iftrue)
                                   (compile-block t argname)
                                   (ix 'label ondone)))]
      [(list '$tag value) (append (compile-block value argname)
                                  (ix 'tag)
                                  (ix 'set-tag $TAG_integer))]
      [(list '$v= a b) (append (compile-block a argname)
                               (compile-block b argname)
                               (ix 'equal)
                               (ix 'to-boolean-tagged))]
      [(list '$throw value) (append (compile-block value argname)
                                    (ix 'panic))]
      [(list '$lookup name) (if (eq? name argname)
                                (ix 'get-context) ; the argument
                                (if (member name '(+ - * /))
                                    (ix 'const $TAG_lambda (string->symbol (string-append "global_" (symbol->string name))))
                                    (error "no such variable" name)))]))
  (let ((main (compile-lambda (gensym "ignored") block)))
    (pretty-print all-output)
    (optimize (append (ix 'const $TAG_null 0) ; argument
                      (ix 'integer 'exit) ; return address
                      (ix 'const $TAG_void 0) ; context
                      (ix 'put-context)
                      (ix 'goto main)
                      all-output
                      (ix 'label 'global_*)    ; (...) ARGUMENT RETURN-ADDRESS
                      (ix 'swap)               ; (...) RETURN-ADDRESS ARGUMENT
                      (ix 'dup)                ; (...) RETURN-ADDRESS ARGUMENT ARGUMENT
                      (ix 'get-car)            ; (...) RETURN-ADDRESS ARGUMENT (A)
                      (ix 'swap)               ; (...) RETURN-ADDRESS (A) ARGUMENT
                      (ix 'get-cdr)            ; (...) RETURN-ADDRESS (A) ((B))
                      (ix 'get-car)            ; (...) RETURN-ADDRESS (A) (B)
                      (ix 'math '*)            ; (...) RETURN-ADDRESS (A*B)
                      (ix 'swap)               ; (...) (A*B) RETURN-ADDRESS
                      (ix 'gotodyn)            ; (...) (A*B) (and we're at the old address)
                      ) 0)))

(test-context code #f)
(let ((output (test-context body #f)))
  (pretty-print output)
  (compile-top output))

(define (write-out)
  (let ((base (symbol->string (gensym "/tmp/opt-steps-"))))
    (make-directory base)
    (for ((i (range (hash-count optimization-steps))))
      (call-with-output-file (string-append base "/" (~v i))
        (lambda (port)
          (pretty-print (hash-ref optimization-steps i) port))))
    (display "finished writing to ")
    (displayln base)))
