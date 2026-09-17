; hwprobe/run_case_mx.lisp — the differential driver's run-case with MXCSR LOADED FROM THE CASE (after
; `init-x86-state-64`, which does not reset it: D265 section 4) and PRINTED after the step, as `mxcsr=`.
; Loaded AFTER scripts/x86isa_driver.lisp, whose functions it uses; nothing in that file is changed.
; Used by D265's oracle probe and by hwprobe/rows_on_x86isa.py (D266).
(in-package "X86ISA")

(defun x86l-run-case-mx (c x86 state)
  (declare (xargs :stobjs (x86 state) :mode :program))
  (b* ((id     (cadr (assoc-keyword :id c)))
       (rip0   (cadr (assoc-keyword :rip c)))
       (len    (cadr (assoc-keyword :len c)))
       (gprs   (cadr (assoc-keyword :gprs c)))
       (msrs   (x86l-msrs c))
       (rflags (cadr (assoc-keyword :rflags c)))
       (mem    (cadr (assoc-keyword :mem c)))
       (xmms   (cadr (assoc-keyword :xmms c)))
       (mx     (cadr (assoc-keyword :mxcsr c)))
       (x86 (!app-view t x86))
       ((mv flg x86)
        (init-x86-state-64 nil rip0 gprs *x86l-ctrs* msrs nil nil nil nil rflags mem x86))
       ((when flg)
        (prog2$ (cw "CASE id=~s0 len=~x1~%POST init-error~%" id len)
                (mv x86 state)))
       (x86 (x86l-set-xmms xmms x86))
       (pre (mxcsr x86))
       (x86 (!mxcsr mx x86))
       (x86 (x86-fetch-decode-execute x86))
       ((mv post x86) (x86l-post x86)))
    (prog2$ (cw "CASE id=~s0 len=~x1~%~s2 mxcsr=~s3 mxcsr-after-init=~s4~%" id len post
                (x86l-hex (mxcsr x86) 8) (x86l-hex pre 8))
            (mv x86 state))))

(defun x86l-run-all-mx (cs x86 state)
  (declare (xargs :stobjs (x86 state) :mode :program))
  (if (endp cs) (mv x86 state)
    (b* (((mv x86 state) (x86l-run-case-mx (car cs) x86 state)))
      (x86l-run-all-mx (cdr cs) x86 state))))
