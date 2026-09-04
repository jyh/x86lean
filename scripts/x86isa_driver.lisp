; x86lean differential driver — the ORACLE side.
;
; Reads the cases emitted by `x86lean-diff emit-acl2` (ordinary Lisp data — this
; file parses nothing; see Main.lean on why) and, for each, initialises an
; x86isa state, runs ONE step, and prints the post-state in the same record
; format the Lean side emits, so `x86lean-diff compare` can read both.
;
; PUBLIC SOURCE.  ACL2 x86isa is BSD-3-Clause, (c) 2015 Regents of the University
; of Texas.  Nothing from it is copied into x86lean; it is CONSULTED BY
; EXECUTION and its answers are recorded as evidence, never as theorems
; (TRUSTBASE.md, "What is validated, not proven").

; ⚠️ The include-books are NOT here.  This file opens with `in-package "X86ISA"`,
; and that package does not exist until a book carrying x86isa's portcullis has
; been included — so the includes must happen in the ACL2 package, BEFORE this
; file is `ld`-ed.  `scripts/run_differential.sh` does that.  (A first draft put
; them here and ACL2 answered "the argument to IN-PACKAGE must be a known
; package" on line 1, which is the correct error and an easy one to misread as a
; missing book.)

(in-package "X86ISA")

; ⭐ x86isa's OWN UNDEFINED-VALUE ORACLE, and why it has to be attached here.
;
; `create-undef` is a CONSTRAINED function in x86isa (machine/
; register-readers-and-writers.lisp): the model knows only that it returns a
; natural, never what natural.  That is the same refusal this project makes with
; `X86.Oracle` — Intel declines to define these bits, so the model declines too —
; and it means x86isa cannot EXECUTE an instruction with an undefined flag until
; somebody attaches a concrete generator.  The first differential run died at
; case 817, the first `and`, with "cannot ev the call of non-executable function
; CREATE-UNDEF".  That error is the two models agreeing about what they do not
; know.
;
; ⚠️ THE ATTACHMENT IS `nfix`, NOT A CONSTANT, AND THE CHOICE MATTERS.  A
; constant 0 would make x86isa's undefined bits agree with the all-zero oracle
; the Lean side runs under, the `undefined-region` class would never fire, and
; the run would look cleaner while testing strictly less.  `nfix` returns the
; seed counter, which varies per draw, so the undefined bits DISAGREE — and the
; run then has to demonstrate that it classifies them as explained rather than
; never meeting one.  Agreement obtained by making both sides guess the same way
; is not agreement about anything.
(defun x86l-undef (x) (declare (xargs :guard t)) (nfix x))
(defattach create-undef x86l-undef)

(set-state-ok t)
(program)

(defun x86l-hexdig (n) (char "0123456789abcdef" n))

(defun x86l-hexn (v k acc)
  (if (zp k) acc
    (x86l-hexn (ash v -4) (1- k) (cons (x86l-hexdig (logand v 15)) acc))))

(defun x86l-hex (v k) (coerce (x86l-hexn v k nil) 'string))

(defconst *x86l-gpr-names*
  '("rax" "rcx" "rdx" "rbx" "rsp" "rbp" "rsi" "rdi"
    "r8" "r9" "r10" "r11" "r12" "r13" "r14" "r15"))

(defun x86l-regs (i acc x86)
  (declare (xargs :stobjs x86))
  (if (or (not (natp i)) (>= i 16))
      acc
    (x86l-regs (1+ i)
               (concatenate 'string acc
                            (if (equal acc "") "" " ")
                            (nth i *x86l-gpr-names*) "="
                            (x86l-hex (n64 (rgfi i x86)) 16))
               x86)))

(defun x86l-bit (b) (if (equal b 1) "1" "0"))

(defun x86l-flags (x86)
  (declare (xargs :stobjs x86))
  (concatenate 'string
    "cf=" (x86l-bit (flgi :cf x86))
    " pf=" (x86l-bit (flgi :pf x86))
    " af=" (x86l-bit (flgi :af x86))
    " zf=" (x86l-bit (flgi :zf x86))
    " sf=" (x86l-bit (flgi :sf x86))
    " of=" (x86l-bit (flgi :of x86))
    " df=" (x86l-bit (flgi :df x86))))

(defun x86l-window-bytes (addr n acc x86)
  (declare (xargs :stobjs x86))
  (if (zp n) (mv acc x86)
    (b* (((mv flg byte x86) (rml08 addr :r x86))
         (byte (if flg 0 byte)))
      (x86l-window-bytes (1+ addr) (1- n)
                         (concatenate 'string acc (x86l-hex byte 2)) x86))))

(defun x86l-windows (ws acc x86)
  (declare (xargs :stobjs x86))
  (if (endp ws) (mv acc x86)
    (b* ((w (car ws))
         ((mv s x86) (x86l-window-bytes (car w) (cdr w) "" x86)))
      (x86l-windows (cdr ws) (concatenate 'string acc " mem@"
                                          (x86l-hex (car w) 16) "=" s) x86))))

; The watch windows.  THIS IS A DUPLICATE of Tests/Vectors.lean `windows`,
; across a language boundary, and until P1 batch 15 a comment was the only thing
; holding the two together.  It fails LOUD rather than silent -- any drift makes
; every rendered record differ and the whole run comes back as disagreement --
; but discovering it costs a full ACL2 run, so `scripts/check_windows.py` now
; compares the two literals directly and is run by CI and by the selftest.
; Widened from (#x1ff0 . 32) in batch 15 to give RSI and RDI a margin in both
; directions; see the note on `windows` for why a backward step off the end of a
; window is a test that passes by construction.
(defconst *x86l-windows* '((#x1fe0 . 64) (#x7fe0 . 48)))

(defun x86l-post (x86)
  (declare (xargs :stobjs x86))
  (b* (((mv wins x86) (x86l-windows *x86l-windows* "" x86)))
    (mv (concatenate 'string
          "POST " (x86l-regs 0 "" x86)
          " rip=" (x86l-hex (n64 (rip x86)) 16)
          " " (x86l-flags x86)
          ; ⚠️ BOTH FIELDS.  x86isa records a #GP(0) in `fault`, NOT in `ms` —
          ; and the first differential run read only `ms`, so eighty
          ; non-canonical branches came back as "x86isa did nothing, and its rip
          ; disagrees", with the oracle's own explanation invisible to the
          ; harness that was asking for it.
          " refused=" (if (or (ms x86) (fault x86)) "1" "0")
          wins)
        x86)))

; ⭐⭐ P2 ITEM 1 — THE FS AND GS SEGMENT BASES, AND WHY THEY ARE MSRs HERE.
;
; In 64-bit mode x86isa reads FS's and GS's bases out of the IA32_FS_BASE and
; IA32_GS_BASE model-specific registers (`segment-base-and-bounds`,
; machine/segmentation.lisp: the 64-bit arm is `(msri *ia32_fs_base-idx* x86)`
; and nothing else), NOT out of the hidden segment-descriptor registers that
; serve the 32-bit modes.  So the fifth argument of `init-x86-state-64` — the
; MSR alist, `nil` in every case this driver emitted before this batch — is
; where a segment base has to arrive.  The Lean side sends the VALUES
; (`:fsbase`/`:gsbase`); these two index constants are x86isa's own and stay on
; this side of the boundary.
;
; ⚠️ A CASE THAT OMITS THEM STILL WORKS AND MEANS BASE ZERO, which is what every
; pre-P2 case intends — so the emitter and this reader can be updated in either
; order without a run that silently compares the wrong thing.
(defun x86l-msrs (c)
  (let ((fs (cadr (assoc-keyword :fsbase c)))
        (gs (cadr (assoc-keyword :gsbase c))))
    (list (cons #.*ia32_fs_base-idx* (if fs fs 0))
          (cons #.*ia32_gs_base-idx* (if gs gs 0)))))

(defun x86l-run-case (c x86 state)
  (declare (xargs :stobjs (x86 state)))
  (b* ((id     (cadr (assoc-keyword :id c)))
       (rip0   (cadr (assoc-keyword :rip c)))
       (len    (cadr (assoc-keyword :len c)))
       (gprs   (cadr (assoc-keyword :gprs c)))
       (msrs   (x86l-msrs c))
       (rflags (cadr (assoc-keyword :rflags c)))
       (mem    (cadr (assoc-keyword :mem c)))
       (x86 (!app-view t x86))
       ((mv flg x86)
        (init-x86-state-64 nil rip0 gprs nil msrs nil nil nil nil rflags mem x86))
       ((when flg)
        (prog2$ (cw "CASE id=~s0 len=~x1~%POST init-error~%" id len)
                (mv x86 state)))
       (x86 (x86-fetch-decode-execute x86))
       ((mv post x86) (x86l-post x86)))
    (prog2$ (cw "CASE id=~s0 len=~x1~%~s2~%" id len post)
            (mv x86 state))))

(defun x86l-run-all (cs x86 state)
  (declare (xargs :stobjs (x86 state)))
  (if (endp cs) (mv x86 state)
    (b* (((mv x86 state) (x86l-run-case (car cs) x86 state)))
      (x86l-run-all (cdr cs) x86 state))))
