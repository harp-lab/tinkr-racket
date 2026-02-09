#lang racket



(require "rkt/build.rkt")


(let ()
  
  (system "rm -rf /tmp/ti") ;; optional
  
  (build-project "test/tiny.ti")
  ;;(build-project "test/fact2.ti")
  
  (void))






