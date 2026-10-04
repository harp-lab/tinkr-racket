#lang racket



(require "rkt/build.rkt")


(let ()
  
  (system "rm -rf /tmp/ti") ;; optional
  
  (build-project "test/files/fact2.ti")
  
  (void))






