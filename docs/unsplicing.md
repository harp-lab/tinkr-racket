# Unsplicing Implementation Notes

Just some (scattered) notes on how unsplicing is implemented as a helpful reference.

This is some tinkr pseudocode for the code that is being generated at compile time (see `desugar.rkt` for the implementation).

```
When we are at a ... pattern with a slice x that's being matched on and gathered pattern variables pv1, pv2, ....:
  def (loop fallback_x sig_param1 sig_param2 .... x_slice pv1 pv2 ....)
  {
    if (is_empty x_slice)
      ;; insert body
      {
        let x (first x_slice)
        ;; insert inner pattern code here
        ;; - which binds pv1^, pv2^, ....
        ;; - and also may fail by using fallback_x, sig_param1, sig_param2, ....
        ;; then do:
          (loop fallback_x sig_param1 sig_param2 .... (rest x_slice) (+ pv1 [pv1^]) (+ pv2 [pv2^]) ....)
      }
  }

  if (is_slice x)
    (loop fallback_x sig_param1 sig_param2 .... x [] [] ....)
    ;; insert fail expression
```