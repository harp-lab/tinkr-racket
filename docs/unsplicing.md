# Unsplicing Implementation Notes

Just some (scattered) notes on how unsplicing is implemented as a helpful reference.

This is some tinkr pseudocode for the code that is being generated at compile time (see `desugar.rkt` for the implementation).

```
When we are at a ... pattern with argument list g and gathered pattern variables pv1, pv2, ....:
  let accs
    (foldl
      (lambda (g' accs)
        if (null? g')
          accs
          insert inner pattern code here (which binds pv1', pv2', ....), then:
            let pv1 (first accs)
            let accs (rest accs)
            let pv2 (first accs)
            ....
            [(+ pv1 [pv1']) (+ pv2 [pv2']) ....])
      [[] [] ....]
      g)
  
  let pv1 (first accs)
  let accs (rest accs)
  let pv2 (first accs)
  ....
  body
```