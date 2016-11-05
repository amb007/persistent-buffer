## persistent-buffer

This directory contains code with persistent data structures that are
primarily meant to be used for buffer implementation, but may also be
used as just balanced trees.

To use any of these buffer implementations (binseq-buffer or
obinseq-buffer), pass them as the :implementation argument when
instatiating climacs-buffer class in pane.lisp.

NOTE: There is a dependency of Persistent/persistent-buffer.lisp on
Flexichain/utilities.lisp (the weak pointer handling).

A more live version at [Drei](https://github.com/robert-strandh/McCLIM/tree/master/Libraries/Drei/Persistent).
