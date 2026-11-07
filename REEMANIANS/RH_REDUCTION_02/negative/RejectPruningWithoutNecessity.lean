import RHFinitePruning.PruningCore

-- Without necessity, a presieve can discard an original acceptance.
example :
    RHFinitePruning.checkPruned
      (fun _ : Unit => false) (fun _ : Unit => true) () = true := by
  decide
