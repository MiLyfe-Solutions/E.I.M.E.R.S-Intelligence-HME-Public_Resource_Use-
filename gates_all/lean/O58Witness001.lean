import CPOQ.MarginTransport

namespace CPOQ

/-- First concrete O5/8 d14 CPOQ proof-transport witness.
    Source: q6049, target: q48569, qbits=14, source q=14241, target q=56761.
    The target positivity proof is obtained through the generic margin transport theorem. -/
theorem o58_witness_001_target_margin_positive :
    margin
      (9444732965739290427392 : Int)
      (8862938119652501095929 : Int)
      (32720488761612761563163 : Int)
      (21178599549948700352189 : Int) > 0 := by
  have hsource :
      margin
        (9444732965739290427392 : Int)
        (8862938119652501095929 : Int)
        (8209377573671194853403 : Int)
        (21967197859099783683773 : Int)
      = (4776173561942372855695891794986152876834816 : Int) := by
    decide

  have hT :
      (8209377573671194853403 : Int)
        + 24511111187941566709760
      = 32720488761612761563163 := by
    decide

  have hC :
      (21967197859099783683773 : Int)
        + (-788598309151083331584 : Int)
      = 21178599549948700352189 := by
    decide

  have hdefect :
      defect
        (9444732965739290427392 : Int)
        (8862938119652501095929 : Int)
        (24511111187941566709760 : Int)
        (-788598309151083331584 : Int)
      = (14260438161004643814321042817118038040510464 : Int) := by
    decide

  have hpositive :
      margin
          (9444732965739290427392 : Int)
          (8862938119652501095929 : Int)
          (8209377573671194853403 : Int)
          (21967197859099783683773 : Int)
        +
        defect
          (9444732965739290427392 : Int)
          (8862938119652501095929 : Int)
          (24511111187941566709760 : Int)
          (-788598309151083331584 : Int)
      > 0 := by
    rw [hsource, hdefect]
    decide

  have htransport :=
    affine_margin_transport_positive
      (9444732965739290427392 : Int)
      (8862938119652501095929 : Int)
      (8209377573671194853403 : Int)
      (21967197859099783683773 : Int)
      (24511111187941566709760 : Int)
      (-788598309151083331584 : Int)
      hpositive

  rw [hT, hC] at htransport
  exact htransport

end CPOQ
