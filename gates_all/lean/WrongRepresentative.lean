import Child24Proof
open CollatzResearch EimersChild24
theorem rejected_wrong_representative (u : Nat) :
  118140960795 + (8388658 + u * 2^24) * 2^59 = 8388658 + u * 2^83 := by
  exact child_q8388658_coordinate_bridge u
