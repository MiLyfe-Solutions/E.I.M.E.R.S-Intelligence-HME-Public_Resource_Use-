import Lean.Elab.Tactic.Omega
import CPOQ.O58Witness001
import CPOQ.O58SegmentGuards69

namespace CPOQ

/-- One accelerated Collatz transition with exact 2-adic valuation a. -/
def ActualExactAccelStep (x y : Int) (a : Nat) : Prop :=
  3 * x + 1 = (2 : Int)^a * y ∧ y % 2 = 1

/-- The concrete step predicate is decidable after unfolding to integer equalities. -/
instance actualExactAccelStepDecidable (x y : Int) (a : Nat) :
    Decidable (ActualExactAccelStep x y a) := by
  unfold ActualExactAccelStep
  infer_instance

/-- A finite accelerated Collatz path whose valuation word is part of the proposition. -/
inductive ActualAccelPath : Int → List Nat → Int → Prop where
  | nil (x : Int) : ActualAccelPath x [] x
  | cons {x y z : Int} {a : Nat} {w : List Nat} :
      ActualExactAccelStep x y a → ActualAccelPath y w z →
      ActualAccelPath x (a :: w) z

def o58w001SourceWord : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 2]
def o58w001TargetWord : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 2]

theorem o58_witness001_source_actual_path :
    ActualAccelPath 8209377573671194853403 o58w001SourceWord 7703680527574930143355 := by
  unfold o58w001SourceWord
  refine ActualAccelPath.cons (x := 8209377573671194853403) (y := 12314066360506792280105) (z := 7703680527574930143355) (a := 1) ?_ ?_
  · decide
  ·
    refine ActualAccelPath.cons (x := 12314066360506792280105) (y := 9235549770380094210079) (z := 7703680527574930143355) (a := 2) ?_ ?_
    · decide
    ·
      refine ActualAccelPath.cons (x := 9235549770380094210079) (y := 13853324655570141315119) (z := 7703680527574930143355) (a := 1) ?_ ?_
      · decide
      ·
        refine ActualAccelPath.cons (x := 13853324655570141315119) (y := 20779986983355211972679) (z := 7703680527574930143355) (a := 1) ?_ ?_
        · decide
        ·
          refine ActualAccelPath.cons (x := 20779986983355211972679) (y := 31169980475032817959019) (z := 7703680527574930143355) (a := 1) ?_ ?_
          · decide
          ·
            refine ActualAccelPath.cons (x := 31169980475032817959019) (y := 46754970712549226938529) (z := 7703680527574930143355) (a := 1) ?_ ?_
            · decide
            ·
              refine ActualAccelPath.cons (x := 46754970712549226938529) (y := 35066228034411920203897) (z := 7703680527574930143355) (a := 2) ?_ ?_
              · decide
              ·
                refine ActualAccelPath.cons (x := 35066228034411920203897) (y := 26299671025808940152923) (z := 7703680527574930143355) (a := 2) ?_ ?_
                · decide
                ·
                  refine ActualAccelPath.cons (x := 26299671025808940152923) (y := 39449506538713410229385) (z := 7703680527574930143355) (a := 1) ?_ ?_
                  · decide
                  ·
                    refine ActualAccelPath.cons (x := 39449506538713410229385) (y := 29587129904035057672039) (z := 7703680527574930143355) (a := 2) ?_ ?_
                    · decide
                    ·
                      refine ActualAccelPath.cons (x := 29587129904035057672039) (y := 44380694856052586508059) (z := 7703680527574930143355) (a := 1) ?_ ?_
                      · decide
                      ·
                        refine ActualAccelPath.cons (x := 44380694856052586508059) (y := 66571042284078879762089) (z := 7703680527574930143355) (a := 1) ?_ ?_
                        · decide
                        ·
                          refine ActualAccelPath.cons (x := 66571042284078879762089) (y := 49928281713059159821567) (z := 7703680527574930143355) (a := 2) ?_ ?_
                          · decide
                          ·
                            refine ActualAccelPath.cons (x := 49928281713059159821567) (y := 74892422569588739732351) (z := 7703680527574930143355) (a := 1) ?_ ?_
                            · decide
                            ·
                              refine ActualAccelPath.cons (x := 74892422569588739732351) (y := 112338633854383109598527) (z := 7703680527574930143355) (a := 1) ?_ ?_
                              · decide
                              ·
                                refine ActualAccelPath.cons (x := 112338633854383109598527) (y := 168507950781574664397791) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                · decide
                                ·
                                  refine ActualAccelPath.cons (x := 168507950781574664397791) (y := 252761926172361996596687) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                  · decide
                                  ·
                                    refine ActualAccelPath.cons (x := 252761926172361996596687) (y := 379142889258542994895031) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                    · decide
                                    ·
                                      refine ActualAccelPath.cons (x := 379142889258542994895031) (y := 568714333887814492342547) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                      · decide
                                      ·
                                        refine ActualAccelPath.cons (x := 568714333887814492342547) (y := 853071500831721738513821) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                        · decide
                                        ·
                                          refine ActualAccelPath.cons (x := 853071500831721738513821) (y := 319901812811895651942683) (z := 7703680527574930143355) (a := 3) ?_ ?_
                                          · decide
                                          ·
                                            refine ActualAccelPath.cons (x := 319901812811895651942683) (y := 479852719217843477914025) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                            · decide
                                            ·
                                              refine ActualAccelPath.cons (x := 479852719217843477914025) (y := 359889539413382608435519) (z := 7703680527574930143355) (a := 2) ?_ ?_
                                              · decide
                                              ·
                                                refine ActualAccelPath.cons (x := 359889539413382608435519) (y := 539834309120073912653279) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                · decide
                                                ·
                                                  refine ActualAccelPath.cons (x := 539834309120073912653279) (y := 809751463680110868979919) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                  · decide
                                                  ·
                                                    refine ActualAccelPath.cons (x := 809751463680110868979919) (y := 1214627195520166303469879) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                    · decide
                                                    ·
                                                      refine ActualAccelPath.cons (x := 1214627195520166303469879) (y := 1821940793280249455204819) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                      · decide
                                                      ·
                                                        refine ActualAccelPath.cons (x := 1821940793280249455204819) (y := 2732911189920374182807229) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                        · decide
                                                        ·
                                                          refine ActualAccelPath.cons (x := 2732911189920374182807229) (y := 1024841696220140318552711) (z := 7703680527574930143355) (a := 3) ?_ ?_
                                                          · decide
                                                          ·
                                                            refine ActualAccelPath.cons (x := 1024841696220140318552711) (y := 1537262544330210477829067) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                            · decide
                                                            ·
                                                              refine ActualAccelPath.cons (x := 1537262544330210477829067) (y := 2305893816495315716743601) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                              · decide
                                                              ·
                                                                refine ActualAccelPath.cons (x := 2305893816495315716743601) (y := 1729420362371486787557701) (z := 7703680527574930143355) (a := 2) ?_ ?_
                                                                · decide
                                                                ·
                                                                  refine ActualAccelPath.cons (x := 1729420362371486787557701) (y := 324266317944653772667069) (z := 7703680527574930143355) (a := 4) ?_ ?_
                                                                  · decide
                                                                  ·
                                                                    refine ActualAccelPath.cons (x := 324266317944653772667069) (y := 121599869229245164750151) (z := 7703680527574930143355) (a := 3) ?_ ?_
                                                                    · decide
                                                                    ·
                                                                      refine ActualAccelPath.cons (x := 121599869229245164750151) (y := 182399803843867747125227) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                                      · decide
                                                                      ·
                                                                        refine ActualAccelPath.cons (x := 182399803843867747125227) (y := 273599705765801620687841) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                                        · decide
                                                                        ·
                                                                          refine ActualAccelPath.cons (x := 273599705765801620687841) (y := 205199779324351215515881) (z := 7703680527574930143355) (a := 2) ?_ ?_
                                                                          · decide
                                                                          ·
                                                                            refine ActualAccelPath.cons (x := 205199779324351215515881) (y := 153899834493263411636911) (z := 7703680527574930143355) (a := 2) ?_ ?_
                                                                            · decide
                                                                            ·
                                                                              refine ActualAccelPath.cons (x := 153899834493263411636911) (y := 230849751739895117455367) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                                              · decide
                                                                              ·
                                                                                refine ActualAccelPath.cons (x := 230849751739895117455367) (y := 346274627609842676183051) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                                                · decide
                                                                                ·
                                                                                  refine ActualAccelPath.cons (x := 346274627609842676183051) (y := 519411941414764014274577) (z := 7703680527574930143355) (a := 1) ?_ ?_
                                                                                  · decide
                                                                                  ·
                                                                                    refine ActualAccelPath.cons (x := 519411941414764014274577) (y := 389558956061073010705933) (z := 7703680527574930143355) (a := 2) ?_ ?_
                                                                                    · decide
                                                                                    ·
                                                                                      refine ActualAccelPath.cons (x := 389558956061073010705933) (y := 146084608522902379014725) (z := 7703680527574930143355) (a := 3) ?_ ?_
                                                                                      · decide
                                                                                      ·
                                                                                        refine ActualAccelPath.cons (x := 146084608522902379014725) (y := 27390864098044196065261) (z := 7703680527574930143355) (a := 4) ?_ ?_
                                                                                        · decide
                                                                                        ·
                                                                                          refine ActualAccelPath.cons (x := 27390864098044196065261) (y := 10271574036766573524473) (z := 7703680527574930143355) (a := 3) ?_ ?_
                                                                                          · decide
                                                                                          ·
                                                                                            refine ActualAccelPath.cons (x := 10271574036766573524473) (y := 7703680527574930143355) (z := 7703680527574930143355) (a := 2) ?_ ?_
                                                                                            · decide
                                                                                            ·
                                                                                              exact ActualAccelPath.nil 7703680527574930143355

theorem o58_witness001_target_actual_path :
    ActualAccelPath 32720488761612761563163 o58w001TargetWord 30704909094934814579323 := by
  unfold o58w001TargetWord
  refine ActualAccelPath.cons (x := 32720488761612761563163) (y := 49080733142419142344745) (z := 30704909094934814579323) (a := 1) ?_ ?_
  · decide
  ·
    refine ActualAccelPath.cons (x := 49080733142419142344745) (y := 36810549856814356758559) (z := 30704909094934814579323) (a := 2) ?_ ?_
    · decide
    ·
      refine ActualAccelPath.cons (x := 36810549856814356758559) (y := 55215824785221535137839) (z := 30704909094934814579323) (a := 1) ?_ ?_
      · decide
      ·
        refine ActualAccelPath.cons (x := 55215824785221535137839) (y := 82823737177832302706759) (z := 30704909094934814579323) (a := 1) ?_ ?_
        · decide
        ·
          refine ActualAccelPath.cons (x := 82823737177832302706759) (y := 124235605766748454060139) (z := 30704909094934814579323) (a := 1) ?_ ?_
          · decide
          ·
            refine ActualAccelPath.cons (x := 124235605766748454060139) (y := 186353408650122681090209) (z := 30704909094934814579323) (a := 1) ?_ ?_
            · decide
            ·
              refine ActualAccelPath.cons (x := 186353408650122681090209) (y := 139765056487592010817657) (z := 30704909094934814579323) (a := 2) ?_ ?_
              · decide
              ·
                refine ActualAccelPath.cons (x := 139765056487592010817657) (y := 104823792365694008113243) (z := 30704909094934814579323) (a := 2) ?_ ?_
                · decide
                ·
                  refine ActualAccelPath.cons (x := 104823792365694008113243) (y := 157235688548541012169865) (z := 30704909094934814579323) (a := 1) ?_ ?_
                  · decide
                  ·
                    refine ActualAccelPath.cons (x := 157235688548541012169865) (y := 117926766411405759127399) (z := 30704909094934814579323) (a := 2) ?_ ?_
                    · decide
                    ·
                      refine ActualAccelPath.cons (x := 117926766411405759127399) (y := 176890149617108638691099) (z := 30704909094934814579323) (a := 1) ?_ ?_
                      · decide
                      ·
                        refine ActualAccelPath.cons (x := 176890149617108638691099) (y := 265335224425662958036649) (z := 30704909094934814579323) (a := 1) ?_ ?_
                        · decide
                        ·
                          refine ActualAccelPath.cons (x := 265335224425662958036649) (y := 199001418319247218527487) (z := 30704909094934814579323) (a := 2) ?_ ?_
                          · decide
                          ·
                            refine ActualAccelPath.cons (x := 199001418319247218527487) (y := 298502127478870827791231) (z := 30704909094934814579323) (a := 1) ?_ ?_
                            · decide
                            ·
                              refine ActualAccelPath.cons (x := 298502127478870827791231) (y := 447753191218306241686847) (z := 30704909094934814579323) (a := 1) ?_ ?_
                              · decide
                              ·
                                refine ActualAccelPath.cons (x := 447753191218306241686847) (y := 671629786827459362530271) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                · decide
                                ·
                                  refine ActualAccelPath.cons (x := 671629786827459362530271) (y := 1007444680241189043795407) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                  · decide
                                  ·
                                    refine ActualAccelPath.cons (x := 1007444680241189043795407) (y := 1511167020361783565693111) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                    · decide
                                    ·
                                      refine ActualAccelPath.cons (x := 1511167020361783565693111) (y := 2266750530542675348539667) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                      · decide
                                      ·
                                        refine ActualAccelPath.cons (x := 2266750530542675348539667) (y := 3400125795814013022809501) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                        · decide
                                        ·
                                          refine ActualAccelPath.cons (x := 3400125795814013022809501) (y := 1275047173430254883553563) (z := 30704909094934814579323) (a := 3) ?_ ?_
                                          · decide
                                          ·
                                            refine ActualAccelPath.cons (x := 1275047173430254883553563) (y := 1912570760145382325330345) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                            · decide
                                            ·
                                              refine ActualAccelPath.cons (x := 1912570760145382325330345) (y := 1434428070109036743997759) (z := 30704909094934814579323) (a := 2) ?_ ?_
                                              · decide
                                              ·
                                                refine ActualAccelPath.cons (x := 1434428070109036743997759) (y := 2151642105163555115996639) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                · decide
                                                ·
                                                  refine ActualAccelPath.cons (x := 2151642105163555115996639) (y := 3227463157745332673994959) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                  · decide
                                                  ·
                                                    refine ActualAccelPath.cons (x := 3227463157745332673994959) (y := 4841194736617999010992439) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                    · decide
                                                    ·
                                                      refine ActualAccelPath.cons (x := 4841194736617999010992439) (y := 7261792104926998516488659) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                      · decide
                                                      ·
                                                        refine ActualAccelPath.cons (x := 7261792104926998516488659) (y := 10892688157390497774732989) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                        · decide
                                                        ·
                                                          refine ActualAccelPath.cons (x := 10892688157390497774732989) (y := 4084758059021436665524871) (z := 30704909094934814579323) (a := 3) ?_ ?_
                                                          · decide
                                                          ·
                                                            refine ActualAccelPath.cons (x := 4084758059021436665524871) (y := 6127137088532154998287307) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                            · decide
                                                            ·
                                                              refine ActualAccelPath.cons (x := 6127137088532154998287307) (y := 9190705632798232497430961) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                              · decide
                                                              ·
                                                                refine ActualAccelPath.cons (x := 9190705632798232497430961) (y := 6893029224598674373073221) (z := 30704909094934814579323) (a := 2) ?_ ?_
                                                                · decide
                                                                ·
                                                                  refine ActualAccelPath.cons (x := 6893029224598674373073221) (y := 1292442979612251444951229) (z := 30704909094934814579323) (a := 4) ?_ ?_
                                                                  · decide
                                                                  ·
                                                                    refine ActualAccelPath.cons (x := 1292442979612251444951229) (y := 484666117354594291856711) (z := 30704909094934814579323) (a := 3) ?_ ?_
                                                                    · decide
                                                                    ·
                                                                      refine ActualAccelPath.cons (x := 484666117354594291856711) (y := 726999176031891437785067) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                                      · decide
                                                                      ·
                                                                        refine ActualAccelPath.cons (x := 726999176031891437785067) (y := 1090498764047837156677601) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                                        · decide
                                                                        ·
                                                                          refine ActualAccelPath.cons (x := 1090498764047837156677601) (y := 817874073035877867508201) (z := 30704909094934814579323) (a := 2) ?_ ?_
                                                                          · decide
                                                                          ·
                                                                            refine ActualAccelPath.cons (x := 817874073035877867508201) (y := 613405554776908400631151) (z := 30704909094934814579323) (a := 2) ?_ ?_
                                                                            · decide
                                                                            ·
                                                                              refine ActualAccelPath.cons (x := 613405554776908400631151) (y := 920108332165362600946727) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                                              · decide
                                                                              ·
                                                                                refine ActualAccelPath.cons (x := 920108332165362600946727) (y := 1380162498248043901420091) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                                                · decide
                                                                                ·
                                                                                  refine ActualAccelPath.cons (x := 1380162498248043901420091) (y := 2070243747372065852130137) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                                                  · decide
                                                                                  ·
                                                                                    refine ActualAccelPath.cons (x := 2070243747372065852130137) (y := 1552682810529049389097603) (z := 30704909094934814579323) (a := 2) ?_ ?_
                                                                                    · decide
                                                                                    ·
                                                                                      refine ActualAccelPath.cons (x := 1552682810529049389097603) (y := 2329024215793574083646405) (z := 30704909094934814579323) (a := 1) ?_ ?_
                                                                                      · decide
                                                                                      ·
                                                                                        refine ActualAccelPath.cons (x := 2329024215793574083646405) (y := 436692040461295140683701) (z := 30704909094934814579323) (a := 4) ?_ ?_
                                                                                        · decide
                                                                                        ·
                                                                                          refine ActualAccelPath.cons (x := 436692040461295140683701) (y := 40939878793246419439097) (z := 30704909094934814579323) (a := 5) ?_ ?_
                                                                                          · decide
                                                                                          ·
                                                                                            refine ActualAccelPath.cons (x := 40939878793246419439097) (y := 30704909094934814579323) (z := 30704909094934814579323) (a := 2) ?_ ?_
                                                                                            · decide
                                                                                            ·
                                                                                              exact ActualAccelPath.nil 30704909094934814579323

theorem o58_witness001_source_word_length : o58w001SourceWord.length = 46 := by decide
theorem o58_witness001_source_word_sum : o58w001SourceWord.sum = 73 := by decide
theorem o58_witness001_target_word_length : o58w001TargetWord.length = 46 := by decide
theorem o58_witness001_target_word_sum : o58w001TargetWord.sum = 73 := by decide

/-- Exact affine block reconstructed from the actual source trajectory. -/
theorem o58_witness001_source_affine_block :
    (9444732965739290427392 : Int) * 7703680527574930143355 = (8862938119652501095929 : Int) * 8209377573671194853403 + 21967197859099783683773 := by decide

/-- Exact affine block reconstructed from the actual transported target trajectory. -/
theorem o58_witness001_target_affine_block :
    (9444732965739290427392 : Int) * 30704909094934814579323 = (8862938119652501095929 : Int) * 32720488761612761563163 + 21178599549948700352189 := by decide

theorem o58_witness001_source_actual_descent : (7703680527574930143355 : Int) < 8209377573671194853403 := by decide
theorem o58_witness001_target_actual_descent_direct : (30704909094934814579323 : Int) < 32720488761612761563163 := by decide

/-- The actual source affine block yields exactly the CPOQ source margin. -/
theorem o58_witness001_source_margin_from_actual_path :
    margin (9444732965739290427392 : Int) (8862938119652501095929 : Int) (8209377573671194853403 : Int) (21967197859099783683773 : Int) = (4776173561942372855695891794986152876834816 : Int) := by
  have hblock := o58_witness001_source_affine_block
  change (9444732965739290427392 : Int) * 8209377573671194853403 - ((8862938119652501095929 : Int) * 8209377573671194853403 + 21967197859099783683773) = (4776173561942372855695891794986152876834816 : Int)
  rw [← hblock]
  decide

/-- Rebuild Witness 001 transport from the actual source path-derived margin and Guard 01. -/
theorem o58_witness001_actual_path_to_cpoq_target_margin :
    0 < margin (9444732965739290427392 : Int) (8862938119652501095929 : Int) (32720488761612761563163 : Int) (21178599549948700352189 : Int) := by
  have hsource : (4776173561942372855695891794986152876834816 : Int) ≤ margin (9444732965739290427392 : Int) (8862938119652501095929 : Int) (8209377573671194853403 : Int) (21967197859099783683773 : Int) := by
    rw [o58_witness001_source_margin_from_actual_path]
    omega
  have htransport := segment_margin_transport_positive
    (9444732965739290427392 : Int) (8862938119652501095929 : Int) (8209377573671194853403 : Int) (21967197859099783683773 : Int)
    (24511111187941566709760 : Int) (-788598309151083331584 : Int) (4776173561942372855695891794986152876834816 : Int)
    hsource o58_segment_guard_01
  have hT : (8209377573671194853403 : Int) + (24511111187941566709760 : Int) = (32720488761612761563163 : Int) := by decide
  have hC : (21967197859099783683773 : Int) + (-788598309151083331584 : Int) = (21178599549948700352189 : Int) := by decide
  rw [hT, hC] at htransport
  exact htransport

/-- Positive transported margin plus the target actual-path affine identity implies actual target descent. -/
theorem o58_witness001_cpoq_transport_to_actual_target_descent :
    (30704909094934814579323 : Int) < (32720488761612761563163 : Int) := by
  have hm := o58_witness001_actual_path_to_cpoq_target_margin
  have hblock := o58_witness001_target_affine_block
  change 0 < (9444732965739290427392 : Int) * 32720488761612761563163 - ((8862938119652501095929 : Int) * 32720488761612761563163 + 21178599549948700352189) at hm
  rw [← hblock] at hm
  omega

/-- End-to-end Witness 001: actual source path → CPOQ transport → actual target path/descent. -/
theorem o58_witness001_actual_path_cpoq_descent_end_to_end :
    ActualAccelPath 8209377573671194853403 o58w001SourceWord 7703680527574930143355 ∧
    ActualAccelPath 32720488761612761563163 o58w001TargetWord 30704909094934814579323 ∧
    0 < margin (9444732965739290427392 : Int) (8862938119652501095929 : Int) (32720488761612761563163 : Int) (21178599549948700352189 : Int) ∧
    (30704909094934814579323 : Int) < (32720488761612761563163 : Int) := by
  exact ⟨o58_witness001_source_actual_path,
         o58_witness001_target_actual_path,
         o58_witness001_actual_path_to_cpoq_target_margin,
         o58_witness001_cpoq_transport_to_actual_target_descent⟩

end CPOQ
