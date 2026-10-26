import V185TrunkScan23Chunk1290

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7646659 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 7]
def baseStart_7646659 : Nat := 118140960795 + 7646659 * 2 ^ 59
def prefixEnd_7646659 : Nat := 4983230072969 + 3 ^ 40 * 7646659 * 2
def baseEnd_7646659 : Nat := 1308803822676167715065387

theorem tailTrace_7646659 : CollatzResearch.WordTrace tailWord_7646659 prefixEnd_7646659 1308803822676167715065387 := by
  unfold tailWord_7646659
  simp only [CollatzResearch.WordTrace]
  refine ⟨278896566004467863230687031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185931044002978575487124687 278896566004467863230687031)
  ·
    refine ⟨418344849006701794846030547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278896566004467863230687031 418344849006701794846030547)
    ·
      refine ⟨627517273510052692269045821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418344849006701794846030547 627517273510052692269045821)
      ·
        refine ⟨235318977566269759600892183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627517273510052692269045821 235318977566269759600892183)
        ·
          refine ⟨352978466349404639401338275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235318977566269759600892183 352978466349404639401338275)
          ·
            refine ⟨529467699524106959102007413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352978466349404639401338275 529467699524106959102007413)
            ·
              refine ⟨49637596830385027415813195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529467699524106959102007413 49637596830385027415813195)
              ·
                refine ⟨74456395245577541123719793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49637596830385027415813195 74456395245577541123719793)
                ·
                  refine ⟨55842296434183155842789845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74456395245577541123719793 55842296434183155842789845)
                  ·
                    refine ⟨1308803822676167715065387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55842296434183155842789845 1308803822676167715065387)
                    ·
                      rfl

theorem cell23_7646659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_7646659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646659 prefixEnd_7646659 := by exact prefixLift 7646659
  have htrace : WordTrace (prefixWord ++ tailWord_7646659) baseStart_7646659 baseEnd_7646659 := by
    simpa [prefixWord, tailWord_7646659, baseEnd_7646659] using wordTrace_append hprefix tailTrace_7646659
  have hstable : (prefixWord ++ tailWord_7646659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646659).length < 2 ^ (prefixWord ++ tailWord_7646659).sum := by decide
  have hdescent : baseEnd_7646659 < baseStart_7646659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646716 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_7646716 : Nat := 118140960795 + 7646716 * 2 ^ 59
def prefixEnd_7646716 : Nat := 4983230072969 + 3 ^ 40 * 7646716 * 2
def baseEnd_7646716 : Nat := 3926440736425809422183399

theorem tailTrace_7646716 : CollatzResearch.WordTrace tailWord_7646716 prefixEnd_7646716 3926440736425809422183399 := by
  unfold tailWord_7646716
  simp only [CollatzResearch.WordTrace]
  refine ⟨139449322482630680982756001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185932429976840907977008001 139449322482630680982756001)
  ·
    refine ⟨104586991861973010737067001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139449322482630680982756001 104586991861973010737067001)
    ·
      refine ⟨78440243896479758052800251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104586991861973010737067001 78440243896479758052800251)
      ·
        refine ⟨117660365844719637079200377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78440243896479758052800251 117660365844719637079200377)
        ·
          refine ⟨88245274383539727809400283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117660365844719637079200377 88245274383539727809400283)
          ·
            refine ⟨132367911575309591714100425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88245274383539727809400283 132367911575309591714100425)
            ·
              refine ⟨99275933681482193785575319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132367911575309591714100425 99275933681482193785575319)
              ·
                refine ⟨148913900522223290678362979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99275933681482193785575319 148913900522223290678362979)
                ·
                  refine ⟨223370850783334936017544469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148913900522223290678362979 223370850783334936017544469)
                  ·
                    refine ⟨10470508630468825125822397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 223370850783334936017544469 10470508630468825125822397)
                    ·
                      refine ⟨3926440736425809422183399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470508630468825125822397 3926440736425809422183399)
                      ·
                        rfl

theorem cell23_7646716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_7646716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646716 prefixEnd_7646716 := by exact prefixLift 7646716
  have htrace : WordTrace (prefixWord ++ tailWord_7646716) baseStart_7646716 baseEnd_7646716 := by
    simpa [prefixWord, tailWord_7646716, baseEnd_7646716] using wordTrace_append hprefix tailTrace_7646716
  have hstable : (prefixWord ++ tailWord_7646716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646716).length < 2 ^ (prefixWord ++ tailWord_7646716).sum := by decide
  have hdescent : baseEnd_7646716 < baseStart_7646716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646724 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7646724 : Nat := 118140960795 + 7646724 * 2 ^ 59
def prefixEnd_7646724 : Nat := 4983230072969 + 3 ^ 40 * 7646724 * 2
def baseEnd_7646724 : Nat := 3926444844271045390883363

theorem tailTrace_7646724 : CollatzResearch.WordTrace tailWord_7646724 prefixEnd_7646724 3926444844271045390883363 := by
  unfold tailWord_7646724
  simp only [CollatzResearch.WordTrace]
  refine ⟨139449468374616189665901613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185932624499488252887868817 139449468374616189665901613)
  ·
    refine ⟨52293550640481071124713105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139449468374616189665901613 52293550640481071124713105)
    ·
      refine ⟨39220162980360803343534829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52293550640481071124713105 39220162980360803343534829)
      ·
        refine ⟨14707561117635301253825561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39220162980360803343534829 14707561117635301253825561)
        ·
          refine ⟨11030670838226475940369171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14707561117635301253825561 11030670838226475940369171)
          ·
            refine ⟨16546006257339713910553757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030670838226475940369171 16546006257339713910553757)
            ·
              refine ⟨6204752346502392716457659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16546006257339713910553757 6204752346502392716457659)
              ·
                refine ⟨9307128519753589074686489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204752346502392716457659 9307128519753589074686489)
                ·
                  refine ⟨6980346389815191806014867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9307128519753589074686489 6980346389815191806014867)
                  ·
                    refine ⟨10470519584722787709022301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6980346389815191806014867 10470519584722787709022301)
                    ·
                      refine ⟨3926444844271045390883363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470519584722787709022301 3926444844271045390883363)
                      ·
                        rfl

theorem cell23_7646724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7646724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646724 prefixEnd_7646724 := by exact prefixLift 7646724
  have htrace : WordTrace (prefixWord ++ tailWord_7646724) baseStart_7646724 baseEnd_7646724 := by
    simpa [prefixWord, tailWord_7646724, baseEnd_7646724] using wordTrace_append hprefix tailTrace_7646724
  have hstable : (prefixWord ++ tailWord_7646724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646724).length < 2 ^ (prefixWord ++ tailWord_7646724).sum := by decide
  have hdescent : baseEnd_7646724 < baseStart_7646724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646730 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_7646730 : Nat := 118140960795 + 7646730 * 2 ^ 59
def prefixEnd_7646730 : Nat := 4983230072969 + 3 ^ 40 * 7646730 * 2
def baseEnd_7646730 : Nat := 3926447925154972367408335

theorem tailTrace_7646730 : CollatzResearch.WordTrace tailWord_7646730 prefixEnd_7646730 3926447925154972367408335 := by
  unfold tailWord_7646730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69724788896802660589130411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185932770391473761571014429 69724788896802660589130411)
  ·
    refine ⟨104587183345203990883695617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69724788896802660589130411 104587183345203990883695617)
    ·
      refine ⟨78440387508902993162771713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104587183345203990883695617 78440387508902993162771713)
      ·
        refine ⟨58830290631677244872078785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78440387508902993162771713 58830290631677244872078785)
        ·
          refine ⟨44122717973757933654059089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58830290631677244872078785 44122717973757933654059089)
          ·
            refine ⟨33092038480318450240544317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44122717973757933654059089 33092038480318450240544317)
            ·
              refine ⟨12409514430119418840204119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33092038480318450240544317 12409514430119418840204119)
              ·
                refine ⟨18614271645179128260306179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12409514430119418840204119 18614271645179128260306179)
                ·
                  refine ⟨27921407467768692390459269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18614271645179128260306179 27921407467768692390459269)
                  ·
                    refine ⟨5235263900206629823211113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27921407467768692390459269 5235263900206629823211113)
                    ·
                      refine ⟨3926447925154972367408335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235263900206629823211113 3926447925154972367408335)
                      ·
                        rfl

theorem cell23_7646730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_7646730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646730 prefixEnd_7646730 := by exact prefixLift 7646730
  have htrace : WordTrace (prefixWord ++ tailWord_7646730) baseStart_7646730 baseEnd_7646730 := by
    simpa [prefixWord, tailWord_7646730, baseEnd_7646730] using wordTrace_append hprefix tailTrace_7646730
  have hstable : (prefixWord ++ tailWord_7646730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646730).length < 2 ^ (prefixWord ++ tailWord_7646730).sum := by decide
  have hdescent : baseEnd_7646730 < baseStart_7646730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646776 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_7646776 : Nat := 118140960795 + 7646776 * 2 ^ 59
def prefixEnd_7646776 : Nat := 4983230072969 + 3 ^ 40 * 7646776 * 2
def baseEnd_7646776 : Nat := 3926471545265079187433123

theorem tailTrace_7646776 : CollatzResearch.WordTrace tailWord_7646776 prefixEnd_7646776 3926471545265079187433123 := by
  unfold tailWord_7646776
  simp only [CollatzResearch.WordTrace]
  refine ⟨139450416672521996106348091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185933888896695994808464121 139450416672521996106348091)
  ·
    refine ⟨209175625008782994159522137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139450416672521996106348091 209175625008782994159522137)
    ·
      refine ⟨156881718756587245619641603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209175625008782994159522137 156881718756587245619641603)
      ·
        refine ⟨235322578134880868429462405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156881718756587245619641603 235322578134880868429462405)
        ·
          refine ⟨44122983400290162830524201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235322578134880868429462405 44122983400290162830524201)
          ·
            refine ⟨33092237550217622122893151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44122983400290162830524201 33092237550217622122893151)
            ·
              refine ⟨49638356325326433184339727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33092237550217622122893151 49638356325326433184339727)
              ·
                refine ⟨74457534487989649776509591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49638356325326433184339727 74457534487989649776509591)
                ·
                  refine ⟨111686301731984474664764387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74457534487989649776509591 111686301731984474664764387)
                  ·
                    refine ⟨167529452597976711997146581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111686301731984474664764387 167529452597976711997146581)
                    ·
                      refine ⟨3926471545265079187433123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167529452597976711997146581 3926471545265079187433123)
                      ·
                        rfl

theorem cell23_7646776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_7646776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646776 prefixEnd_7646776 := by exact prefixLift 7646776
  have htrace : WordTrace (prefixWord ++ tailWord_7646776) baseStart_7646776 baseEnd_7646776 := by
    simpa [prefixWord, tailWord_7646776, baseEnd_7646776] using wordTrace_append hprefix tailTrace_7646776
  have hstable : (prefixWord ++ tailWord_7646776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646776).length < 2 ^ (prefixWord ++ tailWord_7646776).sum := by decide
  have hdescent : baseEnd_7646776 < baseStart_7646776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646781 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7646781 : Nat := 118140960795 + 7646781 * 2 ^ 59
def prefixEnd_7646781 : Nat := 4983230072969 + 3 ^ 40 * 7646781 * 2
def baseEnd_7646781 : Nat := 3926474112668351667870601

theorem tailTrace_7646781 : CollatzResearch.WordTrace tailWord_7646781 prefixEnd_7646781 3926474112668351667870601 := by
  unfold tailWord_7646781
  simp only [CollatzResearch.WordTrace]
  refine ⟨278901015710025878066628197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185934010473350585377752131 278901015710025878066628197)
  ·
    refine ⟨52293940445629852137492787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278901015710025878066628197 52293940445629852137492787)
    ·
      refine ⟨78440910668444778206239181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52293940445629852137492787 78440910668444778206239181)
      ·
        refine ⟨29415341500666791827339693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78440910668444778206239181 29415341500666791827339693)
        ·
          refine ⟨11030753062750046935252385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29415341500666791827339693 11030753062750046935252385)
          ·
            refine ⟨8273064797062535201439289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11030753062750046935252385 8273064797062535201439289)
            ·
              refine ⟨6204798597796901401079467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273064797062535201439289 6204798597796901401079467)
              ·
                refine ⟨9307197896695352101619201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204798597796901401079467 9307197896695352101619201)
                ·
                  refine ⟨6980398422521514076214401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9307197896695352101619201 6980398422521514076214401)
                  ·
                    refine ⟨5235298816891135557160801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980398422521514076214401 5235298816891135557160801)
                    ·
                      refine ⟨3926474112668351667870601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235298816891135557160801 3926474112668351667870601)
                      ·
                        rfl

theorem cell23_7646781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7646781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646781 prefixEnd_7646781 := by exact prefixLift 7646781
  have htrace : WordTrace (prefixWord ++ tailWord_7646781) baseStart_7646781 baseEnd_7646781 := by
    simpa [prefixWord, tailWord_7646781, baseEnd_7646781] using wordTrace_append hprefix tailTrace_7646781
  have hstable : (prefixWord ++ tailWord_7646781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646781).length < 2 ^ (prefixWord ++ tailWord_7646781).sum := by decide
  have hdescent : baseEnd_7646781 < baseStart_7646781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646816 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_7646816 : Nat := 118140960795 + 7646816 * 2 ^ 59
def prefixEnd_7646816 : Nat := 4983230072969 + 3 ^ 40 * 7646816 * 2
def baseEnd_7646816 : Nat := 3926492084491259030932939

theorem tailTrace_7646816 : CollatzResearch.WordTrace tailWord_7646816 prefixEnd_7646816 3926492084491259030932939 := by
  unfold tailWord_7646816
  simp only [CollatzResearch.WordTrace]
  refine ⟨139451146132449539522076151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185934861509932719362768201 139451146132449539522076151)
  ·
    refine ⟨209176719198674309283114227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139451146132449539522076151 209176719198674309283114227)
    ·
      refine ⟨313765078798011463924671341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209176719198674309283114227 313765078798011463924671341)
      ·
        refine ⟨117661904549254298971751753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313765078798011463924671341 117661904549254298971751753)
        ·
          refine ⟨88246428411940724228813815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117661904549254298971751753 88246428411940724228813815)
          ·
            refine ⟨132369642617911086343220723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88246428411940724228813815 132369642617911086343220723)
            ·
              refine ⟨198554463926866629514831085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132369642617911086343220723 198554463926866629514831085)
              ·
                refine ⟨74457923972574986068061657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198554463926866629514831085 74457923972574986068061657)
                ·
                  refine ⟨55843442979431239551046243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74457923972574986068061657 55843442979431239551046243)
                  ·
                    refine ⟨83765164469146859326569365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55843442979431239551046243 83765164469146859326569365)
                    ·
                      refine ⟨3926492084491259030932939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83765164469146859326569365 3926492084491259030932939)
                      ·
                        rfl

theorem cell23_7646816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_7646816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646816 prefixEnd_7646816 := by exact prefixLift 7646816
  have htrace : WordTrace (prefixWord ++ tailWord_7646816) baseStart_7646816 baseEnd_7646816 := by
    simpa [prefixWord, tailWord_7646816, baseEnd_7646816] using wordTrace_append hprefix tailTrace_7646816
  have hstable : (prefixWord ++ tailWord_7646816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646816).length < 2 ^ (prefixWord ++ tailWord_7646816).sum := by decide
  have hdescent : baseEnd_7646816 < baseStart_7646816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646837 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7646837 : Nat := 118140960795 + 7646837 * 2 ^ 59
def prefixEnd_7646837 : Nat := 4983230072969 + 3 ^ 40 * 7646837 * 2
def baseEnd_7646837 : Nat := 3926502867585003448770343

theorem tailTrace_7646837 : CollatzResearch.WordTrace tailWord_7646837 prefixEnd_7646837 3926502867585003448770343 := by
  unfold tailWord_7646837
  simp only [CollatzResearch.WordTrace]
  refine ⟨278903058197822999630666765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185935372131881999753777843 278903058197822999630666765)
  ·
    refine ⟨104588646824183624861500037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278903058197822999630666765 104588646824183624861500037)
    ·
      refine ⟨19610371279534429661531257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104588646824183624861500037 19610371279534429661531257)
      ·
        refine ⟨14707778459650822246148443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19610371279534429661531257 14707778459650822246148443)
        ·
          refine ⟨22061667689476233369222665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14707778459650822246148443 22061667689476233369222665)
          ·
            refine ⟨16546250767107175026916999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22061667689476233369222665 16546250767107175026916999)
            ·
              refine ⟨24819376150660762540375499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16546250767107175026916999 24819376150660762540375499)
              ·
                refine ⟨37229064225991143810563249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24819376150660762540375499 37229064225991143810563249)
                ·
                  refine ⟨27921798169493357857922437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37229064225991143810563249 27921798169493357857922437)
                  ·
                    refine ⟨5235337156780004598360457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27921798169493357857922437 5235337156780004598360457)
                    ·
                      refine ⟨3926502867585003448770343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235337156780004598360457 3926502867585003448770343)
                      ·
                        rfl

theorem cell23_7646837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7646837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646837 prefixEnd_7646837 := by exact prefixLift 7646837
  have htrace : WordTrace (prefixWord ++ tailWord_7646837) baseStart_7646837 baseEnd_7646837 := by
    simpa [prefixWord, tailWord_7646837, baseEnd_7646837] using wordTrace_append hprefix tailTrace_7646837
  have hstable : (prefixWord ++ tailWord_7646837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646837).length < 2 ^ (prefixWord ++ tailWord_7646837).sum := by decide
  have hdescent : baseEnd_7646837 < baseStart_7646837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646894 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_7646894 : Nat := 118140960795 + 7646894 * 2 ^ 59
def prefixEnd_7646894 : Nat := 4983230072969 + 3 ^ 40 * 7646894 * 2
def baseEnd_7646894 : Nat := 436281348442478858417509

theorem tailTrace_7646894 : CollatzResearch.WordTrace tailWord_7646894 prefixEnd_7646894 436281348442478858417509 := by
  unfold tailWord_7646894
  simp only [CollatzResearch.WordTrace]
  refine ⟨34863142144827062295686467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185936758105744332243661157 34863142144827062295686467)
  ·
    refine ⟨52294713217240593443529701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34863142144827062295686467 52294713217240593443529701)
    ·
      refine ⟨9805258728232611270661819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52294713217240593443529701 9805258728232611270661819)
      ·
        refine ⟨14707888092348916905992729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805258728232611270661819 14707888092348916905992729)
        ·
          refine ⟨11030916069261687679494547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14707888092348916905992729 11030916069261687679494547)
          ·
            refine ⟨16546374103892531519241821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030916069261687679494547 16546374103892531519241821)
            ·
              refine ⟨6204890288959699319715683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16546374103892531519241821 6204890288959699319715683)
              ·
                refine ⟨9307335433439548979573525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204890288959699319715683 9307335433439548979573525)
                ·
                  refine ⟨436281348442478858417509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9307335433439548979573525 436281348442478858417509)
                  ·
                    rfl

theorem cell23_7646894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_7646894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646894 prefixEnd_7646894 := by exact prefixLift 7646894
  have htrace : WordTrace (prefixWord ++ tailWord_7646894) baseStart_7646894 baseEnd_7646894 := by
    simpa [prefixWord, tailWord_7646894, baseEnd_7646894] using wordTrace_append hprefix tailTrace_7646894
  have hstable : (prefixWord ++ tailWord_7646894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646894).length < 2 ^ (prefixWord ++ tailWord_7646894).sum := by decide
  have hdescent : baseEnd_7646894 < baseStart_7646894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646923 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4]
def baseStart_7646923 : Nat := 118140960795 + 7646923 * 2 ^ 59
def prefixEnd_7646923 : Nat := 4983230072969 + 3 ^ 40 * 7646923 * 2
def baseEnd_7646923 : Nat := 3926547026921290112294947

theorem tailTrace_7646923 : CollatzResearch.WordTrace tailWord_7646923 prefixEnd_7646923 3926547026921290112294947 := by
  unfold tailWord_7646923
  simp only [CollatzResearch.WordTrace]
  refine ⟨278906194875511436318297423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185937463250340957545531615 278906194875511436318297423)
  ·
    refine ⟨418359292313267154477446135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278906194875511436318297423 418359292313267154477446135)
    ·
      refine ⟨627538938469900731716169203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418359292313267154477446135 627538938469900731716169203)
      ·
        refine ⟨941308407704851097574253805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627538938469900731716169203 941308407704851097574253805)
        ·
          refine ⟨352990652889319161590345177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941308407704851097574253805 352990652889319161590345177)
          ·
            refine ⟨264742989666989371192758883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352990652889319161590345177 264742989666989371192758883)
            ·
              refine ⟨397114484500484056789138325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264742989666989371192758883 397114484500484056789138325)
              ·
                refine ⟨18614741460960190161990859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397114484500484056789138325 18614741460960190161990859)
                ·
                  refine ⟨27922112191440285242986289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18614741460960190161990859 27922112191440285242986289)
                  ·
                    refine ⟨20941584143580213932239717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27922112191440285242986289 20941584143580213932239717)
                    ·
                      refine ⟨3926547026921290112294947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20941584143580213932239717 3926547026921290112294947)
                      ·
                        rfl

theorem cell23_7646923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_7646923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646923 prefixEnd_7646923 := by exact prefixLift 7646923
  have htrace : WordTrace (prefixWord ++ tailWord_7646923) baseStart_7646923 baseEnd_7646923 := by
    simpa [prefixWord, tailWord_7646923, baseEnd_7646923] using wordTrace_append hprefix tailTrace_7646923
  have hstable : (prefixWord ++ tailWord_7646923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646923).length < 2 ^ (prefixWord ++ tailWord_7646923).sum := by decide
  have hdescent : baseEnd_7646923 < baseStart_7646923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646930 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7646930 : Nat := 118140960795 + 7646930 * 2 ^ 59
def prefixEnd_7646930 : Nat := 4983230072969 + 3 ^ 40 * 7646930 * 2
def baseEnd_7646930 : Nat := 3926550621285871584907415

theorem tailTrace_7646930 : CollatzResearch.WordTrace tailWord_7646930 prefixEnd_7646930 3926550621285871584907415 := by
  unfold tailWord_7646930
  simp only [CollatzResearch.WordTrace]
  refine ⟨69726612546621519128450561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185937633457657384342534829 69726612546621519128450561)
  ·
    refine ⟨52294959409966139346337921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69726612546621519128450561 52294959409966139346337921)
    ·
      refine ⟨39221219557474604509753441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52294959409966139346337921 39221219557474604509753441)
      ·
        refine ⟨29415914668105953382315081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39221219557474604509753441 29415914668105953382315081)
        ·
          refine ⟨22061936001079465036736311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29415914668105953382315081 22061936001079465036736311)
          ·
            refine ⟨33092904001619197555104467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22061936001079465036736311 33092904001619197555104467)
            ·
              refine ⟨49639356002428796332656701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33092904001619197555104467 49639356002428796332656701)
              ·
                refine ⟨18614758500910798624746263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49639356002428796332656701 18614758500910798624746263)
                ·
                  refine ⟨27922137751366197937119395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18614758500910798624746263 27922137751366197937119395)
                  ·
                    refine ⟨41883206627049296905679093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27922137751366197937119395 41883206627049296905679093)
                    ·
                      refine ⟨3926550621285871584907415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41883206627049296905679093 3926550621285871584907415)
                      ·
                        rfl

theorem cell23_7646930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7646930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646930 prefixEnd_7646930 := by exact prefixLift 7646930
  have htrace : WordTrace (prefixWord ++ tailWord_7646930) baseStart_7646930 baseEnd_7646930 := by
    simpa [prefixWord, tailWord_7646930, baseEnd_7646930] using wordTrace_append hprefix tailTrace_7646930
  have hstable : (prefixWord ++ tailWord_7646930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646930).length < 2 ^ (prefixWord ++ tailWord_7646930).sum := by decide
  have hdescent : baseEnd_7646930 < baseStart_7646930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646944 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 1, 2, 2]
def baseStart_7646944 : Nat := 118140960795 + 7646944 * 2 ^ 59
def prefixEnd_7646944 : Nat := 4983230072969 + 3 ^ 40 * 7646944 * 2
def baseEnd_7646944 : Nat := 3926557810015034530132351

theorem tailTrace_7646944 : CollatzResearch.WordTrace tailWord_7646944 prefixEnd_7646944 3926557810015034530132351 := by
  unfold tailWord_7646944
  simp only [CollatzResearch.WordTrace]
  refine ⟨139453480404217678452405943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185937973872290237936541257 139453480404217678452405943)
  ·
    refine ⟨209180220606326517678608915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139453480404217678452405943 209180220606326517678608915)
    ·
      refine ⟨313770330909489776517913373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209180220606326517678608915 313770330909489776517913373)
      ·
        refine ⟨117663874091058666194217515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313770330909489776517913373 117663874091058666194217515)
        ·
          refine ⟨176495811136587999291326273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117663874091058666194217515 176495811136587999291326273)
          ·
            refine ⟨132371858352440999468494705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176495811136587999291326273 132371858352440999468494705)
            ·
              refine ⟨99278893764330749601371029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132371858352440999468494705 99278893764330749601371029)
              ·
                refine ⟨4653698145203003887564267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99278893764330749601371029 4653698145203003887564267)
                ·
                  refine ⟨6980547217804505831346401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653698145203003887564267 6980547217804505831346401)
                  ·
                    refine ⟨5235410413353379373509801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980547217804505831346401 5235410413353379373509801)
                    ·
                      refine ⟨3926557810015034530132351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235410413353379373509801 3926557810015034530132351)
                      ·
                        rfl

theorem cell23_7646944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_7646944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646944 prefixEnd_7646944 := by exact prefixLift 7646944
  have htrace : WordTrace (prefixWord ++ tailWord_7646944) baseStart_7646944 baseEnd_7646944 := by
    simpa [prefixWord, tailWord_7646944, baseEnd_7646944] using wordTrace_append hprefix tailTrace_7646944
  have hstable : (prefixWord ++ tailWord_7646944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646944).length < 2 ^ (prefixWord ++ tailWord_7646944).sum := by decide
  have hdescent : baseEnd_7646944 < baseStart_7646944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646960 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3]
def baseStart_7646960 : Nat := 118140960795 + 7646960 * 2 ^ 59
def prefixEnd_7646960 : Nat := 4983230072969 + 3 ^ 40 * 7646960 * 2
def baseEnd_7646960 : Nat := 3926566025705506467532277

theorem tailTrace_7646960 : CollatzResearch.WordTrace tailWord_7646960 prefixEnd_7646960 3926566025705506467532277 := by
  unfold tailWord_7646960
  simp only [CollatzResearch.WordTrace]
  refine ⟨139453772188188695818697167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185938362917584927758262889 139453772188188695818697167)
  ·
    refine ⟨209180658282283043728045751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139453772188188695818697167 209180658282283043728045751)
    ·
      refine ⟨313770987423424565592068627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209180658282283043728045751 313770987423424565592068627)
      ·
        refine ⟨470656481135136848388102941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313770987423424565592068627 470656481135136848388102941)
        ·
          refine ⟨176496180425676318145538603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470656481135136848388102941 176496180425676318145538603)
          ·
            refine ⟨264744270638514477218307905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176496180425676318145538603 264744270638514477218307905)
            ·
              refine ⟨198558202978885857913730929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264744270638514477218307905 198558202978885857913730929)
              ·
                refine ⟨148918652234164393435298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198558202978885857913730929 148918652234164393435298197)
                ·
                  refine ⟨6980561823476455942279603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148918652234164393435298197 6980561823476455942279603)
                  ·
                    refine ⟨10470842735214683913419405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6980561823476455942279603 10470842735214683913419405)
                    ·
                      refine ⟨3926566025705506467532277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470842735214683913419405 3926566025705506467532277)
                      ·
                        rfl

theorem cell23_7646960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_7646960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646960 prefixEnd_7646960 := by exact prefixLift 7646960
  have htrace : WordTrace (prefixWord ++ tailWord_7646960) baseStart_7646960 baseEnd_7646960 := by
    simpa [prefixWord, tailWord_7646960, baseEnd_7646960] using wordTrace_append hprefix tailTrace_7646960
  have hstable : (prefixWord ++ tailWord_7646960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646960).length < 2 ^ (prefixWord ++ tailWord_7646960).sum := by decide
  have hdescent : baseEnd_7646960 < baseStart_7646960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646973 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7646973 : Nat := 118140960795 + 7646973 * 2 ^ 59
def prefixEnd_7646973 : Nat := 4983230072969 + 3 ^ 40 * 7646973 * 2
def baseEnd_7646973 : Nat := 3926572700954014916669717

theorem tailTrace_7646973 : CollatzResearch.WordTrace tailWord_7646973 prefixEnd_7646973 3926572700954014916669717 := by
  unfold tailWord_7646973
  simp only [CollatzResearch.WordTrace]
  refine ⟨278908018525330294857617573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185938679016886863238411715 278908018525330294857617573)
  ·
    refine ⟨52295253473499430285803295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278908018525330294857617573 52295253473499430285803295)
    ·
      refine ⟨78442880210249145428704943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52295253473499430285803295 78442880210249145428704943)
      ·
        refine ⟨117664320315373718143057415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78442880210249145428704943 117664320315373718143057415)
        ·
          refine ⟨176496480473060577214586123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117664320315373718143057415 176496480473060577214586123)
          ·
            refine ⟨264744720709590865821879185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176496480473060577214586123 264744720709590865821879185)
            ·
              refine ⟨198558540532193149366409389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264744720709590865821879185 198558540532193149366409389)
              ·
                refine ⟨74459452699572431012403521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198558540532193149366409389 74459452699572431012403521)
                ·
                  refine ⟨55844589524679323259302641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74459452699572431012403521 55844589524679323259302641)
                  ·
                    refine ⟨41883442143509492444476981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55844589524679323259302641 41883442143509492444476981)
                    ·
                      refine ⟨3926572700954014916669717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41883442143509492444476981 3926572700954014916669717)
                      ·
                        rfl

theorem cell23_7646973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7646973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646973 prefixEnd_7646973 := by exact prefixLift 7646973
  have htrace : WordTrace (prefixWord ++ tailWord_7646973) baseStart_7646973 baseEnd_7646973 := by
    simpa [prefixWord, tailWord_7646973, baseEnd_7646973] using wordTrace_append hprefix tailTrace_7646973
  have hstable : (prefixWord ++ tailWord_7646973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646973).length < 2 ^ (prefixWord ++ tailWord_7646973).sum := by decide
  have hdescent : baseEnd_7646973 < baseStart_7646973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646987 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 1, 3, 2]
def baseStart_7646987 : Nat := 118140960795 + 7646987 * 2 ^ 59
def prefixEnd_7646987 : Nat := 4983230072969 + 3 ^ 40 * 7646987 * 2
def baseEnd_7646987 : Nat := 3926579889683177861894653

theorem tailTrace_7646987 : CollatzResearch.WordTrace tailWord_7646987 prefixEnd_7646987 3926579889683177861894653 := by
  unfold tailWord_7646987
  simp only [CollatzResearch.WordTrace]
  refine ⟨278908529147279575248627215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185939019431519716832418143 278908529147279575248627215)
  ·
    refine ⟨418362793720919362872940823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278908529147279575248627215 418362793720919362872940823)
    ·
      refine ⟨627544190581379044309411235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418362793720919362872940823 627544190581379044309411235)
      ·
        refine ⟨941316285872068566464116853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627544190581379044309411235 941316285872068566464116853)
        ·
          refine ⟨88248401800506428106010955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 941316285872068566464116853 88248401800506428106010955)
          ·
            refine ⟨132372602700759642159016433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88248401800506428106010955 132372602700759642159016433)
            ·
              refine ⟨99279452025569731619262325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132372602700759642159016433 99279452025569731619262325)
              ·
                refine ⟨9307448627397162339305843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99279452025569731619262325 9307448627397162339305843)
                ·
                  refine ⟨13961172941095743508958765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307448627397162339305843 13961172941095743508958765)
                  ·
                    refine ⟨5235439852910903815859537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13961172941095743508958765 5235439852910903815859537)
                    ·
                      refine ⟨3926579889683177861894653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235439852910903815859537 3926579889683177861894653)
                      ·
                        rfl

theorem cell23_7646987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 3, 2].length) (baseStart_7646987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646987 prefixEnd_7646987 := by exact prefixLift 7646987
  have htrace : WordTrace (prefixWord ++ tailWord_7646987) baseStart_7646987 baseEnd_7646987 := by
    simpa [prefixWord, tailWord_7646987, baseEnd_7646987] using wordTrace_append hprefix tailTrace_7646987
  have hstable : (prefixWord ++ tailWord_7646987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646987).length < 2 ^ (prefixWord ++ tailWord_7646987).sum := by decide
  have hdescent : baseEnd_7646987 < baseStart_7646987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646989 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7646989 : Nat := 118140960795 + 7646989 * 2 ^ 59
def prefixEnd_7646989 : Nat := 4983230072969 + 3 ^ 40 * 7646989 * 2
def baseEnd_7646989 : Nat := 3926580916644486854069645

theorem tailTrace_7646989 : CollatzResearch.WordTrace tailWord_7646989 prefixEnd_7646989 3926580916644486854069645 := by
  unfold tailWord_7646989
  simp only [CollatzResearch.WordTrace]
  refine ⟨278908602093272329590200021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185939068062181553060133347 278908602093272329590200021)
  ·
    refine ⟨6536920361561070224770313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 278908602093272329590200021 6536920361561070224770313)
    ·
      refine ⟨4902690271170802668577735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6536920361561070224770313 4902690271170802668577735)
      ·
        refine ⟨7354035406756204002866603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902690271170802668577735 7354035406756204002866603)
        ·
          refine ⟨11031053110134306004299905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354035406756204002866603 11031053110134306004299905)
          ·
            refine ⟨8273289832600729503224929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11031053110134306004299905 8273289832600729503224929)
            ·
              refine ⟨6204967374450547127418697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273289832600729503224929 6204967374450547127418697)
              ·
                refine ⟨4653725530837910345564023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204967374450547127418697 4653725530837910345564023)
                ·
                  refine ⟨6980588296256865518346035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653725530837910345564023 6980588296256865518346035)
                  ·
                    refine ⟨10470882444385298277519053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6980588296256865518346035 10470882444385298277519053)
                    ·
                      refine ⟨3926580916644486854069645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470882444385298277519053 3926580916644486854069645)
                      ·
                        rfl

theorem cell23_7646989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7646989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646989 prefixEnd_7646989 := by exact prefixLift 7646989
  have htrace : WordTrace (prefixWord ++ tailWord_7646989) baseStart_7646989 baseEnd_7646989 := by
    simpa [prefixWord, tailWord_7646989, baseEnd_7646989] using wordTrace_append hprefix tailTrace_7646989
  have hstable : (prefixWord ++ tailWord_7646989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646989).length < 2 ^ (prefixWord ++ tailWord_7646989).sum := by decide
  have hdescent : baseEnd_7646989 < baseStart_7646989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646993 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_7646993 : Nat := 118140960795 + 7646993 * 2 ^ 59
def prefixEnd_7646993 : Nat := 4983230072969 + 3 ^ 40 * 7646993 * 2
def baseEnd_7646993 : Nat := 1308860990189034946139875

theorem tailTrace_7646993 : CollatzResearch.WordTrace tailWord_7646993 prefixEnd_7646993 1308860990189034946139875 := by
  unfold tailWord_7646993
  simp only [CollatzResearch.WordTrace]
  refine ⟨278908747985257838273345633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185939165323505225515563755 278908747985257838273345633)
  ·
    refine ⟨209181560988943378705009225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278908747985257838273345633 209181560988943378705009225)
    ·
      refine ⟨156886170741707534028756919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209181560988943378705009225 156886170741707534028756919)
      ·
        refine ⟨235329256112561301043135379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156886170741707534028756919 235329256112561301043135379)
        ·
          refine ⟨352993884168841951564703069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235329256112561301043135379 352993884168841951564703069)
          ·
            refine ⟨132372706563315731836763651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352993884168841951564703069 132372706563315731836763651)
            ·
              refine ⟨198559059844973597755145477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132372706563315731836763651 198559059844973597755145477)
              ·
                refine ⟨37229823720932549579089777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198559059844973597755145477 37229823720932549579089777)
                ·
                  refine ⟨27922367790699412184317333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37229823720932549579089777 27922367790699412184317333)
                  ·
                    refine ⟨1308860990189034946139875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27922367790699412184317333 1308860990189034946139875)
                    ·
                      rfl

theorem cell23_7646993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_7646993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646993 prefixEnd_7646993 := by exact prefixLift 7646993
  have htrace : WordTrace (prefixWord ++ tailWord_7646993) baseStart_7646993 baseEnd_7646993 := by
    simpa [prefixWord, tailWord_7646993, baseEnd_7646993] using wordTrace_append hprefix tailTrace_7646993
  have hstable : (prefixWord ++ tailWord_7646993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646993).length < 2 ^ (prefixWord ++ tailWord_7646993).sum := by decide
  have hdescent : baseEnd_7646993 < baseStart_7646993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647010 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7647010 : Nat := 118140960795 + 7647010 * 2 ^ 59
def prefixEnd_7647010 : Nat := 4983230072969 + 3 ^ 40 * 7647010 * 2
def baseEnd_7647010 : Nat := 1308863899912743757302349

theorem tailTrace_7647010 : CollatzResearch.WordTrace tailWord_7647010 prefixEnd_7647010 1308863899912743757302349 := by
  unfold tailWord_7647010
  simp only [CollatzResearch.WordTrace]
  refine ⟨69727342006549062544178621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185939578684130833451142989 69727342006549062544178621)
  ·
    refine ⟨26147753252455898454066983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69727342006549062544178621 26147753252455898454066983)
    ·
      refine ⟨39221629878683847681100475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26147753252455898454066983 39221629878683847681100475)
      ·
        refine ⟨58832444818025771521650713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39221629878683847681100475 58832444818025771521650713)
        ·
          refine ⟨44124333613519328641238035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58832444818025771521650713 44124333613519328641238035)
          ·
            refine ⟨66186500420278992961857053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44124333613519328641238035 66186500420278992961857053)
            ·
              refine ⟨24819937657604622360696395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66186500420278992961857053 24819937657604622360696395)
              ·
                refine ⟨37229906486406933541044593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24819937657604622360696395 37229906486406933541044593)
                ·
                  refine ⟨27922429864805200155783445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37229906486406933541044593 27922429864805200155783445)
                  ·
                    refine ⟨1308863899912743757302349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27922429864805200155783445 1308863899912743757302349)
                    ·
                      rfl

theorem cell23_7647010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7647010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647010 prefixEnd_7647010 := by exact prefixLift 7647010
  have htrace : WordTrace (prefixWord ++ tailWord_7647010) baseStart_7647010 baseEnd_7647010 := by
    simpa [prefixWord, tailWord_7647010, baseEnd_7647010] using wordTrace_append hprefix tailTrace_7647010
  have hstable : (prefixWord ++ tailWord_7647010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647010).length < 2 ^ (prefixWord ++ tailWord_7647010).sum := by decide
  have hdescent : baseEnd_7647010 < baseStart_7647010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647023 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 7]
def baseStart_7647023 : Nat := 118140960795 + 7647023 * 2 ^ 59
def prefixEnd_7647023 : Nat := 4983230072969 + 3 ^ 40 * 7647023 * 2
def baseEnd_7647023 : Nat := 436288708331859969004943

theorem tailTrace_7647023 : CollatzResearch.WordTrace tailWord_7647023 prefixEnd_7647023 436288708331859969004943 := by
  unfold tailWord_7647023
  simp only [CollatzResearch.WordTrace]
  refine ⟨278909842175149153396937723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185939894783432768931291815 278909842175149153396937723)
  ·
    refine ⟨418364763262723730095406585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278909842175149153396937723 418364763262723730095406585)
    ·
      refine ⟨313773572447042797571554939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418364763262723730095406585 313773572447042797571554939)
      ·
        refine ⟨470660358670564196357332409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313773572447042797571554939 470660358670564196357332409)
        ·
          refine ⟨352995269002923147267999307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470660358670564196357332409 352995269002923147267999307)
          ·
            refine ⟨529492903504384720901998961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352995269002923147267999307 529492903504384720901998961)
            ·
              refine ⟨397119677628288540676499221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529492903504384720901998961 397119677628288540676499221)
              ·
                refine ⟨18614984888826025344210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397119677628288540676499221 18614984888826025344210901)
                ·
                  refine ⟨436288708331859969004943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18614984888826025344210901 436288708331859969004943)
                  ·
                    rfl

theorem cell23_7647023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 7].length) (baseStart_7647023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647023 prefixEnd_7647023 := by exact prefixLift 7647023
  have htrace : WordTrace (prefixWord ++ tailWord_7647023) baseStart_7647023 baseEnd_7647023 := by
    simpa [prefixWord, tailWord_7647023, baseEnd_7647023] using wordTrace_append hprefix tailTrace_7647023
  have hstable : (prefixWord ++ tailWord_7647023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647023).length < 2 ^ (prefixWord ++ tailWord_7647023).sum := by decide
  have hdescent : baseEnd_7647023 < baseStart_7647023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647038 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_7647038 : Nat := 118140960795 + 7647038 * 2 ^ 59
def prefixEnd_7647038 : Nat := 4983230072969 + 3 ^ 40 * 7647038 * 2
def baseEnd_7647038 : Nat := 3926606077196557162356919

theorem tailTrace_7647038 : CollatzResearch.WordTrace tailWord_7647038 prefixEnd_7647038 3926606077196557162356919 := by
  unfold tailWord_7647038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34863798658761851369841721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185940259513396540639155845 34863798658761851369841721)
  ·
    refine ⟨26147848994071388527381291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34863798658761851369841721 26147848994071388527381291)
    ·
      refine ⟨39221773491107082791071937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26147848994071388527381291 39221773491107082791071937)
      ·
        refine ⟨29416330118330312093303953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39221773491107082791071937 29416330118330312093303953)
        ·
          refine ⟨22062247588747734069977965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29416330118330312093303953 22062247588747734069977965)
          ·
            refine ⟨8273342845780400276241737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22062247588747734069977965 8273342845780400276241737)
            ·
              refine ⟨6205007134335300207181303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273342845780400276241737 6205007134335300207181303)
              ·
                refine ⟨9307510701502950310771955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205007134335300207181303 9307510701502950310771955)
                ·
                  refine ⟨13961266052254425466157933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307510701502950310771955 13961266052254425466157933)
                  ·
                    refine ⟨5235474769595409549809225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13961266052254425466157933 5235474769595409549809225)
                    ·
                      refine ⟨3926606077196557162356919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235474769595409549809225 3926606077196557162356919)
                      ·
                        rfl

theorem cell23_7647038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_7647038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647038 prefixEnd_7647038 := by exact prefixLift 7647038
  have htrace : WordTrace (prefixWord ++ tailWord_7647038) baseStart_7647038 baseEnd_7647038 := by
    simpa [prefixWord, tailWord_7647038, baseEnd_7647038] using wordTrace_append hprefix tailTrace_7647038
  have hstable : (prefixWord ++ tailWord_7647038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647038).length < 2 ^ (prefixWord ++ tailWord_7647038).sum := by decide
  have hdescent : baseEnd_7647038 < baseStart_7647038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647050 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_7647050 : Nat := 118140960795 + 7647050 * 2 ^ 59
def prefixEnd_7647050 : Nat := 4983230072969 + 3 ^ 40 * 7647050 * 2
def baseEnd_7647050 : Nat := 3926612238964411115406863

theorem tailTrace_7647050 : CollatzResearch.WordTrace tailWord_7647050 prefixEnd_7647050 3926612238964411115406863 := by
  unfold tailWord_7647050
  simp only [CollatzResearch.WordTrace]
  refine ⟨69727706736512834252042651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185940551297367558005447069 69727706736512834252042651)
  ·
    refine ⟨104591560104769251378063977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69727706736512834252042651 104591560104769251378063977)
    ·
      refine ⟨78443670078576938533547983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104591560104769251378063977 78443670078576938533547983)
      ·
        refine ⟨117665505117865407800321975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78443670078576938533547983 117665505117865407800321975)
        ·
          refine ⟨176498257676798111700482963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117665505117865407800321975 176498257676798111700482963)
          ·
            refine ⟨264747386515197167550724445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176498257676798111700482963 264747386515197167550724445)
            ·
              refine ⟨99280269943198937831521667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264747386515197167550724445 99280269943198937831521667)
              ·
                refine ⟨148920404914798406747282501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99280269943198937831521667 148920404914798406747282501)
                ·
                  refine ⟨27922575921524701265115469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148920404914798406747282501 27922575921524701265115469)
                  ·
                    refine ⟨10470965970571762974418301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27922575921524701265115469 10470965970571762974418301)
                    ·
                      refine ⟨3926612238964411115406863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470965970571762974418301 3926612238964411115406863)
                      ·
                        rfl

theorem cell23_7647050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_7647050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647050 prefixEnd_7647050 := by exact prefixLift 7647050
  have htrace : WordTrace (prefixWord ++ tailWord_7647050) baseStart_7647050 baseEnd_7647050 := by
    simpa [prefixWord, tailWord_7647050, baseEnd_7647050] using wordTrace_append hprefix tailTrace_7647050
  have hstable : (prefixWord ++ tailWord_7647050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647050).length < 2 ^ (prefixWord ++ tailWord_7647050).sum := by decide
  have hdescent : baseEnd_7647050 < baseStart_7647050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647057 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 5]
def baseStart_7647057 : Nat := 118140960795 + 7647057 * 2 ^ 59
def prefixEnd_7647057 : Nat := 4983230072969 + 3 ^ 40 * 7647057 * 2
def baseEnd_7647057 : Nat := 436290648147665843113259

theorem tailTrace_7647057 : CollatzResearch.WordTrace tailWord_7647057 prefixEnd_7647057 436290648147665843113259 := by
  unfold tailWord_7647057
  simp only [CollatzResearch.WordTrace]
  refine ⟨278911082257025977203675425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185940721504683984802450283 278911082257025977203675425)
  ·
    refine ⟨209183311692769482902756569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278911082257025977203675425 209183311692769482902756569)
    ·
      refine ⟨156887483769577112177067427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209183311692769482902756569 156887483769577112177067427)
      ·
        refine ⟨235331225654365668265601141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156887483769577112177067427 235331225654365668265601141)
        ·
          refine ⟨22062302405096781399900107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235331225654365668265601141 22062302405096781399900107)
          ·
            refine ⟨33093453607645172099850161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22062302405096781399900107 33093453607645172099850161)
            ·
              refine ⟨24820090205733879074887621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33093453607645172099850161 24820090205733879074887621)
              ·
                refine ⟨4653766913575102326541429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24820090205733879074887621 4653766913575102326541429)
                ·
                  refine ⟨436290648147665843113259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4653766913575102326541429 436290648147665843113259)
                  ·
                    rfl

theorem cell23_7647057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 5].length) (baseStart_7647057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647057 prefixEnd_7647057 := by exact prefixLift 7647057
  have htrace : WordTrace (prefixWord ++ tailWord_7647057) baseStart_7647057 baseEnd_7647057 := by
    simpa [prefixWord, tailWord_7647057, baseEnd_7647057] using wordTrace_append hprefix tailTrace_7647057
  have hstable : (prefixWord ++ tailWord_7647057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647057).length < 2 ^ (prefixWord ++ tailWord_7647057).sum := by decide
  have hdescent : baseEnd_7647057 < baseStart_7647057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647068 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7647068 : Nat := 118140960795 + 7647068 * 2 ^ 59
def prefixEnd_7647068 : Nat := 4983230072969 + 3 ^ 40 * 7647068 * 2
def baseEnd_7647068 : Nat := 3926621481616192044981781

theorem tailTrace_7647068 : CollatzResearch.WordTrace tailWord_7647068 prefixEnd_7647068 3926621481616192044981781 := by
  unfold tailWord_7647068
  simp only [CollatzResearch.WordTrace]
  refine ⟨139455741729993063041162929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185940988973324084054883905 139455741729993063041162929)
  ·
    refine ⟨104591806297494797280872197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139455741729993063041162929 104591806297494797280872197)
    ·
      refine ⟨19610963680780274490163537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104591806297494797280872197 19610963680780274490163537)
      ·
        refine ⟨14708222760585205867622653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19610963680780274490163537 14708222760585205867622653)
        ·
          refine ⟨5515583535219452200358495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14708222760585205867622653 5515583535219452200358495)
          ·
            refine ⟨8273375302829178300537743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515583535219452200358495 8273375302829178300537743)
            ·
              refine ⟨12410062954243767450806615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8273375302829178300537743 12410062954243767450806615)
              ·
                refine ⟨18615094431365651176209923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12410062954243767450806615 18615094431365651176209923)
                ·
                  refine ⟨27922641647048476764314885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18615094431365651176209923 27922641647048476764314885)
                  ·
                    refine ⟨5235495308821589393309041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27922641647048476764314885 5235495308821589393309041)
                    ·
                      refine ⟨3926621481616192044981781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235495308821589393309041 3926621481616192044981781)
                      ·
                        rfl

theorem cell23_7647068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7647068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647068 prefixEnd_7647068 := by exact prefixLift 7647068
  have htrace : WordTrace (prefixWord ++ tailWord_7647068) baseStart_7647068 baseEnd_7647068 := by
    simpa [prefixWord, tailWord_7647068, baseEnd_7647068] using wordTrace_append hprefix tailTrace_7647068
  have hstable : (prefixWord ++ tailWord_7647068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647068).length < 2 ^ (prefixWord ++ tailWord_7647068).sum := by decide
  have hdescent : baseEnd_7647068 < baseStart_7647068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647083 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 10]
def baseStart_7647083 : Nat := 118140960795 + 7647083 * 2 ^ 59
def prefixEnd_7647083 : Nat := 4983230072969 + 3 ^ 40 * 7647083 * 2
def baseEnd_7647083 : Nat := 1308876394608669828764737

theorem tailTrace_7647083 : CollatzResearch.WordTrace tailWord_7647083 prefixEnd_7647083 1308876394608669828764737 := by
  unfold tailWord_7647083
  simp only [CollatzResearch.WordTrace]
  refine ⟨278912030554931783644121903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185941353703287855762747935 278912030554931783644121903)
  ·
    refine ⟨418368045832397675466182855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278912030554931783644121903 418368045832397675466182855)
    ·
      refine ⟨627552068748596513199274283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418368045832397675466182855 627552068748596513199274283)
      ·
        refine ⟨941328103122894769798911425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627552068748596513199274283 941328103122894769798911425)
        ·
          refine ⟨705996077342171077349183569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941328103122894769798911425 705996077342171077349183569)
          ·
            refine ⟨529497058006628308011887677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705996077342171077349183569 529497058006628308011887677)
            ·
              refine ⟨198561396752485615504457879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529497058006628308011887677 198561396752485615504457879)
              ·
                refine ⟨297842095128728423256686819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198561396752485615504457879 297842095128728423256686819)
                ·
                  refine ⟨446763142693092634885030229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297842095128728423256686819 446763142693092634885030229)
                  ·
                    refine ⟨1308876394608669828764737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 446763142693092634885030229 1308876394608669828764737)
                    ·
                      rfl

theorem cell23_7647083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_7647083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647083 prefixEnd_7647083 := by exact prefixLift 7647083
  have htrace : WordTrace (prefixWord ++ tailWord_7647083) baseStart_7647083 baseEnd_7647083 := by
    simpa [prefixWord, tailWord_7647083, baseEnd_7647083] using wordTrace_append hprefix tailTrace_7647083
  have hstable : (prefixWord ++ tailWord_7647083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647083).length < 2 ^ (prefixWord ++ tailWord_7647083).sum := by decide
  have hdescent : baseEnd_7647083 < baseStart_7647083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647107 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4]
def baseStart_7647107 : Nat := 118140960795 + 7647107 * 2 ^ 59
def prefixEnd_7647107 : Nat := 4983230072969 + 3 ^ 40 * 7647107 * 2
def baseEnd_7647107 : Nat := 3926641507361717392394101

theorem tailTrace_7647107 : CollatzResearch.WordTrace tailWord_7647107 prefixEnd_7647107 3926641507361717392394101 := by
  unfold tailWord_7647107
  simp only [CollatzResearch.WordTrace]
  refine ⟨278912905906844835742995575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185941937271229890495330383 278912905906844835742995575)
  ·
    refine ⟨418369358860267253614493363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278912905906844835742995575 418369358860267253614493363)
    ·
      refine ⟨627554038290400880421740045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418369358860267253614493363 627554038290400880421740045)
      ·
        refine ⟨235332764358900330158152517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627554038290400880421740045 235332764358900330158152517)
        ·
          refine ⟨44124893317293811904653597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235332764358900330158152517 44124893317293811904653597)
          ·
            refine ⟨16546834993985179464245099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44124893317293811904653597 16546834993985179464245099)
            ·
              refine ⟨24820252490977769196367649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16546834993985179464245099 24820252490977769196367649)
              ·
                refine ⟨18615189368233326897275737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24820252490977769196367649 18615189368233326897275737)
                ·
                  refine ⟨13961392026174995172956803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18615189368233326897275737 13961392026174995172956803)
                  ·
                    refine ⟨20942088039262492759435205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13961392026174995172956803 20942088039262492759435205)
                    ·
                      refine ⟨3926641507361717392394101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20942088039262492759435205 3926641507361717392394101)
                      ·
                        rfl

theorem cell23_7647107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_7647107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647107 prefixEnd_7647107 := by exact prefixLift 7647107
  have htrace : WordTrace (prefixWord ++ tailWord_7647107) baseStart_7647107 baseEnd_7647107 := by
    simpa [prefixWord, tailWord_7647107, baseEnd_7647107] using wordTrace_append hprefix tailTrace_7647107
  have hstable : (prefixWord ++ tailWord_7647107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647107).length < 2 ^ (prefixWord ++ tailWord_7647107).sum := by decide
  have hdescent : baseEnd_7647107 < baseStart_7647107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647224 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_7647224 : Nat := 118140960795 + 7647224 * 2 ^ 59
def prefixEnd_7647224 : Nat := 4983230072969 + 3 ^ 40 * 7647224 * 2
def baseEnd_7647224 : Nat := 1308900528199431144877021

theorem tailTrace_7647224 : CollatzResearch.WordTrace tailWord_7647224 prefixEnd_7647224 1308900528199431144877021 := by
  unfold tailWord_7647224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139458586623710482362502363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185944782164947309816669817 139458586623710482362502363)
  ·
    refine ⟨209187879935565723543753545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139458586623710482362502363 209187879935565723543753545)
    ·
      refine ⟨156890909951674292657815159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209187879935565723543753545 156890909951674292657815159)
      ·
        refine ⟨235336364927511438986722739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156890909951674292657815159 235336364927511438986722739)
        ·
          refine ⟨353004547391267158480084109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235336364927511438986722739 353004547391267158480084109)
          ·
            refine ⟨132376705271725184430031541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353004547391267158480084109 132376705271725184430031541)
            ·
              refine ⟨12410316119224236040315457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132376705271725184430031541 12410316119224236040315457)
              ·
                refine ⟨9307737089418177030236593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12410316119224236040315457 9307737089418177030236593)
                ·
                  refine ⟨6980802817063632772677445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9307737089418177030236593 6980802817063632772677445)
                  ·
                    refine ⟨1308900528199431144877021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6980802817063632772677445 1308900528199431144877021)
                    ·
                      rfl

theorem cell23_7647224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_7647224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647224 prefixEnd_7647224 := by exact prefixLift 7647224
  have htrace : WordTrace (prefixWord ++ tailWord_7647224) baseStart_7647224 baseEnd_7647224 := by
    simpa [prefixWord, tailWord_7647224, baseEnd_7647224] using wordTrace_append hprefix tailTrace_7647224
  have hstable : (prefixWord ++ tailWord_7647224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647224).length < 2 ^ (prefixWord ++ tailWord_7647224).sum := by decide
  have hdescent : baseEnd_7647224 < baseStart_7647224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647245 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7647245 : Nat := 118140960795 + 7647245 * 2 ^ 59
def prefixEnd_7647245 : Nat := 4983230072969 + 3 ^ 40 * 7647245 * 2
def baseEnd_7647245 : Nat := 1308904122564012617489489

theorem tailTrace_7647245 : CollatzResearch.WordTrace tailWord_7647245 prefixEnd_7647245 1308904122564012617489489 := by
  unfold tailWord_7647245
  simp only [CollatzResearch.WordTrace]
  refine ⟨278917939180344885311519189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185945292786896590207679459 278917939180344885311519189)
  ·
    refine ⟨6537139199539333249488731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 278917939180344885311519189 6537139199539333249488731)
    ·
      refine ⟨9805708799308999874233097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6537139199539333249488731 9805708799308999874233097)
      ·
        refine ⟨7354281599481749905674823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805708799308999874233097 7354281599481749905674823)
        ·
          refine ⟨11031422399222624858512235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354281599481749905674823 11031422399222624858512235)
          ·
            refine ⟨16547133598833937287768353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031422399222624858512235 16547133598833937287768353)
            ·
              refine ⟨12410350199125452965826265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547133598833937287768353 12410350199125452965826265)
              ·
                refine ⟨9307762649344089724369699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12410350199125452965826265 9307762649344089724369699)
                ·
                  refine ⟨13961643974016134586554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307762649344089724369699 13961643974016134586554549)
                  ·
                    refine ⟨1308904122564012617489489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13961643974016134586554549 1308904122564012617489489)
                    ·
                      rfl

theorem cell23_7647245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7647245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647245 prefixEnd_7647245 := by exact prefixLift 7647245
  have htrace : WordTrace (prefixWord ++ tailWord_7647245) baseStart_7647245 baseEnd_7647245 := by
    simpa [prefixWord, tailWord_7647245, baseEnd_7647245] using wordTrace_append hprefix tailTrace_7647245
  have hstable : (prefixWord ++ tailWord_7647245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647245).length < 2 ^ (prefixWord ++ tailWord_7647245).sum := by decide
  have hdescent : baseEnd_7647245 < baseStart_7647245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647271 : List Nat := [1, 1, 7, 1, 3, 1, 9]
def baseStart_7647271 : Nat := 118140960795 + 7647271 * 2 ^ 59
def prefixEnd_7647271 : Nat := 4983230072969 + 3 ^ 40 * 7647271 * 2
def baseEnd_7647271 : Nat := 48478095286284626552387

theorem tailTrace_7647271 : CollatzResearch.WordTrace tailWord_7647271 prefixEnd_7647271 48478095286284626552387 := by
  unfold tailWord_7647271
  simp only [CollatzResearch.WordTrace]
  refine ⟨278918887478250691751965667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185945924985500461167977111 278918887478250691751965667)
  ·
    refine ⟨418378331217376037627948501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278918887478250691751965667 418378331217376037627948501)
    ·
      refine ⟨9805742137907250881905043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 418378331217376037627948501 9805742137907250881905043)
      ·
        refine ⟨14708613206860876322857565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805742137907250881905043 14708613206860876322857565)
        ·
          refine ⟨5515729952572828621071587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14708613206860876322857565 5515729952572828621071587)
          ·
            refine ⟨8273594928859242931607381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515729952572828621071587 8273594928859242931607381)
            ·
              refine ⟨48478095286284626552387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8273594928859242931607381 48478095286284626552387)
              ·
                rfl

theorem cell23_7647271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 9].length) (baseStart_7647271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647271 prefixEnd_7647271 := by exact prefixLift 7647271
  have htrace : WordTrace (prefixWord ++ tailWord_7647271) baseStart_7647271 baseEnd_7647271 := by
    simpa [prefixWord, tailWord_7647271, baseEnd_7647271] using wordTrace_append hprefix tailTrace_7647271
  have hstable : (prefixWord ++ tailWord_7647271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647271).length < 2 ^ (prefixWord ++ tailWord_7647271).sum := by decide
  have hdescent : baseEnd_7647271 < baseStart_7647271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647307 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3]
def baseStart_7647307 : Nat := 118140960795 + 7647307 * 2 ^ 59
def prefixEnd_7647307 : Nat := 4983230072969 + 3 ^ 40 * 7647307 * 2
def baseEnd_7647307 : Nat := 3926744203492616609893181

theorem tailTrace_7647307 : CollatzResearch.WordTrace tailWord_7647307 prefixEnd_7647307 3926744203492616609893181 := by
  unfold tailWord_7647307
  simp only [CollatzResearch.WordTrace]
  refine ⟨278920200506120269900276175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185946800337413513266850783 278920200506120269900276175)
  ·
    refine ⟨418380300759180404850414263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278920200506120269900276175 418380300759180404850414263)
    ·
      refine ⟨627570451138770607275621395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418380300759180404850414263 627570451138770607275621395)
      ·
        refine ⟨941355676708155910913432093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627570451138770607275621395 941355676708155910913432093)
        ·
          refine ⟨353008378765558466592537035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941355676708155910913432093 353008378765558466592537035)
          ·
            refine ⟨529512568148337699888805553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353008378765558466592537035 529512568148337699888805553)
            ·
              refine ⟨397134426111253274916604165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529512568148337699888805553 397134426111253274916604165)
              ·
                refine ⟨74462704895859989046863281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397134426111253274916604165 74462704895859989046863281)
                ·
                  refine ⟨55847028671894991785147461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74462704895859989046863281 55847028671894991785147461)
                  ·
                    refine ⟨10471317875980310959715149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55847028671894991785147461 10471317875980310959715149)
                    ·
                      refine ⟨3926744203492616609893181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471317875980310959715149 3926744203492616609893181)
                      ·
                        rfl

theorem cell23_7647307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3].length) (baseStart_7647307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647307 prefixEnd_7647307 := by exact prefixLift 7647307
  have htrace : WordTrace (prefixWord ++ tailWord_7647307) baseStart_7647307 baseEnd_7647307 := by
    simpa [prefixWord, tailWord_7647307, baseEnd_7647307] using wordTrace_append hprefix tailTrace_7647307
  have hstable : (prefixWord ++ tailWord_7647307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647307).length < 2 ^ (prefixWord ++ tailWord_7647307).sum := by decide
  have hdescent : baseEnd_7647307 < baseStart_7647307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647324 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7647324 : Nat := 118140960795 + 7647324 * 2 ^ 59
def prefixEnd_7647324 : Nat := 4983230072969 + 3 ^ 40 * 7647324 * 2
def baseEnd_7647324 : Nat := 3926752932663743043380603

theorem tailTrace_7647324 : CollatzResearch.WordTrace tailWord_7647324 prefixEnd_7647324 3926752932663743043380603 := by
  unfold tailWord_7647324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139460410273529340901822513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185947213698039121202430017 139460410273529340901822513)
  ·
    refine ⟨104595307705147005676366885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139460410273529340901822513 104595307705147005676366885)
    ·
      refine ⟨19611620194715063564318791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104595307705147005676366885 19611620194715063564318791)
      ·
        refine ⟨29417430292072595346478187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19611620194715063564318791 29417430292072595346478187)
        ·
          refine ⟨44126145438108893019717281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29417430292072595346478187 44126145438108893019717281)
          ·
            refine ⟨33094609078581669764787961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44126145438108893019717281 33094609078581669764787961)
            ·
              refine ⟨24820956808936252323590971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33094609078581669764787961 24820956808936252323590971)
              ·
                refine ⟨37231435213404378485386457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24820956808936252323590971 37231435213404378485386457)
                ·
                  refine ⟨27923576410053283864039843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37231435213404378485386457 27923576410053283864039843)
                  ·
                    refine ⟨41885364615079925796059765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27923576410053283864039843 41885364615079925796059765)
                    ·
                      refine ⟨3926752932663743043380603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41885364615079925796059765 3926752932663743043380603)
                      ·
                        rfl

theorem cell23_7647324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7647324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647324 prefixEnd_7647324 := by exact prefixLift 7647324
  have htrace : WordTrace (prefixWord ++ tailWord_7647324) baseStart_7647324 baseEnd_7647324 := by
    simpa [prefixWord, tailWord_7647324, baseEnd_7647324] using wordTrace_append hprefix tailTrace_7647324
  have hstable : (prefixWord ++ tailWord_7647324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647324).length < 2 ^ (prefixWord ++ tailWord_7647324).sum := by decide
  have hdescent : baseEnd_7647324 < baseStart_7647324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647367 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_7647367 : Nat := 118140960795 + 7647367 * 2 ^ 59
def prefixEnd_7647367 : Nat := 4983230072969 + 3 ^ 40 * 7647367 * 2
def baseEnd_7647367 : Nat := 3926775012331886375142905

theorem tailTrace_7647367 : CollatzResearch.WordTrace tailWord_7647367 prefixEnd_7647367 3926775012331886375142905 := by
  unfold tailWord_7647367
  simp only [CollatzResearch.WordTrace]
  refine ⟨278922388885902900147460355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185948259257268600098306903 278922388885902900147460355)
  ·
    refine ⟨418383583328854350221190533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278922388885902900147460355 418383583328854350221190533)
    ·
      refine ⟨78446921874160190666473225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418383583328854350221190533 78446921874160190666473225)
      ·
        refine ⟨58835191405620142999854919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78446921874160190666473225 58835191405620142999854919)
        ·
          refine ⟨88252787108430214499782379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58835191405620142999854919 88252787108430214499782379)
          ·
            refine ⟨132379180662645321749673569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88252787108430214499782379 132379180662645321749673569)
            ·
              refine ⟨99284385496983991312255177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132379180662645321749673569 99284385496983991312255177)
              ·
                refine ⟨74463289122737993484191383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99284385496983991312255177 74463289122737993484191383)
                ·
                  refine ⟨111694933684106990226287075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74463289122737993484191383 111694933684106990226287075)
                  ·
                    refine ⟨167542400526160485339430613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111694933684106990226287075 167542400526160485339430613)
                    ·
                      refine ⟨3926775012331886375142905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167542400526160485339430613 3926775012331886375142905)
                      ·
                        rfl

theorem cell23_7647367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_7647367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647367 prefixEnd_7647367 := by exact prefixLift 7647367
  have htrace : WordTrace (prefixWord ++ tailWord_7647367) baseStart_7647367 baseEnd_7647367 := by
    simpa [prefixWord, tailWord_7647367, baseEnd_7647367] using wordTrace_append hprefix tailTrace_7647367
  have hstable : (prefixWord ++ tailWord_7647367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647367).length < 2 ^ (prefixWord ++ tailWord_7647367).sum := by decide
  have hdescent : baseEnd_7647367 < baseStart_7647367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647407 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_7647407 : Nat := 118140960795 + 7647407 * 2 ^ 59
def prefixEnd_7647407 : Nat := 4983230072969 + 3 ^ 40 * 7647407 * 2
def baseEnd_7647407 : Nat := 3926795551558066218642721

theorem tailTrace_7647407 : CollatzResearch.WordTrace tailWord_7647407 prefixEnd_7647407 3926795551558066218642721 := by
  unfold tailWord_7647407
  simp only [CollatzResearch.WordTrace]
  refine ⟨278923847805757986978916475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185949231870505324652610983 278923847805757986978916475)
  ·
    refine ⟨418385771708636980468374713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278923847805757986978916475 418385771708636980468374713)
    ·
      refine ⟨313789328781477735351281035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418385771708636980468374713 313789328781477735351281035)
      ·
        refine ⟨470683993172216603026921553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313789328781477735351281035 470683993172216603026921553)
        ·
          refine ⟨353012994879162452270191165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470683993172216603026921553 353012994879162452270191165)
          ·
            refine ⟨132379873079685919601321687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353012994879162452270191165 132379873079685919601321687)
            ·
              refine ⟨198569809619528879401982531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132379873079685919601321687 198569809619528879401982531)
              ·
                refine ⟨297854714429293319102973797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198569809619528879401982531 297854714429293319102973797)
                ·
                  refine ⟨55847758955492497331807587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297854714429293319102973797 55847758955492497331807587)
                  ·
                    refine ⟨83771638433238745997711381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55847758955492497331807587 83771638433238745997711381)
                    ·
                      refine ⟨3926795551558066218642721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83771638433238745997711381 3926795551558066218642721)
                      ·
                        rfl

theorem cell23_7647407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_7647407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647407 prefixEnd_7647407 := by exact prefixLift 7647407
  have htrace : WordTrace (prefixWord ++ tailWord_7647407) baseStart_7647407 baseEnd_7647407 := by
    simpa [prefixWord, tailWord_7647407, baseEnd_7647407] using wordTrace_append hprefix tailTrace_7647407
  have hstable : (prefixWord ++ tailWord_7647407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647407).length < 2 ^ (prefixWord ++ tailWord_7647407).sum := by decide
  have hdescent : baseEnd_7647407 < baseStart_7647407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647478 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7647478 : Nat := 118140960795 + 7647478 * 2 ^ 59
def prefixEnd_7647478 : Nat := 4983230072969 + 3 ^ 40 * 7647478 * 2
def baseEnd_7647478 : Nat := 3926832008684535440854895

theorem tailTrace_7647478 : CollatzResearch.WordTrace tailWord_7647478 prefixEnd_7647478 3926832008684535440854895 := by
  unfold tailWord_7647478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432902336781297881546943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185950958259000510736500725 17432902336781297881546943)
  ·
    refine ⟨26149353505171946822320415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17432902336781297881546943 26149353505171946822320415)
    ·
      refine ⟨39224030257757920233480623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26149353505171946822320415 39224030257757920233480623)
      ·
        refine ⟨58836045386636880350220935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39224030257757920233480623 58836045386636880350220935)
        ·
          refine ⟨88254068079955320525331403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58836045386636880350220935 88254068079955320525331403)
          ·
            refine ⟨132381102119932980787997105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88254068079955320525331403 132381102119932980787997105)
            ·
              refine ⟨99285826589949735590997829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132381102119932980787997105 99285826589949735590997829)
              ·
                refine ⟨18616092485615575423312093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99285826589949735590997829 18616092485615575423312093)
                ·
                  refine ⟨6981034682105840783742035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18616092485615575423312093 6981034682105840783742035)
                  ·
                    refine ⟨10471552023158761175613053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981034682105840783742035 10471552023158761175613053)
                    ·
                      refine ⟨3926832008684535440854895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471552023158761175613053 3926832008684535440854895)
                      ·
                        rfl

theorem cell23_7647478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7647478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647478 prefixEnd_7647478 := by exact prefixLift 7647478
  have htrace : WordTrace (prefixWord ++ tailWord_7647478) baseStart_7647478 baseEnd_7647478 := by
    simpa [prefixWord, tailWord_7647478, baseEnd_7647478] using wordTrace_append hprefix tailTrace_7647478
  have hstable : (prefixWord ++ tailWord_7647478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647478).length < 2 ^ (prefixWord ++ tailWord_7647478).sum := by decide
  have hdescent : baseEnd_7647478 < baseStart_7647478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647521 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7647521 : Nat := 118140960795 + 7647521 * 2 ^ 59
def prefixEnd_7647521 : Nat := 4983230072969 + 3 ^ 40 * 7647521 * 2
def baseEnd_7647521 : Nat := 3926854088352678772617197

theorem tailTrace_7647521 : CollatzResearch.WordTrace tailWord_7647521 prefixEnd_7647521 3926854088352678772617197 := by
  unfold tailWord_7647521
  simp only [CollatzResearch.WordTrace]
  refine ⟨278928005727344984448566417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185952003818229989632377611 278928005727344984448566417)
  ·
    refine ⟨209196004295508738336424813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278928005727344984448566417 209196004295508738336424813)
    ·
      refine ⟨78448501610815776876159305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209196004295508738336424813 78448501610815776876159305)
      ·
        refine ⟨58836376208111832657119479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78448501610815776876159305 58836376208111832657119479)
        ·
          refine ⟨88254564312167748985679219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58836376208111832657119479 88254564312167748985679219)
          ·
            refine ⟨132381846468251623478518829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88254564312167748985679219 132381846468251623478518829)
            ·
              refine ⟨49643192425594358804444561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132381846468251623478518829 49643192425594358804444561)
              ·
                refine ⟨37232394319195769103333421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49643192425594358804444561 37232394319195769103333421)
                ·
                  refine ⟨13962147869698413413750033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37232394319195769103333421 13962147869698413413750033)
                  ·
                    refine ⟨10471610902273810060312525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13962147869698413413750033 10471610902273810060312525)
                    ·
                      refine ⟨3926854088352678772617197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471610902273810060312525 3926854088352678772617197)
                      ·
                        rfl

theorem cell23_7647521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7647521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647521 prefixEnd_7647521 := by exact prefixLift 7647521
  have htrace : WordTrace (prefixWord ++ tailWord_7647521) baseStart_7647521 baseEnd_7647521 := by
    simpa [prefixWord, tailWord_7647521, baseEnd_7647521] using wordTrace_append hprefix tailTrace_7647521
  have hstable : (prefixWord ++ tailWord_7647521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647521).length < 2 ^ (prefixWord ++ tailWord_7647521).sum := by decide
  have hdescent : baseEnd_7647521 < baseStart_7647521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647528 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7647528 : Nat := 118140960795 + 7647528 * 2 ^ 59
def prefixEnd_7647528 : Nat := 4983230072969 + 3 ^ 40 * 7647528 * 2
def baseEnd_7647528 : Nat := 1308952560905753415076555

theorem tailTrace_7647528 : CollatzResearch.WordTrace tailWord_7647528 prefixEnd_7647528 1308952560905753415076555 := by
  unfold tailWord_7647528
  simp only [CollatzResearch.WordTrace]
  refine ⟨139464130519159812322035619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185952174025546416429380825 139464130519159812322035619)
  ·
    refine ⟨209196195778739718483053429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139464130519159812322035619 209196195778739718483053429)
    ·
      refine ⟨19612143354256848607786259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209196195778739718483053429 19612143354256848607786259)
      ·
        refine ⟨29418215031385272911679389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19612143354256848607786259 29418215031385272911679389)
        ·
          refine ⟨11031830636769477341879771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29418215031385272911679389 11031830636769477341879771)
          ·
            refine ⟨16547745955154216012819657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031830636769477341879771 16547745955154216012819657)
            ·
              refine ⟨12410809466365662009614743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547745955154216012819657 12410809466365662009614743)
              ·
                refine ⟨18616214199548493014422115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12410809466365662009614743 18616214199548493014422115)
                ·
                  refine ⟨27924321299322739521633173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18616214199548493014422115 27924321299322739521633173)
                  ·
                    refine ⟨1308952560905753415076555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27924321299322739521633173 1308952560905753415076555)
                    ·
                      rfl

theorem cell23_7647528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7647528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647528 prefixEnd_7647528 := by exact prefixLift 7647528
  have htrace : WordTrace (prefixWord ++ tailWord_7647528) baseStart_7647528 baseEnd_7647528 := by
    simpa [prefixWord, tailWord_7647528, baseEnd_7647528] using wordTrace_append hprefix tailTrace_7647528
  have hstable : (prefixWord ++ tailWord_7647528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647528).length < 2 ^ (prefixWord ++ tailWord_7647528).sum := by decide
  have hdescent : baseEnd_7647528 < baseStart_7647528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647541 : List Nat := [1, 3, 3, 1, 2, 1, 5, 7]
def baseStart_7647541 : Nat := 118140960795 + 7647541 * 2 ^ 59
def prefixEnd_7647541 : Nat := 4983230072969 + 3 ^ 40 * 7647541 * 2
def baseEnd_7647541 : Nat := 145439420665398840532115

theorem tailTrace_7647541 : CollatzResearch.WordTrace tailWord_7647541 prefixEnd_7647541 145439420665398840532115 := by
  unfold tailWord_7647541
  simp only [CollatzResearch.WordTrace]
  refine ⟨278928735187272527864294477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185952490124848351909529651 278928735187272527864294477)
  ·
    refine ⟨104598275695227197949110429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278928735187272527864294477 104598275695227197949110429)
    ·
      refine ⟨39224353385710199230916411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104598275695227197949110429 39224353385710199230916411)
      ·
        refine ⟨58836530078565298846374617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39224353385710199230916411 58836530078565298846374617)
        ·
          refine ⟨44127397558923974134780963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58836530078565298846374617 44127397558923974134780963)
          ·
            refine ⟨66191096338385961202171445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44127397558923974134780963 66191096338385961202171445)
            ·
              refine ⟨6205415281723683862703573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66191096338385961202171445 6205415281723683862703573)
              ·
                refine ⟨145439420665398840532115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6205415281723683862703573 145439420665398840532115)
                ·
                  rfl

theorem cell23_7647541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 7].length) (baseStart_7647541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647541 prefixEnd_7647541 := by exact prefixLift 7647541
  have htrace : WordTrace (prefixWord ++ tailWord_7647541) baseStart_7647541 baseEnd_7647541 := by
    simpa [prefixWord, tailWord_7647541, baseEnd_7647541] using wordTrace_append hprefix tailTrace_7647541
  have hstable : (prefixWord ++ tailWord_7647541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647541).length < 2 ^ (prefixWord ++ tailWord_7647541).sum := by decide
  have hdescent : baseEnd_7647541 < baseStart_7647541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647551 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_7647551 : Nat := 118140960795 + 7647551 * 2 ^ 59
def prefixEnd_7647551 : Nat := 4983230072969 + 3 ^ 40 * 7647551 * 2
def baseEnd_7647551 : Nat := 3926869492772313655242059

theorem tailTrace_7647551 : CollatzResearch.WordTrace tailWord_7647551 prefixEnd_7647551 3926869492772313655242059 := by
  unfold tailWord_7647551
  simp only [CollatzResearch.WordTrace]
  refine ⟨278929099917236299572158507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185952733278157533048105671 278929099917236299572158507)
  ·
    refine ⟨418393649875854449358237761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278929099917236299572158507 418393649875854449358237761)
    ·
      refine ⟨313795237406890837018678321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418393649875854449358237761 313795237406890837018678321)
      ·
        refine ⟨235346428055168127764008741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313795237406890837018678321 235346428055168127764008741)
        ·
          refine ⟨44127455260344023955751639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235346428055168127764008741 44127455260344023955751639)
          ·
            refine ⟨66191182890516035933627459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44127455260344023955751639 66191182890516035933627459)
            ·
              refine ⟨99286774335774053900441189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66191182890516035933627459 99286774335774053900441189)
              ·
                refine ⟨18616270187957635106332723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99286774335774053900441189 18616270187957635106332723)
                ·
                  refine ⟨27924405281936452659499085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18616270187957635106332723 27924405281936452659499085)
                  ·
                    refine ⟨10471651980726169747312157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27924405281936452659499085 10471651980726169747312157)
                    ·
                      refine ⟨3926869492772313655242059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471651980726169747312157 3926869492772313655242059)
                      ·
                        rfl

theorem cell23_7647551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_7647551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647551 prefixEnd_7647551 := by exact prefixLift 7647551
  have htrace : WordTrace (prefixWord ++ tailWord_7647551) baseStart_7647551 baseEnd_7647551 := by
    simpa [prefixWord, tailWord_7647551, baseEnd_7647551] using wordTrace_append hprefix tailTrace_7647551
  have hstable : (prefixWord ++ tailWord_7647551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647551).length < 2 ^ (prefixWord ++ tailWord_7647551).sum := by decide
  have hdescent : baseEnd_7647551 < baseStart_7647551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647568 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3]
def baseStart_7647568 : Nat := 118140960795 + 7647568 * 2 ^ 59
def prefixEnd_7647568 : Nat := 4983230072969 + 3 ^ 40 * 7647568 * 2
def baseEnd_7647568 : Nat := 3926878221943440088729481

theorem tailTrace_7647568 : CollatzResearch.WordTrace tailWord_7647568 prefixEnd_7647568 3926878221943440088729481 := by
  unfold tailWord_7647568
  simp only [CollatzResearch.WordTrace]
  refine ⟨139464859979087355737763679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185953146638783140983684905 139464859979087355737763679)
  ·
    refine ⟨209197289968631033606645519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139464859979087355737763679 209197289968631033606645519)
    ·
      refine ⟨313795934952946550409968279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209197289968631033606645519 313795934952946550409968279)
      ·
        refine ⟨470693902429419825614952419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313795934952946550409968279 470693902429419825614952419)
        ·
          refine ⟨706040853644129738422428629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470693902429419825614952419 706040853644129738422428629)
          ·
            refine ⟨16547832507284290744275671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 706040853644129738422428629 16547832507284290744275671)
            ·
              refine ⟨24821748760926436116413507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16547832507284290744275671 24821748760926436116413507)
              ·
                refine ⟨37232623141389654174620261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24821748760926436116413507 37232623141389654174620261)
                ·
                  refine ⟨6981116839010560157741299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37232623141389654174620261 6981116839010560157741299)
                  ·
                    refine ⟨10471675258515840236611949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981116839010560157741299 10471675258515840236611949)
                    ·
                      refine ⟨3926878221943440088729481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471675258515840236611949 3926878221943440088729481)
                      ·
                        rfl

theorem cell23_7647568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_7647568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647568 prefixEnd_7647568 := by exact prefixLift 7647568
  have htrace : WordTrace (prefixWord ++ tailWord_7647568) baseStart_7647568 baseEnd_7647568 := by
    simpa [prefixWord, tailWord_7647568, baseEnd_7647568] using wordTrace_append hprefix tailTrace_7647568
  have hstable : (prefixWord ++ tailWord_7647568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647568).length < 2 ^ (prefixWord ++ tailWord_7647568).sum := by decide
  have hdescent : baseEnd_7647568 < baseStart_7647568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647611 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5]
def baseStart_7647611 : Nat := 118140960795 + 7647611 * 2 ^ 59
def prefixEnd_7647611 : Nat := 4983230072969 + 3 ^ 40 * 7647611 * 2
def baseEnd_7647611 : Nat := 3926900301611583420491783

theorem tailTrace_7647611 : CollatzResearch.WordTrace tailWord_7647611 prefixEnd_7647611 3926900301611583420491783 := by
  unfold tailWord_7647611
  simp only [CollatzResearch.WordTrace]
  refine ⟨278931288297018929819342687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185954192198012619879561791 278931288297018929819342687)
  ·
    refine ⟨418396932445528394729014031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278931288297018929819342687 418396932445528394729014031)
    ·
      refine ⟨627595398668292592093521047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418396932445528394729014031 627595398668292592093521047)
      ·
        refine ⟨941393098002438888140281571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627595398668292592093521047 941393098002438888140281571)
        ·
          refine ⟨1412089647003658332210422357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941393098002438888140281571 1412089647003658332210422357)
          ·
            refine ⟨16547925550824121080590887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1412089647003658332210422357 16547925550824121080590887)
            ·
              refine ⟨24821888326236181620886331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16547925550824121080590887 24821888326236181620886331)
              ·
                refine ⟨37232832489354272431329497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24821888326236181620886331 37232832489354272431329497)
                ·
                  refine ⟨27924624367015704323497123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37232832489354272431329497 27924624367015704323497123)
                  ·
                    refine ⟨41886936550523556485245685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27924624367015704323497123 41886936550523556485245685)
                    ·
                      refine ⟨3926900301611583420491783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41886936550523556485245685 3926900301611583420491783)
                      ·
                        rfl

theorem cell23_7647611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_7647611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647611 prefixEnd_7647611 := by exact prefixLift 7647611
  have htrace : WordTrace (prefixWord ++ tailWord_7647611) baseStart_7647611 baseEnd_7647611 := by
    simpa [prefixWord, tailWord_7647611, baseEnd_7647611] using wordTrace_append hprefix tailTrace_7647611
  have hstable : (prefixWord ++ tailWord_7647611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647611).length < 2 ^ (prefixWord ++ tailWord_7647611).sum := by decide
  have hdescent : baseEnd_7647611 < baseStart_7647611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647625 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 4, 2, 2]
def baseStart_7647625 : Nat := 118140960795 + 7647625 * 2 ^ 59
def prefixEnd_7647625 : Nat := 4983230072969 + 3 ^ 40 * 7647625 * 2
def baseEnd_7647625 : Nat := 3926907490340746365716719

theorem tailTrace_7647625 : CollatzResearch.WordTrace tailWord_7647625 prefixEnd_7647625 3926907490340746365716719 := by
  unfold tailWord_7647625
  simp only [CollatzResearch.WordTrace]
  refine ⟨278931798918968210210352329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185954532612645473473568219 278931798918968210210352329)
  ·
    refine ⟨209198849189226157657764247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278931798918968210210352329 209198849189226157657764247)
    ·
      refine ⟨313798273783839236486646371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209198849189226157657764247 313798273783839236486646371)
      ·
        refine ⟨470697410675758854729969557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313798273783839236486646371 470697410675758854729969557)
        ·
          refine ⟨22063941125426196315467323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 470697410675758854729969557 22063941125426196315467323)
          ·
            refine ⟨33095911688139294473200985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22063941125426196315467323 33095911688139294473200985)
            ·
              refine ⟨24821933766104470854900739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33095911688139294473200985 24821933766104470854900739)
              ·
                refine ⟨37232900649156706282351109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24821933766104470854900739 37232900649156706282351109)
                ·
                  refine ⟨6981168871716882427940833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37232900649156706282351109 6981168871716882427940833)
                  ·
                    refine ⟨5235876653787661820955625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6981168871716882427940833 5235876653787661820955625)
                    ·
                      refine ⟨3926907490340746365716719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235876653787661820955625 3926907490340746365716719)
                      ·
                        rfl

theorem cell23_7647625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 2, 2].length) (baseStart_7647625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647625 prefixEnd_7647625 := by exact prefixLift 7647625
  have htrace : WordTrace (prefixWord ++ tailWord_7647625) baseStart_7647625 baseEnd_7647625 := by
    simpa [prefixWord, tailWord_7647625, baseEnd_7647625] using wordTrace_append hprefix tailTrace_7647625
  have hstable : (prefixWord ++ tailWord_7647625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647625).length < 2 ^ (prefixWord ++ tailWord_7647625).sum := by decide
  have hdescent : baseEnd_7647625 < baseStart_7647625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647636 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7647636 : Nat := 118140960795 + 7647636 * 2 ^ 59
def prefixEnd_7647636 : Nat := 4983230072969 + 3 ^ 40 * 7647636 * 2
def baseEnd_7647636 : Nat := 3926913138627945822679169

theorem tailTrace_7647636 : CollatzResearch.WordTrace tailWord_7647636 prefixEnd_7647636 3926913138627945822679169 := by
  unfold tailWord_7647636
  simp only [CollatzResearch.WordTrace]
  refine ⟨139466100060964179544501381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185954800081285572726001841 139466100060964179544501381)
  ·
    refine ⟨26149893761430783664594009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139466100060964179544501381 26149893761430783664594009)
    ·
      refine ⟨19612420321073087748445507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26149893761430783664594009 19612420321073087748445507)
      ·
        refine ⟨29418630481609631622668261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19612420321073087748445507 29418630481609631622668261)
        ·
          refine ⟨5515993215301805929250299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29418630481609631622668261 5515993215301805929250299)
          ·
            refine ⟨8273989822952708893875449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515993215301805929250299 8273989822952708893875449)
            ·
              refine ⟨6205492367214531670406587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273989822952708893875449 6205492367214531670406587)
              ·
                refine ⟨9308238550821797505609881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205492367214531670406587 9308238550821797505609881)
                ·
                  refine ⟨6981178913116348129207411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9308238550821797505609881 6981178913116348129207411)
                  ·
                    refine ⟨10471768369674522193811117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981178913116348129207411 10471768369674522193811117)
                    ·
                      refine ⟨3926913138627945822679169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471768369674522193811117 3926913138627945822679169)
                      ·
                        rfl

theorem cell23_7647636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7647636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647636 prefixEnd_7647636 := by exact prefixLift 7647636
  have htrace : WordTrace (prefixWord ++ tailWord_7647636) baseStart_7647636 baseEnd_7647636 := by
    simpa [prefixWord, tailWord_7647636, baseEnd_7647636] using wordTrace_append hprefix tailTrace_7647636
  have hstable : (prefixWord ++ tailWord_7647636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647636).length < 2 ^ (prefixWord ++ tailWord_7647636).sum := by decide
  have hdescent : baseEnd_7647636 < baseStart_7647636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647641 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_7647641 : Nat := 118140960795 + 7647641 * 2 ^ 59
def prefixEnd_7647641 : Nat := 4983230072969 + 3 ^ 40 * 7647641 * 2
def baseEnd_7647641 : Nat := 3926915706031218303116645

theorem tailTrace_7647641 : CollatzResearch.WordTrace tailWord_7647641 prefixEnd_7647641 3926915706031218303116645 := by
  unfold tailWord_7647641
  simp only [CollatzResearch.WordTrace]
  refine ⟨278932382486910244942934777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185954921657940163295289851 278932382486910244942934777)
  ·
    refine ⟨209199286865182683707201083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278932382486910244942934777 209199286865182683707201083)
    ·
      refine ⟨313798930297774025560801625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209199286865182683707201083 313798930297774025560801625)
      ·
        refine ⟨235349197723330519170601219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313798930297774025560801625 235349197723330519170601219)
        ·
          refine ⟨353023796584995778755901829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235349197723330519170601219 353023796584995778755901829)
          ·
            refine ⟨66191961859686708516731593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353023796584995778755901829 66191961859686708516731593)
            ·
              refine ⟨49643971394765031387548695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66191961859686708516731593 49643971394765031387548695)
              ·
                refine ⟨74465957092147547081323043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49643971394765031387548695 74465957092147547081323043)
                ·
                  refine ⟨111698935638221320621984565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74465957092147547081323043 111698935638221320621984565)
                  ·
                    refine ⟨10471775216083248808311053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111698935638221320621984565 10471775216083248808311053)
                    ·
                      refine ⟨3926915706031218303116645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471775216083248808311053 3926915706031218303116645)
                      ·
                        rfl

theorem cell23_7647641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_7647641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647641 prefixEnd_7647641 := by exact prefixLift 7647641
  have htrace : WordTrace (prefixWord ++ tailWord_7647641) baseStart_7647641 baseEnd_7647641 := by
    simpa [prefixWord, tailWord_7647641, baseEnd_7647641] using wordTrace_append hprefix tailTrace_7647641
  have hstable : (prefixWord ++ tailWord_7647641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647641).length < 2 ^ (prefixWord ++ tailWord_7647641).sum := by decide
  have hdescent : baseEnd_7647641 < baseStart_7647641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647642 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7647642 : Nat := 118140960795 + 7647642 * 2 ^ 59
def prefixEnd_7647642 : Nat := 4983230072969 + 3 ^ 40 * 7647642 * 2
def baseEnd_7647642 : Nat := 3926916219511872799204141

theorem tailTrace_7647642 : CollatzResearch.WordTrace tailWord_7647642 prefixEnd_7647642 3926916219511872799204141 := by
  unfold tailWord_7647642
  simp only [CollatzResearch.WordTrace]
  refine ⟨69733104739976655528430295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185954945973271081409147453 69733104739976655528430295)
  ·
    refine ⟨104599657109964983292645443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69733104739976655528430295 104599657109964983292645443)
    ·
      refine ⟨156899485664947474938968165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104599657109964983292645443 156899485664947474938968165)
      ·
        refine ⟨29418653562177651551056531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156899485664947474938968165 29418653562177651551056531)
        ·
          refine ⟨44127980343266477326584797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29418653562177651551056531 44127980343266477326584797)
          ·
            refine ⟨16547992628724928997469299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44127980343266477326584797 16547992628724928997469299)
            ·
              refine ⟨24821988943087393496203949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16547992628724928997469299 24821988943087393496203949)
              ·
                refine ⟨9308245853657772561076481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24821988943087393496203949 9308245853657772561076481)
                ·
                  refine ⟨6981184390243329420807361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9308245853657772561076481 6981184390243329420807361)
                  ·
                    refine ⟨5235888292682497065605521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6981184390243329420807361 5235888292682497065605521)
                    ·
                      refine ⟨3926916219511872799204141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235888292682497065605521 3926916219511872799204141)
                      ·
                        rfl

theorem cell23_7647642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7647642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647642 prefixEnd_7647642 := by exact prefixLift 7647642
  have htrace : WordTrace (prefixWord ++ tailWord_7647642) baseStart_7647642 baseEnd_7647642 := by
    simpa [prefixWord, tailWord_7647642, baseEnd_7647642] using wordTrace_append hprefix tailTrace_7647642
  have hstable : (prefixWord ++ tailWord_7647642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647642).length < 2 ^ (prefixWord ++ tailWord_7647642).sum := by decide
  have hdescent : baseEnd_7647642 < baseStart_7647642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647671 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_7647671 : Nat := 118140960795 + 7647671 * 2 ^ 59
def prefixEnd_7647671 : Nat := 4983230072969 + 3 ^ 40 * 7647671 * 2
def baseEnd_7647671 : Nat := 3926931110450853185741507

theorem tailTrace_7647671 : CollatzResearch.WordTrace tailWord_7647671 prefixEnd_7647671 3926931110450853185741507 := by
  unfold tailWord_7647671
  simp only [CollatzResearch.WordTrace]
  refine ⟨278933476676801560066526867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185955651117867706711017911 278933476676801560066526867)
  ·
    refine ⟨418400215015202340099790301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278933476676801560066526867 418400215015202340099790301)
    ·
      refine ⟨156900080630700877537421363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418400215015202340099790301 156900080630700877537421363)
      ·
        refine ⟨235350120946051316306132045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156900080630700877537421363 235350120946051316306132045)
        ·
          refine ⟨88256295354769243614799517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235350120946051316306132045 88256295354769243614799517)
          ·
            refine ⟨33096110758038466355549819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88256295354769243614799517 33096110758038466355549819)
            ·
              refine ⟨49644166137057699533324729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33096110758038466355549819 49644166137057699533324729)
              ·
                refine ⟨37233124602793274649993547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49644166137057699533324729 37233124602793274649993547)
                ·
                  refine ⟨55849686904189911974990321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37233124602793274649993547 55849686904189911974990321)
                  ·
                    refine ⟨41887265178142433981242741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55849686904189911974990321 41887265178142433981242741)
                    ·
                      refine ⟨3926931110450853185741507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41887265178142433981242741 3926931110450853185741507)
                      ·
                        rfl

theorem cell23_7647671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_7647671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647671 prefixEnd_7647671 := by exact prefixLift 7647671
  have htrace : WordTrace (prefixWord ++ tailWord_7647671) baseStart_7647671 baseEnd_7647671 := by
    simpa [prefixWord, tailWord_7647671, baseEnd_7647671] using wordTrace_append hprefix tailTrace_7647671
  have hstable : (prefixWord ++ tailWord_7647671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647671).length < 2 ^ (prefixWord ++ tailWord_7647671).sum := by decide
  have hdescent : baseEnd_7647671 < baseStart_7647671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647678 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7647678 : Nat := 118140960795 + 7647678 * 2 ^ 59
def prefixEnd_7647678 : Nat := 4983230072969 + 3 ^ 40 * 7647678 * 2
def baseEnd_7647678 : Nat := 1308978234938478219451325

theorem tailTrace_7647678 : CollatzResearch.WordTrace tailWord_7647678 prefixEnd_7647678 1308978234938478219451325 := by
  unfold tailWord_7647678
  simp only [CollatzResearch.WordTrace]
  refine ⟨34866716498472025032753961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185955821325184133508021125 34866716498472025032753961)
  ·
    refine ⟨26150037373854018774565471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34866716498472025032753961 26150037373854018774565471)
    ·
      refine ⟨39225056060781028161848207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26150037373854018774565471 39225056060781028161848207)
      ·
        refine ⟨58837584091171542242772311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39225056060781028161848207 58837584091171542242772311)
        ·
          refine ⟨88256376136757313364158467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58837584091171542242772311 88256376136757313364158467)
          ·
            refine ⟨132384564205135970046237701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88256376136757313364158467 132384564205135970046237701)
            ·
              refine ⟨24822105788462994383669569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132384564205135970046237701 24822105788462994383669569)
              ·
                refine ⟨18616579341347245787752177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24822105788462994383669569 18616579341347245787752177)
                ·
                  refine ⟨13962434506010434340814133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18616579341347245787752177 13962434506010434340814133)
                  ·
                    refine ⟨1308978234938478219451325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13962434506010434340814133 1308978234938478219451325)
                    ·
                      rfl

theorem cell23_7647678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7647678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647678 prefixEnd_7647678 := by exact prefixLift 7647678
  have htrace : WordTrace (prefixWord ++ tailWord_7647678) baseStart_7647678 baseEnd_7647678 := by
    simpa [prefixWord, tailWord_7647678, baseEnd_7647678] using wordTrace_append hprefix tailTrace_7647678
  have hstable : (prefixWord ++ tailWord_7647678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647678).length < 2 ^ (prefixWord ++ tailWord_7647678).sum := by decide
  have hdescent : baseEnd_7647678 < baseStart_7647678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647741 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7647741 : Nat := 118140960795 + 7647741 * 2 ^ 59
def prefixEnd_7647741 : Nat := 4983230072969 + 3 ^ 40 * 7647741 * 2
def baseEnd_7647741 : Nat := 3926967054096667911866185

theorem tailTrace_7647741 : CollatzResearch.WordTrace tailWord_7647741 prefixEnd_7647741 3926967054096667911866185 := by
  unfold tailWord_7647741
  simp only [CollatzResearch.WordTrace]
  refine ⟨278936029786547962021575077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185957353191031974681050051 278936029786547962021575077)
  ·
    refine ⟨52300505584977742879045327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278936029786547962021575077 52300505584977742879045327)
    ·
      refine ⟨78450758377466614318567991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52300505584977742879045327 78450758377466614318567991)
      ·
        refine ⟨117676137566199921477851987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78450758377466614318567991 117676137566199921477851987)
        ·
          refine ⟨176514206349299882216777981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117676137566199921477851987 176514206349299882216777981)
          ·
            refine ⟨66192827380987455831291743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176514206349299882216777981 66192827380987455831291743)
            ·
              refine ⟨99289241071481183746937615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66192827380987455831291743 99289241071481183746937615)
              ·
                refine ⟨148933861607221775620406423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99289241071481183746937615 148933861607221775620406423)
                ·
                  refine ⟨223400792410832663430609635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148933861607221775620406423 223400792410832663430609635)
                  ·
                    refine ⟨335101188616248995145914453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223400792410832663430609635 335101188616248995145914453)
                    ·
                      refine ⟨3926967054096667911866185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335101188616248995145914453 3926967054096667911866185)
                      ·
                        rfl

theorem cell23_7647741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7647741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647741 prefixEnd_7647741 := by exact prefixLift 7647741
  have htrace : WordTrace (prefixWord ++ tailWord_7647741) baseStart_7647741 baseEnd_7647741 := by
    simpa [prefixWord, tailWord_7647741, baseEnd_7647741] using wordTrace_append hprefix tailTrace_7647741
  have hstable : (prefixWord ++ tailWord_7647741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647741).length < 2 ^ (prefixWord ++ tailWord_7647741).sum := by decide
  have hdescent : baseEnd_7647741 < baseStart_7647741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647755 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 6]
def baseStart_7647755 : Nat := 118140960795 + 7647755 * 2 ^ 59
def prefixEnd_7647755 : Nat := 4983230072969 + 3 ^ 40 * 7647755 * 2
def baseEnd_7647755 : Nat := 436330471425092317454569

theorem tailTrace_7647755 : CollatzResearch.WordTrace tailWord_7647755 prefixEnd_7647755 436330471425092317454569 := by
  unfold tailWord_7647755
  simp only [CollatzResearch.WordTrace]
  refine ⟨278936540408497242412584719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185957693605664828275056479 278936540408497242412584719)
  ·
    refine ⟨418404810612745863618877079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278936540408497242412584719 418404810612745863618877079)
    ·
      refine ⟨627607215919118795428315619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418404810612745863618877079 627607215919118795428315619)
      ·
        refine ⟨941410823878678193142473429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627607215919118795428315619 941410823878678193142473429)
        ·
          refine ⟨22064316184656520151776721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 941410823878678193142473429 22064316184656520151776721)
          ·
            refine ⟨16548237138492390113832541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22064316184656520151776721 16548237138492390113832541)
            ·
              refine ⟨6205588926934646292687203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16548237138492390113832541 6205588926934646292687203)
              ·
                refine ⟨9308383390401969439030805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205588926934646292687203 9308383390401969439030805)
                ·
                  refine ⟨436330471425092317454569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9308383390401969439030805 436330471425092317454569)
                  ·
                    rfl

theorem cell23_7647755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 6].length) (baseStart_7647755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647755 prefixEnd_7647755 := by exact prefixLift 7647755
  have htrace : WordTrace (prefixWord ++ tailWord_7647755) baseStart_7647755 baseEnd_7647755 := by
    simpa [prefixWord, tailWord_7647755, baseEnd_7647755] using wordTrace_append hprefix tailTrace_7647755
  have hstable : (prefixWord ++ tailWord_7647755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647755).length < 2 ^ (prefixWord ++ tailWord_7647755).sum := by decide
  have hdescent : baseEnd_7647755 < baseStart_7647755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647765 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_7647765 : Nat := 118140960795 + 7647765 * 2 ^ 59
def prefixEnd_7647765 : Nat := 4983230072969 + 3 ^ 40 * 7647765 * 2
def baseEnd_7647765 : Nat := 3926979377632375817966075

theorem tailTrace_7647765 : CollatzResearch.WordTrace tailWord_7647765 prefixEnd_7647765 3926979377632375817966075 := by
  unfold tailWord_7647765
  simp only [CollatzResearch.WordTrace]
  refine ⟨278936905138461014120448749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185957936758974009413632499 278936905138461014120448749)
  ·
    refine ⟨104601339426922880295168281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278936905138461014120448749 104601339426922880295168281)
    ·
      refine ⟨78451004570192160221376211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104601339426922880295168281 78451004570192160221376211)
      ·
        refine ⟨117676506855288240332064317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78451004570192160221376211 117676506855288240332064317)
        ·
          refine ⟨44128690070733090124524119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117676506855288240332064317 44128690070733090124524119)
          ·
            refine ⟨66193035106099635186786179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44128690070733090124524119 66193035106099635186786179)
            ·
              refine ⟨99289552659149452780179269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66193035106099635186786179 99289552659149452780179269)
              ·
                refine ⟨18616791123590522396283613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99289552659149452780179269 18616791123590522396283613)
                ·
                  refine ⟨6981296671346445898606355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18616791123590522396283613 6981296671346445898606355)
                  ·
                    refine ⟨10471945007019668847909533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981296671346445898606355 10471945007019668847909533)
                    ·
                      refine ⟨3926979377632375817966075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471945007019668847909533 3926979377632375817966075)
                      ·
                        rfl

theorem cell23_7647765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_7647765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647765 prefixEnd_7647765 := by exact prefixLift 7647765
  have htrace : WordTrace (prefixWord ++ tailWord_7647765) baseStart_7647765 baseEnd_7647765 := by
    simpa [prefixWord, tailWord_7647765, baseEnd_7647765] using wordTrace_append hprefix tailTrace_7647765
  have hstable : (prefixWord ++ tailWord_7647765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647765).length < 2 ^ (prefixWord ++ tailWord_7647765).sum := by decide
  have hdescent : baseEnd_7647765 < baseStart_7647765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647771 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_7647771 : Nat := 118140960795 + 7647771 * 2 ^ 59
def prefixEnd_7647771 : Nat := 4983230072969 + 3 ^ 40 * 7647771 * 2
def baseEnd_7647771 : Nat := 3926982458516302794491047

theorem tailTrace_7647771 : CollatzResearch.WordTrace tailWord_7647771 prefixEnd_7647771 3926982458516302794491047 := by
  unfold tailWord_7647771
  simp only [CollatzResearch.WordTrace]
  refine ⟨278937123976439277145167167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185958082650959518096778111 278937123976439277145167167)
  ·
    refine ⟨418405685964658915717750751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278937123976439277145167167 418405685964658915717750751)
    ·
      refine ⟨627608528946988373576626127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418405685964658915717750751 627608528946988373576626127)
      ·
        refine ⟨941412793420482560364939191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627608528946988373576626127 941412793420482560364939191)
        ·
          refine ⟨1412119190130723840547408787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941412793420482560364939191 1412119190130723840547408787)
          ·
            refine ⟨2118178785196085760821113181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412119190130723840547408787 2118178785196085760821113181)
            ·
              refine ⟨794317044448532160307917443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2118178785196085760821113181 794317044448532160307917443)
              ·
                refine ⟨1191475566672798240461876165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794317044448532160307917443 1191475566672798240461876165)
                ·
                  refine ⟨223401668751149670086601781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191475566672798240461876165 223401668751149670086601781)
                  ·
                    refine ⟨20943906445420281570618917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223401668751149670086601781 20943906445420281570618917)
                    ·
                      refine ⟨3926982458516302794491047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20943906445420281570618917 3926982458516302794491047)
                      ·
                        rfl

theorem cell23_7647771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_7647771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647771 prefixEnd_7647771 := by exact prefixLift 7647771
  have htrace : WordTrace (prefixWord ++ tailWord_7647771) baseStart_7647771 baseEnd_7647771 := by
    simpa [prefixWord, tailWord_7647771, baseEnd_7647771] using wordTrace_append hprefix tailTrace_7647771
  have hstable : (prefixWord ++ tailWord_7647771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647771).length < 2 ^ (prefixWord ++ tailWord_7647771).sum := by decide
  have hdescent : baseEnd_7647771 < baseStart_7647771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647775 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 2, 3, 2]
def baseStart_7647775 : Nat := 118140960795 + 7647775 * 2 ^ 59
def prefixEnd_7647775 : Nat := 4983230072969 + 3 ^ 40 * 7647775 * 2
def baseEnd_7647775 : Nat := 3926984512438920778841029

theorem tailTrace_7647775 : CollatzResearch.WordTrace tailWord_7647775 prefixEnd_7647775 3926984512438920778841029 := by
  unfold tailWord_7647775
  simp only [CollatzResearch.WordTrace]
  refine ⟨278937269868424785828312779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185958179912283190552208519 278937269868424785828312779)
  ·
    refine ⟨418405904802637178742469169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278937269868424785828312779 418405904802637178742469169)
    ·
      refine ⟨313804428601977884056851877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418405904802637178742469169 313804428601977884056851877)
      ·
        refine ⟨58838330362870853260659727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313804428601977884056851877 58838330362870853260659727)
        ·
          refine ⟨88257495544306279890989591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58838330362870853260659727 88257495544306279890989591)
          ·
            refine ⟨132386243316459419836484387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88257495544306279890989591 132386243316459419836484387)
            ·
              refine ⟨198579364974689129754726581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132386243316459419836484387 198579364974689129754726581)
              ·
                refine ⟨18616815466377105914505617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198579364974689129754726581 18616815466377105914505617)
                ·
                  refine ⟨13962611599782829435879213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18616815466377105914505617 13962611599782829435879213)
                  ·
                    refine ⟨5235979349918561038454705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13962611599782829435879213 5235979349918561038454705)
                    ·
                      refine ⟨3926984512438920778841029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235979349918561038454705 3926984512438920778841029)
                      ·
                        rfl

theorem cell23_7647775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_7647775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647775 prefixEnd_7647775 := by exact prefixLift 7647775
  have htrace : WordTrace (prefixWord ++ tailWord_7647775) baseStart_7647775 baseEnd_7647775 := by
    simpa [prefixWord, tailWord_7647775, baseEnd_7647775] using wordTrace_append hprefix tailTrace_7647775
  have hstable : (prefixWord ++ tailWord_7647775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647775).length < 2 ^ (prefixWord ++ tailWord_7647775).sum := by decide
  have hdescent : baseEnd_7647775 < baseStart_7647775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647776 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 1, 4]
def baseStart_7647776 : Nat := 118140960795 + 7647776 * 2 ^ 59
def prefixEnd_7647776 : Nat := 4983230072969 + 3 ^ 40 * 7647776 * 2
def baseEnd_7647776 : Nat := 1308995008639858424976175

theorem tailTrace_7647776 : CollatzResearch.WordTrace tailWord_7647776 prefixEnd_7647776 1308995008639858424976175 := by
  unfold tailWord_7647776
  simp only [CollatzResearch.WordTrace]
  refine ⟨139468653170710581499549591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185958204227614108666066121 139468653170710581499549591)
  ·
    refine ⟨209202979756065872249324387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139468653170710581499549591 209202979756065872249324387)
    ·
      refine ⟨313804469634098808373986581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209202979756065872249324387 313804469634098808373986581)
      ·
        refine ⟨14709584514098381642530621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 313804469634098808373986581 14709584514098381642530621)
        ·
          refine ⟨5516094192786893115948983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14709584514098381642530621 5516094192786893115948983)
          ·
            refine ⟨8274141289180339673923475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516094192786893115948983 8274141289180339673923475)
            ·
              refine ⟨12411211933770509510885213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274141289180339673923475 12411211933770509510885213)
              ·
                refine ⟨4654204475163941066581955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12411211933770509510885213 4654204475163941066581955)
                ·
                  refine ⟨6981306712745911599872933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654204475163941066581955 6981306712745911599872933)
                  ·
                    refine ⟨1308995008639858424976175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6981306712745911599872933 1308995008639858424976175)
                    ·
                      rfl

theorem cell23_7647776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 4].length) (baseStart_7647776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647776 prefixEnd_7647776 := by exact prefixLift 7647776
  have htrace : WordTrace (prefixWord ++ tailWord_7647776) baseStart_7647776 baseEnd_7647776 := by
    simpa [prefixWord, tailWord_7647776, baseEnd_7647776] using wordTrace_append hprefix tailTrace_7647776
  have hstable : (prefixWord ++ tailWord_7647776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647776).length < 2 ^ (prefixWord ++ tailWord_7647776).sum := by decide
  have hdescent : baseEnd_7647776 < baseStart_7647776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647799 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 1, 1, 3]
def baseStart_7647799 : Nat := 118140960795 + 7647799 * 2 ^ 59
def prefixEnd_7647799 : Nat := 4983230072969 + 3 ^ 40 * 7647799 * 2
def baseEnd_7647799 : Nat := 3926996835974628684940919

theorem tailTrace_7647799 : CollatzResearch.WordTrace tailWord_7647799 prefixEnd_7647799 3926996835974628684940919 := by
  unfold tailWord_7647799
  simp only [CollatzResearch.WordTrace]
  refine ⟨278938145220337837927186451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185958763480225225284790967 278938145220337837927186451)
  ·
    refine ⟨418407217830506756890779677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278938145220337837927186451 418407217830506756890779677)
    ·
      refine ⟨156902706686440033834042379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418407217830506756890779677 156902706686440033834042379)
      ·
        refine ⟨235354060029660050751063569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156902706686440033834042379 235354060029660050751063569)
        ·
          refine ⟨176515545022245038063297677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235354060029660050751063569 176515545022245038063297677)
          ·
            refine ⟨66193329383341889273736629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176515545022245038063297677 66193329383341889273736629)
            ·
              refine ⟨6205624629688302119412809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66193329383341889273736629 6205624629688302119412809)
              ·
                refine ⟨4654218472266226589559607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205624629688302119412809 4654218472266226589559607)
                ·
                  refine ⟨6981327708399339884339411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654218472266226589559607 6981327708399339884339411)
                  ·
                    refine ⟨10471991562599009826509117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981327708399339884339411 10471991562599009826509117)
                    ·
                      refine ⟨3926996835974628684940919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10471991562599009826509117 3926996835974628684940919)
                      ·
                        rfl

theorem cell23_7647799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_7647799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647799 prefixEnd_7647799 := by exact prefixLift 7647799
  have htrace : WordTrace (prefixWord ++ tailWord_7647799) baseStart_7647799 baseEnd_7647799 := by
    simpa [prefixWord, tailWord_7647799, baseEnd_7647799] using wordTrace_append hprefix tailTrace_7647799
  have hstable : (prefixWord ++ tailWord_7647799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647799).length < 2 ^ (prefixWord ++ tailWord_7647799).sum := by decide
  have hdescent : baseEnd_7647799 < baseStart_7647799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647806 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_7647806 : Nat := 118140960795 + 7647806 * 2 ^ 59
def prefixEnd_7647806 : Nat := 4983230072969 + 3 ^ 40 * 7647806 * 2
def baseEnd_7647806 : Nat := 436333381148801128617043

theorem tailTrace_7647806 : CollatzResearch.WordTrace tailWord_7647806 prefixEnd_7647806 436333381148801128617043 := by
  unfold tailWord_7647806
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867300066414059765336409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185958933687541652081794181 34867300066414059765336409)
  ·
    refine ⟨26150475049810544824002307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34867300066414059765336409 26150475049810544824002307)
    ·
      refine ⟨39225712574715817236003461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26150475049810544824002307 39225712574715817236003461)
      ·
        refine ⟨7354821107759215731750649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39225712574715817236003461 7354821107759215731750649)
        ·
          refine ⟨5516115830819411798812987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7354821107759215731750649 5516115830819411798812987)
          ·
            refine ⟨8274173746229117698219481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516115830819411798812987 8274173746229117698219481)
            ·
              refine ⟨6205630309671838273664611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8274173746229117698219481 6205630309671838273664611)
              ·
                refine ⟨9308445464507757410496917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205630309671838273664611 9308445464507757410496917)
                ·
                  refine ⟨436333381148801128617043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9308445464507757410496917 436333381148801128617043)
                  ·
                    rfl

theorem cell23_7647806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_7647806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647806 prefixEnd_7647806 := by exact prefixLift 7647806
  have htrace : WordTrace (prefixWord ++ tailWord_7647806) baseStart_7647806 baseEnd_7647806 := by
    simpa [prefixWord, tailWord_7647806, baseEnd_7647806] using wordTrace_append hprefix tailTrace_7647806
  have hstable : (prefixWord ++ tailWord_7647806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647806).length < 2 ^ (prefixWord ++ tailWord_7647806).sum := by decide
  have hdescent : baseEnd_7647806 < baseStart_7647806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647808 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_7647808 : Nat := 118140960795 + 7647808 * 2 ^ 59
def prefixEnd_7647808 : Nat := 4983230072969 + 3 ^ 40 * 7647808 * 2
def baseEnd_7647808 : Nat := 3927001457300519149728377

theorem tailTrace_7647808 : CollatzResearch.WordTrace tailWord_7647808 prefixEnd_7647808 3927001457300519149728377 := by
  unfold tailWord_7647808
  simp only [CollatzResearch.WordTrace]
  refine ⟨139469236738652616232132039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185958982318203488309509385 139469236738652616232132039)
  ·
    refine ⟨209203855107978924348198059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139469236738652616232132039 209203855107978924348198059)
    ·
      refine ⟨313805782661968386522297089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209203855107978924348198059 313805782661968386522297089)
      ·
        refine ⟨235354336996476289891722817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313805782661968386522297089 235354336996476289891722817)
        ·
          refine ⟨176515752747357217418792113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235354336996476289891722817 176515752747357217418792113)
          ·
            refine ⟨132386814560517913064094085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176515752747357217418792113 132386814560517913064094085)
            ·
              refine ⟨24822527730097108699517641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132386814560517913064094085 24822527730097108699517641)
              ·
                refine ⟨18616895797572831524638231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24822527730097108699517641 18616895797572831524638231)
                ·
                  refine ⟨27925343696359247286957347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18616895797572831524638231 27925343696359247286957347)
                  ·
                    refine ⟨41888015544538870930436021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27925343696359247286957347 41888015544538870930436021)
                    ·
                      refine ⟨3927001457300519149728377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41888015544538870930436021 3927001457300519149728377)
                      ·
                        rfl

theorem cell23_7647808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_7647808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647808 prefixEnd_7647808 := by exact prefixLift 7647808
  have htrace : WordTrace (prefixWord ++ tailWord_7647808) baseStart_7647808 baseEnd_7647808 := by
    simpa [prefixWord, tailWord_7647808, baseEnd_7647808] using wordTrace_append hprefix tailTrace_7647808
  have hstable : (prefixWord ++ tailWord_7647808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647808).length < 2 ^ (prefixWord ++ tailWord_7647808).sum := by decide
  have hdescent : baseEnd_7647808 < baseStart_7647808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647818 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_7647818 : Nat := 118140960795 + 7647818 * 2 ^ 59
def prefixEnd_7647818 : Nat := 4983230072969 + 3 ^ 40 * 7647818 * 2
def baseEnd_7647818 : Nat := 3927006592107064110603331

theorem tailTrace_7647818 : CollatzResearch.WordTrace tailWord_7647818 prefixEnd_7647818 3927006592107064110603331 := by
  unfold tailWord_7647818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69734709551817251043032027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185959225471512669448085405 69734709551817251043032027)
  ·
    refine ⟨104602064327725876564548041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69734709551817251043032027 104602064327725876564548041)
    ·
      refine ⟨78451548245794407423411031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104602064327725876564548041 78451548245794407423411031)
      ·
        refine ⟨117677322368691611135116547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78451548245794407423411031 117677322368691611135116547)
        ·
          refine ⟨176515983553037416702674821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117677322368691611135116547 176515983553037416702674821)
          ·
            refine ⟨33096746916194515631751529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176515983553037416702674821 33096746916194515631751529)
            ·
              refine ⟨24822560187145886723813647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33096746916194515631751529 24822560187145886723813647)
              ·
                refine ⟨37233840280718830085720471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24822560187145886723813647 37233840280718830085720471)
                ·
                  refine ⟨55850760421078245128580707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37233840280718830085720471 55850760421078245128580707)
                  ·
                    refine ⟨83776140631617367692871061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55850760421078245128580707 83776140631617367692871061)
                    ·
                      refine ⟨3927006592107064110603331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83776140631617367692871061 3927006592107064110603331)
                      ·
                        rfl

theorem cell23_7647818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_7647818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647818 prefixEnd_7647818 := by exact prefixLift 7647818
  have htrace : WordTrace (prefixWord ++ tailWord_7647818) baseStart_7647818 baseEnd_7647818 := by
    simpa [prefixWord, tailWord_7647818, baseEnd_7647818] using wordTrace_append hprefix tailTrace_7647818
  have hstable : (prefixWord ++ tailWord_7647818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647818).length < 2 ^ (prefixWord ++ tailWord_7647818).sum := by decide
  have hdescent : baseEnd_7647818 < baseStart_7647818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647822 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_7647822 : Nat := 118140960795 + 7647822 * 2 ^ 59
def prefixEnd_7647822 : Nat := 4983230072969 + 3 ^ 40 * 7647822 * 2
def baseEnd_7647822 : Nat := 3927008646029682094953313

theorem tailTrace_7647822 : CollatzResearch.WordTrace tailWord_7647822 prefixEnd_7647822 3927008646029682094953313 := by
  unfold tailWord_7647822
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867373012406814106909215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185959322732836341903515813 34867373012406814106909215)
  ·
    refine ⟨52301059518610221160363823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34867373012406814106909215 52301059518610221160363823)
    ·
      refine ⟨78451589277915331740545735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52301059518610221160363823 78451589277915331740545735)
      ·
        refine ⟨117677383916872997610818603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78451589277915331740545735 117677383916872997610818603)
        ·
          refine ⟨176516075875309496416227905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117677383916872997610818603 176516075875309496416227905)
          ·
            refine ⟨132387056906482122312170929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176516075875309496416227905 132387056906482122312170929)
            ·
              refine ⟨99290292679861591734128197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132387056906482122312170929 99290292679861591734128197)
              ·
                refine ⟨18616929877474048450149037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99290292679861591734128197 18616929877474048450149037)
                ·
                  refine ⟨6981348704052768168805889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18616929877474048450149037 6981348704052768168805889)
                  ·
                    refine ⟨5236011528039576126604417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6981348704052768168805889 5236011528039576126604417)
                    ·
                      refine ⟨3927008646029682094953313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236011528039576126604417 3927008646029682094953313)
                      ·
                        rfl

theorem cell23_7647822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_7647822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647822 prefixEnd_7647822 := by exact prefixLift 7647822
  have htrace : WordTrace (prefixWord ++ tailWord_7647822) baseStart_7647822 baseEnd_7647822 := by
    simpa [prefixWord, tailWord_7647822, baseEnd_7647822] using wordTrace_append hprefix tailTrace_7647822
  have hstable : (prefixWord ++ tailWord_7647822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647822).length < 2 ^ (prefixWord ++ tailWord_7647822).sum := by decide
  have hdescent : baseEnd_7647822 < baseStart_7647822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647825 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_7647825 : Nat := 118140960795 + 7647825 * 2 ^ 59
def prefixEnd_7647825 : Nat := 4983230072969 + 3 ^ 40 * 7647825 * 2
def baseEnd_7647825 : Nat := 3927010186471645583215799

theorem tailTrace_7647825 : CollatzResearch.WordTrace tailWord_7647825 prefixEnd_7647825 3927010186471645583215799 := by
  unfold tailWord_7647825
  simp only [CollatzResearch.WordTrace]
  refine ⟨278939093518243644367632929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185959395678829096245088619 278939093518243644367632929)
  ·
    refine ⟨209204320138682733275724697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278939093518243644367632929 209204320138682733275724697)
    ·
      refine ⟨156903240104012049956793523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209204320138682733275724697 156903240104012049956793523)
      ·
        refine ⟨235354860156018074935190285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156903240104012049956793523 235354860156018074935190285)
        ·
          refine ⟨88258072558506778100696357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235354860156018074935190285 88258072558506778100696357)
          ·
            refine ⟨16548388604720020893880567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88258072558506778100696357 16548388604720020893880567)
            ·
              refine ⟨24822582907080031340820851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16548388604720020893880567 24822582907080031340820851)
              ·
                refine ⟨37233874360620047011231277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24822582907080031340820851 37233874360620047011231277)
                ·
                  refine ⟨13962702885232517629211729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37233874360620047011231277 13962702885232517629211729)
                  ·
                    refine ⟨10472027163924388221908797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13962702885232517629211729 10472027163924388221908797)
                    ·
                      refine ⟨3927010186471645583215799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472027163924388221908797 3927010186471645583215799)
                      ·
                        rfl

theorem cell23_7647825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_7647825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647825 prefixEnd_7647825 := by exact prefixLift 7647825
  have htrace : WordTrace (prefixWord ++ tailWord_7647825) baseStart_7647825 baseEnd_7647825 := by
    simpa [prefixWord, tailWord_7647825, baseEnd_7647825] using wordTrace_append hprefix tailTrace_7647825
  have hstable : (prefixWord ++ tailWord_7647825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647825).length < 2 ^ (prefixWord ++ tailWord_7647825).sum := by decide
  have hdescent : baseEnd_7647825 < baseStart_7647825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647828 : List Nat := [2, 4, 1, 1, 1, 3, 2, 9]
def baseStart_7647828 : Nat := 118140960795 + 7647828 * 2 ^ 59
def prefixEnd_7647828 : Nat := 4983230072969 + 3 ^ 40 * 7647828 * 2
def baseEnd_7647828 : Nat := 145444878774578113758455

theorem tailTrace_7647828 : CollatzResearch.WordTrace tailWord_7647828 prefixEnd_7647828 145444878774578113758455 := by
  unfold tailWord_7647828
  simp only [CollatzResearch.WordTrace]
  refine ⟨139469601468616387939996069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185959468624821850586661425 139469601468616387939996069)
  ·
    refine ⟨26150550275365572738749263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139469601468616387939996069 26150550275365572738749263)
    ·
      refine ⟨39225825413048359108123895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26150550275365572738749263 39225825413048359108123895)
      ·
        refine ⟨58838738119572538662185843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39225825413048359108123895 58838738119572538662185843)
        ·
          refine ⟨88258107179358807993278765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58838738119572538662185843 88258107179358807993278765)
          ·
            refine ⟨33096790192259552997479537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88258107179358807993278765 33096790192259552997479537)
            ·
              refine ⟨24822592644194664748109653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33096790192259552997479537 24822592644194664748109653)
              ·
                refine ⟨145444878774578113758455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24822592644194664748109653 145444878774578113758455)
                ·
                  rfl

theorem cell23_7647828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 9].length) (baseStart_7647828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647828 prefixEnd_7647828 := by exact prefixLift 7647828
  have htrace : WordTrace (prefixWord ++ tailWord_7647828) baseStart_7647828 baseEnd_7647828 := by
    simpa [prefixWord, tailWord_7647828, baseEnd_7647828] using wordTrace_append hprefix tailTrace_7647828
  have hstable : (prefixWord ++ tailWord_7647828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647828).length < 2 ^ (prefixWord ++ tailWord_7647828).sum := by decide
  have hdescent : baseEnd_7647828 < baseStart_7647828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647855 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 3]
def baseStart_7647855 : Nat := 118140960795 + 7647855 * 2 ^ 59
def prefixEnd_7647855 : Nat := 4983230072969 + 3 ^ 40 * 7647855 * 2
def baseEnd_7647855 : Nat := 3927025590891280465840661

theorem tailTrace_7647855 : CollatzResearch.WordTrace tailWord_7647855 prefixEnd_7647855 3927025590891280465840661 := by
  unfold tailWord_7647855
  simp only [CollatzResearch.WordTrace]
  refine ⟨278940187708134959491225019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185960125138756639660816679 278940187708134959491225019)
  ·
    refine ⟨418410281562202439236837529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278940187708134959491225019 418410281562202439236837529)
    ·
      refine ⟨313807711171651829427628147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418410281562202439236837529 313807711171651829427628147)
      ·
        refine ⟨470711566757477744141442221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313807711171651829427628147 470711566757477744141442221)
        ·
          refine ⟨176516837534054154053040833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470711566757477744141442221 176516837534054154053040833)
          ·
            refine ⟨132387628150540615539780625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176516837534054154053040833 132387628150540615539780625)
            ·
              refine ⟨99290721112905461654835469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132387628150540615539780625 99290721112905461654835469)
              ·
                refine ⟨37234020417339548120563301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99290721112905461654835469 37234020417339548120563301)
                ·
                  refine ⟨6981378828251165272605619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37234020417339548120563301 6981378828251165272605619)
                  ·
                    refine ⟨10472068242376747908908429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981378828251165272605619 10472068242376747908908429)
                    ·
                      refine ⟨3927025590891280465840661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472068242376747908908429 3927025590891280465840661)
                      ·
                        rfl

theorem cell23_7647855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_7647855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647855 prefixEnd_7647855 := by exact prefixLift 7647855
  have htrace : WordTrace (prefixWord ++ tailWord_7647855) baseStart_7647855 baseEnd_7647855 := by
    simpa [prefixWord, tailWord_7647855, baseEnd_7647855] using wordTrace_append hprefix tailTrace_7647855
  have hstable : (prefixWord ++ tailWord_7647855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647855).length < 2 ^ (prefixWord ++ tailWord_7647855).sum := by decide
  have hdescent : baseEnd_7647855 < baseStart_7647855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647856 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 1, 2, 2]
def baseStart_7647856 : Nat := 118140960795 + 7647856 * 2 ^ 59
def prefixEnd_7647856 : Nat := 4983230072969 + 3 ^ 40 * 7647856 * 2
def baseEnd_7647856 : Nat := 3927026104371934961928157

theorem tailTrace_7647856 : CollatzResearch.WordTrace tailWord_7647856 prefixEnd_7647856 3927026104371934961928157 := by
  unfold tailWord_7647856
  simp only [CollatzResearch.WordTrace]
  refine ⟨139470112090565668331005711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185960149454087557774674281 139470112090565668331005711)
  ·
    refine ⟨209205168135848502496508567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139470112090565668331005711 209205168135848502496508567)
    ·
      refine ⟨313807752203772753744762851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209205168135848502496508567 313807752203772753744762851)
      ·
        refine ⟨470711628305659130617144277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313807752203772753744762851 470711628305659130617144277)
        ·
          refine ⟨11032303788413885873839319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 470711628305659130617144277 11032303788413885873839319)
          ·
            refine ⟨16548455682620828810758979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032303788413885873839319 16548455682620828810758979)
            ·
              refine ⟨24822683523931243216138469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16548455682620828810758979 24822683523931243216138469)
              ·
                refine ⟨4654253160737108103025963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24822683523931243216138469 4654253160737108103025963)
                ·
                  refine ⟨6981379741105662154538945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654253160737108103025963 6981379741105662154538945)
                  ·
                    refine ⟨5236034805829246615904209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6981379741105662154538945 5236034805829246615904209)
                    ·
                      refine ⟨3927026104371934961928157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236034805829246615904209 3927026104371934961928157)
                      ·
                        rfl

theorem cell23_7647856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 2, 2].length) (baseStart_7647856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647856 prefixEnd_7647856 := by exact prefixLift 7647856
  have htrace : WordTrace (prefixWord ++ tailWord_7647856) baseStart_7647856 baseEnd_7647856 := by
    simpa [prefixWord, tailWord_7647856, baseEnd_7647856] using wordTrace_append hprefix tailTrace_7647856
  have hstable : (prefixWord ++ tailWord_7647856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647856).length < 2 ^ (prefixWord ++ tailWord_7647856).sum := by decide
  have hdescent : baseEnd_7647856 < baseStart_7647856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647862 : List Nat := [5, 1, 1, 2, 3, 2, 1, 8]
def baseStart_7647862 : Nat := 118140960795 + 7647862 * 2 ^ 59
def prefixEnd_7647862 : Nat := 4983230072969 + 3 ^ 40 * 7647862 * 2
def baseEnd_7647862 : Nat := 145445525379846738461227

theorem tailTrace_7647862 : CollatzResearch.WordTrace tailWord_7647862 prefixEnd_7647862 145445525379846738461227 := by
  unfold tailWord_7647862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433777688694349980420615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185960295346073066457819893 17433777688694349980420615)
  ·
    refine ⟨26150666533041524970630923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17433777688694349980420615 26150666533041524970630923)
    ·
      refine ⟨39225999799562287455946385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26150666533041524970630923 39225999799562287455946385)
      ·
        refine ⟨29419499849671715591959789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39225999799562287455946385 29419499849671715591959789)
        ·
          refine ⟨11032312443626893346984921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29419499849671715591959789 11032312443626893346984921)
          ·
            refine ⟨8274234332720170010238691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11032312443626893346984921 8274234332720170010238691)
            ·
              refine ⟨12411351499080255015358037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274234332720170010238691 12411351499080255015358037)
              ·
                refine ⟨145445525379846738461227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12411351499080255015358037 145445525379846738461227)
                ·
                  rfl

theorem cell23_7647862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_7647862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647862 prefixEnd_7647862 := by exact prefixLift 7647862
  have htrace : WordTrace (prefixWord ++ tailWord_7647862) baseStart_7647862 baseEnd_7647862 := by
    simpa [prefixWord, tailWord_7647862, baseEnd_7647862] using wordTrace_append hprefix tailTrace_7647862
  have hstable : (prefixWord ++ tailWord_7647862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647862).length < 2 ^ (prefixWord ++ tailWord_7647862).sum := by decide
  have hdescent : baseEnd_7647862 < baseStart_7647862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647872 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3]
def baseStart_7647872 : Nat := 118140960795 + 7647872 * 2 ^ 59
def prefixEnd_7647872 : Nat := 4983230072969 + 3 ^ 40 * 7647872 * 2
def baseEnd_7647872 : Nat := 3927034320062406899328083

theorem tailTrace_7647872 : CollatzResearch.WordTrace tailWord_7647872 prefixEnd_7647872 3927034320062406899328083 := by
  unfold tailWord_7647872
  simp only [CollatzResearch.WordTrace]
  refine ⟨139470403874536685697296935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185960538499382247596395913 139470403874536685697296935)
  ·
    refine ⟨209205605811805028545945403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139470403874536685697296935 209205605811805028545945403)
    ·
      refine ⟨313808408717707542818918105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209205605811805028545945403 313808408717707542818918105)
      ·
        refine ⟨235356306538280657114188579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313808408717707542818918105 235356306538280657114188579)
        ·
          refine ⟨353034459807420985671282869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235356306538280657114188579 353034459807420985671282869)
          ·
            refine ⟨33096980606945717406682769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353034459807420985671282869 33096980606945717406682769)
            ·
              refine ⟨24822735455209288055012077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33096980606945717406682769 24822735455209288055012077)
              ·
                refine ⟨9308525795703483020629529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24822735455209288055012077 9308525795703483020629529)
                ·
                  refine ⟨6981394346777612265472147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9308525795703483020629529 6981394346777612265472147)
                  ·
                    refine ⟨10472091520166418398208221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981394346777612265472147 10472091520166418398208221)
                    ·
                      refine ⟨3927034320062406899328083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472091520166418398208221 3927034320062406899328083)
                      ·
                        rfl

theorem cell23_7647872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_7647872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647872 prefixEnd_7647872 := by exact prefixLift 7647872
  have htrace : WordTrace (prefixWord ++ tailWord_7647872) baseStart_7647872 baseEnd_7647872 := by
    simpa [prefixWord, tailWord_7647872, baseEnd_7647872] using wordTrace_append hprefix tailTrace_7647872
  have hstable : (prefixWord ++ tailWord_7647872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647872).length < 2 ^ (prefixWord ++ tailWord_7647872).sum := by decide
  have hdescent : baseEnd_7647872 < baseStart_7647872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647949 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7647949 : Nat := 118140960795 + 7647949 * 2 ^ 59
def prefixEnd_7647949 : Nat := 4983230072969 + 3 ^ 40 * 7647949 * 2
def baseEnd_7647949 : Nat := 3927073858072803098065229

theorem tailTrace_7647949 : CollatzResearch.WordTrace tailWord_7647949 prefixEnd_7647949 3927073858072803098065229 := by
  unfold tailWord_7647949
  simp only [CollatzResearch.WordTrace]
  refine ⟨278943616169794413545146901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185962410779862942363431267 278943616169794413545146901)
  ·
    refine ⟨13075482007959113134928761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 278943616169794413545146901 13075482007959113134928761)
    ·
      refine ⟨9806611505969334851196571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075482007959113134928761 9806611505969334851196571)
      ·
        refine ⟨14709917258954002276794857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9806611505969334851196571 14709917258954002276794857)
        ·
          refine ⟨11032437944215501707596143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14709917258954002276794857 11032437944215501707596143)
          ·
            refine ⟨16548656916323252561394215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032437944215501707596143 16548656916323252561394215)
            ·
              refine ⟨24822985374484878842091323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16548656916323252561394215 24822985374484878842091323)
              ·
                refine ⟨37234478061727318263136985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24822985374484878842091323 37234478061727318263136985)
                ·
                  refine ⟨27925858546295488697352739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37234478061727318263136985 27925858546295488697352739)
                  ·
                    refine ⟨41888787819443233046029109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27925858546295488697352739 41888787819443233046029109)
                    ·
                      refine ⟨3927073858072803098065229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41888787819443233046029109 3927073858072803098065229)
                      ·
                        rfl

theorem cell23_7647949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7647949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647949 prefixEnd_7647949 := by exact prefixLift 7647949
  have htrace : WordTrace (prefixWord ++ tailWord_7647949) baseStart_7647949 baseEnd_7647949 := by
    simpa [prefixWord, tailWord_7647949, baseEnd_7647949] using wordTrace_append hprefix tailTrace_7647949
  have hstable : (prefixWord ++ tailWord_7647949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647949).length < 2 ^ (prefixWord ++ tailWord_7647949).sum := by decide
  have hdescent : baseEnd_7647949 < baseStart_7647949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647969 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 5]
def baseStart_7647969 : Nat := 118140960795 + 7647969 * 2 ^ 59
def prefixEnd_7647969 : Nat := 4983230072969 + 3 ^ 40 * 7647969 * 2
def baseEnd_7647969 : Nat := 436342680853988113312793

theorem tailTrace_7647969 : CollatzResearch.WordTrace tailWord_7647969 prefixEnd_7647969 436342680853988113312793 := by
  unfold tailWord_7647969
  simp only [CollatzResearch.WordTrace]
  refine ⟨278944345629721956960874961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185962897086481304640583307 278944345629721956960874961)
  ·
    refine ⟨209208259222291467720656221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278944345629721956960874961 209208259222291467720656221)
    ·
      refine ⟨78453097208359300395246083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209208259222291467720656221 78453097208359300395246083)
      ·
        refine ⟨117679645812538950592869125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78453097208359300395246083 117679645812538950592869125)
        ·
          refine ⟨22064933589851053236162961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117679645812538950592869125 22064933589851053236162961)
          ·
            refine ⟨16548700192388289927122221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22064933589851053236162961 16548700192388289927122221)
            ·
              refine ⟨6205762572145608722670833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16548700192388289927122221 6205762572145608722670833)
              ·
                refine ⟨4654321929109206542003125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205762572145608722670833 4654321929109206542003125)
                ·
                  refine ⟨436342680853988113312793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654321929109206542003125 436342680853988113312793)
                  ·
                    rfl

theorem cell23_7647969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 5].length) (baseStart_7647969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647969 prefixEnd_7647969 := by exact prefixLift 7647969
  have htrace : WordTrace (prefixWord ++ tailWord_7647969) baseStart_7647969 baseEnd_7647969 := by
    simpa [prefixWord, tailWord_7647969, baseEnd_7647969] using wordTrace_append hprefix tailTrace_7647969
  have hstable : (prefixWord ++ tailWord_7647969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647969).length < 2 ^ (prefixWord ++ tailWord_7647969).sum := by decide
  have hdescent : baseEnd_7647969 < baseStart_7647969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7647985 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_7647985 : Nat := 118140960795 + 7647985 * 2 ^ 59
def prefixEnd_7647985 : Nat := 4983230072969 + 3 ^ 40 * 7647985 * 2
def baseEnd_7647985 : Nat := 3927092343376364957215063

theorem tailTrace_7647985 : CollatzResearch.WordTrace tailWord_7647985 prefixEnd_7647985 3927092343376364957215063 := by
  unfold tailWord_7647985
  simp only [CollatzResearch.WordTrace]
  refine ⟨278944929197663991693457409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185963286131775994462304939 278944929197663991693457409)
  ·
    refine ⟨209208696898247993770093057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278944929197663991693457409 209208696898247993770093057)
    ·
      refine ⟨156906522673685995327569793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209208696898247993770093057 156906522673685995327569793)
      ·
        refine ⟨117679892005264496495677345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156906522673685995327569793 117679892005264496495677345)
        ·
          refine ⟨88259919003948372371758009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117679892005264496495677345 88259919003948372371758009)
          ·
            refine ⟨66194939252961279278818507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88259919003948372371758009 66194939252961279278818507)
            ·
              refine ⟨99292408879441918918227761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66194939252961279278818507 99292408879441918918227761)
              ·
                refine ⟨74469306659581439188670821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99292408879441918918227761 74469306659581439188670821)
                ·
                  refine ⟨13962994998671519847875779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74469306659581439188670821 13962994998671519847875779)
                  ·
                    refine ⟨20944492498007279771813669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13962994998671519847875779 20944492498007279771813669)
                    ·
                      refine ⟨3927092343376364957215063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20944492498007279771813669 3927092343376364957215063)
                      ·
                        rfl

theorem cell23_7647985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_7647985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7647985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7647985 prefixEnd_7647985 := by exact prefixLift 7647985
  have htrace : WordTrace (prefixWord ++ tailWord_7647985) baseStart_7647985 baseEnd_7647985 := by
    simpa [prefixWord, tailWord_7647985, baseEnd_7647985] using wordTrace_append hprefix tailTrace_7647985
  have hstable : (prefixWord ++ tailWord_7647985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7647985).length < 2 ^ (prefixWord ++ tailWord_7647985).sum := by decide
  have hdescent : baseEnd_7647985 < baseStart_7647985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7647985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648005 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_7648005 : Nat := 118140960795 + 7648005 * 2 ^ 59
def prefixEnd_7648005 : Nat := 4983230072969 + 3 ^ 40 * 7648005 * 2
def baseEnd_7648005 : Nat := 3927102612989454878964971

theorem tailTrace_7648005 : CollatzResearch.WordTrace tailWord_7648005 prefixEnd_7648005 3927102612989454878964971 := by
  unfold tailWord_7648005
  simp only [CollatzResearch.WordTrace]
  refine ⟨278945658657591535109185469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185963772438394356739456979 278945658657591535109185469)
  ·
    refine ⟨104604621996596825665944551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278945658657591535109185469 104604621996596825665944551)
    ·
      refine ⟨156906932994895238498916827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104604621996596825665944551 156906932994895238498916827)
      ·
        refine ⟨235360399492342857748375241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156906932994895238498916827 235360399492342857748375241)
        ·
          refine ⟨176520299619257143311281431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235360399492342857748375241 176520299619257143311281431)
          ·
            refine ⟨264780449428885714966922147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176520299619257143311281431 264780449428885714966922147)
            ·
              refine ⟨397170674143328572450383221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264780449428885714966922147 397170674143328572450383221)
              ·
                refine ⟨37234750700937053667223427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397170674143328572450383221 37234750700937053667223427)
                ·
                  refine ⟨55852126051405580500835141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37234750700937053667223427 55852126051405580500835141)
                  ·
                    refine ⟨10472273634638546343906589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55852126051405580500835141 10472273634638546343906589)
                    ·
                      refine ⟨3927102612989454878964971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472273634638546343906589 3927102612989454878964971)
                      ·
                        rfl

theorem cell23_7648005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_7648005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648005 prefixEnd_7648005 := by exact prefixLift 7648005
  have htrace : WordTrace (prefixWord ++ tailWord_7648005) baseStart_7648005 baseEnd_7648005 := by
    simpa [prefixWord, tailWord_7648005, baseEnd_7648005] using wordTrace_append hprefix tailTrace_7648005
  have hstable : (prefixWord ++ tailWord_7648005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648005).length < 2 ^ (prefixWord ++ tailWord_7648005).sum := by decide
  have hdescent : baseEnd_7648005 < baseStart_7648005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648035 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3]
def baseStart_7648035 : Nat := 118140960795 + 7648035 * 2 ^ 59
def prefixEnd_7648035 : Nat := 4983230072969 + 3 ^ 40 * 7648035 * 2
def baseEnd_7648035 : Nat := 3927118017409089761589833

theorem tailTrace_7648035 : CollatzResearch.WordTrace tailWord_7648035 prefixEnd_7648035 3927118017409089761589833 := by
  unfold tailWord_7648035
  simp only [CollatzResearch.WordTrace]
  refine ⟨278946752847482850232777559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185964501898321900155185039 278946752847482850232777559)
  ·
    refine ⟨418420129271224275349166339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278946752847482850232777559 418420129271224275349166339)
    ·
      refine ⟨627630193906836413023749509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418420129271224275349166339 627630193906836413023749509)
      ·
        refine ⟨117680661357531827441953033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627630193906836413023749509 117680661357531827441953033)
        ·
          refine ⟨88260496018148870581464775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117680661357531827441953033 88260496018148870581464775)
          ·
            refine ⟨132390744027223305872197163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88260496018148870581464775 132390744027223305872197163)
            ·
              refine ⟨198586116040834958808295745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132390744027223305872197163 198586116040834958808295745)
              ·
                refine ⟨148939587030626219106221809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198586116040834958808295745 148939587030626219106221809)
                ·
                  refine ⟨111704690272969664329666357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148939587030626219106221809 111704690272969664329666357)
                  ·
                    refine ⟨10472314713090906030906221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111704690272969664329666357 10472314713090906030906221)
                    ·
                      refine ⟨3927118017409089761589833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472314713090906030906221 3927118017409089761589833)
                      ·
                        rfl

theorem cell23_7648035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_7648035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648035 prefixEnd_7648035 := by exact prefixLift 7648035
  have htrace : WordTrace (prefixWord ++ tailWord_7648035) baseStart_7648035 baseEnd_7648035 := by
    simpa [prefixWord, tailWord_7648035, baseEnd_7648035] using wordTrace_append hprefix tailTrace_7648035
  have hstable : (prefixWord ++ tailWord_7648035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648035).length < 2 ^ (prefixWord ++ tailWord_7648035).sum := by decide
  have hdescent : baseEnd_7648035 < baseStart_7648035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648055 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 3, 5]
def baseStart_7648055 : Nat := 118140960795 + 7648055 * 2 ^ 59
def prefixEnd_7648055 : Nat := 4983230072969 + 3 ^ 40 * 7648055 * 2
def baseEnd_7648055 : Nat := 1309042762340726561113247

theorem tailTrace_7648055 : CollatzResearch.WordTrace tailWord_7648055 prefixEnd_7648055 1309042762340726561113247 := by
  unfold tailWord_7648055
  simp only [CollatzResearch.WordTrace]
  refine ⟨278947482307410393648505619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185964988204940262432337079 278947482307410393648505619)
  ·
    refine ⟨418421223461115590472758429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278947482307410393648505619 418421223461115590472758429)
    ·
      refine ⟨156907958797918346427284411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418421223461115590472758429 156907958797918346427284411)
      ·
        refine ⟨235361938196877519640926617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156907958797918346427284411 235361938196877519640926617)
        ·
          refine ⟨176521453647658139730694963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235361938196877519640926617 176521453647658139730694963)
          ·
            refine ⟨264782180471487209596042445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176521453647658139730694963 264782180471487209596042445)
            ·
              refine ⟨99293317676807703598515917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264782180471487209596042445 99293317676807703598515917)
              ·
                refine ⟨37234994128802888849443469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99293317676807703598515917 37234994128802888849443469)
                ·
                  refine ⟨13963122798301083318541301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37234994128802888849443469 13963122798301083318541301)
                  ·
                    refine ⟨1309042762340726561113247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13963122798301083318541301 1309042762340726561113247)
                    ·
                      rfl

theorem cell23_7648055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_7648055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648055 prefixEnd_7648055 := by exact prefixLift 7648055
  have htrace : WordTrace (prefixWord ++ tailWord_7648055) baseStart_7648055 baseEnd_7648055 := by
    simpa [prefixWord, tailWord_7648055, baseEnd_7648055] using wordTrace_append hprefix tailTrace_7648055
  have hstable : (prefixWord ++ tailWord_7648055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648055).length < 2 ^ (prefixWord ++ tailWord_7648055).sum := by decide
  have hdescent : baseEnd_7648055 < baseStart_7648055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648072 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_7648072 : Nat := 118140960795 + 7648072 * 2 ^ 59
def prefixEnd_7648072 : Nat := 4983230072969 + 3 ^ 40 * 7648072 * 2
def baseEnd_7648072 : Nat := 1309045672064435372275721

theorem tailTrace_7648072 : CollatzResearch.WordTrace tailWord_7648072 prefixEnd_7648072 1309045672064435372275721 := by
  unfold tailWord_7648072
  simp only [CollatzResearch.WordTrace]
  refine ⟨139474051174174402775937235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185965401565565870367916313 139474051174174402775937235)
  ·
    refine ⟨209211076761261604163905853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139474051174174402775937235 209211076761261604163905853)
    ·
      refine ⟨78454153785473101561464695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209211076761261604163905853 78454153785473101561464695)
      ·
        refine ⟨117681230678209652342197043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78454153785473101561464695 117681230678209652342197043)
        ·
          refine ⟨176521846017314478513295565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117681230678209652342197043 176521846017314478513295565)
          ·
            refine ⟨66195692256492929442485837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176521846017314478513295565 66195692256492929442485837)
            ·
              refine ⟨24823384596184848540932189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66195692256492929442485837 24823384596184848540932189)
              ·
                refine ⟨9308769223569318202849571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24823384596184848540932189 9308769223569318202849571)
                ·
                  refine ⟨13963153835353977304274357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9308769223569318202849571 13963153835353977304274357)
                  ·
                    refine ⟨1309045672064435372275721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13963153835353977304274357 1309045672064435372275721)
                    ·
                      rfl

theorem cell23_7648072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_7648072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648072 prefixEnd_7648072 := by exact prefixLift 7648072
  have htrace : WordTrace (prefixWord ++ tailWord_7648072) baseStart_7648072 baseEnd_7648072 := by
    simpa [prefixWord, tailWord_7648072, baseEnd_7648072] using wordTrace_append hprefix tailTrace_7648072
  have hstable : (prefixWord ++ tailWord_7648072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648072).length < 2 ^ (prefixWord ++ tailWord_7648072).sum := by decide
  have hdescent : baseEnd_7648072 < baseStart_7648072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648112 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_7648112 : Nat := 118140960795 + 7648112 * 2 ^ 59
def prefixEnd_7648112 : Nat := 4983230072969 + 3 ^ 40 * 7648112 * 2
def baseEnd_7648112 : Nat := 3927157555419485960326979

theorem tailTrace_7648112 : CollatzResearch.WordTrace tailWord_7648112 prefixEnd_7648112 3927157555419485960326979 := by
  unfold tailWord_7648112
  simp only [CollatzResearch.WordTrace]
  refine ⟨139474780634101946191665295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185966374178802594922220393 139474780634101946191665295)
  ·
    refine ⟨209212170951152919287497943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139474780634101946191665295 209212170951152919287497943)
    ·
      refine ⟨313818256426729378931246915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209212170951152919287497943 313818256426729378931246915)
      ·
        refine ⟨470727384640094068396870373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313818256426729378931246915 470727384640094068396870373)
        ·
          refine ⟨88261384620017637824413195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470727384640094068396870373 88261384620017637824413195)
          ·
            refine ⟨132392076930026456736619793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88261384620017637824413195 132392076930026456736619793)
            ·
              refine ⟨99294057697519842552464845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132392076930026456736619793 99294057697519842552464845)
              ·
                refine ⟨37235271636569940957174317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99294057697519842552464845 37235271636569940957174317)
                ·
                  refine ⟨13963226863713727858940369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37235271636569940957174317 13963226863713727858940369)
                  ·
                    refine ⟨10472420147785295894205277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13963226863713727858940369 10472420147785295894205277)
                    ·
                      refine ⟨3927157555419485960326979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472420147785295894205277 3927157555419485960326979)
                      ·
                        rfl

theorem cell23_7648112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_7648112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648112 prefixEnd_7648112 := by exact prefixLift 7648112
  have htrace : WordTrace (prefixWord ++ tailWord_7648112) baseStart_7648112 baseEnd_7648112 := by
    simpa [prefixWord, tailWord_7648112, baseEnd_7648112] using wordTrace_append hprefix tailTrace_7648112
  have hstable : (prefixWord ++ tailWord_7648112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648112).length < 2 ^ (prefixWord ++ tailWord_7648112).sum := by decide
  have hdescent : baseEnd_7648112 < baseStart_7648112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648130 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7648130 : Nat := 118140960795 + 7648130 * 2 ^ 59
def prefixEnd_7648130 : Nat := 4983230072969 + 3 ^ 40 * 7648130 * 2
def baseEnd_7648130 : Nat := 3927166798071266889901897

theorem tailTrace_7648130 : CollatzResearch.WordTrace tailWord_7648130 prefixEnd_7648130 3927166798071266889901897 := by
  unfold tailWord_7648130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69737554445534670364371461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185966811854759120971657229 69737554445534670364371461)
  ·
    refine ⟨13075791458537750693319649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69737554445534670364371461 13075791458537750693319649)
    ·
      refine ⟨9806843593903313019989737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075791458537750693319649 9806843593903313019989737)
      ·
        refine ⟨7355132695427484764992303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9806843593903313019989737 7355132695427484764992303)
        ·
          refine ⟨11032699043141227147488455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7355132695427484764992303 11032699043141227147488455)
          ·
            refine ⟨16549048564711840721232683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032699043141227147488455 16549048564711840721232683)
            ·
              refine ⟨24823572847067761081849025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16549048564711840721232683 24823572847067761081849025)
              ·
                refine ⟨18617679635300820811386769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24823572847067761081849025 18617679635300820811386769)
                ·
                  refine ⟨13963259726475615608540077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18617679635300820811386769 13963259726475615608540077)
                  ·
                    refine ⟨5236222397428355853202529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13963259726475615608540077 5236222397428355853202529)
                    ·
                      refine ⟨3927166798071266889901897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236222397428355853202529 3927166798071266889901897)
                      ·
                        rfl

theorem cell23_7648130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7648130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648130 prefixEnd_7648130 := by exact prefixLift 7648130
  have htrace : WordTrace (prefixWord ++ tailWord_7648130) baseStart_7648130 baseEnd_7648130 := by
    simpa [prefixWord, tailWord_7648130, baseEnd_7648130] using wordTrace_append hprefix tailTrace_7648130
  have hstable : (prefixWord ++ tailWord_7648130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648130).length < 2 ^ (prefixWord ++ tailWord_7648130).sum := by decide
  have hdescent : baseEnd_7648130 < baseStart_7648130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648145 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_7648145 : Nat := 118140960795 + 7648145 * 2 ^ 59
def prefixEnd_7648145 : Nat := 4983230072969 + 3 ^ 40 * 7648145 * 2
def baseEnd_7648145 : Nat := 1309058166760361443738109

theorem tailTrace_7648145 : CollatzResearch.WordTrace tailWord_7648145 prefixEnd_7648145 1309058166760361443738109 := by
  unfold tailWord_7648145
  simp only [CollatzResearch.WordTrace]
  refine ⟨278950764877084339019281889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185967176584722892679521259 278950764877084339019281889)
  ·
    refine ⟨209213073657813254264461417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278950764877084339019281889 209213073657813254264461417)
    ·
      refine ⟨156909805243359940698346063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209213073657813254264461417 156909805243359940698346063)
      ·
        refine ⟨235364707865039911047519095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156909805243359940698346063 235364707865039911047519095)
        ·
          refine ⟨353047061797559866571278643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235364707865039911047519095 353047061797559866571278643)
          ·
            refine ⟨529570592696339799856917965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353047061797559866571278643 529570592696339799856917965)
            ·
              refine ⟨198588972261127424946344237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529570592696339799856917965 198588972261127424946344237)
              ·
                refine ⟨74470864597922784354879089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198588972261127424946344237 74470864597922784354879089)
                ·
                  refine ⟨55853148448442088266159317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74470864597922784354879089 55853148448442088266159317)
                  ·
                    refine ⟨1309058166760361443738109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55853148448442088266159317 1309058166760361443738109)
                    ·
                      rfl

theorem cell23_7648145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_7648145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648145 prefixEnd_7648145 := by exact prefixLift 7648145
  have htrace : WordTrace (prefixWord ++ tailWord_7648145) baseStart_7648145 baseEnd_7648145 := by
    simpa [prefixWord, tailWord_7648145, baseEnd_7648145] using wordTrace_append hprefix tailTrace_7648145
  have hstable : (prefixWord ++ tailWord_7648145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648145).length < 2 ^ (prefixWord ++ tailWord_7648145).sum := by decide
  have hdescent : baseEnd_7648145 < baseStart_7648145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648165 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7648165 : Nat := 118140960795 + 7648165 * 2 ^ 59
def prefixEnd_7648165 : Nat := 4983230072969 + 3 ^ 40 * 7648165 * 2
def baseEnd_7648165 : Nat := 3927184769894174252964235

theorem tailTrace_7648165 : CollatzResearch.WordTrace tailWord_7648165 prefixEnd_7648165 3927184769894174252964235 := by
  unfold tailWord_7648165
  simp only [CollatzResearch.WordTrace]
  refine ⟨278951494337011882435009949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185967662891341254956673299 278951494337011882435009949)
  ·
    refine ⟨104606810376379455913128731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278951494337011882435009949 104606810376379455913128731)
    ·
      refine ⟨156910215564569183869693097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104606810376379455913128731 156910215564569183869693097)
      ·
        refine ⟨117682661673426887902269823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156910215564569183869693097 117682661673426887902269823)
        ·
          refine ⟨176523992510140331853404735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117682661673426887902269823 176523992510140331853404735)
          ·
            refine ⟨264785988765210497780107103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176523992510140331853404735 264785988765210497780107103)
            ·
              refine ⟨397178983147815746670160655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264785988765210497780107103 397178983147815746670160655)
              ·
                refine ⟨595768474721723620005240983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397178983147815746670160655 595768474721723620005240983)
                ·
                  refine ⟨893652712082585430007861475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595768474721723620005240983 893652712082585430007861475)
                  ·
                    refine ⟨1340479068123878145011792213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 893652712082585430007861475 1340479068123878145011792213)
                    ·
                      refine ⟨3927184769894174252964235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1340479068123878145011792213 3927184769894174252964235)
                      ·
                        rfl

theorem cell23_7648165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7648165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648165 prefixEnd_7648165 := by exact prefixLift 7648165
  have htrace : WordTrace (prefixWord ++ tailWord_7648165) baseStart_7648165 baseEnd_7648165 := by
    simpa [prefixWord, tailWord_7648165, baseEnd_7648165] using wordTrace_append hprefix tailTrace_7648165
  have hstable : (prefixWord ++ tailWord_7648165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648165).length < 2 ^ (prefixWord ++ tailWord_7648165).sum := by decide
  have hdescent : baseEnd_7648165 < baseStart_7648165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648169 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 3, 3, 2]
def baseStart_7648169 : Nat := 118140960795 + 7648169 * 2 ^ 59
def prefixEnd_7648169 : Nat := 4983230072969 + 3 ^ 40 * 7648169 * 2
def baseEnd_7648169 : Nat := 3927186823816792237314217

theorem tailTrace_7648169 : CollatzResearch.WordTrace tailWord_7648169 prefixEnd_7648169 3927186823816792237314217 := by
  unfold tailWord_7648169
  simp only [CollatzResearch.WordTrace]
  refine ⟨278951640228997391118155561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185967760152664927412103707 278951640228997391118155561)
  ·
    refine ⟨209213730171748043338616671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278951640228997391118155561 209213730171748043338616671)
    ·
      refine ⟨313820595257622065007925007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209213730171748043338616671 313820595257622065007925007)
      ·
        refine ⟨470730892886433097511887511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313820595257622065007925007 470730892886433097511887511)
        ·
          refine ⟨706096339329649646267831267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470730892886433097511887511 706096339329649646267831267)
          ·
            refine ⟨1059144508994474469401746901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706096339329649646267831267 1059144508994474469401746901)
            ·
              refine ⟨24823699429557995376603443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1059144508994474469401746901 24823699429557995376603443)
              ·
                refine ⟨37235549144336993064905165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24823699429557995376603443 37235549144336993064905165)
                ·
                  refine ⟨13963330929126372399339437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37235549144336993064905165 13963330929126372399339437)
                  ·
                    refine ⟨5236249098422389649752289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13963330929126372399339437 5236249098422389649752289)
                    ·
                      refine ⟨3927186823816792237314217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236249098422389649752289 3927186823816792237314217)
                      ·
                        rfl

theorem cell23_7648169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 3, 2].length) (baseStart_7648169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648169 prefixEnd_7648169 := by exact prefixLift 7648169
  have htrace : WordTrace (prefixWord ++ tailWord_7648169) baseStart_7648169 baseEnd_7648169 := by
    simpa [prefixWord, tailWord_7648169, baseEnd_7648169] using wordTrace_append hprefix tailTrace_7648169
  have hstable : (prefixWord ++ tailWord_7648169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648169).length < 2 ^ (prefixWord ++ tailWord_7648169).sum := by decide
  have hdescent : baseEnd_7648169 < baseStart_7648169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648175 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 8]
def baseStart_7648175 : Nat := 118140960795 + 7648175 * 2 ^ 59
def prefixEnd_7648175 : Nat := 4983230072969 + 3 ^ 40 * 7648175 * 2
def baseEnd_7648175 : Nat := 1309063301566906404613063

theorem tailTrace_7648175 : CollatzResearch.WordTrace tailWord_7648175 prefixEnd_7648175 1309063301566906404613063 := by
  unfold tailWord_7648175
  simp only [CollatzResearch.WordTrace]
  refine ⟨278951859066975654142873979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185967906044650436095249319 278951859066975654142873979)
  ·
    refine ⟨418427788600463481214310969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278951859066975654142873979 418427788600463481214310969)
    ·
      refine ⟨313820841450347610910733227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418427788600463481214310969 313820841450347610910733227)
      ·
        refine ⟨470731262175521416366099841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313820841450347610910733227 470731262175521416366099841)
        ·
          refine ⟨353048446631641062274574881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470731262175521416366099841 353048446631641062274574881)
          ·
            refine ⟨264786334973730796705931161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353048446631641062274574881 264786334973730796705931161)
            ·
              refine ⟨198589751230298097529448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264786334973730796705931161 198589751230298097529448371)
              ·
                refine ⟨297884626845447146294172557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198589751230298097529448371 297884626845447146294172557)
                ·
                  refine ⟨111706735067042679860314709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297884626845447146294172557 111706735067042679860314709)
                  ·
                    refine ⟨1309063301566906404613063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111706735067042679860314709 1309063301566906404613063)
                    ·
                      rfl

theorem cell23_7648175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_7648175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648175 prefixEnd_7648175 := by exact prefixLift 7648175
  have htrace : WordTrace (prefixWord ++ tailWord_7648175) baseStart_7648175 baseEnd_7648175 := by
    simpa [prefixWord, tailWord_7648175, baseEnd_7648175] using wordTrace_append hprefix tailTrace_7648175
  have hstable : (prefixWord ++ tailWord_7648175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648175).length < 2 ^ (prefixWord ++ tailWord_7648175).sum := by decide
  have hdescent : baseEnd_7648175 < baseStart_7648175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648180 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7648180 : Nat := 118140960795 + 7648180 * 2 ^ 59
def prefixEnd_7648180 : Nat := 4983230072969 + 3 ^ 40 * 7648180 * 2
def baseEnd_7648180 : Nat := 3927192472103991694276667

theorem tailTrace_7648180 : CollatzResearch.WordTrace tailWord_7648180 prefixEnd_7648180 3927192472103991694276667 := by
  unfold tailWord_7648180
  simp only [CollatzResearch.WordTrace]
  refine ⟨139476020715978769998402997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185968027621305026664537329 139476020715978769998402997)
  ·
    refine ⟨13075876942123009687350281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139476020715978769998402997 13075876942123009687350281)
    ·
      refine ⟨9806907706592257265512711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13075876942123009687350281 9806907706592257265512711)
      ·
        refine ⟨14710361559888385898269067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9806907706592257265512711 14710361559888385898269067)
        ·
          refine ⟨22065542339832578847403601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14710361559888385898269067 22065542339832578847403601)
          ·
            refine ⟨16549156754874434135552701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22065542339832578847403601 16549156754874434135552701)
            ·
              refine ⟨6205933783077912800832263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16549156754874434135552701 6205933783077912800832263)
              ·
                refine ⟨9308900674616869201248395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205933783077912800832263 9308900674616869201248395)
                ·
                  refine ⟨13963351011925303801872593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9308900674616869201248395 13963351011925303801872593)
                  ·
                    refine ⟨10472513258943977851404445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13963351011925303801872593 10472513258943977851404445)
                    ·
                      refine ⟨3927192472103991694276667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10472513258943977851404445 3927192472103991694276667)
                      ·
                        rfl

theorem cell23_7648180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7648180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648180 prefixEnd_7648180 := by exact prefixLift 7648180
  have htrace : WordTrace (prefixWord ++ tailWord_7648180) baseStart_7648180 baseEnd_7648180 := by
    simpa [prefixWord, tailWord_7648180, baseEnd_7648180] using wordTrace_append hprefix tailTrace_7648180
  have hstable : (prefixWord ++ tailWord_7648180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648180).length < 2 ^ (prefixWord ++ tailWord_7648180).sum := by decide
  have hdescent : baseEnd_7648180 < baseStart_7648180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648216 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_7648216 : Nat := 118140960795 + 7648216 * 2 ^ 59
def prefixEnd_7648216 : Nat := 4983230072969 + 3 ^ 40 * 7648216 * 2
def baseEnd_7648216 : Nat := 3927210957407553553426501

theorem tailTrace_7648216 : CollatzResearch.WordTrace tailWord_7648216 prefixEnd_7648216 3927210957407553553426501 := by
  unfold tailWord_7648216
  simp only [CollatzResearch.WordTrace]
  refine ⟨139476677229913559072558251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185968902973218078763411001 139476677229913559072558251)
  ·
    refine ⟨209215015844870338608837377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139476677229913559072558251 209215015844870338608837377)
    ·
      refine ⟨156911261883652753956628033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209215015844870338608837377 156911261883652753956628033)
      ·
        refine ⟨117683446412739565467471025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156911261883652753956628033 117683446412739565467471025)
        ·
          refine ⟨88262584809554674100603269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117683446412739565467471025 88262584809554674100603269)
          ·
            refine ⟨16549234651791501393863113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88262584809554674100603269 16549234651791501393863113)
            ·
              refine ⟨12411925988843626045397335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16549234651791501393863113 12411925988843626045397335)
              ·
                refine ⟨18617888983265439068096003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12411925988843626045397335 18617888983265439068096003)
                ·
                  refine ⟨27926833474898158602144005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18617888983265439068096003 27926833474898158602144005)
                  ·
                    refine ⟨5236281276543404737902001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27926833474898158602144005 5236281276543404737902001)
                    ·
                      refine ⟨3927210957407553553426501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236281276543404737902001 3927210957407553553426501)
                      ·
                        rfl

theorem cell23_7648216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_7648216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648216 prefixEnd_7648216 := by exact prefixLift 7648216
  have htrace : WordTrace (prefixWord ++ tailWord_7648216) baseStart_7648216 baseEnd_7648216 := by
    simpa [prefixWord, tailWord_7648216, baseEnd_7648216] using wordTrace_append hprefix tailTrace_7648216
  have hstable : (prefixWord ++ tailWord_7648216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648216).length < 2 ^ (prefixWord ++ tailWord_7648216).sum := by decide
  have hdescent : baseEnd_7648216 < baseStart_7648216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648239 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 5]
def baseStart_7648239 : Nat := 118140960795 + 7648239 * 2 ^ 59
def prefixEnd_7648239 : Nat := 4983230072969 + 3 ^ 40 * 7648239 * 2
def baseEnd_7648239 : Nat := 436358085273622995937655

theorem tailTrace_7648239 : CollatzResearch.WordTrace tailWord_7648239 prefixEnd_7648239 436358085273622995937655 := by
  unfold tailWord_7648239
  simp only [CollatzResearch.WordTrace]
  refine ⟨278954193338743793073203771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185969462225829195382135847 278954193338743793073203771)
  ·
    refine ⟨418431290008115689609805657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278954193338743793073203771 418431290008115689609805657)
    ·
      refine ⟨313823467506086767207354243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418431290008115689609805657 313823467506086767207354243)
      ·
        refine ⟨470735201259130150811031365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313823467506086767207354243 470735201259130150811031365)
        ·
          refine ⟨88262850236086903277068381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470735201259130150811031365 88262850236086903277068381)
          ·
            refine ⟨33098568838532588728900643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88262850236086903277068381 33098568838532588728900643)
            ·
              refine ⟨49647853257798883093350965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33098568838532588728900643 49647853257798883093350965)
              ·
                refine ⟨4654486242918645290001653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49647853257798883093350965 4654486242918645290001653)
                ·
                  refine ⟨436358085273622995937655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654486242918645290001653 436358085273622995937655)
                  ·
                    rfl

theorem cell23_7648239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 5].length) (baseStart_7648239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648239 prefixEnd_7648239 := by exact prefixLift 7648239
  have htrace : WordTrace (prefixWord ++ tailWord_7648239) baseStart_7648239 baseEnd_7648239 := by
    simpa [prefixWord, tailWord_7648239, baseEnd_7648239] using wordTrace_append hprefix tailTrace_7648239
  have hstable : (prefixWord ++ tailWord_7648239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648239).length < 2 ^ (prefixWord ++ tailWord_7648239).sum := by decide
  have hdescent : baseEnd_7648239 < baseStart_7648239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648282 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_7648282 : Nat := 118140960795 + 7648282 * 2 ^ 59
def prefixEnd_7648282 : Nat := 4983230072969 + 3 ^ 40 * 7648282 * 2
def baseEnd_7648282 : Nat := 1309081615710250098400399

theorem tailTrace_7648282 : CollatzResearch.WordTrace tailWord_7648282 prefixEnd_7648282 1309081615710250098400399 := by
  unfold tailWord_7648282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69738940419397002854254775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185970507785058674278012733 69738940419397002854254775)
  ·
    refine ⟨104608410629095504281382163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69738940419397002854254775 104608410629095504281382163)
    ·
      refine ⟨156912615943643256422073245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104608410629095504281382163 156912615943643256422073245)
      ·
        refine ⟨58842230978866221158277467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156912615943643256422073245 58842230978866221158277467)
        ·
          refine ⟨88263346468299331737416201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58842230978866221158277467 88263346468299331737416201)
          ·
            refine ⟨66197509851224498803062151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88263346468299331737416201 66197509851224498803062151)
            ·
              refine ⟨99296264776836748204593227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66197509851224498803062151 99296264776836748204593227)
              ·
                refine ⟨148944397165255122306889841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99296264776836748204593227 148944397165255122306889841)
                ·
                  refine ⟨111708297873941341730167381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148944397165255122306889841 111708297873941341730167381)
                  ·
                    refine ⟨1309081615710250098400399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111708297873941341730167381 1309081615710250098400399)
                    ·
                      rfl

theorem cell23_7648282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_7648282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648282 prefixEnd_7648282 := by exact prefixLift 7648282
  have htrace : WordTrace (prefixWord ++ tailWord_7648282) baseStart_7648282 baseEnd_7648282 := by
    simpa [prefixWord, tailWord_7648282, baseEnd_7648282] using wordTrace_append hprefix tailTrace_7648282
  have hstable : (prefixWord ++ tailWord_7648282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648282).length < 2 ^ (prefixWord ++ tailWord_7648282).sum := by decide
  have hdescent : baseEnd_7648282 < baseStart_7648282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648289 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7648289 : Nat := 118140960795 + 7648289 * 2 ^ 59
def prefixEnd_7648289 : Nat := 4983230072969 + 3 ^ 40 * 7648289 * 2
def baseEnd_7648289 : Nat := 3927248441495331767813665

theorem tailTrace_7648289 : CollatzResearch.WordTrace tailWord_7648289 prefixEnd_7648289 3927248441495331767813665 := by
  unfold tailWord_7648289
  simp only [CollatzResearch.WordTrace]
  refine ⟨278956016988562651612523921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185970677992375101075015947 278956016988562651612523921)
  ·
    refine ⟨209217012741421988709392941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278956016988562651612523921 209217012741421988709392941)
    ·
      refine ⟨78456379778033245766022353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209217012741421988709392941 78456379778033245766022353)
      ·
        refine ⟨58842284833524934324516765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78456379778033245766022353 58842284833524934324516765)
        ·
          refine ⟨22065856812571850371693787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58842284833524934324516765 22065856812571850371693787)
          ·
            refine ⟨33098785218857775557540681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22065856812571850371693787 33098785218857775557540681)
            ·
              refine ⟨24824088914143331668155511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33098785218857775557540681 24824088914143331668155511)
              ·
                refine ⟨37236133371214997502233267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24824088914143331668155511 37236133371214997502233267)
                ·
                  refine ⟨55854200056822496253349901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37236133371214997502233267 55854200056822496253349901)
                  ·
                    refine ⟨20945325021308436095006213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55854200056822496253349901 20945325021308436095006213)
                    ·
                      refine ⟨3927248441495331767813665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20945325021308436095006213 3927248441495331767813665)
                      ·
                        rfl

theorem cell23_7648289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7648289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648289 prefixEnd_7648289 := by exact prefixLift 7648289
  have htrace : WordTrace (prefixWord ++ tailWord_7648289) baseStart_7648289 baseEnd_7648289 := by
    simpa [prefixWord, tailWord_7648289, baseEnd_7648289] using wordTrace_append hprefix tailTrace_7648289
  have hstable : (prefixWord ++ tailWord_7648289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648289).length < 2 ^ (prefixWord ++ tailWord_7648289).sum := by decide
  have hdescent : baseEnd_7648289 < baseStart_7648289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648316 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_7648316 : Nat := 118140960795 + 7648316 * 2 ^ 59
def prefixEnd_7648316 : Nat := 4983230072969 + 3 ^ 40 * 7648316 * 2
def baseEnd_7648316 : Nat := 1309087435157667720725347

theorem tailTrace_7648316 : CollatzResearch.WordTrace tailWord_7648316 prefixEnd_7648316 1309087435157667720725347 := by
  unfold tailWord_7648316
  simp only [CollatzResearch.WordTrace]
  refine ⟨139478500879732417611878401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185971334506309890149171201 139478500879732417611878401)
  ·
    refine ⟨104608875659799313208908801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139478500879732417611878401 104608875659799313208908801)
    ·
      refine ⟨78456656744849484906681601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104608875659799313208908801 78456656744849484906681601)
      ·
        refine ⟨58842492558637113680011201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78456656744849484906681601 58842492558637113680011201)
        ·
          refine ⟨44131869418977835260008401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58842492558637113680011201 44131869418977835260008401)
          ·
            refine ⟨33098902064233376445006301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44131869418977835260008401 33098902064233376445006301)
            ·
              refine ⟨12412088274087516166877363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33098902064233376445006301 12412088274087516166877363)
              ·
                refine ⟨18618132411131274250316045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412088274087516166877363 18618132411131274250316045)
                ·
                  refine ⟨6981799654174227843868517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18618132411131274250316045 6981799654174227843868517)
                  ·
                    refine ⟨1309087435157667720725347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6981799654174227843868517 1309087435157667720725347)
                    ·
                      rfl

theorem cell23_7648316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_7648316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648316 prefixEnd_7648316 := by exact prefixLift 7648316
  have htrace : WordTrace (prefixWord ++ tailWord_7648316) baseStart_7648316 baseEnd_7648316 := by
    simpa [prefixWord, tailWord_7648316, baseEnd_7648316] using wordTrace_append hprefix tailTrace_7648316
  have hstable : (prefixWord ++ tailWord_7648316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648316).length < 2 ^ (prefixWord ++ tailWord_7648316).sum := by decide
  have hdescent : baseEnd_7648316 < baseStart_7648316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648410 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_7648410 : Nat := 118140960795 + 7648410 * 2 ^ 59
def prefixEnd_7648410 : Nat := 4983230072969 + 3 ^ 40 * 7648410 * 2
def baseEnd_7648410 : Nat := 1309103524218175264800203

theorem tailTrace_7648410 : CollatzResearch.WordTrace tailWord_7648410 prefixEnd_7648410 1309103524218175264800203 := by
  unfold tailWord_7648410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69740107555281072319419671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185973620147416192851785789 69740107555281072319419671)
  ·
    refine ⟨104610161332921608479129507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69740107555281072319419671 104610161332921608479129507)
    ·
      refine ⟨156915241999382412718694261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104610161332921608479129507 156915241999382412718694261)
      ·
        refine ⟨14710803937442101192377587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156915241999382412718694261 14710803937442101192377587)
        ·
          refine ⟨22066205906163151788566381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14710803937442101192377587 22066205906163151788566381)
          ·
            refine ⟨8274827214811181920712393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22066205906163151788566381 8274827214811181920712393)
            ·
              refine ⟨6206120411108386440534295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8274827214811181920712393 6206120411108386440534295)
              ·
                refine ⟨9309180616662579660801443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206120411108386440534295 9309180616662579660801443)
                ·
                  refine ⟨13963770924993869491202165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309180616662579660801443 13963770924993869491202165)
                  ·
                    refine ⟨1309103524218175264800203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13963770924993869491202165 1309103524218175264800203)
                    ·
                      rfl

theorem cell23_7648410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_7648410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648410 prefixEnd_7648410 := by exact prefixLift 7648410
  have htrace : WordTrace (prefixWord ++ tailWord_7648410) baseStart_7648410 baseEnd_7648410 := by
    simpa [prefixWord, tailWord_7648410, baseEnd_7648410] using wordTrace_append hprefix tailTrace_7648410
  have hstable : (prefixWord ++ tailWord_7648410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648410).length < 2 ^ (prefixWord ++ tailWord_7648410).sum := by decide
  have hdescent : baseEnd_7648410 < baseStart_7648410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648413 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_7648413 : Nat := 118140960795 + 7648413 * 2 ^ 59
def prefixEnd_7648413 : Nat := 4983230072969 + 3 ^ 40 * 7648413 * 2
def baseEnd_7648413 : Nat := 3927312113096489282663095

theorem tailTrace_7648413 : CollatzResearch.WordTrace tailWord_7648413 prefixEnd_7648413 3927312113096489282663095 := by
  unfold tailWord_7648413
  simp only [CollatzResearch.WordTrace]
  refine ⟨278960539640113420790037893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185973693093408947193358595 278960539640113420790037893)
  ·
    refine ⟨52305101182521266398132105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278960539640113420790037893 52305101182521266398132105)
    ·
      refine ⟨39228825886890949798599079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52305101182521266398132105 39228825886890949798599079)
      ·
        refine ⟨58843238830336424697898619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39228825886890949798599079 58843238830336424697898619)
        ·
          refine ⟨88264858245504637046847929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58843238830336424697898619 88264858245504637046847929)
          ·
            refine ⟨66198643684128477785135947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88264858245504637046847929 66198643684128477785135947)
            ·
              refine ⟨99297965526192716677703921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66198643684128477785135947 99297965526192716677703921)
              ·
                refine ⟨74473474144644537508277941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99297965526192716677703921 74473474144644537508277941)
                ·
                  refine ⟨6981888201060425391401057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74473474144644537508277941 6981888201060425391401057)
                  ·
                    refine ⟨5236416150795319043550793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6981888201060425391401057 5236416150795319043550793)
                    ·
                      refine ⟨3927312113096489282663095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236416150795319043550793 3927312113096489282663095)
                      ·
                        rfl

theorem cell23_7648413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_7648413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648413 prefixEnd_7648413 := by exact prefixLift 7648413
  have htrace : WordTrace (prefixWord ++ tailWord_7648413) baseStart_7648413 baseEnd_7648413 := by
    simpa [prefixWord, tailWord_7648413, baseEnd_7648413] using wordTrace_append hprefix tailTrace_7648413
  have hstable : (prefixWord ++ tailWord_7648413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648413).length < 2 ^ (prefixWord ++ tailWord_7648413).sum := by decide
  have hdescent : baseEnd_7648413 < baseStart_7648413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648423 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 4, 4]
def baseStart_7648423 : Nat := 118140960795 + 7648423 * 2 ^ 59
def prefixEnd_7648423 : Nat := 4983230072969 + 3 ^ 40 * 7648423 * 2
def baseEnd_7648423 : Nat := 1309105749301011414512683

theorem tailTrace_7648423 : CollatzResearch.WordTrace tailWord_7648423 prefixEnd_7648423 1309105749301011414512683 := by
  unfold tailWord_7648423
  simp only [CollatzResearch.WordTrace]
  refine ⟨278960904370077192497901923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185973936246718128331934615 278960904370077192497901923)
  ·
    refine ⟨418441356555115788746852885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278960904370077192497901923 418441356555115788746852885)
    ·
      refine ⟨19614438588521052597508729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418441356555115788746852885 19614438588521052597508729)
      ·
        refine ⟨14710828941390789448131547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19614438588521052597508729 14710828941390789448131547)
        ·
          refine ⟨22066243412086184172197321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14710828941390789448131547 22066243412086184172197321)
          ·
            refine ⟨16549682559064638129147991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22066243412086184172197321 16549682559064638129147991)
            ·
              refine ⟨24824523838596957193721987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16549682559064638129147991 24824523838596957193721987)
              ·
                refine ⟨37236785757895435790582981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24824523838596957193721987 37236785757895435790582981)
                ·
                  refine ⟨6981897329605394210734309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37236785757895435790582981 6981897329605394210734309)
                  ·
                    refine ⟨1309105749301011414512683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6981897329605394210734309 1309105749301011414512683)
                    ·
                      rfl

theorem cell23_7648423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_7648423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648423 prefixEnd_7648423 := by exact prefixLift 7648423
  have htrace : WordTrace (prefixWord ++ tailWord_7648423) baseStart_7648423 baseEnd_7648423 := by
    simpa [prefixWord, tailWord_7648423, baseEnd_7648423] using wordTrace_append hprefix tailTrace_7648423
  have hstable : (prefixWord ++ tailWord_7648423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648423).length < 2 ^ (prefixWord ++ tailWord_7648423).sum := by decide
  have hdescent : baseEnd_7648423 < baseStart_7648423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648470 : List Nat := [5, 2, 1, 2, 3, 1, 9]
def baseStart_7648470 : Nat := 118140960795 + 7648470 * 2 ^ 59
def prefixEnd_7648470 : Nat := 4983230072969 + 3 ^ 40 * 7648470 * 2
def baseEnd_7648470 : Nat := 48485696067824636538893

theorem tailTrace_7648470 : CollatzResearch.WordTrace tailWord_7648470 prefixEnd_7648470 48485696067824636538893 := by
  unfold tailWord_7648470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17435163662556682470303929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185975079067271279683241909 17435163662556682470303929)
  ·
    refine ⟨13076372746917511852727947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17435163662556682470303929 13076372746917511852727947)
    ·
      refine ⟨19614559120376267779091921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13076372746917511852727947 19614559120376267779091921)
      ·
        refine ⟨14710919340282200834318941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19614559120376267779091921 14710919340282200834318941)
        ·
          refine ⟨5516594752605825312869603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14710919340282200834318941 5516594752605825312869603)
          ·
            refine ⟨8274892128908737969304405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516594752605825312869603 8274892128908737969304405)
            ·
              refine ⟨48485696067824636538893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8274892128908737969304405 48485696067824636538893)
              ·
                rfl

theorem cell23_7648470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 9].length) (baseStart_7648470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648470 prefixEnd_7648470 := by exact prefixLift 7648470
  have htrace : WordTrace (prefixWord ++ tailWord_7648470) baseStart_7648470 baseEnd_7648470 := by
    simpa [prefixWord, tailWord_7648470, baseEnd_7648470] using wordTrace_append hprefix tailTrace_7648470
  have hstable : (prefixWord ++ tailWord_7648470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648470).length < 2 ^ (prefixWord ++ tailWord_7648470).sum := by decide
  have hdescent : baseEnd_7648470 < baseStart_7648470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648479 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 4, 6]
def baseStart_7648479 : Nat := 118140960795 + 7648479 * 2 ^ 59
def prefixEnd_7648479 : Nat := 4983230072969 + 3 ^ 40 * 7648479 * 2
def baseEnd_7648479 : Nat := 1309115334273228674812597

theorem tailTrace_7648479 : CollatzResearch.WordTrace tailWord_7648479 prefixEnd_7648479 1309115334273228674812597 := by
  unfold tailWord_7648479
  simp only [CollatzResearch.WordTrace]
  refine ⟨278962946857874314061940491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185975297905249542707960327 278962946857874314061940491)
  ·
    refine ⟨418444420286811471092910737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278962946857874314061940491 418444420286811471092910737)
    ·
      refine ⟨313833315215108603319683053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418444420286811471092910737 313833315215108603319683053)
      ·
        refine ⟨117687493205665726244881145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313833315215108603319683053 117687493205665726244881145)
        ·
          refine ⟨88265619904249294683660859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117687493205665726244881145 88265619904249294683660859)
          ·
            refine ⟨132398429856373942025491289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88265619904249294683660859 132398429856373942025491289)
            ·
              refine ⟨99298822392280456519118467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132398429856373942025491289 99298822392280456519118467)
              ·
                refine ⟨148948233588420684778677701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99298822392280456519118467 148948233588420684778677701)
                ·
                  refine ⟨27927793797828878396002069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148948233588420684778677701 27927793797828878396002069)
                  ·
                    refine ⟨1309115334273228674812597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27927793797828878396002069 1309115334273228674812597)
                    ·
                      rfl

theorem cell23_7648479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_7648479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648479 prefixEnd_7648479 := by exact prefixLift 7648479
  have htrace : WordTrace (prefixWord ++ tailWord_7648479) baseStart_7648479 baseEnd_7648479 := by
    simpa [prefixWord, tailWord_7648479, baseEnd_7648479] using wordTrace_append hprefix tailTrace_7648479
  have hstable : (prefixWord ++ tailWord_7648479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648479).length < 2 ^ (prefixWord ++ tailWord_7648479).sum := by decide
  have hdescent : baseEnd_7648479 < baseStart_7648479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648489 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_7648489 : Nat := 118140960795 + 7648489 * 2 ^ 59
def prefixEnd_7648489 : Nat := 4983230072969 + 3 ^ 40 * 7648489 * 2
def baseEnd_7648489 : Nat := 3927351137626230985312745

theorem tailTrace_7648489 : CollatzResearch.WordTrace tailWord_7648489 prefixEnd_7648489 3927351137626230985312745 := by
  unfold tailWord_7648489
  simp only [CollatzResearch.WordTrace]
  refine ⟨278963311587838085769804521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185975541058558723846536347 278963311587838085769804521)
  ·
    refine ⟨209222483690878564327353391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278963311587838085769804521 209222483690878564327353391)
    ·
      refine ⟨313833725536317846491030087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209222483690878564327353391 313833725536317846491030087)
      ·
        refine ⟨470750588304476769736545131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313833725536317846491030087 470750588304476769736545131)
        ·
          refine ⟨706125882456715154604817697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470750588304476769736545131 706125882456715154604817697)
          ·
            refine ⟨529594411842536365953613273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706125882456715154604817697 529594411842536365953613273)
            ·
              refine ⟨397195808881902274465209955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529594411842536365953613273 397195808881902274465209955)
              ·
                refine ⟨595793713322853411697814933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397195808881902274465209955 595793713322853411697814933)
                ·
                  refine ⟨27927830312008753673335075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 595793713322853411697814933 27927830312008753673335075)
                  ·
                    refine ⟨41891745468013130510002613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27927830312008753673335075 41891745468013130510002613)
                    ·
                      refine ⟨3927351137626230985312745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41891745468013130510002613 3927351137626230985312745)
                      ·
                        rfl

theorem cell23_7648489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_7648489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648489 prefixEnd_7648489 := by exact prefixLift 7648489
  have htrace : WordTrace (prefixWord ++ tailWord_7648489) baseStart_7648489 baseEnd_7648489 := by
    simpa [prefixWord, tailWord_7648489, baseEnd_7648489] using wordTrace_append hprefix tailTrace_7648489
  have hstable : (prefixWord ++ tailWord_7648489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648489).length < 2 ^ (prefixWord ++ tailWord_7648489).sum := by decide
  have hdescent : baseEnd_7648489 < baseStart_7648489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648520 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_7648520 : Nat := 118140960795 + 7648520 * 2 ^ 59
def prefixEnd_7648520 : Nat := 4983230072969 + 3 ^ 40 * 7648520 * 2
def baseEnd_7648520 : Nat := 3927367055526520364025103

theorem tailTrace_7648520 : CollatzResearch.WordTrace tailWord_7648520 prefixEnd_7648520 3927367055526520364025103 := by
  unfold tailWord_7648520
  simp only [CollatzResearch.WordTrace]
  refine ⟨139482221125362889032091507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185976294833817185376122009 139482221125362889032091507)
  ·
    refine ⟨209223331688044333548137261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139482221125362889032091507 209223331688044333548137261)
    ·
      refine ⟨78458749383016625080551473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209223331688044333548137261 78458749383016625080551473)
      ·
        refine ⟨58844062037262468810413605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78458749383016625080551473 58844062037262468810413605)
        ·
          refine ⟨11033261631986712901952551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58844062037262468810413605 11033261631986712901952551)
          ·
            refine ⟨16549892447980069352928827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11033261631986712901952551 16549892447980069352928827)
            ·
              refine ⟨24824838671970104029393241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16549892447980069352928827 24824838671970104029393241)
              ·
                refine ⟨18618629003977578022044931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24824838671970104029393241 18618629003977578022044931)
                ·
                  refine ⟨27927943505966367033067397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18618629003977578022044931 27927943505966367033067397)
                  ·
                    refine ⟨5236489407368693818700137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27927943505966367033067397 5236489407368693818700137)
                    ·
                      refine ⟨3927367055526520364025103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236489407368693818700137 3927367055526520364025103)
                      ·
                        rfl

theorem cell23_7648520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_7648520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648520 prefixEnd_7648520 := by exact prefixLift 7648520
  have htrace : WordTrace (prefixWord ++ tailWord_7648520) baseStart_7648520 baseEnd_7648520 := by
    simpa [prefixWord, tailWord_7648520, baseEnd_7648520] using wordTrace_append hprefix tailTrace_7648520
  have hstable : (prefixWord ++ tailWord_7648520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648520).length < 2 ^ (prefixWord ++ tailWord_7648520).sum := by decide
  have hdescent : baseEnd_7648520 < baseStart_7648520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648539 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 7]
def baseStart_7648539 : Nat := 118140960795 + 7648539 * 2 ^ 59
def prefixEnd_7648539 : Nat := 4983230072969 + 3 ^ 40 * 7648539 * 2
def baseEnd_7648539 : Nat := 1309125603886318596562505

theorem tailTrace_7648539 : CollatzResearch.WordTrace tailWord_7648539 prefixEnd_7648539 1309125603886318596562505 := by
  unfold tailWord_7648539
  simp only [CollatzResearch.WordTrace]
  refine ⟨278965135237656944309124671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185976756825104629539416447 278965135237656944309124671)
  ·
    refine ⟨418447702856485416463687007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278965135237656944309124671 418447702856485416463687007)
    ·
      refine ⟨627671554284728124695530511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418447702856485416463687007 627671554284728124695530511)
      ·
        refine ⟨941507331427092187043295767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627671554284728124695530511 941507331427092187043295767)
        ·
          refine ⟨1412260997140638280564943651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941507331427092187043295767 1412260997140638280564943651)
          ·
            refine ⟨2118391495710957420847415477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412260997140638280564943651 2118391495710957420847415477)
            ·
              refine ⟨198599202722902258204445201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2118391495710957420847415477 198599202722902258204445201)
              ·
                refine ⟨148949402042176693653333901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198599202722902258204445201 148949402042176693653333901)
                ·
                  refine ⟨55856025765816260120000213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148949402042176693653333901 55856025765816260120000213)
                  ·
                    refine ⟨1309125603886318596562505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55856025765816260120000213 1309125603886318596562505)
                    ·
                      rfl

theorem cell23_7648539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_7648539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648539 prefixEnd_7648539 := by exact prefixLift 7648539
  have htrace : WordTrace (prefixWord ++ tailWord_7648539) baseStart_7648539 baseEnd_7648539 := by
    simpa [prefixWord, tailWord_7648539, baseEnd_7648539] using wordTrace_append hprefix tailTrace_7648539
  have hstable : (prefixWord ++ tailWord_7648539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648539).length < 2 ^ (prefixWord ++ tailWord_7648539).sum := by decide
  have hdescent : baseEnd_7648539 < baseStart_7648539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648576 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_7648576 : Nat := 118140960795 + 7648576 * 2 ^ 59
def prefixEnd_7648576 : Nat := 4983230072969 + 3 ^ 40 * 7648576 * 2
def baseEnd_7648576 : Nat := 3927395810443172144924845

theorem tailTrace_7648576 : CollatzResearch.WordTrace tailWord_7648576 prefixEnd_7648576 3927395810443172144924845 := by
  unfold tailWord_7648576
  simp only [CollatzResearch.WordTrace]
  refine ⟨139483242369261449814110791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185977656492348599752147721 139483242369261449814110791)
  ·
    refine ⟨209224863553892174721166187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139483242369261449814110791 209224863553892174721166187)
    ·
      refine ⟨313837295330838262081749281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209224863553892174721166187 313837295330838262081749281)
      ·
        refine ⟨235377971498128696561311961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313837295330838262081749281 235377971498128696561311961)
        ·
          refine ⟨176533478623596522420983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235377971498128696561311961 176533478623596522420983971)
          ·
            refine ⟨264800217935394783631475957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176533478623596522420983971 264800217935394783631475957)
            ·
              refine ⟨24825020431443260965450871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264800217935394783631475957 24825020431443260965450871)
              ·
                refine ⟨37237530647164891448176307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24825020431443260965450871 37237530647164891448176307)
                ·
                  refine ⟨55856295970747337172264461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37237530647164891448176307 55856295970747337172264461)
                  ·
                    refine ⟨20946110989030251439599173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55856295970747337172264461 20946110989030251439599173)
                    ·
                      refine ⟨3927395810443172144924845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20946110989030251439599173 3927395810443172144924845)
                      ·
                        rfl

theorem cell23_7648576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_7648576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648576 prefixEnd_7648576 := by exact prefixLift 7648576
  have htrace : WordTrace (prefixWord ++ tailWord_7648576) baseStart_7648576 baseEnd_7648576 := by
    simpa [prefixWord, tailWord_7648576, baseEnd_7648576] using wordTrace_append hprefix tailTrace_7648576
  have hstable : (prefixWord ++ tailWord_7648576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648576).length < 2 ^ (prefixWord ++ tailWord_7648576).sum := by decide
  have hdescent : baseEnd_7648576 < baseStart_7648576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648593 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_7648593 : Nat := 118140960795 + 7648593 * 2 ^ 59
def prefixEnd_7648593 : Nat := 4983230072969 + 3 ^ 40 * 7648593 * 2
def baseEnd_7648593 : Nat := 3927404539614298578412267

theorem tailTrace_7648593 : CollatzResearch.WordTrace tailWord_7648593 prefixEnd_7648593 3927404539614298578412267 := by
  unfold tailWord_7648593
  simp only [CollatzResearch.WordTrace]
  refine ⟨278967104779461311531590433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185978069852974207687726955 278967104779461311531590433)
  ·
    refine ⟨209225328584595983648692825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278967104779461311531590433 209225328584595983648692825)
    ·
      refine ⟨156918996438446987736519619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209225328584595983648692825 156918996438446987736519619)
      ·
        refine ⟨235378494657670481604779429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156918996438446987736519619 235378494657670481604779429)
        ·
          refine ⟨44133467748313215300896143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235378494657670481604779429 44133467748313215300896143)
          ·
            refine ⟨66200201622469822951344215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44133467748313215300896143 66200201622469822951344215)
            ·
              refine ⟨99300302433704734427016323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66200201622469822951344215 99300302433704734427016323)
              ·
                refine ⟨148950453650557101640524485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99300302433704734427016323 148950453650557101640524485)
                ·
                  refine ⟨27928210059479456557598341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148950453650557101640524485 27928210059479456557598341)
                  ·
                    refine ⟨5236539386152398104549689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27928210059479456557598341 5236539386152398104549689)
                    ·
                      refine ⟨3927404539614298578412267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236539386152398104549689 3927404539614298578412267)
                      ·
                        rfl

theorem cell23_7648593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_7648593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648593 prefixEnd_7648593 := by exact prefixLift 7648593
  have htrace : WordTrace (prefixWord ++ tailWord_7648593) baseStart_7648593 baseEnd_7648593 := by
    simpa [prefixWord, tailWord_7648593, baseEnd_7648593] using wordTrace_append hprefix tailTrace_7648593
  have hstable : (prefixWord ++ tailWord_7648593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648593).length < 2 ^ (prefixWord ++ tailWord_7648593).sum := by decide
  have hdescent : baseEnd_7648593 < baseStart_7648593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648610 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7648610 : Nat := 118140960795 + 7648610 * 2 ^ 59
def prefixEnd_7648610 : Nat := 4983230072969 + 3 ^ 40 * 7648610 * 2
def baseEnd_7648610 : Nat := 3927413268785425011899689

theorem tailTrace_7648610 : CollatzResearch.WordTrace tailWord_7648610 prefixEnd_7648610 3927413268785425011899689 := by
  unfold tailWord_7648610
  simp only [CollatzResearch.WordTrace]
  refine ⟨69741931205099930858739821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185978483213599815623306189 69741931205099930858739821)
  ·
    refine ⟨26153224201912474072027433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69741931205099930858739821 26153224201912474072027433)
    ·
      refine ⟨19614918151434355554020575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26153224201912474072027433 19614918151434355554020575)
      ·
        refine ⟨29422377227151533331030863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19614918151434355554020575 29422377227151533331030863)
        ·
          refine ⟨44133565840727299996546295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29422377227151533331030863 44133565840727299996546295)
          ·
            refine ⟨66200348761090949994819443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44133565840727299996546295 66200348761090949994819443)
            ·
              refine ⟨99300523141636424992229165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66200348761090949994819443 99300523141636424992229165)
              ·
                refine ⟨37237696178113659372085937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99300523141636424992229165 37237696178113659372085937)
                ·
                  refine ⟨27928272133585244529064453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37237696178113659372085937 27928272133585244529064453)
                  ·
                    refine ⟨5236551025047233349199585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27928272133585244529064453 5236551025047233349199585)
                    ·
                      refine ⟨3927413268785425011899689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236551025047233349199585 3927413268785425011899689)
                      ·
                        rfl

theorem cell23_7648610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7648610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648610 prefixEnd_7648610 := by exact prefixLift 7648610
  have htrace : WordTrace (prefixWord ++ tailWord_7648610) baseStart_7648610 baseEnd_7648610 := by
    simpa [prefixWord, tailWord_7648610, baseEnd_7648610] using wordTrace_append hprefix tailTrace_7648610
  have hstable : (prefixWord ++ tailWord_7648610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648610).length < 2 ^ (prefixWord ++ tailWord_7648610).sum := by decide
  have hdescent : baseEnd_7648610 < baseStart_7648610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648654 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_7648654 : Nat := 118140960795 + 7648654 * 2 ^ 59
def prefixEnd_7648654 : Nat := 4983230072969 + 3 ^ 40 * 7648654 * 2
def baseEnd_7648654 : Nat := 1309145287311407613249829

theorem tailTrace_7648654 : CollatzResearch.WordTrace tailWord_7648654 prefixEnd_7648654 1309145287311407613249829 := by
  unfold tailWord_7648654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871166204030039868695127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185979553088160212633040677 34871166204030039868695127)
  ·
    refine ⟨52306749306045059803042691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34871166204030039868695127 52306749306045059803042691)
    ·
      refine ⟨78460123959067589704564037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52306749306045059803042691 78460123959067589704564037)
      ·
        refine ⟨14711273242325173069605757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78460123959067589704564037 14711273242325173069605757)
        ·
          refine ⟨5516727465871939901102159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14711273242325173069605757 5516727465871939901102159)
          ·
            refine ⟨8275091198807909851653239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516727465871939901102159 8275091198807909851653239)
            ·
              refine ⟨12412636798211864777479859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275091198807909851653239 12412636798211864777479859)
              ·
                refine ⟨18618955197317797166219789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412636798211864777479859 18618955197317797166219789)
                ·
                  refine ⟨6982108198994173937332421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18618955197317797166219789 6982108198994173937332421)
                  ·
                    refine ⟨1309145287311407613249829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6982108198994173937332421 1309145287311407613249829)
                    ·
                      rfl

theorem cell23_7648654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_7648654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648654 prefixEnd_7648654 := by exact prefixLift 7648654
  have htrace : WordTrace (prefixWord ++ tailWord_7648654) baseStart_7648654 baseEnd_7648654 := by
    simpa [prefixWord, tailWord_7648654, baseEnd_7648654] using wordTrace_append hprefix tailTrace_7648654
  have hstable : (prefixWord ++ tailWord_7648654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648654).length < 2 ^ (prefixWord ++ tailWord_7648654).sum := by decide
  have hdescent : baseEnd_7648654 < baseStart_7648654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648693 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7648693 : Nat := 118140960795 + 7648693 * 2 ^ 59
def prefixEnd_7648693 : Nat := 4983230072969 + 3 ^ 40 * 7648693 * 2
def baseEnd_7648693 : Nat := 1309151962559916062387269

theorem tailTrace_7648693 : CollatzResearch.WordTrace tailWord_7648693 prefixEnd_7648693 1309151962559916062387269 := by
  unfold tailWord_7648693
  simp only [CollatzResearch.WordTrace]
  refine ⟨278970752079099028610230733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185980501386066019073487155 278970752079099028610230733)
  ·
    refine ⟨104614032029662135728836525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278970752079099028610230733 104614032029662135728836525)
    ·
      refine ⟨39230262011123300898313697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104614032029662135728836525 39230262011123300898313697)
      ·
        refine ⟨29422696508342475673735273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39230262011123300898313697 29422696508342475673735273)
        ·
          refine ⟨22067022381256856755301455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29422696508342475673735273 22067022381256856755301455)
          ·
            refine ⟨33100533571885285132952183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22067022381256856755301455 33100533571885285132952183)
            ·
              refine ⟨49650800357827927699428275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33100533571885285132952183 49650800357827927699428275)
              ·
                refine ⟨74476200536741891549142413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49650800357827927699428275 74476200536741891549142413)
                ·
                  refine ⟨27928575201278209330928405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74476200536741891549142413 27928575201278209330928405)
                  ·
                    refine ⟨1309151962559916062387269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27928575201278209330928405 1309151962559916062387269)
                    ·
                      rfl

theorem cell23_7648693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7648693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648693 prefixEnd_7648693 := by exact prefixLift 7648693
  have htrace : WordTrace (prefixWord ++ tailWord_7648693) baseStart_7648693 baseEnd_7648693 := by
    simpa [prefixWord, tailWord_7648693, baseEnd_7648693] using wordTrace_append hprefix tailTrace_7648693
  have hstable : (prefixWord ++ tailWord_7648693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648693).length < 2 ^ (prefixWord ++ tailWord_7648693).sum := by decide
  have hdescent : baseEnd_7648693 < baseStart_7648693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648697 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 1, 5]
def baseStart_7648697 : Nat := 118140960795 + 7648697 * 2 ^ 59
def prefixEnd_7648697 : Nat := 4983230072969 + 3 ^ 40 * 7648697 * 2
def baseEnd_7648697 : Nat := 1309152647200788723837263

theorem tailTrace_7648697 : CollatzResearch.WordTrace tailWord_7648697 prefixEnd_7648697 1309152647200788723837263 := by
  unfold tailWord_7648697
  simp only [CollatzResearch.WordTrace]
  refine ⟨278970897971084537293376345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185980598647389691528917563 278970897971084537293376345)
  ·
    refine ⟨209228173478313402970032259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278970897971084537293376345 209228173478313402970032259)
    ·
      refine ⟨313842260217470104455048389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209228173478313402970032259 313842260217470104455048389)
      ·
        refine ⟨58845423790775644585321573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313842260217470104455048389 58845423790775644585321573)
        ·
          refine ⟨11033516960770433359747795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58845423790775644585321573 11033516960770433359747795)
          ·
            refine ⟨16550275441155650039621693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11033516960770433359747795 16550275441155650039621693)
            ·
              refine ⟨6206353290433368764858135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16550275441155650039621693 6206353290433368764858135)
              ·
                refine ⟨9309529935650053147287203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206353290433368764858135 9309529935650053147287203)
                ·
                  refine ⟨13964294903475079720930805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309529935650053147287203 13964294903475079720930805)
                  ·
                    refine ⟨1309152647200788723837263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13964294903475079720930805 1309152647200788723837263)
                    ·
                      rfl

theorem cell23_7648697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_7648697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648697 prefixEnd_7648697 := by exact prefixLift 7648697
  have htrace : WordTrace (prefixWord ++ tailWord_7648697) baseStart_7648697 baseEnd_7648697 := by
    simpa [prefixWord, tailWord_7648697, baseEnd_7648697] using wordTrace_append hprefix tailTrace_7648697
  have hstable : (prefixWord ++ tailWord_7648697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648697).length < 2 ^ (prefixWord ++ tailWord_7648697).sum := by decide
  have hdescent : baseEnd_7648697 < baseStart_7648697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648730 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_7648730 : Nat := 118140960795 + 7648730 * 2 ^ 59
def prefixEnd_7648730 : Nat := 4983230072969 + 3 ^ 40 * 7648730 * 2
def baseEnd_7648730 : Nat := 3927474886463964542399137

theorem tailTrace_7648730 : CollatzResearch.WordTrace tailWord_7648730 prefixEnd_7648730 3927474886463964542399137 := by
  unfold tailWord_7648730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69743025394991245982331911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185981401053309989286218429 69743025394991245982331911)
  ·
    refine ⟨104614538092486868973497867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69743025394991245982331911 104614538092486868973497867)
    ·
      refine ⟨156921807138730303460246801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104614538092486868973497867 156921807138730303460246801)
      ·
        refine ⟨117691355354047727595185101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156921807138730303460246801 117691355354047727595185101)
        ·
          refine ⟨44134258257767897848194413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117691355354047727595185101 44134258257767897848194413)
          ·
            refine ⟨16550346846662961693072905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44134258257767897848194413 16550346846662961693072905)
            ·
              refine ⟨12412760134997221269804679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16550346846662961693072905 12412760134997221269804679)
              ·
                refine ⟨18619140202495831904707019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412760134997221269804679 18619140202495831904707019)
                ·
                  refine ⟨27928710303743747857060529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18619140202495831904707019 27928710303743747857060529)
                  ·
                    refine ⟨20946532727807810892795397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27928710303743747857060529 20946532727807810892795397)
                    ·
                      refine ⟨3927474886463964542399137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20946532727807810892795397 3927474886463964542399137)
                      ·
                        rfl

theorem cell23_7648730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_7648730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648730 prefixEnd_7648730 := by exact prefixLift 7648730
  have htrace : WordTrace (prefixWord ++ tailWord_7648730) baseStart_7648730 baseEnd_7648730 := by
    simpa [prefixWord, tailWord_7648730, baseEnd_7648730] using wordTrace_append hprefix tailTrace_7648730
  have hstable : (prefixWord ++ tailWord_7648730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648730).length < 2 ^ (prefixWord ++ tailWord_7648730).sum := by decide
  have hdescent : baseEnd_7648730 < baseStart_7648730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648750 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_7648750 : Nat := 118140960795 + 7648750 * 2 ^ 59
def prefixEnd_7648750 : Nat := 4983230072969 + 3 ^ 40 * 7648750 * 2
def baseEnd_7648750 : Nat := 3927485156077054464149045

theorem tailTrace_7648750 : CollatzResearch.WordTrace tailWord_7648750 prefixEnd_7648750 3927485156077054464149045 := by
  unfold tailWord_7648750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871603879986565918131963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185981887359928351563370469 34871603879986565918131963)
  ·
    refine ⟨52307405819979848877197945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34871603879986565918131963 52307405819979848877197945)
    ·
      refine ⟨39230554364984886657898459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52307405819979848877197945 39230554364984886657898459)
      ·
        refine ⟨58845831547477329986847689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39230554364984886657898459 58845831547477329986847689)
        ·
          refine ⟨44134373660607997490135767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58845831547477329986847689 44134373660607997490135767)
          ·
            refine ⟨66201560490911996235203651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44134373660607997490135767 66201560490911996235203651)
            ·
              refine ⟨99302340736367994352805477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66201560490911996235203651 99302340736367994352805477)
              ·
                refine ⟨18619188888068998941151027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99302340736367994352805477 18619188888068998941151027)
                ·
                  refine ⟨27928783332103498411726541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18619188888068998941151027 27928783332103498411726541)
                  ·
                    refine ⟨10473293749538811904397453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27928783332103498411726541 10473293749538811904397453)
                    ·
                      refine ⟨3927485156077054464149045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10473293749538811904397453 3927485156077054464149045)
                      ·
                        rfl

theorem cell23_7648750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_7648750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648750 prefixEnd_7648750 := by exact prefixLift 7648750
  have htrace : WordTrace (prefixWord ++ tailWord_7648750) baseStart_7648750 baseEnd_7648750 := by
    simpa [prefixWord, tailWord_7648750, baseEnd_7648750] using wordTrace_append hprefix tailTrace_7648750
  have hstable : (prefixWord ++ tailWord_7648750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648750).length < 2 ^ (prefixWord ++ tailWord_7648750).sum := by decide
  have hdescent : baseEnd_7648750 < baseStart_7648750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648754 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7648754 : Nat := 118140960795 + 7648754 * 2 ^ 59
def prefixEnd_7648754 : Nat := 4983230072969 + 3 ^ 40 * 7648754 * 2
def baseEnd_7648754 : Nat := 3927487209999672448499027

theorem tailTrace_7648754 : CollatzResearch.WordTrace tailWord_7648754 prefixEnd_7648754 3927487209999672448499027 := by
  unfold tailWord_7648754
  simp only [CollatzResearch.WordTrace]
  refine ⟨69743244232969509007050329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185981984621252024018800877 69743244232969509007050329)
  ·
    refine ⟨52307433174727131755287747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69743244232969509007050329 52307433174727131755287747)
    ·
      refine ⟨78461149762090697632931621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52307433174727131755287747 78461149762090697632931621)
      ·
        refine ⟨14711465580392005806174679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78461149762090697632931621 14711465580392005806174679)
        ·
          refine ⟨22067198370588008709262019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711465580392005806174679 22067198370588008709262019)
          ·
            refine ⟨33100797555882013063893029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22067198370588008709262019 33100797555882013063893029)
            ·
              refine ⟨6206399541727877449479943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33100797555882013063893029 6206399541727877449479943)
              ·
                refine ⟨9309599312591816174219915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206399541727877449479943 9309599312591816174219915)
                ·
                  refine ⟨13964398968887724261329873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309599312591816174219915 13964398968887724261329873)
                  ·
                    refine ⟨10473299226665793195997405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13964398968887724261329873 10473299226665793195997405)
                    ·
                      refine ⟨3927487209999672448499027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10473299226665793195997405 3927487209999672448499027)
                      ·
                        rfl

theorem cell23_7648754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7648754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648754 prefixEnd_7648754 := by exact prefixLift 7648754
  have htrace : WordTrace (prefixWord ++ tailWord_7648754) baseStart_7648754 baseEnd_7648754 := by
    simpa [prefixWord, tailWord_7648754, baseEnd_7648754] using wordTrace_append hprefix tailTrace_7648754
  have hstable : (prefixWord ++ tailWord_7648754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648754).length < 2 ^ (prefixWord ++ tailWord_7648754).sum := by decide
  have hdescent : baseEnd_7648754 < baseStart_7648754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648781 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7648781 : Nat := 118140960795 + 7648781 * 2 ^ 59
def prefixEnd_7648781 : Nat := 4983230072969 + 3 ^ 40 * 7648781 * 2
def baseEnd_7648781 : Nat := 3927501073977343842861403

theorem tailTrace_7648781 : CollatzResearch.WordTrace tailWord_7648781 prefixEnd_7648781 3927501073977343842861403 := by
  unfold tailWord_7648781
  simp only [CollatzResearch.WordTrace]
  refine ⟨278973961702780219639434197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185982641135186813092956131 278973961702780219639434197)
  ·
    refine ⟨6538452227408911397799239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 278973961702780219639434197 6538452227408911397799239)
    ·
      refine ⟨9807678341113367096698859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6538452227408911397799239 9807678341113367096698859)
      ·
        refine ⟨14711517511670050645048289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9807678341113367096698859 14711517511670050645048289)
        ·
          refine ⟨11033638133752537983786217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14711517511670050645048289 11033638133752537983786217)
          ·
            refine ⟨8275228600314403487839663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11033638133752537983786217 8275228600314403487839663)
            ·
              refine ⟨12412842900471605231759495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275228600314403487839663 12412842900471605231759495)
              ·
                refine ⟨18619264350707407847639243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412842900471605231759495 18619264350707407847639243)
                ·
                  refine ⟨27928896526061111771458865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18619264350707407847639243 27928896526061111771458865)
                  ·
                    refine ⟨20946672394545833828594149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27928896526061111771458865 20946672394545833828594149)
                    ·
                      refine ⟨3927501073977343842861403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20946672394545833828594149 3927501073977343842861403)
                      ·
                        rfl

theorem cell23_7648781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7648781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648781 prefixEnd_7648781 := by exact prefixLift 7648781
  have htrace : WordTrace (prefixWord ++ tailWord_7648781) baseStart_7648781 baseEnd_7648781 := by
    simpa [prefixWord, tailWord_7648781, baseEnd_7648781] using wordTrace_append hprefix tailTrace_7648781
  have hstable : (prefixWord ++ tailWord_7648781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648781).length < 2 ^ (prefixWord ++ tailWord_7648781).sum := by decide
  have hdescent : baseEnd_7648781 < baseStart_7648781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648810 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7648810 : Nat := 118140960795 + 7648810 * 2 ^ 59
def prefixEnd_7648810 : Nat := 4983230072969 + 3 ^ 40 * 7648810 * 2
def baseEnd_7648810 : Nat := 3927515964916324229398769

theorem tailTrace_7648810 : CollatzResearch.WordTrace tailWord_7648810 prefixEnd_7648810 3927515964916324229398769 := by
  unfold tailWord_7648810
  simp only [CollatzResearch.WordTrace]
  refine ⟨69743754854918789398059971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185983346279783438394826589 69743754854918789398059971)
  ·
    refine ⟨104615632282378184097089957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69743754854918789398059971 104615632282378184097089957)
    ·
      refine ⟨19615431052945909518204367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104615632282378184097089957 19615431052945909518204367)
      ·
        refine ⟨29423146579418864277306551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19615431052945909518204367 29423146579418864277306551)
        ·
          refine ⟨44134719869128296415959827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29423146579418864277306551 44134719869128296415959827)
          ·
            refine ⟨66202079803692444623939741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44134719869128296415959827 66202079803692444623939741)
            ·
              refine ⟨24825779926384666733977403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66202079803692444623939741 24825779926384666733977403)
              ·
                refine ⟨37238669889577000100966105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24825779926384666733977403 37238669889577000100966105)
                ·
                  refine ⟨27929002417182750075724579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37238669889577000100966105 27929002417182750075724579)
                  ·
                    refine ⟨41893503625774125113586869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27929002417182750075724579 41893503625774125113586869)
                    ·
                      refine ⟨3927515964916324229398769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41893503625774125113586869 3927515964916324229398769)
                      ·
                        rfl

theorem cell23_7648810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7648810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648810 prefixEnd_7648810 := by exact prefixLift 7648810
  have htrace : WordTrace (prefixWord ++ tailWord_7648810) baseStart_7648810 baseEnd_7648810 := by
    simpa [prefixWord, tailWord_7648810, baseEnd_7648810] using wordTrace_append hprefix tailTrace_7648810
  have hstable : (prefixWord ++ tailWord_7648810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648810).length < 2 ^ (prefixWord ++ tailWord_7648810).sum := by decide
  have hdescent : baseEnd_7648810 < baseStart_7648810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648843 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 6, 5]
def baseStart_7648843 : Nat := 118140960795 + 7648843 * 2 ^ 59
def prefixEnd_7648843 : Nat := 4983230072969 + 3 ^ 40 * 7648843 * 2
def baseEnd_7648843 : Nat := 1309177636592640866762039

theorem tailTrace_7648843 : CollatzResearch.WordTrace tailWord_7648843 prefixEnd_7648843 1309177636592640866762039 := by
  unfold tailWord_7648843
  simp only [CollatzResearch.WordTrace]
  refine ⟨278976223028555604228191183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185984148685703736152127455 278976223028555604228191183)
  ·
    refine ⟨418464334542833406342286775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278976223028555604228191183 418464334542833406342286775)
    ·
      refine ⟨627696501814250109513430163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418464334542833406342286775 627696501814250109513430163)
      ·
        refine ⟨941544752721375164270145245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627696501814250109513430163 941544752721375164270145245)
        ·
          refine ⟨353079282270515686601304467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941544752721375164270145245 353079282270515686601304467)
          ·
            refine ⟨529618923405773529901956701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353079282270515686601304467 529618923405773529901956701)
            ·
              refine ⟨198607096277165073713233763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529618923405773529901956701 198607096277165073713233763)
              ·
                refine ⟨297910644415747610569850645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198607096277165073713233763 297910644415747610569850645)
                ·
                  refine ⟨13964561456988169245461749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 297910644415747610569850645 13964561456988169245461749)
                  ·
                    refine ⟨1309177636592640866762039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13964561456988169245461749 1309177636592640866762039)
                    ·
                      rfl

theorem cell23_7648843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 5].length) (baseStart_7648843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648843 prefixEnd_7648843 := by exact prefixLift 7648843
  have htrace : WordTrace (prefixWord ++ tailWord_7648843) baseStart_7648843 baseEnd_7648843 := by
    simpa [prefixWord, tailWord_7648843, baseEnd_7648843] using wordTrace_append hprefix tailTrace_7648843
  have hstable : (prefixWord ++ tailWord_7648843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648843).length < 2 ^ (prefixWord ++ tailWord_7648843).sum := by decide
  have hdescent : baseEnd_7648843 < baseStart_7648843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648853 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7648853 : Nat := 118140960795 + 7648853 * 2 ^ 59
def prefixEnd_7648853 : Nat := 4983230072969 + 3 ^ 40 * 7648853 * 2
def baseEnd_7648853 : Nat := 3927538044584467561161071

theorem tailTrace_7648853 : CollatzResearch.WordTrace tailWord_7648853 prefixEnd_7648853 3927538044584467561161071 := by
  unfold tailWord_7648853
  simp only [CollatzResearch.WordTrace]
  refine ⟨278976587758519375936055213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185984391839012917290703475 278976587758519375936055213)
  ·
    refine ⟨104616220409444765976020705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278976587758519375936055213 104616220409444765976020705)
    ·
      refine ⟨78462165307083574482015529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104616220409444765976020705 78462165307083574482015529)
      ·
        refine ⟨58846623980312680861511647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78462165307083574482015529 58846623980312680861511647)
        ·
          refine ⟨88269935970469021292267471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58846623980312680861511647 88269935970469021292267471)
          ·
            refine ⟨132404903955703531938401207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88269935970469021292267471 132404903955703531938401207)
            ·
              refine ⟨198607355933555297907601811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132404903955703531938401207 198607355933555297907601811)
              ·
                refine ⟨297911033900332946861402717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198607355933555297907601811 297911033900332946861402717)
                ·
                  refine ⟨111716637712624855073026019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297911033900332946861402717 111716637712624855073026019)
                  ·
                    refine ⟨167574956568937282609539029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111716637712624855073026019 167574956568937282609539029)
                    ·
                      refine ⟨3927538044584467561161071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167574956568937282609539029 3927538044584467561161071)
                      ·
                        rfl

theorem cell23_7648853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7648853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648853 prefixEnd_7648853 := by exact prefixLift 7648853
  have htrace : WordTrace (prefixWord ++ tailWord_7648853) baseStart_7648853 baseEnd_7648853 := by
    simpa [prefixWord, tailWord_7648853, baseEnd_7648853] using wordTrace_append hprefix tailTrace_7648853
  have hstable : (prefixWord ++ tailWord_7648853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648853).length < 2 ^ (prefixWord ++ tailWord_7648853).sum := by decide
  have hdescent : baseEnd_7648853 < baseStart_7648853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648897 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_7648897 : Nat := 118140960795 + 7648897 * 2 ^ 59
def prefixEnd_7648897 : Nat := 4983230072969 + 3 ^ 40 * 7648897 * 2
def baseEnd_7648897 : Nat := 3927560637733265389010869

theorem tailTrace_7648897 : CollatzResearch.WordTrace tailWord_7648897 prefixEnd_7648897 3927560637733265389010869 := by
  unfold tailWord_7648897
  simp only [CollatzResearch.WordTrace]
  refine ⟨278978192570359971450656945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185985461713573314300437963 278978192570359971450656945)
  ·
    refine ⟨209233644427769978587992709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278978192570359971450656945 209233644427769978587992709)
    ·
      refine ⟨39231308330206870985248633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209233644427769978587992709 39231308330206870985248633)
      ·
        refine ⟨29423481247655153238936475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39231308330206870985248633 29423481247655153238936475)
        ·
          refine ⟨44135221871482729858404713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29423481247655153238936475 44135221871482729858404713)
          ·
            refine ⟨33101416403612047393803535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44135221871482729858404713 33101416403612047393803535)
            ·
              refine ⟨49652124605418071090705303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33101416403612047393803535 49652124605418071090705303)
              ·
                refine ⟨74478186908127106636057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49652124605418071090705303 74478186908127106636057955)
                ·
                  refine ⟨111717280362190659954086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74478186908127106636057955 111717280362190659954086933)
                  ·
                    refine ⟨5236747516977687185347825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111717280362190659954086933 5236747516977687185347825)
                    ·
                      refine ⟨3927560637733265389010869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236747516977687185347825 3927560637733265389010869)
                      ·
                        rfl

theorem cell23_7648897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_7648897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648897 prefixEnd_7648897 := by exact prefixLift 7648897
  have htrace : WordTrace (prefixWord ++ tailWord_7648897) baseStart_7648897 baseEnd_7648897 := by
    simpa [prefixWord, tailWord_7648897, baseEnd_7648897] using wordTrace_append hprefix tailTrace_7648897
  have hstable : (prefixWord ++ tailWord_7648897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648897).length < 2 ^ (prefixWord ++ tailWord_7648897).sum := by decide
  have hdescent : baseEnd_7648897 < baseStart_7648897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648957 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7648957 : Nat := 118140960795 + 7648957 * 2 ^ 59
def prefixEnd_7648957 : Nat := 4983230072969 + 3 ^ 40 * 7648957 * 2
def baseEnd_7648957 : Nat := 3927591446572535154260593

theorem tailTrace_7648957 : CollatzResearch.WordTrace tailWord_7648957 prefixEnd_7648957 3927591446572535154260593 := by
  unfold tailWord_7648957
  simp only [CollatzResearch.WordTrace]
  refine ⟨278980380950142601697841125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185986920633428401131894083 278980380950142601697841125)
  ·
    refine ⟨52308821428151737818345211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278980380950142601697841125 52308821428151737818345211)
    ·
      refine ⟨78463232142227606727517817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52308821428151737818345211 78463232142227606727517817)
      ·
        refine ⟨58847424106670705045638363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78463232142227606727517817 58847424106670705045638363)
        ·
          refine ⟨88271136160006057568457545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58847424106670705045638363 88271136160006057568457545)
          ·
            refine ⟨66203352120004543176343159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88271136160006057568457545 66203352120004543176343159)
            ·
              refine ⟨99305028180006814764514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66203352120004543176343159 99305028180006814764514739)
              ·
                refine ⟨148957542270010222146772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99305028180006814764514739 148957542270010222146772109)
                ·
                  refine ⟨55859078351253833305039541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148957542270010222146772109 55859078351253833305039541)
                  ·
                    refine ⟨5236788595430046872347457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55859078351253833305039541 5236788595430046872347457)
                    ·
                      refine ⟨3927591446572535154260593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236788595430046872347457 3927591446572535154260593)
                      ·
                        rfl

theorem cell23_7648957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7648957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648957 prefixEnd_7648957 := by exact prefixLift 7648957
  have htrace : WordTrace (prefixWord ++ tailWord_7648957) baseStart_7648957 baseEnd_7648957 := by
    simpa [prefixWord, tailWord_7648957, baseEnd_7648957] using wordTrace_append hprefix tailTrace_7648957
  have hstable : (prefixWord ++ tailWord_7648957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648957).length < 2 ^ (prefixWord ++ tailWord_7648957).sum := by decide
  have hdescent : baseEnd_7648957 < baseStart_7648957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648964 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_7648964 : Nat := 118140960795 + 7648964 * 2 ^ 59
def prefixEnd_7648964 : Nat := 4983230072969 + 3 ^ 40 * 7648964 * 2
def baseEnd_7648964 : Nat := 3927595040937116626873061

theorem tailTrace_7648964 : CollatzResearch.WordTrace tailWord_7648964 prefixEnd_7648964 3927595040937116626873061 := by
  unfold tailWord_7648964
  simp only [CollatzResearch.WordTrace]
  refine ⟨139490318130558620946672973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185987090840744827928897297 139490318130558620946672973)
  ·
    refine ⟨52308869298959482855002365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139490318130558620946672973 52308869298959482855002365)
    ·
      refine ⟨19615825987109806070625887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52308869298959482855002365 19615825987109806070625887)
      ·
        refine ⟨29423738980664709105938831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19615825987109806070625887 29423738980664709105938831)
        ·
          refine ⟨44135608470997063658908247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29423738980664709105938831 44135608470997063658908247)
          ·
            refine ⟨66203412706495595488362371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135608470997063658908247 66203412706495595488362371)
            ·
              refine ⟨99305119059743393232543557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66203412706495595488362371 99305119059743393232543557)
              ·
                refine ⟨18619709823701886231101917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99305119059743393232543557 18619709823701886231101917)
                ·
                  refine ⟨6982391183888207336663219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18619709823701886231101917 6982391183888207336663219)
                  ·
                    refine ⟨10473586775832311004994829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6982391183888207336663219 10473586775832311004994829)
                    ·
                      refine ⟨3927595040937116626873061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10473586775832311004994829 3927595040937116626873061)
                      ·
                        rfl

theorem cell23_7648964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_7648964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648964 prefixEnd_7648964 := by exact prefixLift 7648964
  have htrace : WordTrace (prefixWord ++ tailWord_7648964) baseStart_7648964 baseEnd_7648964 := by
    simpa [prefixWord, tailWord_7648964, baseEnd_7648964] using wordTrace_append hprefix tailTrace_7648964
  have hstable : (prefixWord ++ tailWord_7648964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648964).length < 2 ^ (prefixWord ++ tailWord_7648964).sum := by decide
  have hdescent : baseEnd_7648964 < baseStart_7648964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648967 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 1, 5]
def baseStart_7648967 : Nat := 118140960795 + 7648967 * 2 ^ 59
def prefixEnd_7648967 : Nat := 4983230072969 + 3 ^ 40 * 7648967 * 2
def baseEnd_7648967 : Nat := 1309198860459693371711849

theorem tailTrace_7648967 : CollatzResearch.WordTrace tailWord_7648967 prefixEnd_7648967 1309198860459693371711849 := by
  unfold tailWord_7648967
  simp only [CollatzResearch.WordTrace]
  refine ⟨278980745680106373405705155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185987163786737582270470103 278980745680106373405705155)
  ·
    refine ⟨418471118520159560108557733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278980745680106373405705155 418471118520159560108557733)
    ·
      refine ⟨78463334722529917520354575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418471118520159560108557733 78463334722529917520354575)
      ·
        refine ⟨117695002083794876280531863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78463334722529917520354575 117695002083794876280531863)
        ·
          refine ⟨176542503125692314420797795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117695002083794876280531863 176542503125692314420797795)
          ·
            refine ⟨264813754688538471631196693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176542503125692314420797795 264813754688538471631196693)
            ·
              refine ⟨12413144751025240857712345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 264813754688538471631196693 12413144751025240857712345)
              ·
                refine ⟨9309858563268930643284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12413144751025240857712345 9309858563268930643284259)
                ·
                  refine ⟨13964787844903395964926389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309858563268930643284259 13964787844903395964926389)
                  ·
                    refine ⟨1309198860459693371711849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13964787844903395964926389 1309198860459693371711849)
                    ·
                      rfl

theorem cell23_7648967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_7648967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648967 prefixEnd_7648967 := by exact prefixLift 7648967
  have htrace : WordTrace (prefixWord ++ tailWord_7648967) baseStart_7648967 baseEnd_7648967 := by
    simpa [prefixWord, tailWord_7648967, baseEnd_7648967] using wordTrace_append hprefix tailTrace_7648967
  have hstable : (prefixWord ++ tailWord_7648967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648967).length < 2 ^ (prefixWord ++ tailWord_7648967).sum := by decide
  have hdescent : baseEnd_7648967 < baseStart_7648967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648974 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_7648974 : Nat := 118140960795 + 7648974 * 2 ^ 59
def prefixEnd_7648974 : Nat := 4983230072969 + 3 ^ 40 * 7648974 * 2
def baseEnd_7648974 : Nat := 3927600175743661587748015

theorem tailTrace_7648974 : CollatzResearch.WordTrace tailWord_7648974 prefixEnd_7648974 3927600175743661587748015 := by
  unfold tailWord_7648974
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872625123885126700151247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185987333994054009067473317 34872625123885126700151247)
  ·
    refine ⟨52308937685827690050226871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34872625123885126700151247 52308937685827690050226871)
    ·
      refine ⟨78463406528741535075340307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52308937685827690050226871 78463406528741535075340307)
      ·
        refine ⟨117695109793112302613010461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78463406528741535075340307 117695109793112302613010461)
        ·
          refine ⟨44135666172417113479878923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117695109793112302613010461 44135666172417113479878923)
          ·
            refine ⟨66203499258625670219818385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135666172417113479878923 66203499258625670219818385)
            ·
              refine ⟨49652624443969252664863789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66203499258625670219818385 49652624443969252664863789)
              ·
                refine ⟨18619734166488469749323921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49652624443969252664863789 18619734166488469749323921)
                ·
                  refine ⟨13964800624866352311992941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18619734166488469749323921 13964800624866352311992941)
                  ·
                    refine ⟨5236800234324882116997353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13964800624866352311992941 5236800234324882116997353)
                    ·
                      refine ⟨3927600175743661587748015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236800234324882116997353 3927600175743661587748015)
                      ·
                        rfl

theorem cell23_7648974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_7648974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648974 prefixEnd_7648974 := by exact prefixLift 7648974
  have htrace : WordTrace (prefixWord ++ tailWord_7648974) baseStart_7648974 baseEnd_7648974 := by
    simpa [prefixWord, tailWord_7648974, baseEnd_7648974] using wordTrace_append hprefix tailTrace_7648974
  have hstable : (prefixWord ++ tailWord_7648974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648974).length < 2 ^ (prefixWord ++ tailWord_7648974).sum := by decide
  have hdescent : baseEnd_7648974 < baseStart_7648974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7648997 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_7648997 : Nat := 118140960795 + 7648997 * 2 ^ 59
def prefixEnd_7648997 : Nat := 4983230072969 + 3 ^ 40 * 7648997 * 2
def baseEnd_7648997 : Nat := 1309203995266238332586803

theorem tailTrace_7648997 : CollatzResearch.WordTrace tailWord_7648997 prefixEnd_7648997 1309203995266238332586803 := by
  unfold tailWord_7648997
  simp only [CollatzResearch.WordTrace]
  refine ⟨278981839869997688529297245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185987893246665125686198163 278981839869997688529297245)
  ·
    refine ⟨104618189951249133198486467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278981839869997688529297245 104618189951249133198486467)
    ·
      refine ⟨156927284926873699797729701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104618189951249133198486467 156927284926873699797729701)
      ·
        refine ⟨29423865923788818712074319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156927284926873699797729701 29423865923788818712074319)
        ·
          refine ⟨44135798885683228068111479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29423865923788818712074319 44135798885683228068111479)
          ·
            refine ⟨66203698328524842102167219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135798885683228068111479 66203698328524842102167219)
            ·
              refine ⟨99305547492787263153250829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66203698328524842102167219 99305547492787263153250829)
              ·
                refine ⟨37239580309795223682469061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99305547492787263153250829 37239580309795223682469061)
                ·
                  refine ⟨6982421308086604440462949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37239580309795223682469061 6982421308086604440462949)
                  ·
                    refine ⟨1309203995266238332586803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6982421308086604440462949 1309203995266238332586803)
                    ·
                      rfl

theorem cell23_7648997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_7648997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7648997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7648997 prefixEnd_7648997 := by exact prefixLift 7648997
  have htrace : WordTrace (prefixWord ++ tailWord_7648997) baseStart_7648997 baseEnd_7648997 := by
    simpa [prefixWord, tailWord_7648997, baseEnd_7648997] using wordTrace_append hprefix tailTrace_7648997
  have hstable : (prefixWord ++ tailWord_7648997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7648997).length < 2 ^ (prefixWord ++ tailWord_7648997).sum := by decide
  have hdescent : baseEnd_7648997 < baseStart_7648997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7648997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649007 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_7649007 : Nat := 118140960795 + 7649007 * 2 ^ 59
def prefixEnd_7649007 : Nat := 4983230072969 + 3 ^ 40 * 7649007 * 2
def baseEnd_7649007 : Nat := 3927617120605259958635363

theorem tailTrace_7649007 : CollatzResearch.WordTrace tailWord_7649007 prefixEnd_7649007 3927617120605259958635363 := by
  unfold tailWord_7649007
  simp only [CollatzResearch.WordTrace]
  refine ⟨278982204599961460237161275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185988136399974306824774183 278982204599961460237161275)
  ·
    refine ⟨418473306899942190355741913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278982204599961460237161275 418473306899942190355741913)
    ·
      refine ⟨313854980174956642766806435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418473306899942190355741913 313854980174956642766806435)
      ·
        refine ⟨470782470262434964150209653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313854980174956642766806435 470782470262434964150209653)
        ·
          refine ⟨44135856587103277889082155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470782470262434964150209653 44135856587103277889082155)
          ·
            refine ⟨66203784880654916833623233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135856587103277889082155 66203784880654916833623233)
            ·
              refine ⟨49652838660491187625217425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66203784880654916833623233 49652838660491187625217425)
              ·
                refine ⟨37239628995368390718913069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49652838660491187625217425 37239628995368390718913069)
                ·
                  refine ⟨13964860873263146519592401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37239628995368390718913069 13964860873263146519592401)
                  ·
                    refine ⟨10473645654947359889694301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13964860873263146519592401 10473645654947359889694301)
                    ·
                      refine ⟨3927617120605259958635363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10473645654947359889694301 3927617120605259958635363)
                      ·
                        rfl

theorem cell23_7649007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_7649007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649007 prefixEnd_7649007 := by exact prefixLift 7649007
  have htrace : WordTrace (prefixWord ++ tailWord_7649007) baseStart_7649007 baseEnd_7649007 := by
    simpa [prefixWord, tailWord_7649007, baseEnd_7649007] using wordTrace_append hprefix tailTrace_7649007
  have hstable : (prefixWord ++ tailWord_7649007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649007).length < 2 ^ (prefixWord ++ tailWord_7649007).sum := by decide
  have hdescent : baseEnd_7649007 < baseStart_7649007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649044 : List Nat := [2, 4, 4, 1, 12]
def baseStart_7649044 : Nat := 118140960795 + 7649044 * 2 ^ 59
def prefixEnd_7649044 : Nat := 4983230072969 + 3 ^ 40 * 7649044 * 2
def baseEnd_7649044 : Nat := 5387703867475276150717

theorem tailTrace_7649044 : CollatzResearch.WordTrace tailWord_7649044 prefixEnd_7649044 5387703867475276150717 := by
  unfold tailWord_7649044
  simp only [CollatzResearch.WordTrace]
  refine ⟨139491777050413707778129093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185989036067218277037505457 139491777050413707778129093)
  ·
    refine ⟨26154708196952570208399205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139491777050413707778129093 26154708196952570208399205)
    ·
      refine ⟨4904007786928606914074851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26154708196952570208399205 4904007786928606914074851)
      ·
        refine ⟨7356011680392910371112277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904007786928606914074851 7356011680392910371112277)
        ·
          refine ⟨5387703867475276150717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7356011680392910371112277 5387703867475276150717)
          ·
            rfl

theorem cell23_7649044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 12].length) (baseStart_7649044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649044 prefixEnd_7649044 := by exact prefixLift 7649044
  have htrace : WordTrace (prefixWord ++ tailWord_7649044) baseStart_7649044 baseEnd_7649044 := by
    simpa [prefixWord, tailWord_7649044, baseEnd_7649044] using wordTrace_append hprefix tailTrace_7649044
  have hstable : (prefixWord ++ tailWord_7649044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649044).length < 2 ^ (prefixWord ++ tailWord_7649044).sum := by decide
  have hdescent : baseEnd_7649044 < baseStart_7649044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649134 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_7649134 : Nat := 118140960795 + 7649134 * 2 ^ 59
def prefixEnd_7649134 : Nat := 4983230072969 + 3 ^ 40 * 7649134 * 2
def baseEnd_7649134 : Nat := 436409148072042329083031

theorem tailTrace_7649134 : CollatzResearch.WordTrace tailWord_7649134 prefixEnd_7649134 436409148072042329083031 := by
  unfold tailWord_7649134
  simp only [CollatzResearch.WordTrace]
  refine ⟨34873354583812670115879307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185991224447000907284689637 34873354583812670115879307)
  ·
    refine ⟨52310031875719005173818961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34873354583812670115879307 52310031875719005173818961)
    ·
      refine ⟨39232523906789253880364221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52310031875719005173818961 39232523906789253880364221)
      ·
        refine ⟨14712196465045970205136583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39232523906789253880364221 14712196465045970205136583)
        ·
          refine ⟨22068294697568955307704875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14712196465045970205136583 22068294697568955307704875)
          ·
            refine ⟨33102442046353432961557313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22068294697568955307704875 33102442046353432961557313)
            ·
              refine ⟨24826831534765074721167985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33102442046353432961557313 24826831534765074721167985)
              ·
                refine ⟨18620123651073806040875989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24826831534765074721167985 18620123651073806040875989)
                ·
                  refine ⟨436409148072042329083031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18620123651073806040875989 436409148072042329083031)
                  ·
                    rfl

theorem cell23_7649134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_7649134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649134 prefixEnd_7649134 := by exact prefixLift 7649134
  have htrace : WordTrace (prefixWord ++ tailWord_7649134) baseStart_7649134 baseEnd_7649134 := by
    simpa [prefixWord, tailWord_7649134, baseEnd_7649134] using wordTrace_append hprefix tailTrace_7649134
  have hstable : (prefixWord ++ tailWord_7649134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649134).length < 2 ^ (prefixWord ++ tailWord_7649134).sum := by decide
  have hdescent : baseEnd_7649134 < baseStart_7649134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649147 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 2, 5]
def baseStart_7649147 : Nat := 118140960795 + 7649147 * 2 ^ 59
def prefixEnd_7649147 : Nat := 4983230072969 + 3 ^ 40 * 7649147 * 2
def baseEnd_7649147 : Nat := 1309229669298963136961573

theorem tailTrace_7649147 : CollatzResearch.WordTrace tailWord_7649147 prefixEnd_7649147 1309229669298963136961573 := by
  unfold tailWord_7649147
  simp only [CollatzResearch.WordTrace]
  refine ⟨278987310819454264147257695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185991540546302842764838463 278987310819454264147257695)
  ·
    refine ⟨418480966229181396220886543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278987310819454264147257695 418480966229181396220886543)
    ·
      refine ⟨627721449343772094331329815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418480966229181396220886543 627721449343772094331329815)
      ·
        refine ⟨941582174015658141496994723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627721449343772094331329815 941582174015658141496994723)
        ·
          refine ⟨1412373261023487212245492085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941582174015658141496994723 1412373261023487212245492085)
          ·
            refine ⟨132409993220951926148014883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1412373261023487212245492085 132409993220951926148014883)
            ·
              refine ⟨198614989831427889222022325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132409993220951926148014883 198614989831427889222022325)
              ·
                refine ⟨18620155296696364614564593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198614989831427889222022325 18620155296696364614564593)
                ·
                  refine ⟨13965116472522273460923445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18620155296696364614564593 13965116472522273460923445)
                  ·
                    refine ⟨1309229669298963136961573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13965116472522273460923445 1309229669298963136961573)
                    ·
                      rfl

theorem cell23_7649147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 5].length) (baseStart_7649147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649147 prefixEnd_7649147 := by exact prefixLift 7649147
  have htrace : WordTrace (prefixWord ++ tailWord_7649147) baseStart_7649147 baseEnd_7649147 := by
    simpa [prefixWord, tailWord_7649147, baseEnd_7649147] using wordTrace_append hprefix tailTrace_7649147
  have hstable : (prefixWord ++ tailWord_7649147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649147).length < 2 ^ (prefixWord ++ tailWord_7649147).sum := by decide
  have hdescent : baseEnd_7649147 < baseStart_7649147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649157 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_7649157 : Nat := 118140960795 + 7649157 * 2 ^ 59
def prefixEnd_7649157 : Nat := 4983230072969 + 3 ^ 40 * 7649157 * 2
def baseEnd_7649157 : Nat := 3927694142703434371759673

theorem tailTrace_7649157 : CollatzResearch.WordTrace tailWord_7649157 prefixEnd_7649157 3927694142703434371759673 := by
  unfold tailWord_7649157
  simp only [CollatzResearch.WordTrace]
  refine ⟨278987675549418035855121725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185991783699612023903414483 278987675549418035855121725)
  ·
    refine ⟨104620378331031763445670647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278987675549418035855121725 104620378331031763445670647)
    ·
      refine ⟨156930567496547645168505971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104620378331031763445670647 156930567496547645168505971)
      ·
        refine ⟨235395851244821467752758957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156930567496547645168505971 235395851244821467752758957)
        ·
          refine ⟨88273444216808050407284609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235395851244821467752758957 88273444216808050407284609)
          ·
            refine ⟨66205083162606037805463457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88273444216808050407284609 66205083162606037805463457)
            ·
              refine ⟨49653812371954528354097593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66205083162606037805463457 49653812371954528354097593)
              ·
                refine ⟨37240359278965896265573195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49653812371954528354097593 37240359278965896265573195)
                ·
                  refine ⟨55860538918448844398359793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37240359278965896265573195 55860538918448844398359793)
                  ·
                    refine ⟨41895404188836633298769845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55860538918448844398359793 41895404188836633298769845)
                    ·
                      refine ⟨3927694142703434371759673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41895404188836633298769845 3927694142703434371759673)
                      ·
                        rfl

theorem cell23_7649157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_7649157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649157 prefixEnd_7649157 := by exact prefixLift 7649157
  have htrace : WordTrace (prefixWord ++ tailWord_7649157) baseStart_7649157 baseEnd_7649157 := by
    simpa [prefixWord, tailWord_7649157, baseEnd_7649157] using wordTrace_append hprefix tailTrace_7649157
  have hstable : (prefixWord ++ tailWord_7649157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649157).length < 2 ^ (prefixWord ++ tailWord_7649157).sum := by decide
  have hdescent : baseEnd_7649157 < baseStart_7649157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649184 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2]
def baseStart_7649184 : Nat := 118140960795 + 7649184 * 2 ^ 59
def prefixEnd_7649184 : Nat := 4983230072969 + 3 ^ 40 * 7649184 * 2
def baseEnd_7649184 : Nat := 3927708006681105766122049

theorem tailTrace_7649184 : CollatzResearch.WordTrace tailWord_7649184 prefixEnd_7649184 3927708006681105766122049 := by
  unfold tailWord_7649184
  simp only [CollatzResearch.WordTrace]
  refine ⟨139494330160160109733177303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185992440213546812977569737 139494330160160109733177303)
  ·
    refine ⟨209241495240240164599765955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139494330160160109733177303 209241495240240164599765955)
    ·
      refine ⟨313862242860360246899648933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209241495240240164599765955 313862242860360246899648933)
      ·
        refine ⟨58849170536317546293684175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313862242860360246899648933 58849170536317546293684175)
        ·
          refine ⟨88273755804476319440526263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58849170536317546293684175 88273755804476319440526263)
          ·
            refine ⟨132410633706714479160789395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88273755804476319440526263 132410633706714479160789395)
            ·
              refine ⟨198615950560071718741184093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132410633706714479160789395 198615950560071718741184093)
              ·
                refine ⟨74480981460026894527944035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198615950560071718741184093 74480981460026894527944035)
                ·
                  refine ⟨111721472190040341791916053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74480981460026894527944035 111721472190040341791916053)
                  ·
                    refine ⟨5236944008908141021496065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111721472190040341791916053 5236944008908141021496065)
                    ·
                      refine ⟨3927708006681105766122049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5236944008908141021496065 3927708006681105766122049)
                      ·
                        rfl

theorem cell23_7649184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_7649184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649184 prefixEnd_7649184 := by exact prefixLift 7649184
  have htrace : WordTrace (prefixWord ++ tailWord_7649184) baseStart_7649184 baseEnd_7649184 := by
    simpa [prefixWord, tailWord_7649184, baseEnd_7649184] using wordTrace_append hprefix tailTrace_7649184
  have hstable : (prefixWord ++ tailWord_7649184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649184).length < 2 ^ (prefixWord ++ tailWord_7649184).sum := by decide
  have hdescent : baseEnd_7649184 < baseStart_7649184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649201 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7649201 : Nat := 118140960795 + 7649201 * 2 ^ 59
def prefixEnd_7649201 : Nat := 4983230072969 + 3 ^ 40 * 7649201 * 2
def baseEnd_7649201 : Nat := 3927716735852232199609471

theorem tailTrace_7649201 : CollatzResearch.WordTrace tailWord_7649201 prefixEnd_7649201 3927716735852232199609471 := by
  unfold tailWord_7649201
  simp only [CollatzResearch.WordTrace]
  refine ⟨278989280361258631369723457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185992853574172420913148971 278989280361258631369723457)
  ·
    refine ⟨209241960270943973527292593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278989280361258631369723457 209241960270943973527292593)
    ·
      refine ⟨156931470203207980145469445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209241960270943973527292593 156931470203207980145469445)
      ·
        refine ⟨29424650663101496277275521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156931470203207980145469445 29424650663101496277275521)
        ·
          refine ⟨22068487997326122207956641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29424650663101496277275521 22068487997326122207956641)
          ·
            refine ⟨16551365997994591655967481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22068487997326122207956641 16551365997994591655967481)
            ·
              refine ⟨12413524498495943741975611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16551365997994591655967481 12413524498495943741975611)
              ·
                refine ⟨18620286747743915612963417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413524498495943741975611 18620286747743915612963417)
                ·
                  refine ⟨13965215060807936709722563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18620286747743915612963417 13965215060807936709722563)
                  ·
                    refine ⟨20947822591211905064583845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13965215060807936709722563 20947822591211905064583845)
                    ·
                      refine ⟨3927716735852232199609471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20947822591211905064583845 3927716735852232199609471)
                      ·
                        rfl

theorem cell23_7649201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7649201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649201 prefixEnd_7649201 := by exact prefixLift 7649201
  have htrace : WordTrace (prefixWord ++ tailWord_7649201) baseStart_7649201 baseEnd_7649201 := by
    simpa [prefixWord, tailWord_7649201, baseEnd_7649201] using wordTrace_append hprefix tailTrace_7649201
  have hstable : (prefixWord ++ tailWord_7649201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649201).length < 2 ^ (prefixWord ++ tailWord_7649201).sum := by decide
  have hdescent : baseEnd_7649201 < baseStart_7649201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649224 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 6]
def baseStart_7649224 : Nat := 118140960795 + 7649224 * 2 ^ 59
def prefixEnd_7649224 : Nat := 4983230072969 + 3 ^ 40 * 7649224 * 2
def baseEnd_7649224 : Nat := 436414282878587289957985

theorem tailTrace_7649224 : CollatzResearch.WordTrace tailWord_7649224 prefixEnd_7649224 436414282878587289957985 := by
  unfold tailWord_7649224
  simp only [CollatzResearch.WordTrace]
  refine ⟨139495059620087653148905363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185993412826783537531873817 139495059620087653148905363)
  ·
    refine ⟨209242589430131479723358045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139495059620087653148905363 209242589430131479723358045)
    ·
      refine ⟨78465971036299304896259267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209242589430131479723358045 78465971036299304896259267)
      ·
        refine ⟨117698956554448957344388901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78465971036299304896259267 117698956554448957344388901)
        ·
          refine ⟨22068554353959179502072919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117698956554448957344388901 22068554353959179502072919)
          ·
            refine ⟨33102831530938769253109379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22068554353959179502072919 33102831530938769253109379)
            ·
              refine ⟨49654247296408153879664069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33102831530938769253109379 49654247296408153879664069)
              ·
                refine ⟨9310171368076528852437013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49654247296408153879664069 9310171368076528852437013)
                ·
                  refine ⟨436414282878587289957985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9310171368076528852437013 436414282878587289957985)
                  ·
                    rfl

theorem cell23_7649224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_7649224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649224 prefixEnd_7649224 := by exact prefixLift 7649224
  have htrace : WordTrace (prefixWord ++ tailWord_7649224) baseStart_7649224 baseEnd_7649224 := by
    simpa [prefixWord, tailWord_7649224, baseEnd_7649224] using wordTrace_append hprefix tailTrace_7649224
  have hstable : (prefixWord ++ tailWord_7649224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649224).length < 2 ^ (prefixWord ++ tailWord_7649224).sum := by decide
  have hdescent : baseEnd_7649224 < baseStart_7649224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649227 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_7649227 : Nat := 118140960795 + 7649227 * 2 ^ 59
def prefixEnd_7649227 : Nat := 4983230072969 + 3 ^ 40 * 7649227 * 2
def baseEnd_7649227 : Nat := 3927730086349249097884351

theorem tailTrace_7649227 : CollatzResearch.WordTrace tailWord_7649227 prefixEnd_7649227 3927730086349249097884351 := by
  unfold tailWord_7649227
  simp only [CollatzResearch.WordTrace]
  refine ⟨278990228659164437810169935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185993485772776291873446623 278990228659164437810169935)
  ·
    refine ⟨418485342988746656715254903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278990228659164437810169935 418485342988746656715254903)
    ·
      refine ⟨627728014483119985072882355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418485342988746656715254903 627728014483119985072882355)
      ·
        refine ⟨941592021724679977609323533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627728014483119985072882355 941592021724679977609323533)
        ·
          refine ⟨353097008146754991603496325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941592021724679977609323533 353097008146754991603496325)
          ·
            refine ⟨66205689027516560925655561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353097008146754991603496325 66205689027516560925655561)
            ·
              refine ⟨49654266770637420694241671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66205689027516560925655561 49654266770637420694241671)
              ·
                refine ⟨74481400155956131041362507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49654266770637420694241671 74481400155956131041362507)
                ·
                  refine ⟨111722100233934196562043761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74481400155956131041362507 111722100233934196562043761)
                  ·
                    refine ⟨83791575175450647421532821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111722100233934196562043761 83791575175450647421532821)
                    ·
                      refine ⟨3927730086349249097884351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83791575175450647421532821 3927730086349249097884351)
                      ·
                        rfl

theorem cell23_7649227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_7649227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649227 prefixEnd_7649227 := by exact prefixLift 7649227
  have htrace : WordTrace (prefixWord ++ tailWord_7649227) baseStart_7649227 baseEnd_7649227 := by
    simpa [prefixWord, tailWord_7649227, baseEnd_7649227] using wordTrace_append hprefix tailTrace_7649227
  have hstable : (prefixWord ++ tailWord_7649227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649227).length < 2 ^ (prefixWord ++ tailWord_7649227).sum := by decide
  have hdescent : baseEnd_7649227 < baseStart_7649227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649228 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_7649228 : Nat := 118140960795 + 7649228 * 2 ^ 59
def prefixEnd_7649228 : Nat := 4983230072969 + 3 ^ 40 * 7649228 * 2
def baseEnd_7649228 : Nat := 1309243533276634531323949

theorem tailTrace_7649228 : CollatzResearch.WordTrace tailWord_7649228 prefixEnd_7649228 1309243533276634531323949 := by
  unfold tailWord_7649228
  simp only [CollatzResearch.WordTrace]
  refine ⟨139495132566080407490478169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185993510088107209987304225 139495132566080407490478169)
  ·
    refine ⟨104621349424560305617858627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139495132566080407490478169 104621349424560305617858627)
    ·
      refine ⟨156932024136840458426787941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104621349424560305617858627 156932024136840458426787941)
      ·
        refine ⟨29424754525657585955022739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156932024136840458426787941 29424754525657585955022739)
        ·
          refine ⟨44137131788486378932534109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29424754525657585955022739 44137131788486378932534109)
          ·
            refine ⟨16551424420682392099700291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44137131788486378932534109 16551424420682392099700291)
            ·
              refine ⟨24827136631023588149550437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16551424420682392099700291 24827136631023588149550437)
              ·
                refine ⟨4655088118316922778040707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24827136631023588149550437 4655088118316922778040707)
                ·
                  refine ⟨6982632177475384167061061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655088118316922778040707 6982632177475384167061061)
                  ·
                    refine ⟨1309243533276634531323949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6982632177475384167061061 1309243533276634531323949)
                    ·
                      rfl

theorem cell23_7649228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_7649228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649228 prefixEnd_7649228 := by exact prefixLift 7649228
  have htrace : WordTrace (prefixWord ++ tailWord_7649228) baseStart_7649228 baseEnd_7649228 := by
    simpa [prefixWord, tailWord_7649228, baseEnd_7649228] using wordTrace_append hprefix tailTrace_7649228
  have hstable : (prefixWord ++ tailWord_7649228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649228).length < 2 ^ (prefixWord ++ tailWord_7649228).sum := by decide
  have hdescent : baseEnd_7649228 < baseStart_7649228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649251 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7649251 : Nat := 118140960795 + 7649251 * 2 ^ 59
def prefixEnd_7649251 : Nat := 4983230072969 + 3 ^ 40 * 7649251 * 2
def baseEnd_7649251 : Nat := 3927742409884957003984241

theorem tailTrace_7649251 : CollatzResearch.WordTrace tailWord_7649251 prefixEnd_7649251 3927742409884957003984241 := by
  unfold tailWord_7649251
  simp only [CollatzResearch.WordTrace]
  refine ⟨278991104011077489909043607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185994069340718326606029071 278991104011077489909043607)
  ·
    refine ⟨418486656016616234863565411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278991104011077489909043607 418486656016616234863565411)
    ·
      refine ⟨627729984024924352295348117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418486656016616234863565411 627729984024924352295348117)
      ·
        refine ⟨29424843001168329013844443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 627729984024924352295348117 29424843001168329013844443)
        ·
          refine ⟨44137264501752493520766665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29424843001168329013844443 44137264501752493520766665)
          ·
            refine ⟨33102948376314370140574999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44137264501752493520766665 33102948376314370140574999)
            ·
              refine ⟨49654422564471555210862499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33102948376314370140574999 49654422564471555210862499)
              ·
                refine ⟨74481633846707332816293749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49654422564471555210862499 74481633846707332816293749)
                ·
                  refine ⟨6982653173128812451527539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74481633846707332816293749 6982653173128812451527539)
                  ·
                    refine ⟨10473979759693218677291309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6982653173128812451527539 10473979759693218677291309)
                    ·
                      refine ⟨3927742409884957003984241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10473979759693218677291309 3927742409884957003984241)
                      ·
                        rfl

theorem cell23_7649251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7649251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649251 prefixEnd_7649251 := by exact prefixLift 7649251
  have htrace : WordTrace (prefixWord ++ tailWord_7649251) baseStart_7649251 baseEnd_7649251 := by
    simpa [prefixWord, tailWord_7649251, baseEnd_7649251] using wordTrace_append hprefix tailTrace_7649251
  have hstable : (prefixWord ++ tailWord_7649251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649251).length < 2 ^ (prefixWord ++ tailWord_7649251).sum := by decide
  have hdescent : baseEnd_7649251 < baseStart_7649251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649255 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7649255 : Nat := 118140960795 + 7649255 * 2 ^ 59
def prefixEnd_7649255 : Nat := 4983230072969 + 3 ^ 40 * 7649255 * 2
def baseEnd_7649255 : Nat := 3927744463807574988334223

theorem tailTrace_7649255 : CollatzResearch.WordTrace tailWord_7649255 prefixEnd_7649255 3927744463807574988334223 := by
  unfold tailWord_7649255
  simp only [CollatzResearch.WordTrace]
  refine ⟨278991249903062998592189219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185994166602041999061459479 278991249903062998592189219)
  ·
    refine ⟨418486874854594497888283829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278991249903062998592189219 418486874854594497888283829)
    ·
      refine ⟨39233144517618234177026609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418486874854594497888283829 39233144517618234177026609)
      ·
        refine ⟨29424858388213675632769957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39233144517618234177026609 29424858388213675632769957)
        ·
          refine ⟨5517160947790064181144367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29424858388213675632769957 5517160947790064181144367)
          ·
            refine ⟨8275741421685096271716551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517160947790064181144367 8275741421685096271716551)
            ·
              refine ⟨12413612132527644407574827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275741421685096271716551 12413612132527644407574827)
              ·
                refine ⟨18620418198791466611362241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413612132527644407574827 18620418198791466611362241)
                ·
                  refine ⟨13965313649093599958521681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18620418198791466611362241 13965313649093599958521681)
                  ·
                    refine ⟨10473985236820199968891261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13965313649093599958521681 10473985236820199968891261)
                    ·
                      refine ⟨3927744463807574988334223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10473985236820199968891261 3927744463807574988334223)
                      ·
                        rfl

theorem cell23_7649255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7649255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649255 prefixEnd_7649255 := by exact prefixLift 7649255
  have htrace : WordTrace (prefixWord ++ tailWord_7649255) baseStart_7649255 baseEnd_7649255 := by
    simpa [prefixWord, tailWord_7649255, baseEnd_7649255] using wordTrace_append hprefix tailTrace_7649255
  have hstable : (prefixWord ++ tailWord_7649255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649255).length < 2 ^ (prefixWord ++ tailWord_7649255).sum := by decide
  have hdescent : baseEnd_7649255 < baseStart_7649255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649304 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_7649304 : Nat := 118140960795 + 7649304 * 2 ^ 59
def prefixEnd_7649304 : Nat := 4983230072969 + 3 ^ 40 * 7649304 * 2
def baseEnd_7649304 : Nat := 3927769624359645296621497

theorem tailTrace_7649304 : CollatzResearch.WordTrace tailWord_7649304 prefixEnd_7649304 3927769624359645296621497 := by
  unfold tailWord_7649304
  simp only [CollatzResearch.WordTrace]
  refine ⟨139496518539942739980361483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185995358053256986640481977 139496518539942739980361483)
  ·
    refine ⟨209244777809914109970542225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139496518539942739980361483 209244777809914109970542225)
    ·
      refine ⟨156933583357435582477906669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209244777809914109970542225 156933583357435582477906669)
      ·
        refine ⟨58850093759038343429215001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156933583357435582477906669 58850093759038343429215001)
        ·
          refine ⟨44137570319278757571911251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58850093759038343429215001 44137570319278757571911251)
          ·
            refine ⟨66206355478918136357866877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44137570319278757571911251 66206355478918136357866877)
            ·
              refine ⟨24827383304594301134200079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66206355478918136357866877 24827383304594301134200079)
              ·
                refine ⟨37241074956891451701300119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24827383304594301134200079 37241074956891451701300119)
                ·
                  refine ⟨55861612435337177551950179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37241074956891451701300119 55861612435337177551950179)
                  ·
                    refine ⟨83792418653005766327925269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55861612435337177551950179 83792418653005766327925269)
                    ·
                      refine ⟨3927769624359645296621497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83792418653005766327925269 3927769624359645296621497)
                      ·
                        rfl

theorem cell23_7649304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_7649304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649304 prefixEnd_7649304 := by exact prefixLift 7649304
  have htrace : WordTrace (prefixWord ++ tailWord_7649304) baseStart_7649304 baseEnd_7649304 := by
    simpa [prefixWord, tailWord_7649304, baseEnd_7649304] using wordTrace_append hprefix tailTrace_7649304
  have hstable : (prefixWord ++ tailWord_7649304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649304).length < 2 ^ (prefixWord ++ tailWord_7649304).sum := by decide
  have hdescent : baseEnd_7649304 < baseStart_7649304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649308 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_7649308 : Nat := 118140960795 + 7649308 * 2 ^ 59
def prefixEnd_7649308 : Nat := 4983230072969 + 3 ^ 40 * 7649308 * 2
def baseEnd_7649308 : Nat := 3927771678282263280971479

theorem tailTrace_7649308 : CollatzResearch.WordTrace tailWord_7649308 prefixEnd_7649308 3927771678282263280971479 := by
  unfold tailWord_7649308
  simp only [CollatzResearch.WordTrace]
  refine ⟨139496591485935494321934289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185995455314580659095912385 139496591485935494321934289)
  ·
    refine ⟨104622443614451620741450717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139496591485935494321934289 104622443614451620741450717)
    ·
      refine ⟨39233416355419357778044019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104622443614451620741450717 39233416355419357778044019)
      ·
        refine ⟨58850124533129036667066029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39233416355419357778044019 58850124533129036667066029)
        ·
          refine ⟨22068796699923388750149761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58850124533129036667066029 22068796699923388750149761)
          ·
            refine ⟨16551597524942541562612321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22068796699923388750149761 16551597524942541562612321)
            ·
              refine ⟨12413698143706906171959241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16551597524942541562612321 12413698143706906171959241)
              ·
                refine ⟨9310273607780179628969431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12413698143706906171959241 9310273607780179628969431)
                ·
                  refine ⟨13965410411670269443454147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9310273607780179628969431 13965410411670269443454147)
                  ·
                    refine ⟨20948115617505404165181221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13965410411670269443454147 20948115617505404165181221)
                    ·
                      refine ⟨3927771678282263280971479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20948115617505404165181221 3927771678282263280971479)
                      ·
                        rfl

theorem cell23_7649308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_7649308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649308 prefixEnd_7649308 := by exact prefixLift 7649308
  have htrace : WordTrace (prefixWord ++ tailWord_7649308) baseStart_7649308 baseEnd_7649308 := by
    simpa [prefixWord, tailWord_7649308, baseEnd_7649308] using wordTrace_append hprefix tailTrace_7649308
  have hstable : (prefixWord ++ tailWord_7649308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649308).length < 2 ^ (prefixWord ++ tailWord_7649308).sum := by decide
  have hdescent : baseEnd_7649308 < baseStart_7649308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649314 : List Nat := [3, 3, 1, 1, 1, 2, 3, 9]
def baseStart_7649314 : Nat := 118140960795 + 7649314 * 2 ^ 59
def prefixEnd_7649314 : Nat := 4983230072969 + 3 ^ 40 * 7649314 * 2
def baseEnd_7649314 : Nat := 145473139228377416944313

theorem tailTrace_7649314 : CollatzResearch.WordTrace tailWord_7649314 prefixEnd_7649314 145473139228377416944313 := by
  unfold tailWord_7649314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69748350452462312917146749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185995601206566167779057997 69748350452462312917146749)
  ·
    refine ⟨26155631419673367343930031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69748350452462312917146749 26155631419673367343930031)
    ·
      refine ⟨39233447129510051015895047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26155631419673367343930031 39233447129510051015895047)
      ·
        refine ⟨58850170694265076523842571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39233447129510051015895047 58850170694265076523842571)
        ·
          refine ⟨88275256041397614785763857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58850170694265076523842571 88275256041397614785763857)
          ·
            refine ⟨66206442031048211089322893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88275256041397614785763857 66206442031048211089322893)
            ·
              refine ⟨24827415761643079158496085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66206442031048211089322893 24827415761643079158496085)
              ·
                refine ⟨145473139228377416944313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24827415761643079158496085 145473139228377416944313)
                ·
                  rfl

theorem cell23_7649314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 9].length) (baseStart_7649314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649314 prefixEnd_7649314 := by exact prefixLift 7649314
  have htrace : WordTrace (prefixWord ++ tailWord_7649314) baseStart_7649314 baseEnd_7649314 := by
    simpa [prefixWord, tailWord_7649314, baseEnd_7649314] using wordTrace_append hprefix tailTrace_7649314
  have hstable : (prefixWord ++ tailWord_7649314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649314).length < 2 ^ (prefixWord ++ tailWord_7649314).sum := by decide
  have hdescent : baseEnd_7649314 < baseStart_7649314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649319 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7649319 : Nat := 118140960795 + 7649319 * 2 ^ 59
def prefixEnd_7649319 : Nat := 4983230072969 + 3 ^ 40 * 7649319 * 2
def baseEnd_7649319 : Nat := 3927777326569462737933929

theorem tailTrace_7649319 : CollatzResearch.WordTrace tailWord_7649319 prefixEnd_7649319 3927777326569462737933929 := by
  unfold tailWord_7649319
  simp only [CollatzResearch.WordTrace]
  refine ⟨278993584174831137522519011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185995722783220758348346007 278993584174831137522519011)
  ·
    refine ⟨418490376262246706283778517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278993584174831137522519011 418490376262246706283778517)
    ·
      refine ⟨9808368193646407178526059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 418490376262246706283778517 9808368193646407178526059)
      ·
        refine ⟨14712552290469610767789089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9808368193646407178526059 14712552290469610767789089)
        ·
          refine ⟨11034414217852208075841817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14712552290469610767789089 11034414217852208075841817)
          ·
            refine ⟨8275810663389156056881363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034414217852208075841817 8275810663389156056881363)
            ·
              refine ⟨12413715995083734085322045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275810663389156056881363 12413715995083734085322045)
              ·
                refine ⟨4655143498156400281995767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12413715995083734085322045 4655143498156400281995767)
                ·
                  refine ⟨6982715247234600422993651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655143498156400281995767 6982715247234600422993651)
                  ·
                    refine ⟨10474072870851900634490477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6982715247234600422993651 10474072870851900634490477)
                    ·
                      refine ⟨3927777326569462737933929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474072870851900634490477 3927777326569462737933929)
                      ·
                        rfl

theorem cell23_7649319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7649319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649319 prefixEnd_7649319 := by exact prefixLift 7649319
  have htrace : WordTrace (prefixWord ++ tailWord_7649319) baseStart_7649319 baseEnd_7649319 := by
    simpa [prefixWord, tailWord_7649319, baseEnd_7649319] using wordTrace_append hprefix tailTrace_7649319
  have hstable : (prefixWord ++ tailWord_7649319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649319).length < 2 ^ (prefixWord ++ tailWord_7649319).sum := by decide
  have hdescent : baseEnd_7649319 < baseStart_7649319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649362 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_7649362 : Nat := 118140960795 + 7649362 * 2 ^ 59
def prefixEnd_7649362 : Nat := 4983230072969 + 3 ^ 40 * 7649362 * 2
def baseEnd_7649362 : Nat := 3927799406237606069696231

theorem tailTrace_7649362 : CollatzResearch.WordTrace tailWord_7649362 prefixEnd_7649362 3927799406237606069696231 := by
  unfold tailWord_7649362
  simp only [CollatzResearch.WordTrace]
  refine ⟨69748788128418838966583585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185996768342450237244222893 69748788128418838966583585)
  ·
    refine ⟨52311591096314129224937689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69748788128418838966583585 52311591096314129224937689)
    ·
      refine ⟨39233693322235596918703267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52311591096314129224937689 39233693322235596918703267)
      ·
        refine ⟨58850539983353395378054901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39233693322235596918703267 58850539983353395378054901)
        ·
          refine ⟨5517238123439380816692647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58850539983353395378054901 5517238123439380816692647)
          ·
            refine ⟨8275857185159071225038971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517238123439380816692647 8275857185159071225038971)
            ·
              refine ⟨12413785777738606837558457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275857185159071225038971 12413785777738606837558457)
              ·
                refine ⟨9310339333303955128168843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12413785777738606837558457 9310339333303955128168843)
                ·
                  refine ⟨13965508999955932692253265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9310339333303955128168843 13965508999955932692253265)
                  ·
                    refine ⟨10474131749966949519189949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13965508999955932692253265 10474131749966949519189949)
                    ·
                      refine ⟨3927799406237606069696231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474131749966949519189949 3927799406237606069696231)
                      ·
                        rfl

theorem cell23_7649362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_7649362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649362 prefixEnd_7649362 := by exact prefixLift 7649362
  have htrace : WordTrace (prefixWord ++ tailWord_7649362) baseStart_7649362 baseEnd_7649362 := by
    simpa [prefixWord, tailWord_7649362, baseEnd_7649362] using wordTrace_append hprefix tailTrace_7649362
  have hstable : (prefixWord ++ tailWord_7649362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649362).length < 2 ^ (prefixWord ++ tailWord_7649362).sum := by decide
  have hdescent : baseEnd_7649362 < baseStart_7649362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649364 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_7649364 : Nat := 118140960795 + 7649364 * 2 ^ 59
def prefixEnd_7649364 : Nat := 4983230072969 + 3 ^ 40 * 7649364 * 2
def baseEnd_7649364 : Nat := 3927800433198915061871221

theorem tailTrace_7649364 : CollatzResearch.WordTrace tailWord_7649364 prefixEnd_7649364 3927800433198915061871221 := by
  unfold tailWord_7649364
  simp only [CollatzResearch.WordTrace]
  refine ⟨139497612729834055103953573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185996816973112073471938097 139497612729834055103953573)
  ·
    refine ⟨26155802386843885331991295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139497612729834055103953573 26155802386843885331991295)
    ·
      refine ⟨39233703580265827997986943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26155802386843885331991295 39233703580265827997986943)
      ·
        refine ⟨58850555370398741996980415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39233703580265827997986943 58850555370398741996980415)
        ·
          refine ⟨88275833055598112995470623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58850555370398741996980415 88275833055598112995470623)
          ·
            refine ⟨132413749583397169493205935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88275833055598112995470623 132413749583397169493205935)
            ·
              refine ⟨198620624375095754239808903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132413749583397169493205935 198620624375095754239808903)
              ·
                refine ⟨297930936562643631359713355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198620624375095754239808903 297930936562643631359713355)
                ·
                  refine ⟨446896404843965447039570033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297930936562643631359713355 446896404843965447039570033)
                  ·
                    refine ⟨335172303632974085279677525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 446896404843965447039570033 335172303632974085279677525)
                    ·
                      refine ⟨3927800433198915061871221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335172303632974085279677525 3927800433198915061871221)
                      ·
                        rfl

theorem cell23_7649364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_7649364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649364 prefixEnd_7649364 := by exact prefixLift 7649364
  have htrace : WordTrace (prefixWord ++ tailWord_7649364) baseStart_7649364 baseEnd_7649364 := by
    simpa [prefixWord, tailWord_7649364, baseEnd_7649364] using wordTrace_append hprefix tailTrace_7649364
  have hstable : (prefixWord ++ tailWord_7649364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649364).length < 2 ^ (prefixWord ++ tailWord_7649364).sum := by decide
  have hdescent : baseEnd_7649364 < baseStart_7649364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649368 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_7649368 : Nat := 118140960795 + 7649368 * 2 ^ 59
def prefixEnd_7649368 : Nat := 4983230072969 + 3 ^ 40 * 7649368 * 2
def baseEnd_7649368 : Nat := 3927802487121533046221203

theorem tailTrace_7649368 : CollatzResearch.WordTrace tailWord_7649368 prefixEnd_7649368 3927802487121533046221203 := by
  unfold tailWord_7649368
  simp only [CollatzResearch.WordTrace]
  refine ⟨139497685675826809445526379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185996914234435745927368505 139497685675826809445526379)
  ·
    refine ⟨209246528513740214168289569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139497685675826809445526379 209246528513740214168289569)
    ·
      refine ⟨156934896385305160626217177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209246528513740214168289569 156934896385305160626217177)
      ·
        refine ⟨117701172288978870469662883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156934896385305160626217177 117701172288978870469662883)
        ·
          refine ⟨176551758433468305704494325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117701172288978870469662883 176551758433468305704494325)
          ·
            refine ⟨16551727353137653659796343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176551758433468305704494325 16551727353137653659796343)
            ·
              refine ⟨24827591029706480489694515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16551727353137653659796343 24827591029706480489694515)
              ·
                refine ⟨37241386544559720734541773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24827591029706480489694515 37241386544559720734541773)
                ·
                  refine ⟨13965519954209895275453165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37241386544559720734541773 13965519954209895275453165)
                  ·
                    refine ⟨5237069982828710728294937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13965519954209895275453165 5237069982828710728294937)
                    ·
                      refine ⟨3927802487121533046221203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237069982828710728294937 3927802487121533046221203)
                      ·
                        rfl

theorem cell23_7649368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_7649368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649368 prefixEnd_7649368 := by exact prefixLift 7649368
  have htrace : WordTrace (prefixWord ++ tailWord_7649368) baseStart_7649368 baseEnd_7649368 := by
    simpa [prefixWord, tailWord_7649368, baseEnd_7649368] using wordTrace_append hprefix tailTrace_7649368
  have hstable : (prefixWord ++ tailWord_7649368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649368).length < 2 ^ (prefixWord ++ tailWord_7649368).sum := by decide
  have hdescent : baseEnd_7649368 < baseStart_7649368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649385 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 1, 3, 2]
def baseStart_7649385 : Nat := 118140960795 + 7649385 * 2 ^ 59
def prefixEnd_7649385 : Nat := 4983230072969 + 3 ^ 40 * 7649385 * 2
def baseEnd_7649385 : Nat := 3927811216292659479708625

theorem tailTrace_7649385 : CollatzResearch.WordTrace tailWord_7649385 prefixEnd_7649385 3927811216292659479708625 := by
  unfold tailWord_7649385
  simp only [CollatzResearch.WordTrace]
  refine ⟨278995991392592030794421609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185997327595061353862947739 278995991392592030794421609)
  ·
    refine ⟨209246993544444023095816207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278995991392592030794421609 209246993544444023095816207)
    ·
      refine ⟨313870490316666034643724311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209246993544444023095816207 313870490316666034643724311)
      ·
        refine ⟨470805735474999051965586467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313870490316666034643724311 470805735474999051965586467)
        ·
          refine ⟨706208603212498577948379701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470805735474999051965586467 706208603212498577948379701)
          ·
            refine ⟨66207056551171741682660597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 706208603212498577948379701 66207056551171741682660597)
            ·
              refine ⟨6206911551672350782749431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66207056551171741682660597 6206911551672350782749431)
              ·
                refine ⟨9310367327508526174124147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206911551672350782749431 9310367327508526174124147)
                ·
                  refine ⟨13965550991262789261186221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9310367327508526174124147 13965550991262789261186221)
                  ·
                    refine ⟨5237081621723545972944833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13965550991262789261186221 5237081621723545972944833)
                    ·
                      refine ⟨3927811216292659479708625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237081621723545972944833 3927811216292659479708625)
                      ·
                        rfl

theorem cell23_7649385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 3, 2].length) (baseStart_7649385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649385 prefixEnd_7649385 := by exact prefixLift 7649385
  have htrace : WordTrace (prefixWord ++ tailWord_7649385) baseStart_7649385 baseEnd_7649385 := by
    simpa [prefixWord, tailWord_7649385, baseEnd_7649385] using wordTrace_append hprefix tailTrace_7649385
  have hstable : (prefixWord ++ tailWord_7649385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649385).length < 2 ^ (prefixWord ++ tailWord_7649385).sum := by decide
  have hdescent : baseEnd_7649385 < baseStart_7649385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649401 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_7649401 : Nat := 118140960795 + 7649401 * 2 ^ 59
def prefixEnd_7649401 : Nat := 4983230072969 + 3 ^ 40 * 7649401 * 2
def baseEnd_7649401 : Nat := 3927819431983131417108551

theorem tailTrace_7649401 : CollatzResearch.WordTrace tailWord_7649401 prefixEnd_7649401 3927819431983131417108551 := by
  unfold tailWord_7649401
  simp only [CollatzResearch.WordTrace]
  refine ⟨278996574960534065527004057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185997716640356043684669371 278996574960534065527004057)
  ·
    refine ⟨209247431220400549145253043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278996574960534065527004057 209247431220400549145253043)
    ·
      refine ⟨313871146830600823717879565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209247431220400549145253043 313871146830600823717879565)
      ·
        refine ⟨117701680061475308894204837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313871146830600823717879565 117701680061475308894204837)
        ·
          refine ⟨22069065011526620417663407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117701680061475308894204837 22069065011526620417663407)
          ·
            refine ⟨33103597517289930626495111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22069065011526620417663407 33103597517289930626495111)
            ·
              refine ⟨49655396275934895939742667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33103597517289930626495111 49655396275934895939742667)
              ·
                refine ⟨74483094413902343909614001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49655396275934895939742667 74483094413902343909614001)
                ·
                  refine ⟨55862320810426757932210501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74483094413902343909614001 55862320810426757932210501)
                  ·
                    refine ⟨10474185151955017112289469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55862320810426757932210501 10474185151955017112289469)
                    ·
                      refine ⟨3927819431983131417108551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474185151955017112289469 3927819431983131417108551)
                      ·
                        rfl

theorem cell23_7649401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_7649401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649401 prefixEnd_7649401 := by exact prefixLift 7649401
  have htrace : WordTrace (prefixWord ++ tailWord_7649401) baseStart_7649401 baseEnd_7649401 := by
    simpa [prefixWord, tailWord_7649401, baseEnd_7649401] using wordTrace_append hprefix tailTrace_7649401
  have hstable : (prefixWord ++ tailWord_7649401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649401).length < 2 ^ (prefixWord ++ tailWord_7649401).sum := by decide
  have hdescent : baseEnd_7649401 < baseStart_7649401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649411 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4]
def baseStart_7649411 : Nat := 118140960795 + 7649411 * 2 ^ 59
def prefixEnd_7649411 : Nat := 4983230072969 + 3 ^ 40 * 7649411 * 2
def baseEnd_7649411 : Nat := 3927824566789676377983505

theorem tailTrace_7649411 : CollatzResearch.WordTrace tailWord_7649411 prefixEnd_7649411 3927824566789676377983505 := by
  unfold tailWord_7649411
  simp only [CollatzResearch.WordTrace]
  refine ⟨278996939690497837234868087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185997959793665224823245391 278996939690497837234868087)
  ·
    refine ⟨418495409535746755852302131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278996939690497837234868087 418495409535746755852302131)
    ·
      refine ⟨627743114303620133778453197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418495409535746755852302131 627743114303620133778453197)
      ·
        refine ⟨235403667863857550166919949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627743114303620133778453197 235403667863857550166919949)
        ·
          refine ⟨88276375448946581312594981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235403667863857550166919949 88276375448946581312594981)
          ·
            refine ⟨16551820396677483996111559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88276375448946581312594981 16551820396677483996111559)
            ·
              refine ⟨24827730595016225994167339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16551820396677483996111559 24827730595016225994167339)
              ·
                refine ⟨37241595892524338991251009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24827730595016225994167339 37241595892524338991251009)
                ·
                  refine ⟨27931196919393254243438257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37241595892524338991251009 27931196919393254243438257)
                  ·
                    refine ⟨20948397689544940682578693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27931196919393254243438257 20948397689544940682578693)
                    ·
                      refine ⟨3927824566789676377983505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20948397689544940682578693 3927824566789676377983505)
                      ·
                        rfl

theorem cell23_7649411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_7649411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649411 prefixEnd_7649411 := by exact prefixLift 7649411
  have htrace : WordTrace (prefixWord ++ tailWord_7649411) baseStart_7649411 baseEnd_7649411 := by
    simpa [prefixWord, tailWord_7649411, baseEnd_7649411] using wordTrace_append hprefix tailTrace_7649411
  have hstable : (prefixWord ++ tailWord_7649411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649411).length < 2 ^ (prefixWord ++ tailWord_7649411).sum := by decide
  have hdescent : baseEnd_7649411 < baseStart_7649411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649415 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_7649415 : Nat := 118140960795 + 7649415 * 2 ^ 59
def prefixEnd_7649415 : Nat := 4983230072969 + 3 ^ 40 * 7649415 * 2
def baseEnd_7649415 : Nat := 3927826620712294362333487

theorem tailTrace_7649415 : CollatzResearch.WordTrace tailWord_7649415 prefixEnd_7649415 3927826620712294362333487 := by
  unfold tailWord_7649415
  simp only [CollatzResearch.WordTrace]
  refine ⟨278997085582483345918013699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185998057054988897278675799 278997085582483345918013699)
  ·
    refine ⟨418495628373725018877020549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278997085582483345918013699 418495628373725018877020549)
    ·
      refine ⟨78467930320073441039441353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418495628373725018877020549 78467930320073441039441353)
      ·
        refine ⟨58850947740055080779581015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78467930320073441039441353 58850947740055080779581015)
        ·
          refine ⟨88276421610082621169371523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58850947740055080779581015 88276421610082621169371523)
          ·
            refine ⟨132414632415123931754057285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88276421610082621169371523 132414632415123931754057285)
            ·
              refine ⟨24827743577835737203885741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132414632415123931754057285 24827743577835737203885741)
              ·
                refine ⟨9310403841688401451457153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24827743577835737203885741 9310403841688401451457153)
                ·
                  refine ⟨6982802881266301088592865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9310403841688401451457153 6982802881266301088592865)
                  ·
                    refine ⟨5237102160949725816444649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6982802881266301088592865 5237102160949725816444649)
                    ·
                      refine ⟨3927826620712294362333487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237102160949725816444649 3927826620712294362333487)
                      ·
                        rfl

theorem cell23_7649415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_7649415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649415 prefixEnd_7649415 := by exact prefixLift 7649415
  have htrace : WordTrace (prefixWord ++ tailWord_7649415) baseStart_7649415 baseEnd_7649415 := by
    simpa [prefixWord, tailWord_7649415, baseEnd_7649415] using wordTrace_append hprefix tailTrace_7649415
  have hstable : (prefixWord ++ tailWord_7649415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649415).length < 2 ^ (prefixWord ++ tailWord_7649415).sum := by decide
  have hdescent : baseEnd_7649415 < baseStart_7649415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649430 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7649430 : Nat := 118140960795 + 7649430 * 2 ^ 59
def prefixEnd_7649430 : Nat := 4983230072969 + 3 ^ 40 * 7649430 * 2
def baseEnd_7649430 : Nat := 3927834322922111803645919

theorem tailTrace_7649430 : CollatzResearch.WordTrace tailWord_7649430 prefixEnd_7649430 3927834322922111803645919 := by
  unfold tailWord_7649430
  simp only [CollatzResearch.WordTrace]
  refine ⟨17437352042339312717488109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185998421784952668986539829 17437352042339312717488109)
  ·
    refine ⟨6539007015877242269058041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17437352042339312717488109 6539007015877242269058041)
    ·
      refine ⟨4904255261907931701793531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6539007015877242269058041 4904255261907931701793531)
      ·
        refine ⟨7356382892861897552690297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904255261907931701793531 7356382892861897552690297)
        ·
          refine ⟨5517287169646423164517723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7356382892861897552690297 5517287169646423164517723)
          ·
            refine ⟨8275930754469634746776585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517287169646423164517723 8275930754469634746776585)
            ·
              refine ⟨6206948065852226060082439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8275930754469634746776585 6206948065852226060082439)
              ·
                refine ⟨9310422098778339090123659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206948065852226060082439 9310422098778339090123659)
                ·
                  refine ⟨13965633148167508635185489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9310422098778339090123659 13965633148167508635185489)
                  ·
                    refine ⟨10474224861125631476389117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13965633148167508635185489 10474224861125631476389117)
                    ·
                      refine ⟨3927834322922111803645919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474224861125631476389117 3927834322922111803645919)
                      ·
                        rfl

theorem cell23_7649430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7649430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649430 prefixEnd_7649430 := by exact prefixLift 7649430
  have htrace : WordTrace (prefixWord ++ tailWord_7649430) baseStart_7649430 baseEnd_7649430 := by
    simpa [prefixWord, tailWord_7649430, baseEnd_7649430] using wordTrace_append hprefix tailTrace_7649430
  have hstable : (prefixWord ++ tailWord_7649430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649430).length < 2 ^ (prefixWord ++ tailWord_7649430).sum := by decide
  have hdescent : baseEnd_7649430 < baseStart_7649430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649481 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_7649481 : Nat := 118140960795 + 7649481 * 2 ^ 59
def prefixEnd_7649481 : Nat := 4983230072969 + 3 ^ 40 * 7649481 * 2
def baseEnd_7649481 : Nat := 1309286836811830368036061

theorem tailTrace_7649481 : CollatzResearch.WordTrace tailWord_7649481 prefixEnd_7649481 1309286836811830368036061 := by
  unfold tailWord_7649481
  simp only [CollatzResearch.WordTrace]
  refine ⟨278999492800244239189916297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185999661866829492793277531 278999492800244239189916297)
  ·
    refine ⟨209249619600183179392437223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278999492800244239189916297 209249619600183179392437223)
    ·
      refine ⟨313874429400274769088655835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209249619600183179392437223 313874429400274769088655835)
      ·
        refine ⟨470811644100412153632983753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313874429400274769088655835 470811644100412153632983753)
        ·
          refine ⟨353108733075309115224737815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470811644100412153632983753 353108733075309115224737815)
          ·
            refine ⟨529663099612963672837106723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353108733075309115224737815 529663099612963672837106723)
            ·
              refine ⟨794494649419445509255660085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529663099612963672837106723 794494649419445509255660085)
              ·
                refine ⟨74483873383073016492718133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 794494649419445509255660085 74483873383073016492718133)
                ·
                  refine ⟨6982863129663095296192325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74483873383073016492718133 6982863129663095296192325)
                  ·
                    refine ⟨1309286836811830368036061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6982863129663095296192325 1309286836811830368036061)
                    ·
                      rfl

theorem cell23_7649481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_7649481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649481 prefixEnd_7649481 := by exact prefixLift 7649481
  have htrace : WordTrace (prefixWord ++ tailWord_7649481) baseStart_7649481 baseEnd_7649481 := by
    simpa [prefixWord, tailWord_7649481, baseEnd_7649481] using wordTrace_append hprefix tailTrace_7649481
  have hstable : (prefixWord ++ tailWord_7649481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649481).length < 2 ^ (prefixWord ++ tailWord_7649481).sum := by decide
  have hdescent : baseEnd_7649481 < baseStart_7649481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649506 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 5]
def baseStart_7649506 : Nat := 118140960795 + 7649506 * 2 ^ 59
def prefixEnd_7649506 : Nat := 4983230072969 + 3 ^ 40 * 7649506 * 2
def baseEnd_7649506 : Nat := 436430371939094834032841

theorem tailTrace_7649506 : CollatzResearch.WordTrace tailWord_7649506 prefixEnd_7649506 436430371939094834032841 := by
  unfold tailWord_7649506
  simp only [CollatzResearch.WordTrace]
  refine ⟨69750101156288417114894093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186000269750102445639717581 69750101156288417114894093)
  ·
    refine ⟨26156287933608156418085285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69750101156288417114894093 26156287933608156418085285)
    ·
      refine ⟨4904303987551529328390991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26156287933608156418085285 4904303987551529328390991)
      ·
        refine ⟨7356455981327293992586487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904303987551529328390991 7356455981327293992586487)
        ·
          refine ⟨11034683971990940988879731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356455981327293992586487 11034683971990940988879731)
          ·
            refine ⟨16552025957986411483319597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034683971990940988879731 16552025957986411483319597)
            ·
              refine ⟨6207009734244904306244849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16552025957986411483319597 6207009734244904306244849)
              ·
                refine ⟨4655257300683678229683637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207009734244904306244849 4655257300683678229683637)
                ·
                  refine ⟨436430371939094834032841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4655257300683678229683637 436430371939094834032841)
                  ·
                    rfl

theorem cell23_7649506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_7649506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649506 prefixEnd_7649506 := by exact prefixLift 7649506
  have htrace : WordTrace (prefixWord ++ tailWord_7649506) baseStart_7649506 baseEnd_7649506 := by
    simpa [prefixWord, tailWord_7649506, baseEnd_7649506] using wordTrace_append hprefix tailTrace_7649506
  have hstable : (prefixWord ++ tailWord_7649506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649506).length < 2 ^ (prefixWord ++ tailWord_7649506).sum := by decide
  have hdescent : baseEnd_7649506 < baseStart_7649506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649566 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7649566 : Nat := 118140960795 + 7649566 * 2 ^ 59
def prefixEnd_7649566 : Nat := 4983230072969 + 3 ^ 40 * 7649566 * 2
def baseEnd_7649566 : Nat := 1309301385430374423848431

theorem tailTrace_7649566 : CollatzResearch.WordTrace tailWord_7649566 prefixEnd_7649566 1309301385430374423848431 := by
  unfold tailWord_7649566
  simp only [CollatzResearch.WordTrace]
  refine ⟨34875324125617037338345069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186001728669957532471173701 34875324125617037338345069)
  ·
    refine ⟨13078246547106389001879401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34875324125617037338345069 13078246547106389001879401)
    ·
      refine ⟨9808684910329791751409551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13078246547106389001879401 9808684910329791751409551)
      ·
        refine ⟨14713027365494687627114327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9808684910329791751409551 14713027365494687627114327)
        ·
          refine ⟨22069541048242031440671491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14713027365494687627114327 22069541048242031440671491)
          ·
            refine ⟨33104311572363047161007237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22069541048242031440671491 33104311572363047161007237)
            ·
              refine ⟨6207058419818071342688857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33104311572363047161007237 6207058419818071342688857)
              ·
                refine ⟨4655293814863553507016643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207058419818071342688857 4655293814863553507016643)
                ·
                  refine ⟨6982940722295330260524965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655293814863553507016643 6982940722295330260524965)
                  ·
                    refine ⟨1309301385430374423848431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6982940722295330260524965 1309301385430374423848431)
                    ·
                      rfl

theorem cell23_7649566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7649566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649566 prefixEnd_7649566 := by exact prefixLift 7649566
  have htrace : WordTrace (prefixWord ++ tailWord_7649566) baseStart_7649566 baseEnd_7649566 := by
    simpa [prefixWord, tailWord_7649566, baseEnd_7649566] using wordTrace_append hprefix tailTrace_7649566
  have hstable : (prefixWord ++ tailWord_7649566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649566).length < 2 ^ (prefixWord ++ tailWord_7649566).sum := by decide
  have hdescent : baseEnd_7649566 < baseStart_7649566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649571 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 3, 6]
def baseStart_7649571 : Nat := 118140960795 + 7649571 * 2 ^ 59
def prefixEnd_7649571 : Nat := 4983230072969 + 3 ^ 40 * 7649571 * 2
def baseEnd_7649571 : Nat := 1309302241231465250660923

theorem tailTrace_7649571 : CollatzResearch.WordTrace tailWord_7649571 prefixEnd_7649571 1309302241231465250660923 := by
  unfold tailWord_7649571
  simp only [CollatzResearch.WordTrace]
  refine ⟨279002775369918184560692567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186001850246612123040461711 279002775369918184560692567)
  ·
    refine ⟨418504163054877276841038851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279002775369918184560692567 418504163054877276841038851)
    ·
      refine ⟨627756244582315915261558277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418504163054877276841038851 627756244582315915261558277)
      ·
        refine ⟨117704295859184234111542177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627756244582315915261558277 117704295859184234111542177)
        ·
          refine ⟨88278221894388175583656633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117704295859184234111542177 88278221894388175583656633)
          ·
            refine ⟨66208666420791131687742475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88278221894388175583656633 66208666420791131687742475)
            ·
              refine ⟨99312999631186697531613713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66208666420791131687742475 99312999631186697531613713)
              ·
                refine ⟨74484749723390023148710285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99312999631186697531613713 74484749723390023148710285)
                ·
                  refine ⟨27931781146271258680766357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74484749723390023148710285 27931781146271258680766357)
                  ·
                    refine ⟨1309302241231465250660923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27931781146271258680766357 1309302241231465250660923)
                    ·
                      rfl

theorem cell23_7649571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_7649571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649571 prefixEnd_7649571 := by exact prefixLift 7649571
  have htrace : WordTrace (prefixWord ++ tailWord_7649571) baseStart_7649571 baseEnd_7649571 := by
    simpa [prefixWord, tailWord_7649571, baseEnd_7649571] using wordTrace_append hprefix tailTrace_7649571
  have hstable : (prefixWord ++ tailWord_7649571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649571).length < 2 ^ (prefixWord ++ tailWord_7649571).sum := by decide
  have hdescent : baseEnd_7649571 < baseStart_7649571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649591 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_7649591 : Nat := 118140960795 + 7649591 * 2 ^ 59
def prefixEnd_7649591 : Nat := 4983230072969 + 3 ^ 40 * 7649591 * 2
def baseEnd_7649591 : Nat := 3927916993307485673732677

theorem tailTrace_7649591 : CollatzResearch.WordTrace tailWord_7649591 prefixEnd_7649591 3927916993307485673732677 := by
  unfold tailWord_7649591
  simp only [CollatzResearch.WordTrace]
  refine ⟨279003504829845727976420627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186002336553230485317613751 279003504829845727976420627)
  ·
    refine ⟨418505257244768591964630941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279003504829845727976420627 418505257244768591964630941)
    ·
      refine ⟨156939471466788221986736603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418505257244768591964630941 156939471466788221986736603)
      ·
        refine ⟨235409207200182332980104905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156939471466788221986736603 235409207200182332980104905)
        ·
          refine ⟨176556905400136749735078679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235409207200182332980104905 176556905400136749735078679)
          ·
            refine ⟨264835358100205124602618019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176556905400136749735078679 264835358100205124602618019)
            ·
              refine ⟨397253037150307686903927029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264835358100205124602618019 397253037150307686903927029)
              ·
                refine ⟨37242472232841345647243159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397253037150307686903927029 37242472232841345647243159)
                ·
                  refine ⟨55863708349262018470864739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37242472232841345647243159 55863708349262018470864739)
                  ·
                    refine ⟨83795562523893027706297109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55863708349262018470864739 83795562523893027706297109)
                    ·
                      refine ⟨3927916993307485673732677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83795562523893027706297109 3927916993307485673732677)
                      ·
                        rfl

theorem cell23_7649591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_7649591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649591 prefixEnd_7649591 := by exact prefixLift 7649591
  have htrace : WordTrace (prefixWord ++ tailWord_7649591) baseStart_7649591 baseEnd_7649591 := by
    simpa [prefixWord, tailWord_7649591, baseEnd_7649591] using wordTrace_append hprefix tailTrace_7649591
  have hstable : (prefixWord ++ tailWord_7649591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649591).length < 2 ^ (prefixWord ++ tailWord_7649591).sum := by decide
  have hdescent : baseEnd_7649591 < baseStart_7649591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649608 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_7649608 : Nat := 118140960795 + 7649608 * 2 ^ 59
def prefixEnd_7649608 : Nat := 4983230072969 + 3 ^ 40 * 7649608 * 2
def baseEnd_7649608 : Nat := 3927925722478612107220099

theorem tailTrace_7649608 : CollatzResearch.WordTrace tailWord_7649608 prefixEnd_7649608 3927925722478612107220099 := by
  unfold tailWord_7649608
  simp only [CollatzResearch.WordTrace]
  refine ⟨139502062435392069939894739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186002749913856093253192985 139502062435392069939894739)
  ·
    refine ⟨209253093653088104909842109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139502062435392069939894739 209253093653088104909842109)
    ·
      refine ⟨78469910119908039341190791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209253093653088104909842109 78469910119908039341190791)
      ·
        refine ⟨117704865179862059011786187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78469910119908039341190791 117704865179862059011786187)
        ·
          refine ⟨176557297769793088517679281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117704865179862059011786187 176557297769793088517679281)
          ·
            refine ⟨132417973327344816388259461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176557297769793088517679281 132417973327344816388259461)
            ·
              refine ⟨24828369998877153072798649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132417973327344816388259461 24828369998877153072798649)
              ·
                refine ⟨18621277499157864804598987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24828369998877153072798649 18621277499157864804598987)
                ·
                  refine ⟨27931916248736797206898481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18621277499157864804598987 27931916248736797206898481)
                  ·
                    refine ⟨20948937186552597905173861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27931916248736797206898481 20948937186552597905173861)
                    ·
                      refine ⟨3927925722478612107220099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20948937186552597905173861 3927925722478612107220099)
                      ·
                        rfl

theorem cell23_7649608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_7649608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649608 prefixEnd_7649608 := by exact prefixLift 7649608
  have htrace : WordTrace (prefixWord ++ tailWord_7649608) baseStart_7649608 baseEnd_7649608 := by
    simpa [prefixWord, tailWord_7649608, baseEnd_7649608] using wordTrace_append hprefix tailTrace_7649608
  have hstable : (prefixWord ++ tailWord_7649608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649608).length < 2 ^ (prefixWord ++ tailWord_7649608).sum := by decide
  have hdescent : baseEnd_7649608 < baseStart_7649608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649631 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 9]
def baseStart_7649631 : Nat := 118140960795 + 7649631 * 2 ^ 59
def prefixEnd_7649631 : Nat := 4983230072969 + 3 ^ 40 * 7649631 * 2
def baseEnd_7649631 : Nat := 1309312510844555172410831

theorem tailTrace_7649631 : CollatzResearch.WordTrace tailWord_7649631 prefixEnd_7649631 1309312510844555172410831 := by
  unfold tailWord_7649631
  simp only [CollatzResearch.WordTrace]
  refine ⟨279004963749700814807876747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186003309166467209871917831 279004963749700814807876747)
  ·
    refine ⟨418507445624551222211815121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279004963749700814807876747 418507445624551222211815121)
    ·
      refine ⟨313880584218413416658861341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418507445624551222211815121 313880584218413416658861341)
      ·
        refine ⟨117705219081905031247073003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313880584218413416658861341 117705219081905031247073003)
        ·
          refine ⟨176557828622857546870609505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117705219081905031247073003 176557828622857546870609505)
          ·
            refine ⟨132418371467143160152957129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176557828622857546870609505 132418371467143160152957129)
            ·
              refine ⟨99313778600357370114717847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132418371467143160152957129 99313778600357370114717847)
              ·
                refine ⟨148970667900536055172076771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99313778600357370114717847 148970667900536055172076771)
                ·
                  refine ⟨223456001850804082758115157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148970667900536055172076771 223456001850804082758115157)
                  ·
                    refine ⟨1309312510844555172410831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223456001850804082758115157 1309312510844555172410831)
                    ·
                      rfl

theorem cell23_7649631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_7649631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649631 prefixEnd_7649631 := by exact prefixLift 7649631
  have htrace : WordTrace (prefixWord ++ tailWord_7649631) baseStart_7649631 baseEnd_7649631 := by
    simpa [prefixWord, tailWord_7649631, baseEnd_7649631] using wordTrace_append hprefix tailTrace_7649631
  have hstable : (prefixWord ++ tailWord_7649631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649631).length < 2 ^ (prefixWord ++ tailWord_7649631).sum := by decide
  have hdescent : baseEnd_7649631 < baseStart_7649631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649642 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7649642 : Nat := 118140960795 + 7649642 * 2 ^ 59
def prefixEnd_7649642 : Nat := 4983230072969 + 3 ^ 40 * 7649642 * 2
def baseEnd_7649642 : Nat := 3927943180820864974194943

theorem tailTrace_7649642 : CollatzResearch.WordTrace tailWord_7649642 prefixEnd_7649642 3927943180820864974194943 := by
  unfold tailWord_7649642
  simp only [CollatzResearch.WordTrace]
  refine ⟨69751341238165240921631795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186003576635107309124351453 69751341238165240921631795)
  ·
    refine ⟨104627011857247861382447693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69751341238165240921631795 104627011857247861382447693)
    ·
      refine ⟨39235129446467948018417885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104627011857247861382447693 39235129446467948018417885)
      ·
        refine ⟨14713173542425480506906707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39235129446467948018417885 14713173542425480506906707)
        ·
          refine ⟨22069760313638220760360061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14713173542425480506906707 22069760313638220760360061)
          ·
            refine ⟨8276160117614332785135023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22069760313638220760360061 8276160117614332785135023)
            ·
              refine ⟨12414240176421499177702535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276160117614332785135023 12414240176421499177702535)
              ·
                refine ⟨18621360264632248766553803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12414240176421499177702535 18621360264632248766553803)
                ·
                  refine ⟨27932040396948373149830705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18621360264632248766553803 27932040396948373149830705)
                  ·
                    refine ⟨20949030297711279862373029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27932040396948373149830705 20949030297711279862373029)
                    ·
                      refine ⟨3927943180820864974194943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20949030297711279862373029 3927943180820864974194943)
                      ·
                        rfl

theorem cell23_7649642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7649642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649642 prefixEnd_7649642 := by exact prefixLift 7649642
  have htrace : WordTrace (prefixWord ++ tailWord_7649642) baseStart_7649642 baseEnd_7649642 := by
    simpa [prefixWord, tailWord_7649642, baseEnd_7649642] using wordTrace_append hprefix tailTrace_7649642
  have hstable : (prefixWord ++ tailWord_7649642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649642).length < 2 ^ (prefixWord ++ tailWord_7649642).sum := by decide
  have hdescent : baseEnd_7649642 < baseStart_7649642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649672 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7649672 : Nat := 118140960795 + 7649672 * 2 ^ 59
def prefixEnd_7649672 : Nat := 4983230072969 + 3 ^ 40 * 7649672 * 2
def baseEnd_7649672 : Nat := 3927958585240499856819805

theorem tailTrace_7649672 : CollatzResearch.WordTrace tailWord_7649672 prefixEnd_7649672 3927958585240499856819805 := by
  unfold tailWord_7649672
  simp only [CollatzResearch.WordTrace]
  refine ⟨139503229571276139405059635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186004306095034852540079513 139503229571276139405059635)
  ·
    refine ⟨209254844356914209107589453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139503229571276139405059635 209254844356914209107589453)
    ·
      refine ⟨78470566633842828415346045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209254844356914209107589453 78470566633842828415346045)
      ·
        refine ⟨29426462487691060655754767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78470566633842828415346045 29426462487691060655754767)
        ·
          refine ⟨44139693731536590983632151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29426462487691060655754767 44139693731536590983632151)
          ·
            refine ⟨66209540597304886475448227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44139693731536590983632151 66209540597304886475448227)
            ·
              refine ⟨99314310895957329713172341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66209540597304886475448227 99314310895957329713172341)
              ·
                refine ⟨9310716646495999660609907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99314310895957329713172341 9310716646495999660609907)
                ·
                  refine ⟨13966074969743999490914861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9310716646495999660609907 13966074969743999490914861)
                  ·
                    refine ⟨5237278113653999809093073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13966074969743999490914861 5237278113653999809093073)
                    ·
                      refine ⟨3927958585240499856819805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237278113653999809093073 3927958585240499856819805)
                      ·
                        rfl

theorem cell23_7649672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7649672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649672 prefixEnd_7649672 := by exact prefixLift 7649672
  have htrace : WordTrace (prefixWord ++ tailWord_7649672) baseStart_7649672 baseEnd_7649672 := by
    simpa [prefixWord, tailWord_7649672, baseEnd_7649672] using wordTrace_append hprefix tailTrace_7649672
  have hstable : (prefixWord ++ tailWord_7649672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649672).length < 2 ^ (prefixWord ++ tailWord_7649672).sum := by decide
  have hdescent : baseEnd_7649672 < baseStart_7649672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649775 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 6, 2]
def baseStart_7649775 : Nat := 118140960795 + 7649775 * 2 ^ 59
def prefixEnd_7649775 : Nat := 4983230072969 + 3 ^ 40 * 7649775 * 2
def baseEnd_7649775 : Nat := 3928011473747912953831831

theorem tailTrace_7649775 : CollatzResearch.WordTrace tailWord_7649775 prefixEnd_7649775 3928011473747912953831831 := by
  unfold tailWord_7649775
  simp only [CollatzResearch.WordTrace]
  refine ⟨279010215861179127401118779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186006810574119418267412519 279010215861179127401118779)
  ·
    refine ⟨418515323791768691101678169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279010215861179127401118779 418515323791768691101678169)
    ·
      refine ⟨313886492843826518326258627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418515323791768691101678169 313886492843826518326258627)
      ·
        refine ⟨470829739265739777489387941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313886492843826518326258627 470829739265739777489387941)
        ·
          refine ⟨88280576112326208279260239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470829739265739777489387941 88280576112326208279260239)
          ·
            refine ⟨132420864168489312418890359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88280576112326208279260239 132420864168489312418890359)
            ·
              refine ⟨198631296252733968628335539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132420864168489312418890359 198631296252733968628335539)
              ·
                refine ⟨297946944379100952942503309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198631296252733968628335539 297946944379100952942503309)
                ·
                  refine ⟨111730104142162857353438741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297946944379100952942503309 111730104142162857353438741)
                  ·
                    refine ⟨5237348631663883938442441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111730104142162857353438741 5237348631663883938442441)
                    ·
                      refine ⟨3928011473747912953831831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237348631663883938442441 3928011473747912953831831)
                      ·
                        rfl

theorem cell23_7649775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6, 2].length) (baseStart_7649775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649775 prefixEnd_7649775 := by exact prefixLift 7649775
  have htrace : WordTrace (prefixWord ++ tailWord_7649775) baseStart_7649775 baseEnd_7649775 := by
    simpa [prefixWord, tailWord_7649775, baseEnd_7649775] using wordTrace_append hprefix tailTrace_7649775
  have hstable : (prefixWord ++ tailWord_7649775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649775).length < 2 ^ (prefixWord ++ tailWord_7649775).sum := by decide
  have hdescent : baseEnd_7649775 < baseStart_7649775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649795 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3]
def baseStart_7649795 : Nat := 118140960795 + 7649795 * 2 ^ 59
def prefixEnd_7649795 : Nat := 4983230072969 + 3 ^ 40 * 7649795 * 2
def baseEnd_7649795 : Nat := 3928021743361002875581739

theorem tailTrace_7649795 : CollatzResearch.WordTrace tailWord_7649795 prefixEnd_7649795 3928021743361002875581739 := by
  unfold tailWord_7649795
  simp only [CollatzResearch.WordTrace]
  refine ⟨279010945321106670816846839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186007296880737780544564559 279010945321106670816846839)
  ·
    refine ⟨418516417981660006225270259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279010945321106670816846839 418516417981660006225270259)
    ·
      refine ⟨627774626972490009337905389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418516417981660006225270259 627774626972490009337905389)
      ·
        refine ⟨235415485114683753501714521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627774626972490009337905389 235415485114683753501714521)
        ·
          refine ⟨176561613836012815126285891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235415485114683753501714521 176561613836012815126285891)
          ·
            refine ⟨264842420754019222689428837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176561613836012815126285891 264842420754019222689428837)
            ·
              refine ⟨49657953891378604254267907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264842420754019222689428837 49657953891378604254267907)
              ·
                refine ⟨74486930837067906381401861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49657953891378604254267907 74486930837067906381401861)
                ·
                  refine ⟨13966299531950232446512849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74486930837067906381401861 13966299531950232446512849)
                  ·
                    refine ⟨10474724648962674334884637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13966299531950232446512849 10474724648962674334884637)
                    ·
                      refine ⟨3928021743361002875581739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474724648962674334884637 3928021743361002875581739)
                      ·
                        rfl

theorem cell23_7649795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_7649795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649795 prefixEnd_7649795 := by exact prefixLift 7649795
  have htrace : WordTrace (prefixWord ++ tailWord_7649795) baseStart_7649795 baseEnd_7649795 := by
    simpa [prefixWord, tailWord_7649795, baseEnd_7649795] using wordTrace_append hprefix tailTrace_7649795
  have hstable : (prefixWord ++ tailWord_7649795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649795).length < 2 ^ (prefixWord ++ tailWord_7649795).sum := by decide
  have hdescent : baseEnd_7649795 < baseStart_7649795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649802 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_7649802 : Nat := 118140960795 + 7649802 * 2 ^ 59
def prefixEnd_7649802 : Nat := 4983230072969 + 3 ^ 40 * 7649802 * 2
def baseEnd_7649802 : Nat := 1309341779241861449398069

theorem tailTrace_7649802 : CollatzResearch.WordTrace tailWord_7649802 prefixEnd_7649802 1309341779241861449398069 := by
  unfold tailWord_7649802
  simp only [CollatzResearch.WordTrace]
  refine ⟨69752800158020327753087915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186007467088054207341567773 69752800158020327753087915)
  ·
    refine ⟨104629200237030491629631873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69752800158020327753087915 104629200237030491629631873)
    ·
      refine ⟨78471900177772868722223905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104629200237030491629631873 78471900177772868722223905)
      ·
        refine ⟨58853925133329651541667929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78471900177772868722223905 58853925133329651541667929)
        ·
          refine ⟨44140443849997238656250947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58853925133329651541667929 44140443849997238656250947)
          ·
            refine ⟨66210665774995857984376421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44140443849997238656250947 66210665774995857984376421)
            ·
              refine ⟨12414499832811723372070579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66210665774995857984376421 12414499832811723372070579)
              ·
                refine ⟨18621749749217585058105869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12414499832811723372070579 18621749749217585058105869)
                ·
                  refine ⟨6983156155956594396789701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18621749749217585058105869 6983156155956594396789701)
                  ·
                    refine ⟨1309341779241861449398069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983156155956594396789701 1309341779241861449398069)
                    ·
                      rfl

theorem cell23_7649802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_7649802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649802 prefixEnd_7649802 := by exact prefixLift 7649802
  have htrace : WordTrace (prefixWord ++ tailWord_7649802) baseStart_7649802 baseEnd_7649802 := by
    simpa [prefixWord, tailWord_7649802, baseEnd_7649802] using wordTrace_append hprefix tailTrace_7649802
  have hstable : (prefixWord ++ tailWord_7649802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649802).length < 2 ^ (prefixWord ++ tailWord_7649802).sum := by decide
  have hdescent : baseEnd_7649802 < baseStart_7649802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649825 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7649825 : Nat := 118140960795 + 7649825 * 2 ^ 59
def prefixEnd_7649825 : Nat := 4983230072969 + 3 ^ 40 * 7649825 * 2
def baseEnd_7649825 : Nat := 3928037147780637758206601

theorem tailTrace_7649825 : CollatzResearch.WordTrace tailWord_7649825 prefixEnd_7649825 3928037147780637758206601 := by
  unfold tailWord_7649825
  simp only [CollatzResearch.WordTrace]
  refine ⟨279012039510997985940438929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186008026340665323960292619 279012039510997985940438929)
  ·
    refine ⟨209259029633248489455329197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279012039510997985940438929 209259029633248489455329197)
    ·
      refine ⟨78472136112468183545748449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209259029633248489455329197 78472136112468183545748449)
      ·
        refine ⟨58854102084351137659311337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78472136112468183545748449 58854102084351137659311337)
        ·
          refine ⟨44140576563263353244483503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58854102084351137659311337 44140576563263353244483503)
          ·
            refine ⟨66210864844895029866725255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44140576563263353244483503 66210864844895029866725255)
            ·
              refine ⟨99316297267342544800087883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66210864844895029866725255 99316297267342544800087883)
              ·
                refine ⟨148974445901013817200131825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99316297267342544800087883 148974445901013817200131825)
                ·
                  refine ⟨111730834425760362900098869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148974445901013817200131825 111730834425760362900098869)
                  ·
                    refine ⟨10474765727415034021884269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111730834425760362900098869 10474765727415034021884269)
                    ·
                      refine ⟨3928037147780637758206601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474765727415034021884269 3928037147780637758206601)
                      ·
                        rfl

theorem cell23_7649825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7649825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649825 prefixEnd_7649825 := by exact prefixLift 7649825
  have htrace : WordTrace (prefixWord ++ tailWord_7649825) baseStart_7649825 baseEnd_7649825 := by
    simpa [prefixWord, tailWord_7649825, baseEnd_7649825] using wordTrace_append hprefix tailTrace_7649825
  have hstable : (prefixWord ++ tailWord_7649825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649825).length < 2 ^ (prefixWord ++ tailWord_7649825).sum := by decide
  have hdescent : baseEnd_7649825 < baseStart_7649825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649842 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_7649842 : Nat := 118140960795 + 7649842 * 2 ^ 59
def prefixEnd_7649842 : Nat := 4983230072969 + 3 ^ 40 * 7649842 * 2
def baseEnd_7649842 : Nat := 3928045876951764191694023

theorem tailTrace_7649842 : CollatzResearch.WordTrace tailWord_7649842 prefixEnd_7649842 3928045876951764191694023 := by
  unfold tailWord_7649842
  simp only [CollatzResearch.WordTrace]
  refine ⟨69753164887984099460951945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186008439701290931895871853 69753164887984099460951945)
  ·
    refine ⟨52314873665988074595713959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69753164887984099460951945 52314873665988074595713959)
    ·
      refine ⟨78472310498982111893570939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52314873665988074595713959 78472310498982111893570939)
      ·
        refine ⟨117708465748473167840356409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78472310498982111893570939 117708465748473167840356409)
        ·
          refine ⟨88281349311354875880267307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117708465748473167840356409 88281349311354875880267307)
          ·
            refine ⟨132422023967032313820400961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88281349311354875880267307 132422023967032313820400961)
            ·
              refine ⟨99316517975274235365300721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132422023967032313820400961 99316517975274235365300721)
              ·
                refine ⟨74487388481455676523975541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99316517975274235365300721 74487388481455676523975541)
                ·
                  refine ⟨6983192670136469674122707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74487388481455676523975541 6983192670136469674122707)
                  ·
                    refine ⟨10474789005204704511184061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983192670136469674122707 10474789005204704511184061)
                    ·
                      refine ⟨3928045876951764191694023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474789005204704511184061 3928045876951764191694023)
                      ·
                        rfl

theorem cell23_7649842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_7649842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649842 prefixEnd_7649842 := by exact prefixLift 7649842
  have htrace : WordTrace (prefixWord ++ tailWord_7649842) baseStart_7649842 baseEnd_7649842 := by
    simpa [prefixWord, tailWord_7649842, baseEnd_7649842] using wordTrace_append hprefix tailTrace_7649842
  have hstable : (prefixWord ++ tailWord_7649842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649842).length < 2 ^ (prefixWord ++ tailWord_7649842).sum := by decide
  have hdescent : baseEnd_7649842 < baseStart_7649842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649859 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 1, 1, 3]
def baseStart_7649859 : Nat := 118140960795 + 7649859 * 2 ^ 59
def prefixEnd_7649859 : Nat := 4983230072969 + 3 ^ 40 * 7649859 * 2
def baseEnd_7649859 : Nat := 3928054606122890625181445

theorem tailTrace_7649859 : CollatzResearch.WordTrace tailWord_7649859 prefixEnd_7649859 3928054606122890625181445 := by
  unfold tailWord_7649859
  simp only [CollatzResearch.WordTrace]
  refine ⟨279013279592874809747176631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186008853061916539831451087 279013279592874809747176631)
  ·
    refine ⟨418519919389312214620764947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279013279592874809747176631 418519919389312214620764947)
    ·
      refine ⟨627779879083968321931147421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418519919389312214620764947 627779879083968321931147421)
      ·
        refine ⟨235417454656488120724180283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627779879083968321931147421 235417454656488120724180283)
        ·
          refine ⟨353126181984732181086270425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235417454656488120724180283 353126181984732181086270425)
          ·
            refine ⟨264844636488549135814702819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353126181984732181086270425 264844636488549135814702819)
            ·
              refine ⟨397266954732823703722054229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264844636488549135814702819 397266954732823703722054229)
              ·
                refine ⟨4655472125775277777992823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 397266954732823703722054229 4655472125775277777992823)
                ·
                  refine ⟨6983208188662916666989235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655472125775277777992823 6983208188662916666989235)
                  ·
                    refine ⟨10474812282994375000483853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983208188662916666989235 10474812282994375000483853)
                    ·
                      refine ⟨3928054606122890625181445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474812282994375000483853 3928054606122890625181445)
                      ·
                        rfl

theorem cell23_7649859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_7649859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649859 prefixEnd_7649859 := by exact prefixLift 7649859
  have htrace : WordTrace (prefixWord ++ tailWord_7649859) baseStart_7649859 baseEnd_7649859 := by
    simpa [prefixWord, tailWord_7649859, baseEnd_7649859] using wordTrace_append hprefix tailTrace_7649859
  have hstable : (prefixWord ++ tailWord_7649859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649859).length < 2 ^ (prefixWord ++ tailWord_7649859).sum := by decide
  have hdescent : baseEnd_7649859 < baseStart_7649859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649896 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 1, 5]
def baseStart_7649896 : Nat := 118140960795 + 7649896 * 2 ^ 59
def prefixEnd_7649896 : Nat := 4983230072969 + 3 ^ 40 * 7649896 * 2
def baseEnd_7649896 : Nat := 1309357868302368993472925

theorem tailTrace_7649896 : CollatzResearch.WordTrace tailWord_7649896 prefixEnd_7649896 1309357868302368993472925 := by
  unfold tailWord_7649896
  simp only [CollatzResearch.WordTrace]
  refine ⟨139507314546870382533136771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186009752729160510044182361 139507314546870382533136771)
  ·
    refine ⟨209260971820305573799705157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139507314546870382533136771 209260971820305573799705157)
    ·
      refine ⟨39236432216307295087444717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209260971820305573799705157 39236432216307295087444717)
      ·
        refine ⟨14713662081115235657791769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39236432216307295087444717 14713662081115235657791769)
        ·
          refine ⟨11035246560836426743343827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14713662081115235657791769 11035246560836426743343827)
          ·
            refine ⟨16552869841254640115015741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11035246560836426743343827 16552869841254640115015741)
            ·
              refine ⟨6207326190470490043130903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16552869841254640115015741 6207326190470490043130903)
              ·
                refine ⟨9310989285705735064696355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207326190470490043130903 9310989285705735064696355)
                ·
                  refine ⟨13966483928558602597044533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9310989285705735064696355 13966483928558602597044533)
                  ·
                    refine ⟨1309357868302368993472925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13966483928558602597044533 1309357868302368993472925)
                    ·
                      rfl

theorem cell23_7649896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_7649896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649896 prefixEnd_7649896 := by exact prefixLift 7649896
  have htrace : WordTrace (prefixWord ++ tailWord_7649896) baseStart_7649896 baseEnd_7649896 := by
    simpa [prefixWord, tailWord_7649896, baseEnd_7649896] using wordTrace_append hprefix tailTrace_7649896
  have hstable : (prefixWord ++ tailWord_7649896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649896).length < 2 ^ (prefixWord ++ tailWord_7649896).sum := by decide
  have hdescent : baseEnd_7649896 < baseStart_7649896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649945 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_7649945 : Nat := 118140960795 + 7649945 * 2 ^ 59
def prefixEnd_7649945 : Nat := 4983230072969 + 3 ^ 40 * 7649945 * 2
def baseEnd_7649945 : Nat := 3928098765459177288706049

theorem tailTrace_7649945 : CollatzResearch.WordTrace tailWord_7649945 prefixEnd_7649945 3928098765459177288706049 := by
  unfold tailWord_7649945
  simp only [CollatzResearch.WordTrace]
  refine ⟨279016416270563246434807289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186010944180375497623204859 279016416270563246434807289)
  ·
    refine ⟨209262312202922434826105467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279016416270563246434807289 209262312202922434826105467)
    ·
      refine ⟨313893468304383652239158201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209262312202922434826105467 313893468304383652239158201)
      ·
        refine ⟨235420101228287739179368651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313893468304383652239158201 235420101228287739179368651)
        ·
          refine ⟨353130151842431608769052977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235420101228287739179368651 353130151842431608769052977)
          ·
            refine ⟨264847613881823706576789733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353130151842431608769052977 264847613881823706576789733)
            ·
              refine ⟨49658927602841944983148075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264847613881823706576789733 49658927602841944983148075)
              ·
                refine ⟨74488391404262917474722113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49658927602841944983148075 74488391404262917474722113)
                ·
                  refine ⟨55866293553197188106041585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74488391404262917474722113 55866293553197188106041585)
                  ·
                    refine ⟨41899720164897891079531189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55866293553197188106041585 41899720164897891079531189)
                    ·
                      refine ⟨3928098765459177288706049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41899720164897891079531189 3928098765459177288706049)
                      ·
                        rfl

theorem cell23_7649945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_7649945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649945 prefixEnd_7649945 := by exact prefixLift 7649945
  have htrace : WordTrace (prefixWord ++ tailWord_7649945) baseStart_7649945 baseEnd_7649945 := by
    simpa [prefixWord, tailWord_7649945, baseEnd_7649945] using wordTrace_append hprefix tailTrace_7649945
  have hstable : (prefixWord ++ tailWord_7649945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649945).length < 2 ^ (prefixWord ++ tailWord_7649945).sum := by decide
  have hdescent : baseEnd_7649945 < baseStart_7649945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649950 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7649950 : Nat := 118140960795 + 7649950 * 2 ^ 59
def prefixEnd_7649950 : Nat := 4983230072969 + 3 ^ 40 * 7649950 * 2
def baseEnd_7649950 : Nat := 3928101332862449769143527

theorem tailTrace_7649950 : CollatzResearch.WordTrace tailWord_7649950 prefixEnd_7649950 3928101332862449769143527 := by
  unfold tailWord_7649950
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877074829443141536092413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186011065757030088192492869 34877074829443141536092413)
  ·
    refine ⟨13078903061041178076034655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34877074829443141536092413 13078903061041178076034655)
    ·
      refine ⟨19618354591561767114051983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13078903061041178076034655 19618354591561767114051983)
      ·
        refine ⟨29427531887342650671077975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618354591561767114051983 29427531887342650671077975)
        ·
          refine ⟨44141297831013976006616963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29427531887342650671077975 44141297831013976006616963)
          ·
            refine ⟨66211946746520964009925445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44141297831013976006616963 66211946746520964009925445)
            ·
              refine ⟨12414740014972680751861021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66211946746520964009925445 12414740014972680751861021)
              ·
                refine ⟨4655527505614755281947883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12414740014972680751861021 4655527505614755281947883)
                ·
                  refine ⟨6983291258422132922921825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655527505614755281947883 6983291258422132922921825)
                  ·
                    refine ⟨5237468443816599692191369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6983291258422132922921825 5237468443816599692191369)
                    ·
                      refine ⟨3928101332862449769143527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237468443816599692191369 3928101332862449769143527)
                      ·
                        rfl

theorem cell23_7649950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7649950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649950 prefixEnd_7649950 := by exact prefixLift 7649950
  have htrace : WordTrace (prefixWord ++ tailWord_7649950) baseStart_7649950 baseEnd_7649950 := by
    simpa [prefixWord, tailWord_7649950, baseEnd_7649950] using wordTrace_append hprefix tailTrace_7649950
  have hstable : (prefixWord ++ tailWord_7649950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649950).length < 2 ^ (prefixWord ++ tailWord_7649950).sum := by decide
  have hdescent : baseEnd_7649950 < baseStart_7649950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649953 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7649953 : Nat := 118140960795 + 7649953 * 2 ^ 59
def prefixEnd_7649953 : Nat := 4983230072969 + 3 ^ 40 * 7649953 * 2
def baseEnd_7649953 : Nat := 3928102873304413257406013

theorem tailTrace_7649953 : CollatzResearch.WordTrace tailWord_7649953 prefixEnd_7649953 3928102873304413257406013 := by
  unfold tailWord_7649953
  simp only [CollatzResearch.WordTrace]
  refine ⟨279016708054534263801098513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186011138703022842534065675 279016708054534263801098513)
  ·
    refine ⟨209262531040900697850823885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279016708054534263801098513 209262531040900697850823885)
    ·
      refine ⟨78473449140337761694058957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209262531040900697850823885 78473449140337761694058957)
      ·
        refine ⟨29427543427626660635272109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78473449140337761694058957 29427543427626660635272109)
        ·
          refine ⟨11035328785359997738227041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29427543427626660635272109 11035328785359997738227041)
          ·
            refine ⟨8276496589019998303670281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11035328785359997738227041 8276496589019998303670281)
            ·
              refine ⟨6207372441764998727752711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276496589019998303670281 6207372441764998727752711)
              ·
                refine ⟨9311058662647498091629067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207372441764998727752711 9311058662647498091629067)
                ·
                  refine ⟨13966587993971247137443601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9311058662647498091629067 13966587993971247137443601)
                  ·
                    refine ⟨10474940995478435353082701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13966587993971247137443601 10474940995478435353082701)
                    ·
                      refine ⟨3928102873304413257406013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10474940995478435353082701 3928102873304413257406013)
                      ·
                        rfl

theorem cell23_7649953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7649953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649953 prefixEnd_7649953 := by exact prefixLift 7649953
  have htrace : WordTrace (prefixWord ++ tailWord_7649953) baseStart_7649953 baseEnd_7649953 := by
    simpa [prefixWord, tailWord_7649953, baseEnd_7649953] using wordTrace_append hprefix tailTrace_7649953
  have hstable : (prefixWord ++ tailWord_7649953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649953).length < 2 ^ (prefixWord ++ tailWord_7649953).sum := by decide
  have hdescent : baseEnd_7649953 < baseStart_7649953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649955 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7649955 : Nat := 118140960795 + 7649955 * 2 ^ 59
def prefixEnd_7649955 : Nat := 4983230072969 + 3 ^ 40 * 7649955 * 2
def baseEnd_7649955 : Nat := 3928103900265722249581003

theorem tailTrace_7649955 : CollatzResearch.WordTrace tailWord_7649955 prefixEnd_7649955 3928103900265722249581003 := by
  unfold tailWord_7649955
  simp only [CollatzResearch.WordTrace]
  refine ⟨279016781000527018142671319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186011187333684678761780879 279016781000527018142671319)
  ·
    refine ⟨418525171500790527214006979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279016781000527018142671319 418525171500790527214006979)
    ·
      refine ⟨627787757251185790821010469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418525171500790527214006979 627787757251185790821010469)
      ·
        refine ⟨117710204484597335778939463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627787757251185790821010469 117710204484597335778939463)
        ·
          refine ⟨176565306726896003668409195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117710204484597335778939463 176565306726896003668409195)
          ·
            refine ⟨264847960090344005502613793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176565306726896003668409195 264847960090344005502613793)
            ·
              refine ⟨198635970067758004126960345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264847960090344005502613793 198635970067758004126960345)
              ·
                refine ⟨148976977550818503095220259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198635970067758004126960345 148976977550818503095220259)
                ·
                  refine ⟨223465466326227754642830389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148976977550818503095220259 223465466326227754642830389)
                  ·
                    refine ⟨20949887468083851997765349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223465466326227754642830389 20949887468083851997765349)
                    ·
                      refine ⟨3928103900265722249581003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20949887468083851997765349 3928103900265722249581003)
                      ·
                        rfl

theorem cell23_7649955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7649955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649955 prefixEnd_7649955 := by exact prefixLift 7649955
  have htrace : WordTrace (prefixWord ++ tailWord_7649955) baseStart_7649955 baseEnd_7649955 := by
    simpa [prefixWord, tailWord_7649955, baseEnd_7649955] using wordTrace_append hprefix tailTrace_7649955
  have hstable : (prefixWord ++ tailWord_7649955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649955).length < 2 ^ (prefixWord ++ tailWord_7649955).sum := by decide
  have hdescent : baseEnd_7649955 < baseStart_7649955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649982 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7649982 : Nat := 118140960795 + 7649982 * 2 ^ 59
def prefixEnd_7649982 : Nat := 4983230072969 + 3 ^ 40 * 7649982 * 2
def baseEnd_7649982 : Nat := 1309372588081131214647793

theorem tailTrace_7649982 : CollatzResearch.WordTrace tailWord_7649982 prefixEnd_7649982 1309372588081131214647793 := by
  unfold tailWord_7649982
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877220721428650219238025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186011843847619467835936133 34877220721428650219238025)
  ·
    refine ⟨26157915541071487664428519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34877220721428650219238025 26157915541071487664428519)
    ·
      refine ⟨39236873311607231496642779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26157915541071487664428519 39236873311607231496642779)
      ·
        refine ⟨58855309967410847244964169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39236873311607231496642779 58855309967410847244964169)
        ·
          refine ⟨44141482475558135433723127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58855309967410847244964169 44141482475558135433723127)
          ·
            refine ⟨66212223713337203150584691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44141482475558135433723127 66212223713337203150584691)
            ·
              refine ⟨99318335570005804725877037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66212223713337203150584691 99318335570005804725877037)
              ·
                refine ⟨37244375838752176772203889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99318335570005804725877037 37244375838752176772203889)
                ·
                  refine ⟨27933281879064132579152917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37244375838752176772203889 27933281879064132579152917)
                  ·
                    refine ⟨1309372588081131214647793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27933281879064132579152917 1309372588081131214647793)
                    ·
                      rfl

theorem cell23_7649982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7649982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649982 prefixEnd_7649982 := by exact prefixLift 7649982
  have htrace : WordTrace (prefixWord ++ tailWord_7649982) baseStart_7649982 baseEnd_7649982 := by
    simpa [prefixWord, tailWord_7649982, baseEnd_7649982] using wordTrace_append hprefix tailTrace_7649982
  have hstable : (prefixWord ++ tailWord_7649982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649982).length < 2 ^ (prefixWord ++ tailWord_7649982).sum := by decide
  have hdescent : baseEnd_7649982 < baseStart_7649982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649989 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_7649989 : Nat := 118140960795 + 7649989 * 2 ^ 59
def prefixEnd_7649989 : Nat := 4983230072969 + 3 ^ 40 * 7649989 * 2
def baseEnd_7649989 : Nat := 3928121358607975116555847

theorem tailTrace_7649989 : CollatzResearch.WordTrace tailWord_7649989 prefixEnd_7649989 3928121358607975116555847 := by
  unfold tailWord_7649989
  simp only [CollatzResearch.WordTrace]
  refine ⟨279018021082403841949409021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186012014054935894632939347 279018021082403841949409021)
  ·
    refine ⟨104631757905901440731028383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279018021082403841949409021 104631757905901440731028383)
    ·
      refine ⟨156947636858852161096542575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104631757905901440731028383 156947636858852161096542575)
      ·
        refine ⟨235421455288278241644813863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156947636858852161096542575 235421455288278241644813863)
        ·
          refine ⟨353132182932417362467220795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235421455288278241644813863 353132182932417362467220795)
          ·
            refine ⟨529698274398626043700831193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353132182932417362467220795 529698274398626043700831193)
            ·
              refine ⟨397273705798969532775623395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529698274398626043700831193 397273705798969532775623395)
              ·
                refine ⟨595910558698454299163435093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397273705798969532775623395 595910558698454299163435093)
                ·
                  refine ⟨6983326859747511318321505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 595910558698454299163435093 6983326859747511318321505)
                  ·
                    refine ⟨5237495144810633488741129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6983326859747511318321505 5237495144810633488741129)
                    ·
                      refine ⟨3928121358607975116555847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237495144810633488741129 3928121358607975116555847)
                      ·
                        rfl

theorem cell23_7649989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_7649989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649989 prefixEnd_7649989 := by exact prefixLift 7649989
  have htrace : WordTrace (prefixWord ++ tailWord_7649989) baseStart_7649989 baseEnd_7649989 := by
    simpa [prefixWord, tailWord_7649989, baseEnd_7649989] using wordTrace_append hprefix tailTrace_7649989
  have hstable : (prefixWord ++ tailWord_7649989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649989).length < 2 ^ (prefixWord ++ tailWord_7649989).sum := by decide
  have hdescent : baseEnd_7649989 < baseStart_7649989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7649990 : List Nat := [6, 1, 2, 1, 3, 1, 2, 7]
def baseStart_7649990 : Nat := 118140960795 + 7649990 * 2 ^ 59
def prefixEnd_7649990 : Nat := 4983230072969 + 3 ^ 40 * 7649990 * 2
def baseEnd_7649990 : Nat := 145485995262541837505309

theorem tailTrace_7649990 : CollatzResearch.WordTrace tailWord_7649990 prefixEnd_7649990 145485995262541837505309 := by
  unfold tailWord_7649990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719314298606256847506107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186012038370266812746796949 8719314298606256847506107)
  ·
    refine ⟨13078971447909385271259161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8719314298606256847506107 13078971447909385271259161)
    ·
      refine ⟨9809228585932038953444371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13078971447909385271259161 9809228585932038953444371)
      ·
        refine ⟨14713842878898058430166557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809228585932038953444371 14713842878898058430166557)
        ·
          refine ⟨5517691079586771911312459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14713842878898058430166557 5517691079586771911312459)
          ·
            refine ⟨8276536619380157866968689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517691079586771911312459 8276536619380157866968689)
            ·
              refine ⟨6207402464535118400226517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276536619380157866968689 6207402464535118400226517)
              ·
                refine ⟨145485995262541837505309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6207402464535118400226517 145485995262541837505309)
                ·
                  rfl

theorem cell23_7649990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_7649990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7649990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7649990 prefixEnd_7649990 := by exact prefixLift 7649990
  have htrace : WordTrace (prefixWord ++ tailWord_7649990) baseStart_7649990 baseEnd_7649990 := by
    simpa [prefixWord, tailWord_7649990, baseEnd_7649990] using wordTrace_append hprefix tailTrace_7649990
  have hstable : (prefixWord ++ tailWord_7649990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7649990).length < 2 ^ (prefixWord ++ tailWord_7649990).sum := by decide
  have hdescent : baseEnd_7649990 < baseStart_7649990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7649990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650052 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7650052 : Nat := 118140960795 + 7650052 * 2 ^ 59
def prefixEnd_7650052 : Nat := 4983230072969 + 3 ^ 40 * 7650052 * 2
def baseEnd_7650052 : Nat := 3928153707889208370068057

theorem tailTrace_7650052 : CollatzResearch.WordTrace tailWord_7650052 prefixEnd_7650052 3928153707889208370068057 := by
  unfold tailWord_7650052
  simp only [CollatzResearch.WordTrace]
  refine ⟨139510159440587801854476205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186013545920783735805968273 139510159440587801854476205)
  ·
    refine ⟨52316309790220425695428577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139510159440587801854476205 52316309790220425695428577)
    ·
      refine ⟨39237232342665319271571433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52316309790220425695428577 39237232342665319271571433)
      ·
        refine ⟨29427924256998989453678575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39237232342665319271571433 29427924256998989453678575)
        ·
          refine ⟨44141886385498484180517863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29427924256998989453678575 44141886385498484180517863)
          ·
            refine ⟨66212829578247726270776795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44141886385498484180517863 66212829578247726270776795)
            ·
              refine ⟨99319244367371589406165193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66212829578247726270776795 99319244367371589406165193)
              ·
                refine ⟨74489433275528692054623895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99319244367371589406165193 74489433275528692054623895)
                ·
                  refine ⟨111734149913293038081935843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74489433275528692054623895 111734149913293038081935843)
                  ·
                    refine ⟨167601224869939557122903765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111734149913293038081935843 167601224869939557122903765)
                    ·
                      refine ⟨3928153707889208370068057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167601224869939557122903765 3928153707889208370068057)
                      ·
                        rfl

theorem cell23_7650052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7650052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650052 prefixEnd_7650052 := by exact prefixLift 7650052
  have htrace : WordTrace (prefixWord ++ tailWord_7650052) baseStart_7650052 baseEnd_7650052 := by
    simpa [prefixWord, tailWord_7650052, baseEnd_7650052] using wordTrace_append hprefix tailTrace_7650052
  have hstable : (prefixWord ++ tailWord_7650052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650052).length < 2 ^ (prefixWord ++ tailWord_7650052).sum := by decide
  have hdescent : baseEnd_7650052 < baseStart_7650052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650079 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_7650079 : Nat := 118140960795 + 7650079 * 2 ^ 59
def prefixEnd_7650079 : Nat := 4983230072969 + 3 ^ 40 * 7650079 * 2
def baseEnd_7650079 : Nat := 3928167571866879764430433

theorem tailTrace_7650079 : CollatzResearch.WordTrace tailWord_7650079 prefixEnd_7650079 3928167571866879764430433 := by
  unfold tailWord_7650079
  simp only [CollatzResearch.WordTrace]
  refine ⟨279021303652077787320185291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186014202434718524880123527 279021303652077787320185291)
  ·
    refine ⟨418531955478116680980277937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279021303652077787320185291 418531955478116680980277937)
    ·
      refine ⟨313898966608587510735208453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418531955478116680980277937 313898966608587510735208453)
      ·
        refine ⟨58856056239110158262851585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313898966608587510735208453 58856056239110158262851585)
        ·
          refine ⟨44142042179332618697138689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58856056239110158262851585 44142042179332618697138689)
          ·
            refine ⟨33106531634499464022854017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44142042179332618697138689 33106531634499464022854017)
            ·
              refine ⟨24829898725874598017140513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33106531634499464022854017 24829898725874598017140513)
              ·
                refine ⟨18622424044405948512855385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24829898725874598017140513 18622424044405948512855385)
                ·
                  refine ⟨13966818033304461384641539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18622424044405948512855385 13966818033304461384641539)
                  ·
                    refine ⟨20950227049956692076962309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13966818033304461384641539 20950227049956692076962309)
                    ·
                      refine ⟨3928167571866879764430433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20950227049956692076962309 3928167571866879764430433)
                      ·
                        rfl

theorem cell23_7650079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_7650079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650079 prefixEnd_7650079 := by exact prefixLift 7650079
  have htrace : WordTrace (prefixWord ++ tailWord_7650079) baseStart_7650079 baseEnd_7650079 := by
    simpa [prefixWord, tailWord_7650079, baseEnd_7650079] using wordTrace_append hprefix tailTrace_7650079
  have hstable : (prefixWord ++ tailWord_7650079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650079).length < 2 ^ (prefixWord ++ tailWord_7650079).sum := by decide
  have hdescent : baseEnd_7650079 < baseStart_7650079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650106 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_7650106 : Nat := 118140960795 + 7650106 * 2 ^ 59
def prefixEnd_7650106 : Nat := 4983230072969 + 3 ^ 40 * 7650106 * 2
def baseEnd_7650106 : Nat := 1309393811948183719597603

theorem tailTrace_7650106 : CollatzResearch.WordTrace tailWord_7650106 prefixEnd_7650106 1309393811948183719597603 := by
  unfold tailWord_7650106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69755572105744992732854543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186014858948653313954278781 69755572105744992732854543)
  ·
    refine ⟨104633358158617489099281815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69755572105744992732854543 104633358158617489099281815)
    ·
      refine ⟨156950037237926233648922723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104633358158617489099281815 156950037237926233648922723)
      ·
        refine ⟨235425055856889350473384085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156950037237926233648922723 235425055856889350473384085)
        ·
          refine ⟨11035549493291688303439879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235425055856889350473384085 11035549493291688303439879)
          ·
            refine ⟨16553324239937532455159819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11035549493291688303439879 16553324239937532455159819)
            ·
              refine ⟨24829986359906298682739729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16553324239937532455159819 24829986359906298682739729)
              ·
                refine ⟨18622489769929724012054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24829986359906298682739729 18622489769929724012054797)
                ·
                  refine ⟨6983433663723646504520549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18622489769929724012054797 6983433663723646504520549)
                  ·
                    refine ⟨1309393811948183719597603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983433663723646504520549 1309393811948183719597603)
                    ·
                      rfl

theorem cell23_7650106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_7650106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650106 prefixEnd_7650106 := by exact prefixLift 7650106
  have htrace : WordTrace (prefixWord ++ tailWord_7650106) baseStart_7650106 baseEnd_7650106 := by
    simpa [prefixWord, tailWord_7650106, baseEnd_7650106] using wordTrace_append hprefix tailTrace_7650106
  have hstable : (prefixWord ++ tailWord_7650106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650106).length < 2 ^ (prefixWord ++ tailWord_7650106).sum := by decide
  have hdescent : baseEnd_7650106 < baseStart_7650106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650174 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7650174 : Nat := 118140960795 + 7650174 * 2 ^ 59
def prefixEnd_7650174 : Nat := 4983230072969 + 3 ^ 40 * 7650174 * 2
def baseEnd_7650174 : Nat := 1309405450843018964247499

theorem tailTrace_7650174 : CollatzResearch.WordTrace tailWord_7650174 prefixEnd_7650174 1309405450843018964247499 := by
  unfold tailWord_7650174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878096073341702318111697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186016512391155745696595717 34878096073341702318111697)
  ·
    refine ⟨26158572055006276738583773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34878096073341702318111697 26158572055006276738583773)
    ·
      refine ⟨9809464520627353776968915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26158572055006276738583773 9809464520627353776968915)
      ·
        refine ⟨14714196780941030665453373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809464520627353776968915 14714196780941030665453373)
        ·
          refine ⟨5517823792852886499545015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14714196780941030665453373 5517823792852886499545015)
          ·
            refine ⟨8276735689279329749317523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517823792852886499545015 8276735689279329749317523)
            ·
              refine ⟨12415103533918994623976285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276735689279329749317523 12415103533918994623976285)
              ·
                refine ⟨4655663825219622983991107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12415103533918994623976285 4655663825219622983991107)
                ·
                  refine ⟨6983495737829434475986661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655663825219622983991107 6983495737829434475986661)
                  ·
                    refine ⟨1309405450843018964247499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983495737829434475986661 1309405450843018964247499)
                    ·
                      rfl

theorem cell23_7650174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7650174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650174 prefixEnd_7650174 := by exact prefixLift 7650174
  have htrace : WordTrace (prefixWord ++ tailWord_7650174) baseStart_7650174 baseEnd_7650174 := by
    simpa [prefixWord, tailWord_7650174, baseEnd_7650174] using wordTrace_append hprefix tailTrace_7650174
  have hstable : (prefixWord ++ tailWord_7650174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650174).length < 2 ^ (prefixWord ++ tailWord_7650174).sum := by decide
  have hdescent : baseEnd_7650174 < baseStart_7650174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650179 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 6, 4]
def baseStart_7650179 : Nat := 118140960795 + 7650179 * 2 ^ 59
def prefixEnd_7650179 : Nat := 4983230072969 + 3 ^ 40 * 7650179 * 2
def baseEnd_7650179 : Nat := 1309406306644109791059991

theorem tailTrace_7650179 : CollatzResearch.WordTrace tailWord_7650179 prefixEnd_7650179 1309406306644109791059991 := by
  unfold tailWord_7650179
  simp only [CollatzResearch.WordTrace]
  refine ⟨279024950951715504398825591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186016633967810336265883727 279024950951715504398825591)
  ·
    refine ⟨418537426427573256598238387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279024950951715504398825591 418537426427573256598238387)
    ·
      refine ⟨627806139641359884897357581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418537426427573256598238387 627806139641359884897357581)
      ·
        refine ⟨235427302365509956836509093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627806139641359884897357581 235427302365509956836509093)
        ·
          refine ⟨44142619193533116906845455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235427302365509956836509093 44142619193533116906845455)
          ·
            refine ⟨66213928790299675360268183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44142619193533116906845455 66213928790299675360268183)
            ·
              refine ⟨99320893185449513040402275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66213928790299675360268183 99320893185449513040402275)
              ·
                refine ⟨148981339778174269560603413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99320893185449513040402275 148981339778174269560603413)
                ·
                  refine ⟨6983500302101918885653285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148981339778174269560603413 6983500302101918885653285)
                  ·
                    refine ⟨1309406306644109791059991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983500302101918885653285 1309406306644109791059991)
                    ·
                      rfl

theorem cell23_7650179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 4].length) (baseStart_7650179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650179 prefixEnd_7650179 := by exact prefixLift 7650179
  have htrace : WordTrace (prefixWord ++ tailWord_7650179) baseStart_7650179 baseEnd_7650179 := by
    simpa [prefixWord, tailWord_7650179, baseEnd_7650179] using wordTrace_append hprefix tailTrace_7650179
  have hstable : (prefixWord ++ tailWord_7650179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650179).length < 2 ^ (prefixWord ++ tailWord_7650179).sum := by decide
  have hdescent : baseEnd_7650179 < baseStart_7650179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650196 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7650196 : Nat := 118140960795 + 7650196 * 2 ^ 59
def prefixEnd_7650196 : Nat := 4983230072969 + 3 ^ 40 * 7650196 * 2
def baseEnd_7650196 : Nat := 1309409216367818602222465

theorem tailTrace_7650196 : CollatzResearch.WordTrace tailWord_7650196 prefixEnd_7650196 1309409216367818602222465 := by
  unfold tailWord_7650196
  simp only [CollatzResearch.WordTrace]
  refine ⟨139512785496326958151097221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186017047328435944201462961 139512785496326958151097221)
  ·
    refine ⟨26158647280561304653330729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139512785496326958151097221 26158647280561304653330729)
    ·
      refine ⟨19618985460420978489998047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26158647280561304653330729 19618985460420978489998047)
      ·
        refine ⟨29428478190631467734997071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618985460420978489998047 29428478190631467734997071)
        ·
          refine ⟨44142717285947201602495607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29428478190631467734997071 44142717285947201602495607)
          ·
            refine ⟨66214075928920802403743411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44142717285947201602495607 66214075928920802403743411)
            ·
              refine ⟨99321113893381203605615117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66214075928920802403743411 99321113893381203605615117)
              ·
                refine ⟨37245417710017951352105669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99321113893381203605615117 37245417710017951352105669)
                ·
                  refine ⟨6983515820628365878519813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37245417710017951352105669 6983515820628365878519813)
                  ·
                    refine ⟨1309409216367818602222465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983515820628365878519813 1309409216367818602222465)
                    ·
                      rfl

theorem cell23_7650196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7650196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650196 prefixEnd_7650196 := by exact prefixLift 7650196
  have htrace : WordTrace (prefixWord ++ tailWord_7650196) baseStart_7650196 baseEnd_7650196 := by
    simpa [prefixWord, tailWord_7650196, baseEnd_7650196] using wordTrace_append hprefix tailTrace_7650196
  have hstable : (prefixWord ++ tailWord_7650196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650196).length < 2 ^ (prefixWord ++ tailWord_7650196).sum := by decide
  have hdescent : baseEnd_7650196 < baseStart_7650196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650209 : List Nat := [1, 2, 3, 4, 1, 1, 1, 10]
def baseStart_7650209 : Nat := 118140960795 + 7650209 * 2 ^ 59
def prefixEnd_7650209 : Nat := 4983230072969 + 3 ^ 40 * 7650209 * 2
def baseEnd_7650209 : Nat := 145490160161183861326105

theorem tailTrace_7650209 : CollatzResearch.WordTrace tailWord_7650209 prefixEnd_7650209 145490160161183861326105 := by
  unfold tailWord_7650209
  simp only [CollatzResearch.WordTrace]
  refine ⟨279026045141606819522417681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186017363427737879681611787 279026045141606819522417681)
  ·
    refine ⟨209269533856205114641813261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279026045141606819522417681 209269533856205114641813261)
    ·
      refine ⟨78476075196076917990679973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209269533856205114641813261 78476075196076917990679973)
      ·
        refine ⟨14714264099264422123252495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78476075196076917990679973 14714264099264422123252495)
        ·
          refine ⟨22071396148896633184878743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714264099264422123252495 22071396148896633184878743)
          ·
            refine ⟨33107094223344949777318115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22071396148896633184878743 33107094223344949777318115)
            ·
              refine ⟨49660641335017424665977173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33107094223344949777318115 49660641335017424665977173)
              ·
                refine ⟨145490160161183861326105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49660641335017424665977173 145490160161183861326105)
                ·
                  rfl

theorem cell23_7650209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 10].length) (baseStart_7650209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650209 prefixEnd_7650209 := by exact prefixLift 7650209
  have htrace : WordTrace (prefixWord ++ tailWord_7650209) baseStart_7650209 baseEnd_7650209 := by
    simpa [prefixWord, tailWord_7650209, baseEnd_7650209] using wordTrace_append hprefix tailTrace_7650209
  have hstable : (prefixWord ++ tailWord_7650209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650209).length < 2 ^ (prefixWord ++ tailWord_7650209).sum := by decide
  have hdescent : baseEnd_7650209 < baseStart_7650209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650254 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_7650254 : Nat := 118140960795 + 7650254 * 2 ^ 59
def prefixEnd_7650254 : Nat := 4983230072969 + 3 ^ 40 * 7650254 * 2
def baseEnd_7650254 : Nat := 3928257430981416579742129

theorem tailTrace_7650254 : CollatzResearch.WordTrace tailWord_7650254 prefixEnd_7650254 3928257430981416579742129 := by
  unfold tailWord_7650254
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878460803305474025975727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186018457617629194805203877 34878460803305474025975727)
  ·
    refine ⟨52317691204958211038963591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34878460803305474025975727 52317691204958211038963591)
    ·
      refine ⟨78476536807437316558445387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52317691204958211038963591 78476536807437316558445387)
      ·
        refine ⟨117714805211155974837668081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78476536807437316558445387 117714805211155974837668081)
        ·
          refine ⟨88286103908366981128251061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117714805211155974837668081 88286103908366981128251061)
          ·
            refine ⟨8276822241409404480773537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88286103908366981128251061 8276822241409404480773537)
            ·
              refine ⟨6207616681057053360580153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276822241409404480773537 6207616681057053360580153)
              ·
                refine ⟨4655712510792790020435115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207616681057053360580153 4655712510792790020435115)
                ·
                  refine ⟨6983568766189185030652673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655712510792790020435115 6983568766189185030652673)
                  ·
                    refine ⟨5237676574641888772989505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6983568766189185030652673 5237676574641888772989505)
                    ·
                      refine ⟨3928257430981416579742129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237676574641888772989505 3928257430981416579742129)
                      ·
                        rfl

theorem cell23_7650254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_7650254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650254 prefixEnd_7650254 := by exact prefixLift 7650254
  have htrace : WordTrace (prefixWord ++ tailWord_7650254) baseStart_7650254 baseEnd_7650254 := by
    simpa [prefixWord, tailWord_7650254, baseEnd_7650254] using wordTrace_append hprefix tailTrace_7650254
  have hstable : (prefixWord ++ tailWord_7650254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650254).length < 2 ^ (prefixWord ++ tailWord_7650254).sum := by decide
  have hdescent : baseEnd_7650254 < baseStart_7650254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650316 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 7]
def baseStart_7650316 : Nat := 118140960795 + 7650316 * 2 ^ 59
def prefixEnd_7650316 : Nat := 4983230072969 + 3 ^ 40 * 7650316 * 2
def baseEnd_7650316 : Nat := 436476585197999481907427

theorem tailTrace_7650316 : CollatzResearch.WordTrace tailWord_7650316 prefixEnd_7650316 436476585197999481907427 := by
  unfold tailWord_7650316
  simp only [CollatzResearch.WordTrace]
  refine ⟨139514973876109588398281401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186019965168146117864375201 139514973876109588398281401)
  ·
    refine ⟨104636230407082191298711051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139514973876109588398281401 104636230407082191298711051)
    ·
      refine ⟨156954345610623286948066577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104636230407082191298711051 156954345610623286948066577)
      ·
        refine ⟨117715759207967465211049933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156954345610623286948066577 117715759207967465211049933)
        ·
          refine ⟨44143409702987799454143725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117715759207967465211049933 44143409702987799454143725)
          ·
            refine ⟨16553778638620424795303897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44143409702987799454143725 16553778638620424795303897)
            ·
              refine ⟨12415333978965318596477923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16553778638620424795303897 12415333978965318596477923)
              ·
                refine ⟨18623000968447977894716885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12415333978965318596477923 18623000968447977894716885)
                ·
                  refine ⟨436476585197999481907427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18623000968447977894716885 436476585197999481907427)
                  ·
                    rfl

theorem cell23_7650316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_7650316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650316 prefixEnd_7650316 := by exact prefixLift 7650316
  have htrace : WordTrace (prefixWord ++ tailWord_7650316) baseStart_7650316 baseEnd_7650316 := by
    simpa [prefixWord, tailWord_7650316, baseEnd_7650316] using wordTrace_append hprefix tailTrace_7650316
  have hstable : (prefixWord ++ tailWord_7650316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650316).length < 2 ^ (prefixWord ++ tailWord_7650316).sum := by decide
  have hdescent : baseEnd_7650316 < baseStart_7650316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650329 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_7650329 : Nat := 118140960795 + 7650329 * 2 ^ 59
def prefixEnd_7650329 : Nat := 4983230072969 + 3 ^ 40 * 7650329 * 2
def baseEnd_7650329 : Nat := 1309431980676834595434761

theorem tailTrace_7650329 : CollatzResearch.WordTrace tailWord_7650329 prefixEnd_7650329 1309431980676834595434761 := by
  unfold tailWord_7650329
  simp only [CollatzResearch.WordTrace]
  refine ⟨279030421901172080016786041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186020281267448053344524027 279030421901172080016786041)
  ·
    refine ⟨209272816425879060012589531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279030421901172080016786041 209272816425879060012589531)
    ·
      refine ⟨313909224638818590018884297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209272816425879060012589531 313909224638818590018884297)
      ·
        refine ⟨235431918479113942514163223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313909224638818590018884297 235431918479113942514163223)
        ·
          refine ⟨353147877718670913771244835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235431918479113942514163223 353147877718670913771244835)
          ·
            refine ⟨529721816578006370656867253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353147877718670913771244835 529721816578006370656867253)
            ·
              refine ⟨49661420304188097249081305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529721816578006370656867253 49661420304188097249081305)
              ·
                refine ⟨37246065228141072936810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49661420304188097249081305 37246065228141072936810979)
                ·
                  refine ⟨55869097842211609405216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37246065228141072936810979 55869097842211609405216469)
                  ·
                    refine ⟨1309431980676834595434761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55869097842211609405216469 1309431980676834595434761)
                    ·
                      rfl

theorem cell23_7650329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_7650329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650329 prefixEnd_7650329 := by exact prefixLift 7650329
  have htrace : WordTrace (prefixWord ++ tailWord_7650329) baseStart_7650329 baseEnd_7650329 := by
    simpa [prefixWord, tailWord_7650329, baseEnd_7650329] using wordTrace_append hprefix tailTrace_7650329
  have hstable : (prefixWord ++ tailWord_7650329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650329).length < 2 ^ (prefixWord ++ tailWord_7650329).sum := by decide
  have hdescent : baseEnd_7650329 < baseStart_7650329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 4, 3, 2]
def baseStart_7650443 : Nat := 118140960795 + 7650443 * 2 ^ 59
def prefixEnd_7650443 : Nat := 4983230072969 + 3 ^ 40 * 7650443 * 2
def baseEnd_7650443 : Nat := 3928354478825116340278759

theorem tailTrace_7650443 : CollatzResearch.WordTrace tailWord_7650443 prefixEnd_7650443 3928354478825116340278759 := by
  unfold tailWord_7650443
  simp only [CollatzResearch.WordTrace]
  refine ⟨279034579822759077486435983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186023053215172718324290655 279034579822759077486435983)
  ·
    refine ⟨418551869734138616229653975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279034579822759077486435983 418551869734138616229653975)
    ·
      refine ⟨627827804601207924344480963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418551869734138616229653975 627827804601207924344480963)
      ·
        refine ⟨941741706901811886516721445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627827804601207924344480963 941741706901811886516721445)
        ·
          refine ⟨176576570044089728721885271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 941741706901811886516721445 176576570044089728721885271)
          ·
            refine ⟨264864855066134593082827907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176576570044089728721885271 264864855066134593082827907)
            ·
              refine ⟨397297282599201889624241861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264864855066134593082827907 397297282599201889624241861)
              ·
                refine ⟨74493240487350354304545349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397297282599201889624241861 74493240487350354304545349)
                ·
                  refine ⟨13967482591378191432102253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74493240487350354304545349 13967482591378191432102253)
                  ·
                    refine ⟨5237805971766821787038345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13967482591378191432102253 5237805971766821787038345)
                    ·
                      refine ⟨3928354478825116340278759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237805971766821787038345 3928354478825116340278759)
                      ·
                        rfl

theorem cell23_7650443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3, 2].length) (baseStart_7650443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650443 prefixEnd_7650443 := by exact prefixLift 7650443
  have htrace : WordTrace (prefixWord ++ tailWord_7650443) baseStart_7650443 baseEnd_7650443 := by
    simpa [prefixWord, tailWord_7650443, baseEnd_7650443] using wordTrace_append hprefix tailTrace_7650443
  have hstable : (prefixWord ++ tailWord_7650443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650443).length < 2 ^ (prefixWord ++ tailWord_7650443).sum := by decide
  have hdescent : baseEnd_7650443 < baseStart_7650443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650450 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_7650450 : Nat := 118140960795 + 7650450 * 2 ^ 59
def prefixEnd_7650450 : Nat := 4983230072969 + 3 ^ 40 * 7650450 * 2
def baseEnd_7650450 : Nat := 3928358073189697812891227

theorem tailTrace_7650450 : CollatzResearch.WordTrace tailWord_7650450 prefixEnd_7650450 3928358073189697812891227 := by
  unfold tailWord_7650450
  simp only [CollatzResearch.WordTrace]
  refine ⟨69758708783433429420485201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186023223422489145121293869 69758708783433429420485201)
  ·
    refine ⟨52319031587575072065363901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69758708783433429420485201 52319031587575072065363901)
    ·
      refine ⟨19619636845340652024511463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52319031587575072065363901 19619636845340652024511463)
      ·
        refine ⟨29429455268010978036767195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19619636845340652024511463 29429455268010978036767195)
        ·
          refine ⟨44144182902016467055150793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29429455268010978036767195 44144182902016467055150793)
          ·
            refine ⟨33108137176512350291363095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44144182902016467055150793 33108137176512350291363095)
            ·
              refine ⟨49662205764768525437044643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33108137176512350291363095 49662205764768525437044643)
              ·
                refine ⟨74493308647152788155566965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49662205764768525437044643 74493308647152788155566965)
                ·
                  refine ⟨6983747685670573889584403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74493308647152788155566965 6983747685670573889584403)
                  ·
                    refine ⟨10475621528505860834376605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983747685670573889584403 10475621528505860834376605)
                    ·
                      refine ⟨3928358073189697812891227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10475621528505860834376605 3928358073189697812891227)
                      ·
                        rfl

theorem cell23_7650450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_7650450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650450 prefixEnd_7650450 := by exact prefixLift 7650450
  have htrace : WordTrace (prefixWord ++ tailWord_7650450) baseStart_7650450 baseEnd_7650450 := by
    simpa [prefixWord, tailWord_7650450, baseEnd_7650450] using wordTrace_append hprefix tailTrace_7650450
  have hstable : (prefixWord ++ tailWord_7650450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650450).length < 2 ^ (prefixWord ++ tailWord_7650450).sum := by decide
  have hdescent : baseEnd_7650450 < baseStart_7650450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650460 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7650460 : Nat := 118140960795 + 7650460 * 2 ^ 59
def prefixEnd_7650460 : Nat := 4983230072969 + 3 ^ 40 * 7650460 * 2
def baseEnd_7650460 : Nat := 3928363207996242773766181

theorem tailTrace_7650460 : CollatzResearch.WordTrace tailWord_7650460 prefixEnd_7650460 3928363207996242773766181 := by
  unfold tailWord_7650460
  simp only [CollatzResearch.WordTrace]
  refine ⟨139517599931848744694902417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186023466575798326259869889 139517599931848744694902417)
  ·
    refine ⟨104638199948886558521176813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139517599931848744694902417 104638199948886558521176813)
    ·
      refine ⟨39239324980832459445441305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104638199948886558521176813 39239324980832459445441305)
      ·
        refine ⟨29429493735624344584080979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39239324980832459445441305 29429493735624344584080979)
        ·
          refine ⟨44144240603436516876121469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29429493735624344584080979 44144240603436516876121469)
          ·
            refine ⟨16554090226288693828545551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44144240603436516876121469 16554090226288693828545551)
            ·
              refine ⟨24831135339433040742818327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16554090226288693828545551 24831135339433040742818327)
              ·
                refine ⟨37246703009149561114227491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24831135339433040742818327 37246703009149561114227491)
                ·
                  refine ⟨55870054513724341671341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37246703009149561114227491 55870054513724341671341237)
                  ·
                    refine ⟨5237817610661657031688241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55870054513724341671341237 5237817610661657031688241)
                    ·
                      refine ⟨3928363207996242773766181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237817610661657031688241 3928363207996242773766181)
                      ·
                        rfl

theorem cell23_7650460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7650460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650460 prefixEnd_7650460 := by exact prefixLift 7650460
  have htrace : WordTrace (prefixWord ++ tailWord_7650460) baseStart_7650460 baseEnd_7650460 := by
    simpa [prefixWord, tailWord_7650460, baseEnd_7650460] using wordTrace_append hprefix tailTrace_7650460
  have hstable : (prefixWord ++ tailWord_7650460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650460).length < 2 ^ (prefixWord ++ tailWord_7650460).sum := by decide
  have hdescent : baseEnd_7650460 < baseStart_7650460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650493 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7650493 : Nat := 118140960795 + 7650493 * 2 ^ 59
def prefixEnd_7650493 : Nat := 4983230072969 + 3 ^ 40 * 7650493 * 2
def baseEnd_7650493 : Nat := 3928380152857841144653529

theorem tailTrace_7650493 : CollatzResearch.WordTrace tailWord_7650493 prefixEnd_7650493 3928380152857841144653529 := by
  unfold tailWord_7650493
  simp only [CollatzResearch.WordTrace]
  refine ⟨279036403472577936025756133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186024268981718624017170755 279036403472577936025756133)
  ·
    refine ⟨52319325651108363004829275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279036403472577936025756133 52319325651108363004829275)
    ·
      refine ⟨78478988476662544507243913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52319325651108363004829275 78478988476662544507243913)
      ·
        refine ⟨58859241357496908380432935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78478988476662544507243913 58859241357496908380432935)
        ·
          refine ⟨88288862036245362570649403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58859241357496908380432935 88288862036245362570649403)
          ·
            refine ⟨132433293054368043855974105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88288862036245362570649403 132433293054368043855974105)
            ·
              refine ⟨99324969790776032891980579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132433293054368043855974105 99324969790776032891980579)
              ·
                refine ⟨148987454686164049337970869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99324969790776032891980579 148987454686164049337970869)
                ·
                  refine ⟨13967573876827879625434769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148987454686164049337970869 13967573876827879625434769)
                  ·
                    refine ⟨10475680407620909719076077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13967573876827879625434769 10475680407620909719076077)
                    ·
                      refine ⟨3928380152857841144653529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10475680407620909719076077 3928380152857841144653529)
                      ·
                        rfl

theorem cell23_7650493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7650493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650493 prefixEnd_7650493 := by exact prefixLift 7650493
  have htrace : WordTrace (prefixWord ++ tailWord_7650493) baseStart_7650493 baseEnd_7650493 := by
    simpa [prefixWord, tailWord_7650493, baseEnd_7650493] using wordTrace_append hprefix tailTrace_7650493
  have hstable : (prefixWord ++ tailWord_7650493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650493).length < 2 ^ (prefixWord ++ tailWord_7650493).sum := by decide
  have hdescent : baseEnd_7650493 < baseStart_7650493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650518 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7650518 : Nat := 118140960795 + 7650518 * 2 ^ 59
def prefixEnd_7650518 : Nat := 4983230072969 + 3 ^ 40 * 7650518 * 2
def baseEnd_7650518 : Nat := 3928392989874203546840915

theorem tailTrace_7650518 : CollatzResearch.WordTrace tailWord_7650518 prefixEnd_7650518 3928392989874203546840915 := by
  unfold tailWord_7650518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439832206092960330963513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186024876864991576863610805 17439832206092960330963513)
  ·
    refine ⟨13079874154569720248222635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17439832206092960330963513 13079874154569720248222635)
    ·
      refine ⟨19619811231854580372333953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13079874154569720248222635 19619811231854580372333953)
      ·
        refine ⟨14714858423890935279250465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19619811231854580372333953 14714858423890935279250465)
        ·
          refine ⟨11036143817918201459437849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14714858423890935279250465 11036143817918201459437849)
          ·
            refine ⟨8277107863438651094578387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11036143817918201459437849 8277107863438651094578387)
            ·
              refine ⟨12415661795157976641867581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277107863438651094578387 12415661795157976641867581)
              ·
                refine ⟨4655873173184241240700343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12415661795157976641867581 4655873173184241240700343)
                ·
                  refine ⟨6983809759776361861050515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655873173184241240700343 6983809759776361861050515)
                  ·
                    refine ⟨10475714639664542791575773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983809759776361861050515 10475714639664542791575773)
                    ·
                      refine ⟨3928392989874203546840915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10475714639664542791575773 3928392989874203546840915)
                      ·
                        rfl

theorem cell23_7650518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7650518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650518 prefixEnd_7650518 := by exact prefixLift 7650518
  have htrace : WordTrace (prefixWord ++ tailWord_7650518) baseStart_7650518 baseEnd_7650518 := by
    simpa [prefixWord, tailWord_7650518, baseEnd_7650518] using wordTrace_append hprefix tailTrace_7650518
  have hstable : (prefixWord ++ tailWord_7650518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650518).length < 2 ^ (prefixWord ++ tailWord_7650518).sum := by decide
  have hdescent : baseEnd_7650518 < baseStart_7650518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650540 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_7650540 : Nat := 118140960795 + 7650540 * 2 ^ 59
def prefixEnd_7650540 : Nat := 4983230072969 + 3 ^ 40 * 7650540 * 2
def baseEnd_7650540 : Nat := 3928404286448602460765813

theorem tailTrace_7650540 : CollatzResearch.WordTrace tailWord_7650540 prefixEnd_7650540 3928404286448602460765813 := by
  unfold tailWord_7650540
  simp only [CollatzResearch.WordTrace]
  refine ⟨139519058851703831526358537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186025411802271775368478049 139519058851703831526358537)
  ·
    refine ⟨104639294138777873644768903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139519058851703831526358537 104639294138777873644768903)
    ·
      refine ⟨156958941208166810467153355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104639294138777873644768903 156958941208166810467153355)
      ·
        refine ⟨235438411812250215700730033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156958941208166810467153355 235438411812250215700730033)
        ·
          refine ⟨176578808859187661775547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235438411812250215700730033 176578808859187661775547525)
          ·
            refine ⟨33108526661097686582915161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176578808859187661775547525 33108526661097686582915161)
            ·
              refine ⟨24831394995823264937186371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33108526661097686582915161 24831394995823264937186371)
              ·
                refine ⟨37247092493734897405779557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24831394995823264937186371 37247092493734897405779557)
                ·
                  refine ⟨6983829842575293263583667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37247092493734897405779557 6983829842575293263583667)
                  ·
                    refine ⟨10475744763862939895375501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983829842575293263583667 10475744763862939895375501)
                    ·
                      refine ⟨3928404286448602460765813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10475744763862939895375501 3928404286448602460765813)
                      ·
                        rfl

theorem cell23_7650540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_7650540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650540 prefixEnd_7650540 := by exact prefixLift 7650540
  have htrace : WordTrace (prefixWord ++ tailWord_7650540) baseStart_7650540 baseEnd_7650540 := by
    simpa [prefixWord, tailWord_7650540, baseEnd_7650540] using wordTrace_append hprefix tailTrace_7650540
  have hstable : (prefixWord ++ tailWord_7650540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650540).length < 2 ^ (prefixWord ++ tailWord_7650540).sum := by decide
  have hdescent : baseEnd_7650540 < baseStart_7650540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650550 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7650550 : Nat := 118140960795 + 7650550 * 2 ^ 59
def prefixEnd_7650550 : Nat := 4983230072969 + 3 ^ 40 * 7650550 * 2
def baseEnd_7650550 : Nat := 3928409421255147421640767

theorem tailTrace_7650550 : CollatzResearch.WordTrace tailWord_7650550 prefixEnd_7650550 3928409421255147421640767 := by
  unfold tailWord_7650550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439905152085714672536319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186025654955580956507054069 17439905152085714672536319)
  ·
    refine ⟨26159857728128572008804479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17439905152085714672536319 26159857728128572008804479)
    ·
      refine ⟨39239786592192858013206719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26159857728128572008804479 39239786592192858013206719)
      ·
        refine ⟨58859679888289287019810079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39239786592192858013206719 58859679888289287019810079)
        ·
          refine ⟨88289519832433930529715119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58859679888289287019810079 88289519832433930529715119)
          ·
            refine ⟨132434279748650895794572679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88289519832433930529715119 132434279748650895794572679)
            ·
              refine ⟨198651419622976343691859019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132434279748650895794572679 198651419622976343691859019)
              ·
                refine ⟨297977129434464515537788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198651419622976343691859019 297977129434464515537788529)
                ·
                  refine ⟨223482847075848386653341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297977129434464515537788529 223482847075848386653341397)
                  ·
                    refine ⟨5237879228340196562187689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223482847075848386653341397 5237879228340196562187689)
                    ·
                      refine ⟨3928409421255147421640767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237879228340196562187689 3928409421255147421640767)
                      ·
                        rfl

theorem cell23_7650550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7650550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650550 prefixEnd_7650550 := by exact prefixLift 7650550
  have htrace : WordTrace (prefixWord ++ tailWord_7650550) baseStart_7650550 baseEnd_7650550 := by
    simpa [prefixWord, tailWord_7650550, baseEnd_7650550] using wordTrace_append hprefix tailTrace_7650550
  have hstable : (prefixWord ++ tailWord_7650550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650550).length < 2 ^ (prefixWord ++ tailWord_7650550).sum := by decide
  have hdescent : baseEnd_7650550 < baseStart_7650550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650576 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_7650576 : Nat := 118140960795 + 7650576 * 2 ^ 59
def prefixEnd_7650576 : Nat := 4983230072969 + 3 ^ 40 * 7650576 * 2
def baseEnd_7650576 : Nat := 3928422771752164319915647

theorem tailTrace_7650576 : CollatzResearch.WordTrace tailWord_7650576 prefixEnd_7650576 3928422771752164319915647 := by
  unfold tailWord_7650576
  simp only [CollatzResearch.WordTrace]
  refine ⟨139519715365638620600513791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186026287154184827467351721 139519715365638620600513791)
  ·
    refine ⟨209279573048457930900770687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139519715365638620600513791 209279573048457930900770687)
    ·
      refine ⟨313919359572686896351156031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209279573048457930900770687 313919359572686896351156031)
      ·
        refine ⟨470879039359030344526734047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313919359572686896351156031 470879039359030344526734047)
        ·
          refine ⟨706318559038545516790101071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470879039359030344526734047 706318559038545516790101071)
          ·
            refine ⟨1059477838557818275185151607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706318559038545516790101071 1059477838557818275185151607)
            ·
              refine ⟨1589216757836727412777727411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059477838557818275185151607 1589216757836727412777727411)
              ·
                refine ⟨2383825136755091119166591117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589216757836727412777727411 2383825136755091119166591117)
                ·
                  refine ⟨893934426283159169687471669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2383825136755091119166591117 893934426283159169687471669)
                  ·
                    refine ⟨83806352464046172158200469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 893934426283159169687471669 83806352464046172158200469)
                    ·
                      refine ⟨3928422771752164319915647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83806352464046172158200469 3928422771752164319915647)
                      ·
                        rfl

theorem cell23_7650576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_7650576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650576 prefixEnd_7650576 := by exact prefixLift 7650576
  have htrace : WordTrace (prefixWord ++ tailWord_7650576) baseStart_7650576 baseEnd_7650576 := by
    simpa [prefixWord, tailWord_7650576, baseEnd_7650576] using wordTrace_append hprefix tailTrace_7650576
  have hstable : (prefixWord ++ tailWord_7650576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650576).length < 2 ^ (prefixWord ++ tailWord_7650576).sum := by decide
  have hdescent : baseEnd_7650576 < baseStart_7650576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650583 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7650583 : Nat := 118140960795 + 7650583 * 2 ^ 59
def prefixEnd_7650583 : Nat := 4983230072969 + 3 ^ 40 * 7650583 * 2
def baseEnd_7650583 : Nat := 3928426366116745792528115

theorem tailTrace_7650583 : CollatzResearch.WordTrace tailWord_7650583 prefixEnd_7650583 3928426366116745792528115 := by
  unfold tailWord_7650583
  simp only [CollatzResearch.WordTrace]
  refine ⟨279039686042251881396532403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186026457361501254264354935 279039686042251881396532403)
  ·
    refine ⟨418559529063377822094798605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279039686042251881396532403 418559529063377822094798605)
    ·
      refine ⟨156959823398766683285549477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418559529063377822094798605 156959823398766683285549477)
      ·
        refine ⟨29429966887268753116040527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156959823398766683285549477 29429966887268753116040527)
        ·
          refine ⟨44144950330903129674060791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29429966887268753116040527 44144950330903129674060791)
          ·
            refine ⟨66217425496354694511091187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44144950330903129674060791 66217425496354694511091187)
            ·
              refine ⟨99326138244532041766636781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66217425496354694511091187 99326138244532041766636781)
              ·
                refine ⟨37247301841699515662488793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99326138244532041766636781 37247301841699515662488793)
                ·
                  refine ⟨27935476381274636746866595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37247301841699515662488793 27935476381274636746866595)
                  ·
                    refine ⟨41903214571911955120299893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27935476381274636746866595 41903214571911955120299893)
                    ·
                      refine ⟨3928426366116745792528115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41903214571911955120299893 3928426366116745792528115)
                      ·
                        rfl

theorem cell23_7650583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7650583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650583 prefixEnd_7650583 := by exact prefixLift 7650583
  have htrace : WordTrace (prefixWord ++ tailWord_7650583) baseStart_7650583 baseEnd_7650583 := by
    simpa [prefixWord, tailWord_7650583, baseEnd_7650583] using wordTrace_append hprefix tailTrace_7650583
  have hstable : (prefixWord ++ tailWord_7650583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650583).length < 2 ^ (prefixWord ++ tailWord_7650583).sum := by decide
  have hdescent : baseEnd_7650583 < baseStart_7650583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650584 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_7650584 : Nat := 118140960795 + 7650584 * 2 ^ 59
def prefixEnd_7650584 : Nat := 4983230072969 + 3 ^ 40 * 7650584 * 2
def baseEnd_7650584 : Nat := 3928426879597400288615611

theorem tailTrace_7650584 : CollatzResearch.WordTrace tailWord_7650584 prefixEnd_7650584 3928426879597400288615611 := by
  unfold tailWord_7650584
  simp only [CollatzResearch.WordTrace]
  refine ⟨139519861257624129283659403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186026481676832172378212537 139519861257624129283659403)
  ·
    refine ⟨209279791886436193925489105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139519861257624129283659403 209279791886436193925489105)
    ·
      refine ⟨156959843914827145444116829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209279791886436193925489105 156959843914827145444116829)
      ·
        refine ⟨58859941468060179541543811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156959843914827145444116829 58859941468060179541543811)
        ·
          refine ⟨88289912202090269312315717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58859941468060179541543811 88289912202090269312315717)
          ·
            refine ⟨16554358537891925496059197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88289912202090269312315717 16554358537891925496059197)
            ·
              refine ⟨6207884451709472061022199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16554358537891925496059197 6207884451709472061022199)
              ·
                refine ⟨9311826677564208091533299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207884451709472061022199 9311826677564208091533299)
                ·
                  refine ⟨13967740016346312137299949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9311826677564208091533299 13967740016346312137299949)
                  ·
                    refine ⟨5237902506129867051487481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13967740016346312137299949 5237902506129867051487481)
                    ·
                      refine ⟨3928426879597400288615611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5237902506129867051487481 3928426879597400288615611)
                      ·
                        rfl

theorem cell23_7650584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_7650584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650584 prefixEnd_7650584 := by exact prefixLift 7650584
  have htrace : WordTrace (prefixWord ++ tailWord_7650584) baseStart_7650584 baseEnd_7650584 := by
    simpa [prefixWord, tailWord_7650584, baseEnd_7650584] using wordTrace_append hprefix tailTrace_7650584
  have hstable : (prefixWord ++ tailWord_7650584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650584).length < 2 ^ (prefixWord ++ tailWord_7650584).sum := by decide
  have hdescent : baseEnd_7650584 < baseStart_7650584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650593 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7650593 : Nat := 118140960795 + 7650593 * 2 ^ 59
def prefixEnd_7650593 : Nat := 4983230072969 + 3 ^ 40 * 7650593 * 2
def baseEnd_7650593 : Nat := 3928431500923290753403069

theorem tailTrace_7650593 : CollatzResearch.WordTrace tailWord_7650593 prefixEnd_7650593 3928431500923290753403069 := by
  unfold tailWord_7650593
  simp only [CollatzResearch.WordTrace]
  refine ⟨279040050772215653104396433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186026700514810435402930955 279040050772215653104396433)
  ·
    refine ⟨209280038079161739828297325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279040050772215653104396433 209280038079161739828297325)
    ·
      refine ⟨78480014279685652435611497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209280038079161739828297325 78480014279685652435611497)
      ·
        refine ⟨58860010709764239326708623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78480014279685652435611497 58860010709764239326708623)
        ·
          refine ⟨88290016064646358990062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58860010709764239326708623 88290016064646358990062935)
          ·
            refine ⟨132435024096969538485094403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88290016064646358990062935 132435024096969538485094403)
            ·
              refine ⟨198652536145454307727641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132435024096969538485094403 198652536145454307727641605)
              ·
                refine ⟨37247350527272682698932801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198652536145454307727641605 37247350527272682698932801)
                ·
                  refine ⟨27935512895454512024199601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37247350527272682698932801 27935512895454512024199601)
                  ·
                    refine ⟨20951634671590884018149701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27935512895454512024199601 20951634671590884018149701)
                    ·
                      refine ⟨3928431500923290753403069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20951634671590884018149701 3928431500923290753403069)
                      ·
                        rfl

theorem cell23_7650593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7650593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650593 prefixEnd_7650593 := by exact prefixLift 7650593
  have htrace : WordTrace (prefixWord ++ tailWord_7650593) baseStart_7650593 baseEnd_7650593 := by
    simpa [prefixWord, tailWord_7650593, baseEnd_7650593] using wordTrace_append hprefix tailTrace_7650593
  have hstable : (prefixWord ++ tailWord_7650593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650593).length < 2 ^ (prefixWord ++ tailWord_7650593).sum := by decide
  have hdescent : baseEnd_7650593 < baseStart_7650593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650600 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7650600 : Nat := 118140960795 + 7650600 * 2 ^ 59
def prefixEnd_7650600 : Nat := 4983230072969 + 3 ^ 40 * 7650600 * 2
def baseEnd_7650600 : Nat := 3928435095287872226015537

theorem tailTrace_7650600 : CollatzResearch.WordTrace tailWord_7650600 prefixEnd_7650600 3928435095287872226015537 := by
  unfold tailWord_7650600
  simp only [CollatzResearch.WordTrace]
  refine ⟨139520153041595146649950627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186026870722126862199934169 139520153041595146649950627)
  ·
    refine ⟨209280229562392719974925941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139520153041595146649950627 209280229562392719974925941)
    ·
      refine ⟨19620021521474317497649307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209280229562392719974925941 19620021521474317497649307)
      ·
        refine ⟨29430032282211476246473961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19620021521474317497649307 29430032282211476246473961)
        ·
          refine ⟨22072524211658607184855471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29430032282211476246473961 22072524211658607184855471)
          ·
            refine ⟨33108786317487910777283207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22072524211658607184855471 33108786317487910777283207)
            ·
              refine ⟨49663179476231866165924811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33108786317487910777283207 49663179476231866165924811)
              ·
                refine ⟨74494769214347799248887217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49663179476231866165924811 74494769214347799248887217)
                ·
                  refine ⟨55871076910760849436665413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74494769214347799248887217 55871076910760849436665413)
                  ·
                    refine ⟨10475826920767659269374765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55871076910760849436665413 10475826920767659269374765)
                    ·
                      refine ⟨3928435095287872226015537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10475826920767659269374765 3928435095287872226015537)
                      ·
                        rfl

theorem cell23_7650600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7650600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650600 prefixEnd_7650600 := by exact prefixLift 7650600
  have htrace : WordTrace (prefixWord ++ tailWord_7650600) baseStart_7650600 baseEnd_7650600 := by
    simpa [prefixWord, tailWord_7650600, baseEnd_7650600] using wordTrace_append hprefix tailTrace_7650600
  have hstable : (prefixWord ++ tailWord_7650600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650600).length < 2 ^ (prefixWord ++ tailWord_7650600).sum := by decide
  have hdescent : baseEnd_7650600 < baseStart_7650600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650610 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_7650610 : Nat := 118140960795 + 7650610 * 2 ^ 59
def prefixEnd_7650610 : Nat := 4983230072969 + 3 ^ 40 * 7650610 * 2
def baseEnd_7650610 : Nat := 3928440230094417186890491

theorem tailTrace_7650610 : CollatzResearch.WordTrace tailWord_7650610 prefixEnd_7650610 3928440230094417186890491 := by
  unfold tailWord_7650610
  simp only [CollatzResearch.WordTrace]
  refine ⟨69760167703288516251941321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186027113875436043338510189 69760167703288516251941321)
  ·
    refine ⟨52320125777466387188955991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69760167703288516251941321 52320125777466387188955991)
    ·
      refine ⟨78480188666199580783433987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52320125777466387188955991 78480188666199580783433987)
      ·
        refine ⟨117720282999299371175150981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78480188666199580783433987 117720282999299371175150981)
        ·
          refine ⟨22072553062368632095340809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117720282999299371175150981 22072553062368632095340809)
          ·
            refine ⟨16554414796776474071505607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22072553062368632095340809 16554414796776474071505607)
            ·
              refine ⟨24831622195164711107258411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16554414796776474071505607 24831622195164711107258411)
              ·
                refine ⟨37247433292747066660887617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24831622195164711107258411 37247433292747066660887617)
                ·
                  refine ⟨27935574969560299995665713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37247433292747066660887617 27935574969560299995665713)
                  ·
                    refine ⟨20951681227170224996749285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27935574969560299995665713 20951681227170224996749285)
                    ·
                      refine ⟨3928440230094417186890491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20951681227170224996749285 3928440230094417186890491)
                      ·
                        rfl

theorem cell23_7650610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_7650610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650610 prefixEnd_7650610 := by exact prefixLift 7650610
  have htrace : WordTrace (prefixWord ++ tailWord_7650610) baseStart_7650610 baseEnd_7650610 := by
    simpa [prefixWord, tailWord_7650610, baseEnd_7650610] using wordTrace_append hprefix tailTrace_7650610
  have hstable : (prefixWord ++ tailWord_7650610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650610).length < 2 ^ (prefixWord ++ tailWord_7650610).sum := by decide
  have hdescent : baseEnd_7650610 < baseStart_7650610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650683 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_7650683 : Nat := 118140960795 + 7650683 * 2 ^ 59
def prefixEnd_7650683 : Nat := 4983230072969 + 3 ^ 40 * 7650683 * 2
def baseEnd_7650683 : Nat := 3928477714182195401277655

theorem tailTrace_7650683 : CollatzResearch.WordTrace tailWord_7650683 prefixEnd_7650683 3928477714182195401277655 := by
  unfold tailWord_7650683
  simp only [CollatzResearch.WordTrace]
  refine ⟨279043333341889598475172703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186028888894593065650115135 279043333341889598475172703)
  ·
    refine ⟨418565000012834397712759055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279043333341889598475172703 418565000012834397712759055)
    ·
      refine ⟨627847500019251596569138583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418565000012834397712759055 627847500019251596569138583)
      ·
        refine ⟨941771250028877394853707875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627847500019251596569138583 941771250028877394853707875)
        ·
          refine ⟨1412656875043316092280561813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941771250028877394853707875 1412656875043316092280561813)
          ·
            refine ⟨66218291017655441825651335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1412656875043316092280561813 66218291017655441825651335)
            ·
              refine ⟨99327436526483162738477003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66218291017655441825651335 99327436526483162738477003)
              ·
                refine ⟨148991154789724744107715505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99327436526483162738477003 148991154789724744107715505)
                ·
                  refine ⟨111743366092293558080786629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148991154789724744107715505 111743366092293558080786629)
                  ·
                    refine ⟨20951881142305042140147493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111743366092293558080786629 20951881142305042140147493)
                    ·
                      refine ⟨3928477714182195401277655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20951881142305042140147493 3928477714182195401277655)
                      ·
                        rfl

theorem cell23_7650683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_7650683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650683 prefixEnd_7650683 := by exact prefixLift 7650683
  have htrace : WordTrace (prefixWord ++ tailWord_7650683) baseStart_7650683 baseEnd_7650683 := by
    simpa [prefixWord, tailWord_7650683, baseEnd_7650683] using wordTrace_append hprefix tailTrace_7650683
  have hstable : (prefixWord ++ tailWord_7650683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650683).length < 2 ^ (prefixWord ++ tailWord_7650683).sum := by decide
  have hdescent : baseEnd_7650683 < baseStart_7650683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650693 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 8]
def baseStart_7650693 : Nat := 118140960795 + 7650693 * 2 ^ 59
def prefixEnd_7650693 : Nat := 4983230072969 + 3 ^ 40 * 7650693 * 2
def baseEnd_7650693 : Nat := 436498094332082262461401

theorem tailTrace_7650693 : CollatzResearch.WordTrace tailWord_7650693 prefixEnd_7650693 436498094332082262461401 := by
  unfold tailWord_7650693
  simp only [CollatzResearch.WordTrace]
  refine ⟨279043698071853370183036733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186029132047902246788691155 279043698071853370183036733)
  ·
    refine ⟨104641386776945013818638775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279043698071853370183036733 104641386776945013818638775)
    ·
      refine ⟨156962080165417520727958163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104641386776945013818638775 156962080165417520727958163)
      ·
        refine ⟨235443120248126281091937245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156962080165417520727958163 235443120248126281091937245)
        ·
          refine ⟨88291170093047355409476467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235443120248126281091937245 88291170093047355409476467)
          ·
            refine ⟨132436755139571033114214701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88291170093047355409476467 132436755139571033114214701)
            ·
              refine ⟨49663783177339137417830513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132436755139571033114214701 49663783177339137417830513)
              ·
                refine ⟨37247837383004353063372885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49663783177339137417830513 37247837383004353063372885)
                ·
                  refine ⟨436498094332082262461401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37247837383004353063372885 436498094332082262461401)
                  ·
                    rfl

theorem cell23_7650693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_7650693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650693 prefixEnd_7650693 := by exact prefixLift 7650693
  have htrace : WordTrace (prefixWord ++ tailWord_7650693) baseStart_7650693 baseEnd_7650693 := by
    simpa [prefixWord, tailWord_7650693, baseEnd_7650693] using wordTrace_append hprefix tailTrace_7650693
  have hstable : (prefixWord ++ tailWord_7650693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650693).length < 2 ^ (prefixWord ++ tailWord_7650693).sum := by decide
  have hdescent : baseEnd_7650693 < baseStart_7650693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650737 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7650737 : Nat := 118140960795 + 7650737 * 2 ^ 59
def prefixEnd_7650737 : Nat := 4983230072969 + 3 ^ 40 * 7650737 * 2
def baseEnd_7650737 : Nat := 3928505442137538190002407

theorem tailTrace_7650737 : CollatzResearch.WordTrace tailWord_7650737 prefixEnd_7650737 3928505442137538190002407 := by
  unfold tailWord_7650737
  simp only [CollatzResearch.WordTrace]
  refine ⟨279045302883693965697638465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186030201922462643798425643 279045302883693965697638465)
  ·
    refine ⟨209283977162770474273228849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279045302883693965697638465 209283977162770474273228849)
    ·
      refine ⟨156962982872077855704921637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209283977162770474273228849 156962982872077855704921637)
      ·
        refine ⟨29430559288514597944672807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156962982872077855704921637 29430559288514597944672807)
        ·
          refine ⟨44145838932771896917009211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29430559288514597944672807 44145838932771896917009211)
          ·
            refine ⟨66218758399157845375513817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44145838932771896917009211 66218758399157845375513817)
            ·
              refine ⟨49664068799368384031635363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66218758399157845375513817 49664068799368384031635363)
              ·
                refine ⟨74496103199052576047453045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49664068799368384031635363 74496103199052576047453045)
                ·
                  refine ⟨6984009674911179004448723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74496103199052576047453045 6984009674911179004448723)
                  ·
                    refine ⟨10476014512366768506673085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6984009674911179004448723 10476014512366768506673085)
                    ·
                      refine ⟨3928505442137538190002407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476014512366768506673085 3928505442137538190002407)
                      ·
                        rfl

theorem cell23_7650737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7650737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650737 prefixEnd_7650737 := by exact prefixLift 7650737
  have htrace : WordTrace (prefixWord ++ tailWord_7650737) baseStart_7650737 baseEnd_7650737 := by
    simpa [prefixWord, tailWord_7650737, baseEnd_7650737] using wordTrace_append hprefix tailTrace_7650737
  have hstable : (prefixWord ++ tailWord_7650737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650737).length < 2 ^ (prefixWord ++ tailWord_7650737).sum := by decide
  have hdescent : baseEnd_7650737 < baseStart_7650737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650764 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7650764 : Nat := 118140960795 + 7650764 * 2 ^ 59
def prefixEnd_7650764 : Nat := 4983230072969 + 3 ^ 40 * 7650764 * 2
def baseEnd_7650764 : Nat := 3928519306115209584364783

theorem tailTrace_7650764 : CollatzResearch.WordTrace tailWord_7650764 prefixEnd_7650764 3928519306115209584364783 := by
  unfold tailWord_7650764
  simp only [CollatzResearch.WordTrace]
  refine ⟨139523143827298074654435673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186030858436397432872580897 139523143827298074654435673)
  ·
    refine ⟨104642357870473555990826755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139523143827298074654435673 104642357870473555990826755)
    ·
      refine ⟨156963536805710333986240133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104642357870473555990826755 156963536805710333986240133)
      ·
        refine ⟨29430663151070687622420025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156963536805710333986240133 29430663151070687622420025)
        ·
          refine ⟨22072997363303015716815019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29430663151070687622420025 22072997363303015716815019)
          ·
            refine ⟨33109496044954523575222529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22072997363303015716815019 33109496044954523575222529)
            ·
              refine ⟨24832122033715892681416897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33109496044954523575222529 24832122033715892681416897)
              ·
                refine ⟨18624091525286919511062673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24832122033715892681416897 18624091525286919511062673)
                ·
                  refine ⟨13968068643965189633297005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18624091525286919511062673 13968068643965189633297005)
                  ·
                    refine ⟨5238025741486946112486377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13968068643965189633297005 5238025741486946112486377)
                    ·
                      refine ⟨3928519306115209584364783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238025741486946112486377 3928519306115209584364783)
                      ·
                        rfl

theorem cell23_7650764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7650764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650764 prefixEnd_7650764 := by exact prefixLift 7650764
  have htrace : WordTrace (prefixWord ++ tailWord_7650764) baseStart_7650764 baseEnd_7650764 := by
    simpa [prefixWord, tailWord_7650764, baseEnd_7650764] using wordTrace_append hprefix tailTrace_7650764
  have hstable : (prefixWord ++ tailWord_7650764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650764).length < 2 ^ (prefixWord ++ tailWord_7650764).sum := by decide
  have hdescent : baseEnd_7650764 < baseStart_7650764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650787 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 1, 6]
def baseStart_7650787 : Nat := 118140960795 + 7650787 * 2 ^ 59
def prefixEnd_7650787 : Nat := 4983230072969 + 3 ^ 40 * 7650787 * 2
def baseEnd_7650787 : Nat := 1309510372056754331459059

theorem tailTrace_7650787 : CollatzResearch.WordTrace tailWord_7650787 prefixEnd_7650787 1309510372056754331459059 := by
  unfold tailWord_7650787
  simp only [CollatzResearch.WordTrace]
  refine ⟨279047126533512824236958615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186031417689008549491305743 279047126533512824236958615)
  ·
    refine ⟨418570689800269236355437923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279047126533512824236958615 418570689800269236355437923)
    ·
      refine ⟨627856034700403854533156885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418570689800269236355437923 627856034700403854533156885)
      ·
        refine ⟨29430751626581430681241729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 627856034700403854533156885 29430751626581430681241729)
        ·
          refine ⟨22073063719936073010931297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29430751626581430681241729 22073063719936073010931297)
          ·
            refine ⟨16554797789952054758198473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22073063719936073010931297 16554797789952054758198473)
            ·
              refine ⟨12416098342464041068648855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16554797789952054758198473 12416098342464041068648855)
              ·
                refine ⟨18624147513696061602973283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12416098342464041068648855 18624147513696061602973283)
                ·
                  refine ⟨27936221270544092404459925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18624147513696061602973283 27936221270544092404459925)
                  ·
                    refine ⟨1309510372056754331459059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27936221270544092404459925 1309510372056754331459059)
                    ·
                      rfl

theorem cell23_7650787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 6].length) (baseStart_7650787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650787 prefixEnd_7650787 := by exact prefixLift 7650787
  have htrace : WordTrace (prefixWord ++ tailWord_7650787) baseStart_7650787 baseEnd_7650787 := by
    simpa [prefixWord, tailWord_7650787, baseEnd_7650787] using wordTrace_append hprefix tailTrace_7650787
  have hstable : (prefixWord ++ tailWord_7650787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650787).length < 2 ^ (prefixWord ++ tailWord_7650787).sum := by decide
  have hdescent : baseEnd_7650787 < baseStart_7650787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650937 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_7650937 : Nat := 118140960795 + 7650937 * 2 ^ 59
def prefixEnd_7650937 : Nat := 4983230072969 + 3 ^ 40 * 7650937 * 2
def baseEnd_7650937 : Nat := 1309536046089479135833829

theorem tailTrace_7650937 : CollatzResearch.WordTrace tailWord_7650937 prefixEnd_7650937 1309536046089479135833829 := by
  unfold tailWord_7650937
  simp only [CollatzResearch.WordTrace]
  refine ⟨279052597482969399854919065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186035064988646266569946043 279052597482969399854919065)
  ·
    refine ⟨209289448112227049891189299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279052597482969399854919065 209289448112227049891189299)
    ·
      refine ⟨313934172168340574836783949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209289448112227049891189299 313934172168340574836783949)
      ·
        refine ⟨117725314563127715563793981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313934172168340574836783949 117725314563127715563793981)
        ·
          refine ⟨44146992961172893336422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117725314563127715563793981 44146992961172893336422743)
          ·
            refine ⟨66220489441759340004634115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44146992961172893336422743 66220489441759340004634115)
            ·
              refine ⟨99330734162639010006951173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66220489441759340004634115 99330734162639010006951173)
              ·
                refine ⟨18624512655494814376303345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99330734162639010006951173 18624512655494814376303345)
                ·
                  refine ⟨13968384491621110782227509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18624512655494814376303345 13968384491621110782227509)
                  ·
                    refine ⟨1309536046089479135833829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13968384491621110782227509 1309536046089479135833829)
                    ·
                      rfl

theorem cell23_7650937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_7650937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650937 prefixEnd_7650937 := by exact prefixLift 7650937
  have htrace : WordTrace (prefixWord ++ tailWord_7650937) baseStart_7650937 baseEnd_7650937 := by
    simpa [prefixWord, tailWord_7650937, baseEnd_7650937] using wordTrace_append hprefix tailTrace_7650937
  have hstable : (prefixWord ++ tailWord_7650937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650937).length < 2 ^ (prefixWord ++ tailWord_7650937).sum := by decide
  have hdescent : baseEnd_7650937 < baseStart_7650937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650941 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 5]
def baseStart_7650941 : Nat := 118140960795 + 7650941 * 2 ^ 59
def prefixEnd_7650941 : Nat := 4983230072969 + 3 ^ 40 * 7650941 * 2
def baseEnd_7650941 : Nat := 436512243576783932427941

theorem tailTrace_7650941 : CollatzResearch.WordTrace tailWord_7650941 prefixEnd_7650941 436512243576783932427941 := by
  unfold tailWord_7650941
  simp only [CollatzResearch.WordTrace]
  refine ⟨279052743374954908538064677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186035162249969939025376451 279052743374954908538064677)
  ·
    refine ⟨52322389382804045350887127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279052743374954908538064677 52322389382804045350887127)
    ·
      refine ⟨78483584074206068026330691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52322389382804045350887127 78483584074206068026330691)
      ·
        refine ⟨117725376111309102039496037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78483584074206068026330691 117725376111309102039496037)
        ·
          refine ⟨22073508020870456632405507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117725376111309102039496037 22073508020870456632405507)
          ·
            refine ⟨33110262031305684948608261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22073508020870456632405507 33110262031305684948608261)
            ·
              refine ⟨6208174130869815927864049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33110262031305684948608261 6208174130869815927864049)
              ·
                refine ⟨4656130598152361945898037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208174130869815927864049 4656130598152361945898037)
                ·
                  refine ⟨436512243576783932427941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4656130598152361945898037 436512243576783932427941)
                  ·
                    rfl

theorem cell23_7650941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_7650941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650941 prefixEnd_7650941 := by exact prefixLift 7650941
  have htrace : WordTrace (prefixWord ++ tailWord_7650941) baseStart_7650941 baseEnd_7650941 := by
    simpa [prefixWord, tailWord_7650941, baseEnd_7650941] using wordTrace_append hprefix tailTrace_7650941
  have hstable : (prefixWord ++ tailWord_7650941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650941).length < 2 ^ (prefixWord ++ tailWord_7650941).sum := by decide
  have hdescent : baseEnd_7650941 < baseStart_7650941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7650994 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_7650994 : Nat := 118140960795 + 7650994 * 2 ^ 59
def prefixEnd_7650994 : Nat := 4983230072969 + 3 ^ 40 * 7650994 * 2
def baseEnd_7650994 : Nat := 3928637406665743684488725

theorem tailTrace_7650994 : CollatzResearch.WordTrace tailWord_7650994 prefixEnd_7650994 3928637406665743684488725 := by
  unfold tailWord_7650994
  simp only [CollatzResearch.WordTrace]
  refine ⟨69763669110940724647436009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186036450962508599059829357 69763669110940724647436009)
  ·
    refine ⟨52322751833205543485577007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69763669110940724647436009 52322751833205543485577007)
    ·
      refine ⟨78484127749808315228365511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52322751833205543485577007 78484127749808315228365511)
      ·
        refine ⟨117726191624712472842548267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78484127749808315228365511 117726191624712472842548267)
        ·
          refine ⟨176589287437068709263822401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117726191624712472842548267 176589287437068709263822401)
          ·
            refine ⟨132441965577801531947866801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176589287437068709263822401 132441965577801531947866801)
            ·
              refine ⟨99331474183351148960900101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132441965577801531947866801 99331474183351148960900101)
              ·
                refine ⟨18624651409378340430168769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99331474183351148960900101 18624651409378340430168769)
                ·
                  refine ⟨13968488557033755322626577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18624651409378340430168769 13968488557033755322626577)
                  ·
                    refine ⟨10476366417775316491969933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13968488557033755322626577 10476366417775316491969933)
                    ·
                      refine ⟨3928637406665743684488725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476366417775316491969933 3928637406665743684488725)
                      ·
                        rfl

theorem cell23_7650994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_7650994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7650994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7650994 prefixEnd_7650994 := by exact prefixLift 7650994
  have htrace : WordTrace (prefixWord ++ tailWord_7650994) baseStart_7650994 baseEnd_7650994 := by
    simpa [prefixWord, tailWord_7650994, baseEnd_7650994] using wordTrace_append hprefix tailTrace_7650994
  have hstable : (prefixWord ++ tailWord_7650994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7650994).length < 2 ^ (prefixWord ++ tailWord_7650994).sum := by decide
  have hdescent : baseEnd_7650994 < baseStart_7650994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7650994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651001 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 1, 4]
def baseStart_7651001 : Nat := 118140960795 + 7651001 * 2 ^ 59
def prefixEnd_7651001 : Nat := 4983230072969 + 3 ^ 40 * 7651001 * 2
def baseEnd_7651001 : Nat := 1309547000343441719033731

theorem tailTrace_7651001 : CollatzResearch.WordTrace tailWord_7651001 prefixEnd_7651001 1309547000343441719033731 := by
  unfold tailWord_7651001
  simp only [CollatzResearch.WordTrace]
  refine ⟨279054931754737538785248857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186036621169825025856832571 279054931754737538785248857)
  ·
    refine ⟨209291198816053154088936643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279054931754737538785248857 209291198816053154088936643)
    ·
      refine ⟨313936798224079731133404965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209291198816053154088936643 313936798224079731133404965)
      ·
        refine ⟨58863149667014949587513431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313936798224079731133404965 58863149667014949587513431)
        ·
          refine ⟨88294724500522424381270147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58863149667014949587513431 88294724500522424381270147)
          ·
            refine ⟨132442086750783636571905221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88294724500522424381270147 132442086750783636571905221)
            ·
              refine ⟨24832891265771931857232229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132442086750783636571905221 24832891265771931857232229)
              ·
                refine ⟨4656167112332237223231043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24832891265771931857232229 4656167112332237223231043)
                ·
                  refine ⟨6984250668498355834846565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656167112332237223231043 6984250668498355834846565)
                  ·
                    refine ⟨1309547000343441719033731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6984250668498355834846565 1309547000343441719033731)
                    ·
                      rfl

theorem cell23_7651001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 4].length) (baseStart_7651001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651001 prefixEnd_7651001 := by exact prefixLift 7651001
  have htrace : WordTrace (prefixWord ++ tailWord_7651001) baseStart_7651001 baseEnd_7651001 := by
    simpa [prefixWord, tailWord_7651001, baseEnd_7651001] using wordTrace_append hprefix tailTrace_7651001
  have hstable : (prefixWord ++ tailWord_7651001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651001).length < 2 ^ (prefixWord ++ tailWord_7651001).sum := by decide
  have hdescent : baseEnd_7651001 < baseStart_7651001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651024 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3]
def baseStart_7651024 : Nat := 118140960795 + 7651024 * 2 ^ 59
def prefixEnd_7651024 : Nat := 4983230072969 + 3 ^ 40 * 7651024 * 2
def baseEnd_7651024 : Nat := 3928652811085378567113587

theorem tailTrace_7651024 : CollatzResearch.WordTrace tailWord_7651024 prefixEnd_7651024 3928652811085378567113587 := by
  unfold tailWord_7651024
  simp only [CollatzResearch.WordTrace]
  refine ⟨139527885316827106856668063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186037180422436142475557417 139527885316827106856668063)
  ·
    refine ⟨209291827975240660285002095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139527885316827106856668063 209291827975240660285002095)
    ·
      refine ⟨313937741962860990427503143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209291827975240660285002095 313937741962860990427503143)
      ·
        refine ⟨470906612944291485641254715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313937741962860990427503143 470906612944291485641254715)
        ·
          refine ⟨706359919416437228461882073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470906612944291485641254715 706359919416437228461882073)
          ·
            refine ⟨529769939562327921346411555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706359919416437228461882073 529769939562327921346411555)
            ·
              refine ⟨794654909343491882019617333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529769939562327921346411555 794654909343491882019617333)
              ·
                refine ⟨74498897750952363939339125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 794654909343491882019617333 74498897750952363939339125)
                ·
                  refine ⟨6984271664151784119313043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74498897750952363939339125 6984271664151784119313043)
                  ·
                    refine ⟨10476407496227676178969565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6984271664151784119313043 10476407496227676178969565)
                    ·
                      refine ⟨3928652811085378567113587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476407496227676178969565 3928652811085378567113587)
                      ·
                        rfl

theorem cell23_7651024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_7651024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651024 prefixEnd_7651024 := by exact prefixLift 7651024
  have htrace : WordTrace (prefixWord ++ tailWord_7651024) baseStart_7651024 baseEnd_7651024 := by
    simpa [prefixWord, tailWord_7651024, baseEnd_7651024] using wordTrace_append hprefix tailTrace_7651024
  have hstable : (prefixWord ++ tailWord_7651024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651024).length < 2 ^ (prefixWord ++ tailWord_7651024).sum := by decide
  have hdescent : baseEnd_7651024 < baseStart_7651024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651044 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_7651044 : Nat := 118140960795 + 7651044 * 2 ^ 59
def prefixEnd_7651044 : Nat := 4983230072969 + 3 ^ 40 * 7651044 * 2
def baseEnd_7651044 : Nat := 1309554360232822829621165

theorem tailTrace_7651044 : CollatzResearch.WordTrace tailWord_7651044 prefixEnd_7651044 1309554360232822829621165 := by
  unfold tailWord_7651044
  simp only [CollatzResearch.WordTrace]
  refine ⟨139528250046790878564532093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186037666729054504752709457 139528250046790878564532093)
  ·
    refine ⟨52323093767546579461699535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139528250046790878564532093 52323093767546579461699535)
    ·
      refine ⟨78484640651319869192549303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52323093767546579461699535 78484640651319869192549303)
      ·
        refine ⟨117726960976979803788823955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78484640651319869192549303 117726960976979803788823955)
        ·
          refine ⟨176590441465469705683235933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117726960976979803788823955 176590441465469705683235933)
          ·
            refine ⟨66221415549551139631213475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176590441465469705683235933 66221415549551139631213475)
            ·
              refine ⟨99332123324326709446820213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66221415549551139631213475 99332123324326709446820213)
              ·
                refine ⟨9312386561655629010639395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99332123324326709446820213 9312386561655629010639395)
                ·
                  refine ⟨13968579842483443515959093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9312386561655629010639395 13968579842483443515959093)
                  ·
                    refine ⟨1309554360232822829621165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13968579842483443515959093 1309554360232822829621165)
                    ·
                      rfl

theorem cell23_7651044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_7651044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651044 prefixEnd_7651044 := by exact prefixLift 7651044
  have htrace : WordTrace (prefixWord ++ tailWord_7651044) baseStart_7651044 baseEnd_7651044 := by
    simpa [prefixWord, tailWord_7651044, baseEnd_7651044] using wordTrace_append hprefix tailTrace_7651044
  have hstable : (prefixWord ++ tailWord_7651044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651044).length < 2 ^ (prefixWord ++ tailWord_7651044).sum := by decide
  have hdescent : baseEnd_7651044 < baseStart_7651044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651064 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_7651064 : Nat := 118140960795 + 7651064 * 2 ^ 59
def prefixEnd_7651064 : Nat := 4983230072969 + 3 ^ 40 * 7651064 * 2
def baseEnd_7651064 : Nat := 3928673350311558410613403

theorem tailTrace_7651064 : CollatzResearch.WordTrace tailWord_7651064 prefixEnd_7651064 3928673350311558410613403 := by
  unfold tailWord_7651064
  simp only [CollatzResearch.WordTrace]
  refine ⟨139528614776754650272396123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186038153035672867029861497 139528614776754650272396123)
  ·
    refine ⟨209292922165131975408594185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139528614776754650272396123 209292922165131975408594185)
    ·
      refine ⟨156969691623848981556445639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209292922165131975408594185 156969691623848981556445639)
      ·
        refine ⟨235454537435773472334668459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156969691623848981556445639 235454537435773472334668459)
        ·
          refine ⟨353181806153660208502002689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235454537435773472334668459 353181806153660208502002689)
          ·
            refine ⟨264886354615245156376502017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353181806153660208502002689 264886354615245156376502017)
            ·
              refine ⟨198664765961433867282376513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264886354615245156376502017 198664765961433867282376513)
              ·
                refine ⟨148998574471075400461782385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198664765961433867282376513 148998574471075400461782385)
                ·
                  refine ⟨111748930853306550346336789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148998574471075400461782385 111748930853306550346336789)
                  ·
                    refine ⟨5238231133748744547484537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111748930853306550346336789 5238231133748744547484537)
                    ·
                      refine ⟨3928673350311558410613403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238231133748744547484537 3928673350311558410613403)
                      ·
                        rfl

theorem cell23_7651064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_7651064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651064 prefixEnd_7651064 := by exact prefixLift 7651064
  have htrace : WordTrace (prefixWord ++ tailWord_7651064) baseStart_7651064 baseEnd_7651064 := by
    simpa [prefixWord, tailWord_7651064, baseEnd_7651064] using wordTrace_append hprefix tailTrace_7651064
  have hstable : (prefixWord ++ tailWord_7651064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651064).length < 2 ^ (prefixWord ++ tailWord_7651064).sum := by decide
  have hdescent : baseEnd_7651064 < baseStart_7651064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651067 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_7651067 : Nat := 118140960795 + 7651067 * 2 ^ 59
def prefixEnd_7651067 : Nat := 4983230072969 + 3 ^ 40 * 7651067 * 2
def baseEnd_7651067 : Nat := 3928674890753521898875889

theorem tailTrace_7651067 : CollatzResearch.WordTrace tailWord_7651067 prefixEnd_7651067 3928674890753521898875889 := by
  unfold tailWord_7651067
  simp only [CollatzResearch.WordTrace]
  refine ⟨279057338972498432057151455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186038225981665621371434303 279057338972498432057151455)
  ·
    refine ⟨418586008458747648085727183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279057338972498432057151455 418586008458747648085727183)
    ·
      refine ⟨627879012688121472128590775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418586008458747648085727183 627879012688121472128590775)
      ·
        refine ⟨941818519032182208192886163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627879012688121472128590775 941818519032182208192886163)
        ·
          refine ⟨1412727778548273312289329245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941818519032182208192886163 1412727778548273312289329245)
          ·
            refine ⟨529772916955602492108498467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1412727778548273312289329245 529772916955602492108498467)
            ·
              refine ⟨794659375433403738162747701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529772916955602492108498467 794659375433403738162747701)
              ·
                refine ⟨74499316446881600452757597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 794659375433403738162747701 74499316446881600452757597)
                ·
                  refine ⟨27937243667580600169784099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74499316446881600452757597 27937243667580600169784099)
                  ·
                    refine ⟨41905865501370900254676149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27937243667580600169784099 41905865501370900254676149)
                    ·
                      refine ⟨3928674890753521898875889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41905865501370900254676149 3928674890753521898875889)
                      ·
                        rfl

theorem cell23_7651067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_7651067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651067 prefixEnd_7651067 := by exact prefixLift 7651067
  have htrace : WordTrace (prefixWord ++ tailWord_7651067) baseStart_7651067 baseEnd_7651067 := by
    simpa [prefixWord, tailWord_7651067, baseEnd_7651067] using wordTrace_append hprefix tailTrace_7651067
  have hstable : (prefixWord ++ tailWord_7651067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651067).length < 2 ^ (prefixWord ++ tailWord_7651067).sum := by decide
  have hdescent : baseEnd_7651067 < baseStart_7651067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651081 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 5, 2, 2]
def baseStart_7651081 : Nat := 118140960795 + 7651081 * 2 ^ 59
def prefixEnd_7651081 : Nat := 4983230072969 + 3 ^ 40 * 7651081 * 2
def baseEnd_7651081 : Nat := 3928682079482684844100825

theorem tailTrace_7651081 : CollatzResearch.WordTrace tailWord_7651081 prefixEnd_7651081 3928682079482684844100825 := by
  unfold tailWord_7651081
  simp only [CollatzResearch.WordTrace]
  refine ⟨279057849594447712448161097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186038566396298474965440731 279057849594447712448161097)
  ·
    refine ⟨209293387195835784336120823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279057849594447712448161097 209293387195835784336120823)
    ·
      refine ⟨313940080793753676504181235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209293387195835784336120823 313940080793753676504181235)
      ·
        refine ⟨470910121190630514756271853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313940080793753676504181235 470910121190630514756271853)
        ·
          refine ⟨176591295446486443033601945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470910121190630514756271853 176591295446486443033601945)
          ·
            refine ⟨132443471584864832275201459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176591295446486443033601945 132443471584864832275201459)
            ·
              refine ⟨198665207377297248412802189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132443471584864832275201459 198665207377297248412802189)
              ·
                refine ⟨74499452766486468154800821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198665207377297248412802189 74499452766486468154800821)
                ·
                  refine ⟨6984323696858106389512577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74499452766486468154800821 6984323696858106389512577)
                  ·
                    refine ⟨5238242772643579792134433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984323696858106389512577 5238242772643579792134433)
                    ·
                      refine ⟨3928682079482684844100825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238242772643579792134433 3928682079482684844100825)
                      ·
                        rfl

theorem cell23_7651081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2, 2].length) (baseStart_7651081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651081 prefixEnd_7651081 := by exact prefixLift 7651081
  have htrace : WordTrace (prefixWord ++ tailWord_7651081) baseStart_7651081 baseEnd_7651081 := by
    simpa [prefixWord, tailWord_7651081, baseEnd_7651081] using wordTrace_append hprefix tailTrace_7651081
  have hstable : (prefixWord ++ tailWord_7651081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651081).length < 2 ^ (prefixWord ++ tailWord_7651081).sum := by decide
  have hdescent : baseEnd_7651081 < baseStart_7651081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651098 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_7651098 : Nat := 118140960795 + 7651098 * 2 ^ 59
def prefixEnd_7651098 : Nat := 4983230072969 + 3 ^ 40 * 7651098 * 2
def baseEnd_7651098 : Nat := 3928690808653811277588247

theorem tailTrace_7651098 : CollatzResearch.WordTrace tailWord_7651098 prefixEnd_7651098 3928690808653811277588247 := by
  unfold tailWord_7651098
  simp only [CollatzResearch.WordTrace]
  refine ⟨69764617408846531087882487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186038979756924082901019965 69764617408846531087882487)
  ·
    refine ⟨104646926113269796631823731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69764617408846531087882487 104646926113269796631823731)
    ·
      refine ⟨156970389169904694947735597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104646926113269796631823731 156970389169904694947735597)
      ·
        refine ⟨58863895938714260605400849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156970389169904694947735597 58863895938714260605400849)
        ·
          refine ⟨44147921954035695454050637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58863895938714260605400849 44147921954035695454050637)
          ·
            refine ⟨16555470732763385795268989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44147921954035695454050637 16555470732763385795268989)
            ·
              refine ⟨6208301524786269673225871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16555470732763385795268989 6208301524786269673225871)
              ·
                refine ⟨9312452287179404509838807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208301524786269673225871 9312452287179404509838807)
                ·
                  refine ⟨13968678430769106764758211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9312452287179404509838807 13968678430769106764758211)
                  ·
                    refine ⟨20953017646153660147137317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13968678430769106764758211 20953017646153660147137317)
                    ·
                      refine ⟨3928690808653811277588247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20953017646153660147137317 3928690808653811277588247)
                      ·
                        rfl

theorem cell23_7651098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_7651098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651098 prefixEnd_7651098 := by exact prefixLift 7651098
  have htrace : WordTrace (prefixWord ++ tailWord_7651098) baseStart_7651098 baseEnd_7651098 := by
    simpa [prefixWord, tailWord_7651098, baseEnd_7651098] using wordTrace_append hprefix tailTrace_7651098
  have hstable : (prefixWord ++ tailWord_7651098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651098).length < 2 ^ (prefixWord ++ tailWord_7651098).sum := by decide
  have hdescent : baseEnd_7651098 < baseStart_7651098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651108 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_7651108 : Nat := 118140960795 + 7651108 * 2 ^ 59
def prefixEnd_7651108 : Nat := 4983230072969 + 3 ^ 40 * 7651108 * 2
def baseEnd_7651108 : Nat := 1309565314486785412821067

theorem tailTrace_7651108 : CollatzResearch.WordTrace tailWord_7651108 prefixEnd_7651108 1309565314486785412821067 := by
  unfold tailWord_7651108
  simp only [CollatzResearch.WordTrace]
  refine ⟨139529417182674948029696989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186039222910233264039595985 139529417182674948029696989)
  ·
    refine ⟨52323531443503105511136371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139529417182674948029696989 52323531443503105511136371)
    ·
      refine ⟨78485297165254658266704557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52323531443503105511136371 78485297165254658266704557)
      ·
        refine ⟨29431986436970496850014209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78485297165254658266704557 29431986436970496850014209)
        ·
          refine ⟨22073989827727872637510657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29431986436970496850014209 22073989827727872637510657)
          ·
            refine ⟨16555492370795904478132993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22073989827727872637510657 16555492370795904478132993)
            ·
              refine ⟨12416619278096928358599745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16555492370795904478132993 12416619278096928358599745)
              ·
                refine ⟨9312464458572696268949809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12416619278096928358599745 9312464458572696268949809)
                ·
                  refine ⟨6984348343929522201712357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9312464458572696268949809 6984348343929522201712357)
                  ·
                    refine ⟨1309565314486785412821067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6984348343929522201712357 1309565314486785412821067)
                    ·
                      rfl

theorem cell23_7651108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_7651108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651108 prefixEnd_7651108 := by exact prefixLift 7651108
  have htrace : WordTrace (prefixWord ++ tailWord_7651108) baseStart_7651108 baseEnd_7651108 := by
    simpa [prefixWord, tailWord_7651108, baseEnd_7651108] using wordTrace_append hprefix tailTrace_7651108
  have hstable : (prefixWord ++ tailWord_7651108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651108).length < 2 ^ (prefixWord ++ tailWord_7651108).sum := by decide
  have hdescent : baseEnd_7651108 < baseStart_7651108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651141 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_7651141 : Nat := 118140960795 + 7651141 * 2 ^ 59
def prefixEnd_7651141 : Nat := 4983230072969 + 3 ^ 40 * 7651141 * 2
def baseEnd_7651141 : Nat := 3928712888321954609350549

theorem tailTrace_7651141 : CollatzResearch.WordTrace tailWord_7651141 prefixEnd_7651141 3928712888321954609350549 := by
  unfold tailWord_7651141
  simp only [CollatzResearch.WordTrace]
  refine ⟨279060037974230342695345277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186040025316153561796896851 279060037974230342695345277)
  ·
    refine ⟨104647514240336378510754479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279060037974230342695345277 104647514240336378510754479)
    ·
      refine ⟨156971271360504567766131719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104647514240336378510754479 156971271360504567766131719)
      ·
        refine ⟨235456907040756851649197579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156971271360504567766131719 235456907040756851649197579)
        ·
          refine ⟨353185360561135277473796369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235456907040756851649197579 353185360561135277473796369)
          ·
            refine ⟨264889020420851458105347277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353185360561135277473796369 264889020420851458105347277)
            ·
              refine ⟨99333382657819296789505229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264889020420851458105347277 99333382657819296789505229)
              ·
                refine ⟨37250018496682236296064461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99333382657819296789505229 37250018496682236296064461)
                ·
                  refine ⟨13968756936255838611024173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37250018496682236296064461 13968756936255838611024173)
                  ·
                    refine ⟨5238283851095939479134065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13968756936255838611024173 5238283851095939479134065)
                    ·
                      refine ⟨3928712888321954609350549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238283851095939479134065 3928712888321954609350549)
                      ·
                        rfl

theorem cell23_7651141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_7651141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651141 prefixEnd_7651141 := by exact prefixLift 7651141
  have htrace : WordTrace (prefixWord ++ tailWord_7651141) baseStart_7651141 baseEnd_7651141 := by
    simpa [prefixWord, tailWord_7651141, baseEnd_7651141] using wordTrace_append hprefix tailTrace_7651141
  have hstable : (prefixWord ++ tailWord_7651141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651141).length < 2 ^ (prefixWord ++ tailWord_7651141).sum := by decide
  have hdescent : baseEnd_7651141 < baseStart_7651141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651149 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7651149 : Nat := 118140960795 + 7651149 * 2 ^ 59
def prefixEnd_7651149 : Nat := 4983230072969 + 3 ^ 40 * 7651149 * 2
def baseEnd_7651149 : Nat := 3928716996167190578050513

theorem tailTrace_7651149 : CollatzResearch.WordTrace tailWord_7651149 prefixEnd_7651149 3928716996167190578050513 := by
  unfold tailWord_7651149
  simp only [CollatzResearch.WordTrace]
  refine ⟨279060329758201360061636501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186040219838800906707757667 279060329758201360061636501)
  ·
    refine ⟨13080952957415688752889211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279060329758201360061636501 13080952957415688752889211)
    ·
      refine ⟨19621429436123533129333817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13080952957415688752889211 19621429436123533129333817)
      ·
        refine ⟨14716072077092649847000363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19621429436123533129333817 14716072077092649847000363)
        ·
          refine ⟨22074108115638974770500545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716072077092649847000363 22074108115638974770500545)
          ·
            refine ⟨16555581086729231077875409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22074108115638974770500545 16555581086729231077875409)
            ·
              refine ⟨12416685815046923308406557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16555581086729231077875409 12416685815046923308406557)
              ·
                refine ⟨4656257180642596240652459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12416685815046923308406557 4656257180642596240652459)
                ·
                  refine ⟨6984385770963894360978689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656257180642596240652459 6984385770963894360978689)
                  ·
                    refine ⟨5238289328222920770734017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984385770963894360978689 5238289328222920770734017)
                    ·
                      refine ⟨3928716996167190578050513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238289328222920770734017 3928716996167190578050513)
                      ·
                        rfl

theorem cell23_7651149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7651149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651149 prefixEnd_7651149 := by exact prefixLift 7651149
  have htrace : WordTrace (prefixWord ++ tailWord_7651149) baseStart_7651149 baseEnd_7651149 := by
    simpa [prefixWord, tailWord_7651149, baseEnd_7651149] using wordTrace_append hprefix tailTrace_7651149
  have hstable : (prefixWord ++ tailWord_7651149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651149).length < 2 ^ (prefixWord ++ tailWord_7651149).sum := by decide
  have hdescent : baseEnd_7651149 < baseStart_7651149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651182 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7651182 : Nat := 118140960795 + 7651182 * 2 ^ 59
def prefixEnd_7651182 : Nat := 4983230072969 + 3 ^ 40 * 7651182 * 2
def baseEnd_7651182 : Nat := 3928733941028788948937861

theorem tailTrace_7651182 : CollatzResearch.WordTrace tailWord_7651182 prefixEnd_7651182 3928733941028788948937861 := by
  unfold tailWord_7651182
  simp only [CollatzResearch.WordTrace]
  refine ⟨34882691670885225837198475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186041022244721204465058533 34882691670885225837198475)
  ·
    refine ⟨52324037506327838755797713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34882691670885225837198475 52324037506327838755797713)
    ·
      refine ⟨39243028129745879066848285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52324037506327838755797713 39243028129745879066848285)
      ·
        refine ⟨14716135548654704650068107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39243028129745879066848285 14716135548654704650068107)
        ·
          refine ⟨22074203322982056975102161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716135548654704650068107 22074203322982056975102161)
          ·
            refine ⟨16555652492236542731326621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22074203322982056975102161 16555652492236542731326621)
            ·
              refine ⟨6208369684588703524247483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16555652492236542731326621 6208369684588703524247483)
              ·
                refine ⟨9312554526883055286371225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208369684588703524247483 9312554526883055286371225)
                ·
                  refine ⟨6984415895162291464778419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9312554526883055286371225 6984415895162291464778419)
                  ·
                    refine ⟨10476623842743437197167629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6984415895162291464778419 10476623842743437197167629)
                    ·
                      refine ⟨3928733941028788948937861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476623842743437197167629 3928733941028788948937861)
                      ·
                        rfl

theorem cell23_7651182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7651182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651182 prefixEnd_7651182 := by exact prefixLift 7651182
  have htrace : WordTrace (prefixWord ++ tailWord_7651182) baseStart_7651182 baseEnd_7651182 := by
    simpa [prefixWord, tailWord_7651182, baseEnd_7651182] using wordTrace_append hprefix tailTrace_7651182
  have hstable : (prefixWord ++ tailWord_7651182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651182).length < 2 ^ (prefixWord ++ tailWord_7651182).sum := by decide
  have hdescent : baseEnd_7651182 < baseStart_7651182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651194 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_7651194 : Nat := 118140960795 + 7651194 * 2 ^ 59
def prefixEnd_7651194 : Nat := 4983230072969 + 3 ^ 40 * 7651194 * 2
def baseEnd_7651194 : Nat := 436526678088515877998645

theorem tailTrace_7651194 : CollatzResearch.WordTrace tailWord_7651194 prefixEnd_7651194 436526678088515877998645 := by
  unfold tailWord_7651194
  simp only [CollatzResearch.WordTrace]
  refine ⟨69765492760759583186756159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186041314028692221831349757 69765492760759583186756159)
  ·
    refine ⟨104648239141139374780134239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69765492760759583186756159 104648239141139374780134239)
    ·
      refine ⟨156972358711709062170201359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104648239141139374780134239 156972358711709062170201359)
      ·
        refine ⟨235458538067563593255302039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156972358711709062170201359 235458538067563593255302039)
        ·
          refine ⟨353187807101345389882953059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235458538067563593255302039 353187807101345389882953059)
          ·
            refine ⟨529781710652018084824429589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353187807101345389882953059 529781710652018084824429589)
            ·
              refine ⟨24833517686813347726145137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 529781710652018084824429589 24833517686813347726145137)
              ·
                refine ⟨18625138265110010794608853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24833517686813347726145137 18625138265110010794608853)
                ·
                  refine ⟨436526678088515877998645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18625138265110010794608853 436526678088515877998645)
                  ·
                    rfl

theorem cell23_7651194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_7651194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651194 prefixEnd_7651194 := by exact prefixLift 7651194
  have htrace : WordTrace (prefixWord ++ tailWord_7651194) baseStart_7651194 baseEnd_7651194 := by
    simpa [prefixWord, tailWord_7651194, baseEnd_7651194] using wordTrace_append hprefix tailTrace_7651194
  have hstable : (prefixWord ++ tailWord_7651194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651194).length < 2 ^ (prefixWord ++ tailWord_7651194).sum := by decide
  have hdescent : baseEnd_7651194 < baseStart_7651194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651228 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 7]
def baseStart_7651228 : Nat := 118140960795 + 7651228 * 2 ^ 59
def prefixEnd_7651228 : Nat := 4983230072969 + 3 ^ 40 * 7651228 * 2
def baseEnd_7651228 : Nat := 436528617904321752106961

theorem tailTrace_7651228 : CollatzResearch.WordTrace tailWord_7651228 prefixEnd_7651228 436528617904321752106961 := by
  unfold tailWord_7651228
  simp only [CollatzResearch.WordTrace]
  refine ⟨139531605562457578276881169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186042140749943437702508225 139531605562457578276881169)
  ·
    refine ⟨104648704171843183707660877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139531605562457578276881169 104648704171843183707660877)
    ·
      refine ⟨39243264064441193890372829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104648704171843183707660877 39243264064441193890372829)
      ·
        refine ⟨14716224024165447708889811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39243264064441193890372829 14716224024165447708889811)
        ·
          refine ⟨22074336036248171563334717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716224024165447708889811 22074336036248171563334717)
          ·
            refine ⟨8277876013593064336250519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22074336036248171563334717 8277876013593064336250519)
            ·
              refine ⟨12416814020389596504375779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277876013593064336250519 12416814020389596504375779)
              ·
                refine ⟨18625221030584394756563669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12416814020389596504375779 18625221030584394756563669)
                ·
                  refine ⟨436528617904321752106961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18625221030584394756563669 436528617904321752106961)
                  ·
                    rfl

theorem cell23_7651228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_7651228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651228 prefixEnd_7651228 := by exact prefixLift 7651228
  have htrace : WordTrace (prefixWord ++ tailWord_7651228) baseStart_7651228 baseEnd_7651228 := by
    simpa [prefixWord, tailWord_7651228, baseEnd_7651228] using wordTrace_append hprefix tailTrace_7651228
  have hstable : (prefixWord ++ tailWord_7651228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651228).length < 2 ^ (prefixWord ++ tailWord_7651228).sum := by decide
  have hdescent : baseEnd_7651228 < baseStart_7651228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651239 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7651239 : Nat := 118140960795 + 7651239 * 2 ^ 59
def prefixEnd_7651239 : Nat := 4983230072969 + 3 ^ 40 * 7651239 * 2
def baseEnd_7651239 : Nat := 3928763209426095225925099

theorem tailTrace_7651239 : CollatzResearch.WordTrace tailWord_7651239 prefixEnd_7651239 3928763209426095225925099 := by
  unfold tailWord_7651239
  simp only [CollatzResearch.WordTrace]
  refine ⟨279063612327875305432412771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186042408218583536954941847 279063612327875305432412771)
  ·
    refine ⟨418595418491812958148619157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279063612327875305432412771 418595418491812958148619157)
    ·
      refine ⟨19621660241803732413216523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418595418491812958148619157 19621660241803732413216523)
      ·
        refine ⟨29432490362705598619824785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621660241803732413216523 29432490362705598619824785)
        ·
          refine ⟨22074367772029198964868589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29432490362705598619824785 22074367772029198964868589)
          ·
            refine ⟨8277887914510949611825721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22074367772029198964868589 8277887914510949611825721)
            ·
              refine ⟨6208415935883212208869291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8277887914510949611825721 6208415935883212208869291)
              ·
                refine ⟨9312623903824818313303937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208415935883212208869291 9312623903824818313303937)
                ·
                  refine ⟨6984467927868613734977953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9312623903824818313303937 6984467927868613734977953)
                  ·
                    refine ⟨5238350945901460301233465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984467927868613734977953 5238350945901460301233465)
                    ·
                      refine ⟨3928763209426095225925099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238350945901460301233465 3928763209426095225925099)
                      ·
                        rfl

theorem cell23_7651239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7651239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651239 prefixEnd_7651239 := by exact prefixLift 7651239
  have htrace : WordTrace (prefixWord ++ tailWord_7651239) baseStart_7651239 baseEnd_7651239 := by
    simpa [prefixWord, tailWord_7651239, baseEnd_7651239] using wordTrace_append hprefix tailTrace_7651239
  have hstable : (prefixWord ++ tailWord_7651239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651239).length < 2 ^ (prefixWord ++ tailWord_7651239).sum := by decide
  have hdescent : baseEnd_7651239 < baseStart_7651239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651278 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_7651278 : Nat := 118140960795 + 7651278 * 2 ^ 59
def prefixEnd_7651278 : Nat := 4983230072969 + 3 ^ 40 * 7651278 * 2
def baseEnd_7651278 : Nat := 3928783235171620573337419

theorem tailTrace_7651278 : CollatzResearch.WordTrace tailWord_7651278 prefixEnd_7651278 3928783235171620573337419 := by
  unfold tailWord_7651278
  simp only [CollatzResearch.WordTrace]
  refine ⟨34883129346841751886635311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186043356516489343395388325 34883129346841751886635311)
  ·
    refine ⟨52324694020262627829952967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34883129346841751886635311 52324694020262627829952967)
    ·
      refine ⟨78487041030393941744929451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52324694020262627829952967 78487041030393941744929451)
      ·
        refine ⟨117730561545590912617394177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78487041030393941744929451 117730561545590912617394177)
        ·
          refine ⟨88297921159193184463045633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117730561545590912617394177 88297921159193184463045633)
          ·
            refine ⟨66223440869394888347284225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88297921159193184463045633 66223440869394888347284225)
            ·
              refine ⟨49667580652046166260463169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66223440869394888347284225 49667580652046166260463169)
              ·
                refine ⟨37250685489034624695347377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49667580652046166260463169 37250685489034624695347377)
                ·
                  refine ⟨27938014116775968521510533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37250685489034624695347377 27938014116775968521510533)
                  ·
                    refine ⟨5238377646895494097783225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27938014116775968521510533 5238377646895494097783225)
                    ·
                      refine ⟨3928783235171620573337419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238377646895494097783225 3928783235171620573337419)
                      ·
                        rfl

theorem cell23_7651278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_7651278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651278 prefixEnd_7651278 := by exact prefixLift 7651278
  have htrace : WordTrace (prefixWord ++ tailWord_7651278) baseStart_7651278 baseEnd_7651278 := by
    simpa [prefixWord, tailWord_7651278, baseEnd_7651278] using wordTrace_append hprefix tailTrace_7651278
  have hstable : (prefixWord ++ tailWord_7651278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651278).length < 2 ^ (prefixWord ++ tailWord_7651278).sum := by decide
  have hdescent : baseEnd_7651278 < baseStart_7651278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651281 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_7651281 : Nat := 118140960795 + 7651281 * 2 ^ 59
def prefixEnd_7651281 : Nat := 4983230072969 + 3 ^ 40 * 7651281 * 2
def baseEnd_7651281 : Nat := 3928784775613584061599905

theorem tailTrace_7651281 : CollatzResearch.WordTrace tailWord_7651281 prefixEnd_7651281 3928784775613584061599905 := by
  unfold tailWord_7651281
  simp only [CollatzResearch.WordTrace]
  refine ⟨279065144193723146605441697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186043429462482097736961131 279065144193723146605441697)
  ·
    refine ⟨209298858145292359954081273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279065144193723146605441697 209298858145292359954081273)
    ·
      refine ⟨156974143608969269965560955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209298858145292359954081273 156974143608969269965560955)
      ·
        refine ⟨235461215413453904948341433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156974143608969269965560955 235461215413453904948341433)
        ·
          refine ⟨176595911560090428711256075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235461215413453904948341433 176595911560090428711256075)
          ·
            refine ⟨264893867340135643066884113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176595911560090428711256075 264893867340135643066884113)
            ·
              refine ⟨198670400505101732300163085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264893867340135643066884113 198670400505101732300163085)
              ·
                refine ⟨74501400189413149612561157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198670400505101732300163085 74501400189413149612561157)
                ·
                  refine ⟨13969012535514965552355217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74501400189413149612561157 13969012535514965552355217)
                  ·
                    refine ⟨10476759401636224164266413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13969012535514965552355217 10476759401636224164266413)
                    ·
                      refine ⟨3928784775613584061599905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476759401636224164266413 3928784775613584061599905)
                      ·
                        rfl

theorem cell23_7651281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_7651281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651281 prefixEnd_7651281 := by exact prefixLift 7651281
  have htrace : WordTrace (prefixWord ++ tailWord_7651281) baseStart_7651281 baseEnd_7651281 := by
    simpa [prefixWord, tailWord_7651281, baseEnd_7651281] using wordTrace_append hprefix tailTrace_7651281
  have hstable : (prefixWord ++ tailWord_7651281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651281).length < 2 ^ (prefixWord ++ tailWord_7651281).sum := by decide
  have hdescent : baseEnd_7651281 < baseStart_7651281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651378 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_7651378 : Nat := 118140960795 + 7651378 * 2 ^ 59
def prefixEnd_7651378 : Nat := 4983230072969 + 3 ^ 40 * 7651378 * 2
def baseEnd_7651378 : Nat := 1309611527745690060695653

theorem tailTrace_7651378 : CollatzResearch.WordTrace tailWord_7651378 prefixEnd_7651378 1309611527745690060695653 := by
  unfold tailWord_7651378
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767170518592933042930697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186045788049581154781148525 69767170518592933042930697)
  ·
    refine ⟨52325377888944699782198023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69767170518592933042930697 52325377888944699782198023)
    ·
      refine ⟨78488066833417049673297035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52325377888944699782198023 78488066833417049673297035)
      ·
        refine ⟨117732100250125574509945553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78488066833417049673297035 117732100250125574509945553)
        ·
          refine ⟨88299075187594180882459165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117732100250125574509945553 88299075187594180882459165)
          ·
            refine ⟨33112153195347817830922187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88299075187594180882459165 33112153195347817830922187)
            ·
              refine ⟨49668229793021726746383281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33112153195347817830922187 49668229793021726746383281)
              ·
                refine ⟨37251172344766295059787461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49668229793021726746383281 37251172344766295059787461)
                ·
                  refine ⟨6984594814643680323710149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37251172344766295059787461 6984594814643680323710149)
                  ·
                    refine ⟨1309611527745690060695653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6984594814643680323710149 1309611527745690060695653)
                    ·
                      rfl

theorem cell23_7651378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_7651378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651378 prefixEnd_7651378 := by exact prefixLift 7651378
  have htrace : WordTrace (prefixWord ++ tailWord_7651378) baseStart_7651378 baseEnd_7651378 := by
    simpa [prefixWord, tailWord_7651378, baseEnd_7651378] using wordTrace_append hprefix tailTrace_7651378
  have hstable : (prefixWord ++ tailWord_7651378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651378).length < 2 ^ (prefixWord ++ tailWord_7651378).sum := by decide
  have hdescent : baseEnd_7651378 < baseStart_7651378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651388 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_7651388 : Nat := 118140960795 + 7651388 * 2 ^ 59
def prefixEnd_7651388 : Nat := 4983230072969 + 3 ^ 40 * 7651388 * 2
def baseEnd_7651388 : Nat := 3928839718043615142961913

theorem tailTrace_7651388 : CollatzResearch.WordTrace tailWord_7651388 prefixEnd_7651388 3928839718043615142961913 := by
  unfold tailWord_7651388
  simp only [CollatzResearch.WordTrace]
  refine ⟨139534523402167751939793409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186046031202890335919724545 139534523402167751939793409)
  ·
    refine ⟨104650892551625813954845057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139534523402167751939793409 104650892551625813954845057)
    ·
      refine ⟨78488169413719360466133793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104650892551625813954845057 78488169413719360466133793)
      ·
        refine ⟨58866127060289520349600345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78488169413719360466133793 58866127060289520349600345)
        ·
          refine ⟨44149595295217140262200259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58866127060289520349600345 44149595295217140262200259)
          ·
            refine ⟨66224392942825710393300389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44149595295217140262200259 66224392942825710393300389)
            ·
              refine ⟨12417073676779820698743823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66224392942825710393300389 12417073676779820698743823)
              ·
                refine ⟨18625610515169731048115735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12417073676779820698743823 18625610515169731048115735)
                ·
                  refine ⟨27938415772754596572173603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18625610515169731048115735 27938415772754596572173603)
                  ·
                    refine ⟨41907623659131894858260405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27938415772754596572173603 41907623659131894858260405)
                    ·
                      refine ⟨3928839718043615142961913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41907623659131894858260405 3928839718043615142961913)
                      ·
                        rfl

theorem cell23_7651388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_7651388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651388 prefixEnd_7651388 := by exact prefixLift 7651388
  have htrace : WordTrace (prefixWord ++ tailWord_7651388) baseStart_7651388 baseEnd_7651388 := by
    simpa [prefixWord, tailWord_7651388, baseEnd_7651388] using wordTrace_append hprefix tailTrace_7651388
  have hstable : (prefixWord ++ tailWord_7651388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651388).length < 2 ^ (prefixWord ++ tailWord_7651388).sum := by decide
  have hdescent : baseEnd_7651388 < baseStart_7651388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651405 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7651405 : Nat := 118140960795 + 7651405 * 2 ^ 59
def prefixEnd_7651405 : Nat := 4983230072969 + 3 ^ 40 * 7651405 * 2
def baseEnd_7651405 : Nat := 3928848447214741576449335

theorem tailTrace_7651405 : CollatzResearch.WordTrace tailWord_7651405 prefixEnd_7651405 3928848447214741576449335 := by
  unfold tailWord_7651405
  simp only [CollatzResearch.WordTrace]
  refine ⟨279069666845273915782955669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186046444563515943855303779 279069666845273915782955669)
  ·
    refine ⟨13081390633372214802326047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279069666845273915782955669 13081390633372214802326047)
    ·
      refine ⟨19622085950058322203489071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081390633372214802326047 19622085950058322203489071)
      ·
        refine ⟨29433128925087483305233607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19622085950058322203489071 29433128925087483305233607)
        ·
          refine ⟨44149693387631224957850411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29433128925087483305233607 44149693387631224957850411)
          ·
            refine ⟨66224540081446837436775617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44149693387631224957850411 66224540081446837436775617)
            ·
              refine ⟨49668405061085128077581713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66224540081446837436775617 49668405061085128077581713)
              ·
                refine ⟨37251303795813846058186285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49668405061085128077581713 37251303795813846058186285)
                ·
                  refine ⟨13969238923430192271819857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37251303795813846058186285 13969238923430192271819857)
                  ·
                    refine ⟨10476929192572644203864893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13969238923430192271819857 10476929192572644203864893)
                    ·
                      refine ⟨3928848447214741576449335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476929192572644203864893 3928848447214741576449335)
                      ·
                        rfl

theorem cell23_7651405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7651405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651405 prefixEnd_7651405 := by exact prefixLift 7651405
  have htrace : WordTrace (prefixWord ++ tailWord_7651405) baseStart_7651405 baseEnd_7651405 := by
    simpa [prefixWord, tailWord_7651405, baseEnd_7651405] using wordTrace_append hprefix tailTrace_7651405
  have hstable : (prefixWord ++ tailWord_7651405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651405).length < 2 ^ (prefixWord ++ tailWord_7651405).sum := by decide
  have hdescent : baseEnd_7651405 < baseStart_7651405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651418 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_7651418 : Nat := 118140960795 + 7651418 * 2 ^ 59
def prefixEnd_7651418 : Nat := 4983230072969 + 3 ^ 40 * 7651418 * 2
def baseEnd_7651418 : Nat := 3928855122463250025586775

theorem tailTrace_7651418 : CollatzResearch.WordTrace tailWord_7651418 prefixEnd_7651418 3928855122463250025586775 := by
  unfold tailWord_7651418
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767535248556704750794727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186046760662817879335452605 69767535248556704750794727)
  ·
    refine ⟨104651302872835057126192091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69767535248556704750794727 104651302872835057126192091)
    ·
      refine ⟨156976954309252585689288137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104651302872835057126192091 156976954309252585689288137)
      ·
        refine ⟨117732715731939439266966103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156976954309252585689288137 117732715731939439266966103)
        ·
          refine ⟨176599073597909158900449155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117732715731939439266966103 176599073597909158900449155)
          ·
            refine ⟨264898610396863738350673733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176599073597909158900449155 264898610396863738350673733)
            ·
              refine ⟨49668489449411950940751325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264898610396863738350673733 49668489449411950940751325)
              ·
                refine ⟨18625683543529481602781747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49668489449411950940751325 18625683543529481602781747)
                ·
                  refine ⟨27938525315294222404172621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18625683543529481602781747 27938525315294222404172621)
                  ·
                    refine ⟨10476946993235333401564733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27938525315294222404172621 10476946993235333401564733)
                    ·
                      refine ⟨3928855122463250025586775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476946993235333401564733 3928855122463250025586775)
                      ·
                        rfl

theorem cell23_7651418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_7651418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651418 prefixEnd_7651418 := by exact prefixLift 7651418
  have htrace : WordTrace (prefixWord ++ tailWord_7651418) baseStart_7651418 baseEnd_7651418 := by
    simpa [prefixWord, tailWord_7651418, baseEnd_7651418] using wordTrace_append hprefix tailTrace_7651418
  have hstable : (prefixWord ++ tailWord_7651418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651418).length < 2 ^ (prefixWord ++ tailWord_7651418).sum := by decide
  have hdescent : baseEnd_7651418 < baseStart_7651418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651452 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_7651452 : Nat := 118140960795 + 7651452 * 2 ^ 59
def prefixEnd_7651452 : Nat := 4983230072969 + 3 ^ 40 * 7651452 * 2
def baseEnd_7651452 : Nat := 3928872580805502892561619

theorem tailTrace_7651452 : CollatzResearch.WordTrace tailWord_7651452 prefixEnd_7651452 3928872580805502892561619 := by
  unfold tailWord_7651452
  simp only [CollatzResearch.WordTrace]
  refine ⟨139535690538051821404958305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186047587384069095206611073 139535690538051821404958305)
  ·
    refine ⟨104651767903538866053718729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139535690538051821404958305 104651767903538866053718729)
    ·
      refine ⟨78488825927654149540289047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104651767903538866053718729 78488825927654149540289047)
      ·
        refine ⟨117733238891481224310433571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78488825927654149540289047 117733238891481224310433571)
        ·
          refine ⟨176599858337221836465650357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117733238891481224310433571 176599858337221836465650357)
          ·
            refine ⟨16556236719114547168654721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176599858337221836465650357 16556236719114547168654721)
            ·
              refine ⟨12417177539335910376491041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16556236719114547168654721 12417177539335910376491041)
              ·
                refine ⟨9312883154501932782368281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12417177539335910376491041 9312883154501932782368281)
                ·
                  refine ⟨6984662365876449586776211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9312883154501932782368281 6984662365876449586776211)
                  ·
                    refine ⟨10476993548814674380164317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6984662365876449586776211 10476993548814674380164317)
                    ·
                      refine ⟨3928872580805502892561619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10476993548814674380164317 3928872580805502892561619)
                      ·
                        rfl

theorem cell23_7651452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_7651452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651452 prefixEnd_7651452 := by exact prefixLift 7651452
  have htrace : WordTrace (prefixWord ++ tailWord_7651452) baseStart_7651452 baseEnd_7651452 := by
    simpa [prefixWord, tailWord_7651452, baseEnd_7651452] using wordTrace_append hprefix tailTrace_7651452
  have hstable : (prefixWord ++ tailWord_7651452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651452).length < 2 ^ (prefixWord ++ tailWord_7651452).sum := by decide
  have hdescent : baseEnd_7651452 < baseStart_7651452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651475 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 6, 2, 2]
def baseStart_7651475 : Nat := 118140960795 + 7651475 * 2 ^ 59
def prefixEnd_7651475 : Nat := 4983230072969 + 3 ^ 40 * 7651475 * 2
def baseEnd_7651475 : Nat := 3928884390860556302574013

theorem tailTrace_7651475 : CollatzResearch.WordTrace tailWord_7651475 prefixEnd_7651475 3928884390860556302574013 := by
  unfold tailWord_7651475
  simp only [CollatzResearch.WordTrace]
  refine ⟨279072219955020317738003879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186048146636680211825335919 279072219955020317738003879)
  ·
    refine ⟨418608329932530476607005819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279072219955020317738003879 418608329932530476607005819)
    ·
      refine ⟨627912494898795714910508729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418608329932530476607005819 627912494898795714910508729)
      ·
        refine ⟨470934371174096786182881547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627912494898795714910508729 470934371174096786182881547)
        ·
          refine ⟨706401556761145179274322321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470934371174096786182881547 706401556761145179274322321)
          ·
            refine ⟨529801167570858884455741741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706401556761145179274322321 529801167570858884455741741)
            ·
              refine ⟨198675437839072081670903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529801167570858884455741741 198675437839072081670903153)
              ·
                refine ⟨149006578379304061253177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198675437839072081670903153 149006578379304061253177365)
                ·
                  refine ⟨6984683361529877871242689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149006578379304061253177365 6984683361529877871242689)
                  ·
                    refine ⟨5238512521147408403432017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984683361529877871242689 5238512521147408403432017)
                    ·
                      refine ⟨3928884390860556302574013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238512521147408403432017 3928884390860556302574013)
                      ·
                        rfl

theorem cell23_7651475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2, 2].length) (baseStart_7651475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651475 prefixEnd_7651475 := by exact prefixLift 7651475
  have htrace : WordTrace (prefixWord ++ tailWord_7651475) baseStart_7651475 baseEnd_7651475 := by
    simpa [prefixWord, tailWord_7651475, baseEnd_7651475] using wordTrace_append hprefix tailTrace_7651475
  have hstable : (prefixWord ++ tailWord_7651475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651475).length < 2 ^ (prefixWord ++ tailWord_7651475).sum := by decide
  have hdescent : baseEnd_7651475 < baseStart_7651475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651491 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7651491 : Nat := 118140960795 + 7651491 * 2 ^ 59
def prefixEnd_7651491 : Nat := 4983230072969 + 3 ^ 40 * 7651491 * 2
def baseEnd_7651491 : Nat := 3928892606551028239973939

theorem tailTrace_7651491 : CollatzResearch.WordTrace tailWord_7651491 prefixEnd_7651491 3928892606551028239973939 := by
  unfold tailWord_7651491
  simp only [CollatzResearch.WordTrace]
  refine ⟨279072803522962352470586327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186048535681974901647057551 279072803522962352470586327)
  ·
    refine ⟨418609205284443528705879491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279072803522962352470586327 418609205284443528705879491)
    ·
      refine ⟨627913807926665293058819237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418609205284443528705879491 627913807926665293058819237)
      ·
        refine ⟨117733838986249742448528607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627913807926665293058819237 117733838986249742448528607)
        ·
          refine ⟨176600758479374613672792911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117733838986249742448528607 176600758479374613672792911)
          ·
            refine ⟨264901137719061920509189367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176600758479374613672792911 264901137719061920509189367)
            ·
              refine ⟨397351706578592880763784051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264901137719061920509189367 397351706578592880763784051)
              ·
                refine ⟨596027559867889321145676077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397351706578592880763784051 596027559867889321145676077)
                ·
                  refine ⟨223510334950458495429628529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596027559867889321145676077 223510334950458495429628529)
                  ·
                    refine ⟨167632751212843871572221397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223510334950458495429628529 167632751212843871572221397)
                    ·
                      refine ⟨3928892606551028239973939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167632751212843871572221397 3928892606551028239973939)
                      ·
                        rfl

theorem cell23_7651491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7651491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651491 prefixEnd_7651491 := by exact prefixLift 7651491
  have htrace : WordTrace (prefixWord ++ tailWord_7651491) baseStart_7651491 baseEnd_7651491 := by
    simpa [prefixWord, tailWord_7651491, baseEnd_7651491] using wordTrace_append hprefix tailTrace_7651491
  have hstable : (prefixWord ++ tailWord_7651491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651491).length < 2 ^ (prefixWord ++ tailWord_7651491).sum := by decide
  have hdescent : baseEnd_7651491 < baseStart_7651491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651549 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 5]
def baseStart_7651549 : Nat := 118140960795 + 7651549 * 2 ^ 59
def prefixEnd_7651549 : Nat := 4983230072969 + 3 ^ 40 * 7651549 * 2
def baseEnd_7651549 : Nat := 436546932047665445894297

theorem tailTrace_7651549 : CollatzResearch.WordTrace tailWord_7651549 prefixEnd_7651549 436546932047665445894297 := by
  unfold tailWord_7651549
  simp only [CollatzResearch.WordTrace]
  refine ⟨279074918956752228376197701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186049945971168152250798467 279074918956752228376197701)
  ·
    refine ⟨52326547304391042820537069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279074918956752228376197701 52326547304391042820537069)
    ·
      refine ⟨19622455239146641057701401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52326547304391042820537069 19622455239146641057701401)
      ·
        refine ⟨14716841429359980793276051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19622455239146641057701401 14716841429359980793276051)
        ·
          refine ⟨22075262144039971189914077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716841429359980793276051 22075262144039971189914077)
          ·
            refine ⟨8278223304014989196217779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22075262144039971189914077 8278223304014989196217779)
            ·
              refine ⟨12417334956022483794326669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278223304014989196217779 12417334956022483794326669)
              ·
                refine ⟨4656500608508431422872501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12417334956022483794326669 4656500608508431422872501)
                ·
                  refine ⟨436546932047665445894297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4656500608508431422872501 436546932047665445894297)
                  ·
                    rfl

theorem cell23_7651549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_7651549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651549 prefixEnd_7651549 := by exact prefixLift 7651549
  have htrace : WordTrace (prefixWord ++ tailWord_7651549) baseStart_7651549 baseEnd_7651549 := by
    simpa [prefixWord, tailWord_7651549, baseEnd_7651549] using wordTrace_append hprefix tailTrace_7651549
  have hstable : (prefixWord ++ tailWord_7651549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651549).length < 2 ^ (prefixWord ++ tailWord_7651549).sum := by decide
  have hdescent : baseEnd_7651549 < baseStart_7651549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651582 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7651582 : Nat := 118140960795 + 7651582 * 2 ^ 59
def prefixEnd_7651582 : Nat := 4983230072969 + 3 ^ 40 * 7651582 * 2
def baseEnd_7651582 : Nat := 3928939333290587383936021

theorem tailTrace_7651582 : CollatzResearch.WordTrace tailWord_7651582 prefixEnd_7651582 3928939333290587383936021 := by
  unfold tailWord_7651582
  simp only [CollatzResearch.WordTrace]
  refine ⟨34884515320704084376518625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186050748377088450008099333 34884515320704084376518625)
  ·
    refine ⟨26163386490528063282388969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34884515320704084376518625 26163386490528063282388969)
    ·
      refine ⟨19622539867896047461791727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26163386490528063282388969 19622539867896047461791727)
      ·
        refine ⟨29433809801844071192687591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19622539867896047461791727 29433809801844071192687591)
        ·
          refine ⟨44150714702766106789031387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29433809801844071192687591 44150714702766106789031387)
          ·
            refine ⟨66226072054149160183547081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44150714702766106789031387 66226072054149160183547081)
            ·
              refine ⟨49669554040611870137660311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66226072054149160183547081 49669554040611870137660311)
              ·
                refine ⟨74504331060917805206490467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49669554040611870137660311 74504331060917805206490467)
                ·
                  refine ⟨111756496591376707809735701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74504331060917805206490467 111756496591376707809735701)
                  ·
                    refine ⟨5238585777720783178581361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111756496591376707809735701 5238585777720783178581361)
                    ·
                      refine ⟨3928939333290587383936021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238585777720783178581361 3928939333290587383936021)
                      ·
                        rfl

theorem cell23_7651582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7651582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651582 prefixEnd_7651582 := by exact prefixLift 7651582
  have htrace : WordTrace (prefixWord ++ tailWord_7651582) baseStart_7651582 baseEnd_7651582 := by
    simpa [prefixWord, tailWord_7651582, baseEnd_7651582] using wordTrace_append hprefix tailTrace_7651582
  have hstable : (prefixWord ++ tailWord_7651582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651582).length < 2 ^ (prefixWord ++ tailWord_7651582).sum := by decide
  have hdescent : baseEnd_7651582 < baseStart_7651582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651585 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_7651585 : Nat := 118140960795 + 7651585 * 2 ^ 59
def prefixEnd_7651585 : Nat := 4983230072969 + 3 ^ 40 * 7651585 * 2
def baseEnd_7651585 : Nat := 3928940873732550872198507

theorem tailTrace_7651585 : CollatzResearch.WordTrace tailWord_7651585 prefixEnd_7651585 3928940873732550872198507 := by
  unfold tailWord_7651585
  simp only [CollatzResearch.WordTrace]
  refine ⟨279076231984621806524508209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186050821323081204349672139 279076231984621806524508209)
  ·
    refine ⟨209307173988466354893381157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279076231984621806524508209 209307173988466354893381157)
    ·
      refine ⟨39245095122837441542508967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209307173988466354893381157 39245095122837441542508967)
      ·
        refine ⟨58867642684256162313763451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39245095122837441542508967 58867642684256162313763451)
        ·
          refine ⟨88301464026384243470645177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58867642684256162313763451 88301464026384243470645177)
          ·
            refine ⟨66226098019788182602983883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88301464026384243470645177 66226098019788182602983883)
            ·
              refine ⟨99339147029682273904475825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66226098019788182602983883 99339147029682273904475825)
              ·
                refine ⟨74504360272261705428356869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99339147029682273904475825 74504360272261705428356869)
                ·
                  refine ⟨13969567551049069767816913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74504360272261705428356869 13969567551049069767816913)
                  ·
                    refine ⟨10477175663286802325862685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13969567551049069767816913 10477175663286802325862685)
                    ·
                      refine ⟨3928940873732550872198507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477175663286802325862685 3928940873732550872198507)
                      ·
                        rfl

theorem cell23_7651585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_7651585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651585 prefixEnd_7651585 := by exact prefixLift 7651585
  have htrace : WordTrace (prefixWord ++ tailWord_7651585) baseStart_7651585 baseEnd_7651585 := by
    simpa [prefixWord, tailWord_7651585, baseEnd_7651585] using wordTrace_append hprefix tailTrace_7651585
  have hstable : (prefixWord ++ tailWord_7651585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651585).length < 2 ^ (prefixWord ++ tailWord_7651585).sum := by decide
  have hdescent : baseEnd_7651585 < baseStart_7651585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651626 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_7651626 : Nat := 118140960795 + 7651626 * 2 ^ 59
def prefixEnd_7651626 : Nat := 4983230072969 + 3 ^ 40 * 7651626 * 2
def baseEnd_7651626 : Nat := 1309653975479795070595273

theorem tailTrace_7651626 : CollatzResearch.WordTrace tailWord_7651626 prefixEnd_7651626 1309653975479795070595273 := by
  unfold tailWord_7651626
  simp only [CollatzResearch.WordTrace]
  refine ⟨69769431844368317631687683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186051818251648847017833821 69769431844368317631687683)
  ·
    refine ⟨104654147766552476447531525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69769431844368317631687683 104654147766552476447531525)
    ·
      refine ⟨19622652706228589333912161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104654147766552476447531525 19622652706228589333912161)
      ·
        refine ⟨14716989529671442000434121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19622652706228589333912161 14716989529671442000434121)
        ·
          refine ⟨11037742147253581500325591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14716989529671442000434121 11037742147253581500325591)
          ·
            refine ⟨16556613220880372250488387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037742147253581500325591 16556613220880372250488387)
            ·
              refine ⟨24834919831320558375732581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16556613220880372250488387 24834919831320558375732581)
              ·
                refine ⟨4656547468372604695449859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24834919831320558375732581 4656547468372604695449859)
                ·
                  refine ⟨6984821202558907043174789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656547468372604695449859 6984821202558907043174789)
                  ·
                    refine ⟨1309653975479795070595273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6984821202558907043174789 1309653975479795070595273)
                    ·
                      rfl

theorem cell23_7651626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_7651626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651626 prefixEnd_7651626 := by exact prefixLift 7651626
  have htrace : WordTrace (prefixWord ++ tailWord_7651626) baseStart_7651626 baseEnd_7651626 := by
    simpa [prefixWord, tailWord_7651626, baseEnd_7651626] using wordTrace_append hprefix tailTrace_7651626
  have hstable : (prefixWord ++ tailWord_7651626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651626).length < 2 ^ (prefixWord ++ tailWord_7651626).sum := by decide
  have hdescent : baseEnd_7651626 < baseStart_7651626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651655 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_7651655 : Nat := 118140960795 + 7651655 * 2 ^ 59
def prefixEnd_7651655 : Nat := 4983230072969 + 3 ^ 40 * 7651655 * 2
def baseEnd_7651655 : Nat := 3928976817378365598323185

theorem tailTrace_7651655 : CollatzResearch.WordTrace tailWord_7651655 prefixEnd_7651655 3928976817378365598323185 := by
  unfold tailWord_7651655
  simp only [CollatzResearch.WordTrace]
  refine ⟨279078785094368208479556419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186052523396245472319704279 279078785094368208479556419)
  ·
    refine ⟨418618177641552312719334629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279078785094368208479556419 418618177641552312719334629)
    ·
      refine ⟨78490908307791058634875243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418618177641552312719334629 78490908307791058634875243)
      ·
        refine ⟨117736362461686587952312865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78490908307791058634875243 117736362461686587952312865)
        ·
          refine ⟨88302271846264940964234649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117736362461686587952312865 88302271846264940964234649)
          ·
            refine ⟨66226703884698705723175987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88302271846264940964234649 66226703884698705723175987)
            ·
              refine ⟨99340055827048058584763981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66226703884698705723175987 99340055827048058584763981)
              ·
                refine ⟨37252520935143021969286493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99340055827048058584763981 37252520935143021969286493)
                ·
                  refine ⟨13969695350678633238482435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37252520935143021969286493 13969695350678633238482435)
                  ·
                    refine ⟨20954543026017949857723653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13969695350678633238482435 20954543026017949857723653)
                    ·
                      refine ⟨3928976817378365598323185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20954543026017949857723653 3928976817378365598323185)
                      ·
                        rfl

theorem cell23_7651655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_7651655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651655 prefixEnd_7651655 := by exact prefixLift 7651655
  have htrace : WordTrace (prefixWord ++ tailWord_7651655) baseStart_7651655 baseEnd_7651655 := by
    simpa [prefixWord, tailWord_7651655, baseEnd_7651655] using wordTrace_append hprefix tailTrace_7651655
  have hstable : (prefixWord ++ tailWord_7651655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651655).length < 2 ^ (prefixWord ++ tailWord_7651655).sum := by decide
  have hdescent : baseEnd_7651655 < baseStart_7651655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651665 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_7651665 : Nat := 118140960795 + 7651665 * 2 ^ 59
def prefixEnd_7651665 : Nat := 4983230072969 + 3 ^ 40 * 7651665 * 2
def baseEnd_7651665 : Nat := 1309660650728303519732713

theorem tailTrace_7651665 : CollatzResearch.WordTrace tailWord_7651665 prefixEnd_7651665 1309660650728303519732713 := by
  unfold tailWord_7651665
  simp only [CollatzResearch.WordTrace]
  refine ⟨279079149824331980187420449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186052766549554653458280299 279079149824331980187420449)
  ·
    refine ⟨209309362368248985140565337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279079149824331980187420449 209309362368248985140565337)
    ·
      refine ⟨156982021776186738855424003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209309362368248985140565337 156982021776186738855424003)
      ·
        refine ⟨235473032664280108283136005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156982021776186738855424003 235473032664280108283136005)
        ·
          refine ⟨44151193624552520303088001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235473032664280108283136005 44151193624552520303088001)
          ·
            refine ⟨33113395218414390227316001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44151193624552520303088001 33113395218414390227316001)
            ·
              refine ⟨24835046413810792670487001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33113395218414390227316001 24835046413810792670487001)
              ·
                refine ⟨18626284810358094502865251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24835046413810792670487001 18626284810358094502865251)
                ·
                  refine ⟨27939427215537141754297877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18626284810358094502865251 27939427215537141754297877)
                  ·
                    refine ⟨1309660650728303519732713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27939427215537141754297877 1309660650728303519732713)
                    ·
                      rfl

theorem cell23_7651665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_7651665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651665 prefixEnd_7651665 := by exact prefixLift 7651665
  have htrace : WordTrace (prefixWord ++ tailWord_7651665) baseStart_7651665 baseEnd_7651665 := by
    simpa [prefixWord, tailWord_7651665, baseEnd_7651665] using wordTrace_append hprefix tailTrace_7651665
  have hstable : (prefixWord ++ tailWord_7651665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651665).length < 2 ^ (prefixWord ++ tailWord_7651665).sum := by decide
  have hdescent : baseEnd_7651665 < baseStart_7651665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651689 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 3, 2, 2]
def baseStart_7651689 : Nat := 118140960795 + 7651689 * 2 ^ 59
def prefixEnd_7651689 : Nat := 4983230072969 + 3 ^ 40 * 7651689 * 2
def baseEnd_7651689 : Nat := 3928994275720618465298029

theorem tailTrace_7651689 : CollatzResearch.WordTrace tailWord_7651689 prefixEnd_7651689 3928994275720618465298029 := by
  unfold tailWord_7651689
  simp only [CollatzResearch.WordTrace]
  refine ⟨279080025176245032286294121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186053350117496688190862747 279080025176245032286294121)
  ·
    refine ⟨209310018882183774214720591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279080025176245032286294121 209310018882183774214720591)
    ·
      refine ⟨313965028323275661322080887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209310018882183774214720591 313965028323275661322080887)
      ·
        refine ⟨470947542484913491983121331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313965028323275661322080887 470947542484913491983121331)
        ·
          refine ⟨706421313727370237974681997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470947542484913491983121331 706421313727370237974681997)
          ·
            refine ⟨264907992647763839240505749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706421313727370237974681997 264907992647763839240505749)
            ·
              refine ⟨12417562155363929964398707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 264907992647763839240505749 12417562155363929964398707)
              ·
                refine ⟨18626343233045894946598061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12417562155363929964398707 18626343233045894946598061)
                ·
                  refine ⟨6984878712392210604974273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18626343233045894946598061 6984878712392210604974273)
                  ·
                    refine ⟨5238659034294157953730705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984878712392210604974273 5238659034294157953730705)
                    ·
                      refine ⟨3928994275720618465298029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238659034294157953730705 3928994275720618465298029)
                      ·
                        rfl

theorem cell23_7651689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2, 2].length) (baseStart_7651689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651689 prefixEnd_7651689 := by exact prefixLift 7651689
  have htrace : WordTrace (prefixWord ++ tailWord_7651689) baseStart_7651689 baseEnd_7651689 := by
    simpa [prefixWord, tailWord_7651689, baseEnd_7651689] using wordTrace_append hprefix tailTrace_7651689
  have hstable : (prefixWord ++ tailWord_7651689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651689).length < 2 ^ (prefixWord ++ tailWord_7651689).sum := by decide
  have hdescent : baseEnd_7651689 < baseStart_7651689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651692 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_7651692 : Nat := 118140960795 + 7651692 * 2 ^ 59
def prefixEnd_7651692 : Nat := 4983230072969 + 3 ^ 40 * 7651692 * 2
def baseEnd_7651692 : Nat := 3928995816162581953560515

theorem tailTrace_7651692 : CollatzResearch.WordTrace tailWord_7651692 prefixEnd_7651692 3928995816162581953560515 := by
  unfold tailWord_7651692
  simp only [CollatzResearch.WordTrace]
  refine ⟨139540067297617081899326665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186053423063489442532435553 139540067297617081899326665)
  ·
    refine ⟨104655050473212811424494999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139540067297617081899326665 104655050473212811424494999)
    ·
      refine ⟨156982575709819217136742499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104655050473212811424494999 156982575709819217136742499)
      ·
        refine ⟨235473863564728825705113749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156982575709819217136742499 235473863564728825705113749)
        ·
          refine ⟨11037837354596663704927207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235473863564728825705113749 11037837354596663704927207)
          ·
            refine ⟨16556756031894995557390811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037837354596663704927207 16556756031894995557390811)
            ·
              refine ⟨24835134047842493336086217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16556756031894995557390811 24835134047842493336086217)
              ·
                refine ⟨18626350535881870002064663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24835134047842493336086217 18626350535881870002064663)
                ·
                  refine ⟨27939525803822805003096995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18626350535881870002064663 27939525803822805003096995)
                  ·
                    refine ⟨41909288705734207504645493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27939525803822805003096995 41909288705734207504645493)
                    ·
                      refine ⟨3928995816162581953560515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41909288705734207504645493 3928995816162581953560515)
                      ·
                        rfl

theorem cell23_7651692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_7651692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651692 prefixEnd_7651692 := by exact prefixLift 7651692
  have htrace : WordTrace (prefixWord ++ tailWord_7651692) baseStart_7651692 baseEnd_7651692 := by
    simpa [prefixWord, tailWord_7651692, baseEnd_7651692] using wordTrace_append hprefix tailTrace_7651692
  have hstable : (prefixWord ++ tailWord_7651692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651692).length < 2 ^ (prefixWord ++ tailWord_7651692).sum := by decide
  have hdescent : baseEnd_7651692 < baseStart_7651692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651709 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_7651709 : Nat := 118140960795 + 7651709 * 2 ^ 59
def prefixEnd_7651709 : Nat := 4983230072969 + 3 ^ 40 * 7651709 * 2
def baseEnd_7651709 : Nat := 3929004545333708387047937

theorem tailTrace_7651709 : CollatzResearch.WordTrace tailWord_7651709 prefixEnd_7651709 3929004545333708387047937 := by
  unfold tailWord_7651709
  simp only [CollatzResearch.WordTrace]
  refine ⟨279080754636172575702022181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186053836424115050468014787 279080754636172575702022181)
  ·
    refine ⟨52327641494282357944129159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 279080754636172575702022181 52327641494282357944129159)
    ·
      refine ⟨78491462241423536916193739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52327641494282357944129159 78491462241423536916193739)
      ·
        refine ⟨117737193362135305374290609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78491462241423536916193739 117737193362135305374290609)
        ·
          refine ⟨88302895021601479030717957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117737193362135305374290609 88302895021601479030717957)
          ·
            refine ⟨16556792816550277318259617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88302895021601479030717957 16556792816550277318259617)
            ·
              refine ⟨12417594612412707988694713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16556792816550277318259617 12417594612412707988694713)
              ·
                refine ⟨9313195959309530991521035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12417594612412707988694713 9313195959309530991521035)
                ·
                  refine ⟨13969793938964296487281553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313195959309530991521035 13969793938964296487281553)
                  ·
                    refine ⟨10477345454223222365461165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13969793938964296487281553 10477345454223222365461165)
                    ·
                      refine ⟨3929004545333708387047937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477345454223222365461165 3929004545333708387047937)
                      ·
                        rfl

theorem cell23_7651709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_7651709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651709 prefixEnd_7651709 := by exact prefixLift 7651709
  have htrace : WordTrace (prefixWord ++ tailWord_7651709) baseStart_7651709 baseEnd_7651709 := by
    simpa [prefixWord, tailWord_7651709, baseEnd_7651709] using wordTrace_append hprefix tailTrace_7651709
  have hstable : (prefixWord ++ tailWord_7651709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651709).length < 2 ^ (prefixWord ++ tailWord_7651709).sum := by decide
  have hdescent : baseEnd_7651709 < baseStart_7651709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651723 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 1, 2, 2]
def baseStart_7651723 : Nat := 118140960795 + 7651723 * 2 ^ 59
def prefixEnd_7651723 : Nat := 4983230072969 + 3 ^ 40 * 7651723 * 2
def baseEnd_7651723 : Nat := 3929011734062871332272873

theorem tailTrace_7651723 : CollatzResearch.WordTrace tailWord_7651723 prefixEnd_7651723 3929011734062871332272873 := by
  unfold tailWord_7651723
  simp only [CollatzResearch.WordTrace]
  refine ⟨279081265258121856093031823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186054176838747904062021215 279081265258121856093031823)
  ·
    refine ⟨418621897887182784139547735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279081265258121856093031823 418621897887182784139547735)
    ·
      refine ⟨627932846830774176209321603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418621897887182784139547735 627932846830774176209321603)
      ·
        refine ⟨941899270246161264313982405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627932846830774176209321603 941899270246161264313982405)
        ·
          refine ⟨176606113171155237058871701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 941899270246161264313982405 176606113171155237058871701)
          ·
            refine ⟨8278411554897901737134611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176606113171155237058871701 8278411554897901737134611)
            ·
              refine ⟨12417617332346852605701917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278411554897901737134611 12417617332346852605701917)
              ·
                refine ⟨4656606499630069727138219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12417617332346852605701917 4656606499630069727138219)
                ·
                  refine ⟨6984909749445104590707329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656606499630069727138219 6984909749445104590707329)
                  ·
                    refine ⟨5238682312083828443030497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6984909749445104590707329 5238682312083828443030497)
                    ·
                      refine ⟨3929011734062871332272873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238682312083828443030497 3929011734062871332272873)
                      ·
                        rfl

theorem cell23_7651723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 2, 2].length) (baseStart_7651723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651723 prefixEnd_7651723 := by exact prefixLift 7651723
  have htrace : WordTrace (prefixWord ++ tailWord_7651723) baseStart_7651723 baseEnd_7651723 := by
    simpa [prefixWord, tailWord_7651723, baseEnd_7651723] using wordTrace_append hprefix tailTrace_7651723
  have hstable : (prefixWord ++ tailWord_7651723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651723).length < 2 ^ (prefixWord ++ tailWord_7651723).sum := by decide
  have hdescent : baseEnd_7651723 < baseStart_7651723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651734 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7651734 : Nat := 118140960795 + 7651734 * 2 ^ 59
def prefixEnd_7651734 : Nat := 4983230072969 + 3 ^ 40 * 7651734 * 2
def baseEnd_7651734 : Nat := 3929017382350070789235323

theorem tailTrace_7651734 : CollatzResearch.WordTrace tailWord_7651734 prefixEnd_7651734 3929017382350070789235323 := by
  unfold tailWord_7651734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442604153817625310730141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186054444307388003314454837 17442604153817625310730141)
  ·
    refine ⟨6540976557681609491523803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17442604153817625310730141 6540976557681609491523803)
    ·
      refine ⟨9811464836522414237285705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6540976557681609491523803 9811464836522414237285705)
      ·
        refine ⟨7358598627391810677964279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9811464836522414237285705 7358598627391810677964279)
        ·
          refine ⟨11037897941087716016946419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358598627391810677964279 11037897941087716016946419)
          ·
            refine ⟨16556846911631574025419629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037897941087716016946419 16556846911631574025419629)
            ·
              refine ⟨6208817591861840259532361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16556846911631574025419629 6208817591861840259532361)
              ·
                refine ⟨4656613193896380194649271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208817591861840259532361 4656613193896380194649271)
                ·
                  refine ⟨6984919790844570291973907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656613193896380194649271 6984919790844570291973907)
                  ·
                    refine ⟨10477379686266855437960861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6984919790844570291973907 10477379686266855437960861)
                    ·
                      refine ⟨3929017382350070789235323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477379686266855437960861 3929017382350070789235323)
                      ·
                        rfl

theorem cell23_7651734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7651734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651734 prefixEnd_7651734 := by exact prefixLift 7651734
  have htrace : WordTrace (prefixWord ++ tailWord_7651734) baseStart_7651734 baseEnd_7651734 := by
    simpa [prefixWord, tailWord_7651734, baseEnd_7651734] using wordTrace_append hprefix tailTrace_7651734
  have hstable : (prefixWord ++ tailWord_7651734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651734).length < 2 ^ (prefixWord ++ tailWord_7651734).sum := by decide
  have hdescent : baseEnd_7651734 < baseStart_7651734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651775 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_7651775 : Nat := 118140960795 + 7651775 * 2 ^ 59
def prefixEnd_7651775 : Nat := 4983230072969 + 3 ^ 40 * 7651775 * 2
def baseEnd_7651775 : Nat := 3929038435056905128822633

theorem tailTrace_7651775 : CollatzResearch.WordTrace tailWord_7651775 prefixEnd_7651775 3929038435056905128822633 := by
  unfold tailWord_7651775
  simp only [CollatzResearch.WordTrace]
  refine ⟨279083161853933468973924779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186055441235955645982616519 279083161853933468973924779)
  ·
    refine ⟨418624742780900203460887169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279083161853933468973924779 418624742780900203460887169)
    ·
      refine ⟨313968557085675152595665377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418624742780900203460887169 313968557085675152595665377)
      ·
        refine ⟨235476417814256364446749033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313968557085675152595665377 235476417814256364446749033)
        ·
          refine ⟨176607313360692273335061775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235476417814256364446749033 176607313360692273335061775)
          ·
            refine ⟨264910970041038410002592663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176607313360692273335061775 264910970041038410002592663)
            ·
              refine ⟨397366455061557615003888995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264910970041038410002592663 397366455061557615003888995)
              ·
                refine ⟨596049682592336422505833493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397366455061557615003888995 596049682592336422505833493)
                ·
                  refine ⟨27939828871515769804960945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 596049682592336422505833493 27939828871515769804960945)
                  ·
                    refine ⟨20954871653636827353720709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27939828871515769804960945 20954871653636827353720709)
                    ·
                      refine ⟨3929038435056905128822633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20954871653636827353720709 3929038435056905128822633)
                      ·
                        rfl

theorem cell23_7651775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_7651775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651775 prefixEnd_7651775 := by exact prefixLift 7651775
  have htrace : WordTrace (prefixWord ++ tailWord_7651775) baseStart_7651775 baseEnd_7651775 := by
    simpa [prefixWord, tailWord_7651775, baseEnd_7651775] using wordTrace_append hprefix tailTrace_7651775
  have hstable : (prefixWord ++ tailWord_7651775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651775).length < 2 ^ (prefixWord ++ tailWord_7651775).sum := by decide
  have hdescent : baseEnd_7651775 < baseStart_7651775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651853 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7651853 : Nat := 118140960795 + 7651853 * 2 ^ 59
def prefixEnd_7651853 : Nat := 4983230072969 + 3 ^ 40 * 7651853 * 2
def baseEnd_7651853 : Nat := 436564276283106202627475

theorem tailTrace_7651853 : CollatzResearch.WordTrace tailWord_7651853 prefixEnd_7651853 436564276283106202627475 := by
  unfold tailWord_7651853
  simp only [CollatzResearch.WordTrace]
  refine ⟨279086006747650888295264213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186057337831767258863509475 279086006747650888295264213)
  ·
    refine ⟨6541078283148067694420255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 279086006747650888295264213 6541078283148067694420255)
    ·
      refine ⟨9811617424722101541630383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6541078283148067694420255 9811617424722101541630383)
      ·
        refine ⟨14717426137083152312445575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811617424722101541630383 14717426137083152312445575)
        ·
          refine ⟨22076139205624728468668363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717426137083152312445575 22076139205624728468668363)
          ·
            refine ⟨33114208808437092703002545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076139205624728468668363 33114208808437092703002545)
            ·
              refine ⟨24835656606327819527251909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33114208808437092703002545 24835656606327819527251909)
              ·
                refine ⟨4656685613686466161359733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24835656606327819527251909 4656685613686466161359733)
                ·
                  refine ⟨436564276283106202627475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4656685613686466161359733 436564276283106202627475)
                  ·
                    rfl

theorem cell23_7651853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7651853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651853 prefixEnd_7651853 := by exact prefixLift 7651853
  have htrace : WordTrace (prefixWord ++ tailWord_7651853) baseStart_7651853 baseEnd_7651853 := by
    simpa [prefixWord, tailWord_7651853, baseEnd_7651853] using wordTrace_append hprefix tailTrace_7651853
  have hstable : (prefixWord ++ tailWord_7651853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651853).length < 2 ^ (prefixWord ++ tailWord_7651853).sum := by decide
  have hdescent : baseEnd_7651853 < baseStart_7651853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651855 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_7651855 : Nat := 118140960795 + 7651855 * 2 ^ 59
def prefixEnd_7651855 : Nat := 4983230072969 + 3 ^ 40 * 7651855 * 2
def baseEnd_7651855 : Nat := 3929079513509264815822265

theorem tailTrace_7651855 : CollatzResearch.WordTrace tailWord_7651855 prefixEnd_7651855 3929079513509264815822265 := by
  unfold tailWord_7651855
  simp only [CollatzResearch.WordTrace]
  refine ⟨279086079693643642636837019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186057386462429095091224679 279086079693643642636837019)
  ·
    refine ⟨418629119540465463955255529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279086079693643642636837019 418629119540465463955255529)
    ·
      refine ⟨313971839655349097966441647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418629119540465463955255529 313971839655349097966441647)
      ·
        refine ⟨470957759483023646949662471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313971839655349097966441647 470957759483023646949662471)
        ·
          refine ⟨706436639224535470424493707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470957759483023646949662471 706436639224535470424493707)
          ·
            refine ⟨1059654958836803205636740561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706436639224535470424493707 1059654958836803205636740561)
            ·
              refine ⟨794741219127602404227555421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059654958836803205636740561 794741219127602404227555421)
              ·
                refine ⟨298027957172850901585333283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794741219127602404227555421 298027957172850901585333283)
                ·
                  refine ⟨447041935759276352377999925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298027957172850901585333283 447041935759276352377999925)
                  ·
                    refine ⟨41910181477432158035437493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 447041935759276352377999925 41910181477432158035437493)
                    ·
                      refine ⟨3929079513509264815822265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41910181477432158035437493 3929079513509264815822265)
                      ·
                        rfl

theorem cell23_7651855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_7651855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651855 prefixEnd_7651855 := by exact prefixLift 7651855
  have htrace : WordTrace (prefixWord ++ tailWord_7651855) baseStart_7651855 baseEnd_7651855 := by
    simpa [prefixWord, tailWord_7651855, baseEnd_7651855] using wordTrace_append hprefix tailTrace_7651855
  have hstable : (prefixWord ++ tailWord_7651855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651855).length < 2 ^ (prefixWord ++ tailWord_7651855).sum := by decide
  have hdescent : baseEnd_7651855 < baseStart_7651855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651959 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_7651959 : Nat := 118140960795 + 7651959 * 2 ^ 59
def prefixEnd_7651959 : Nat := 4983230072969 + 3 ^ 40 * 7651959 * 2
def baseEnd_7651959 : Nat := 3929132915497332408921787

theorem tailTrace_7651959 : CollatzResearch.WordTrace tailWord_7651959 prefixEnd_7651959 3929132915497332408921787 := by
  unfold tailWord_7651959
  simp only [CollatzResearch.WordTrace]
  refine ⟨279089872885266868398622931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186059915256844578932415287 279089872885266868398622931)
  ·
    refine ⟨418634809327900302597934397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279089872885266868398622931 418634809327900302597934397)
    ·
      refine ⟨156988053497962613474225399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418634809327900302597934397 156988053497962613474225399)
      ·
        refine ⟨235482080246943920211338099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156988053497962613474225399 235482080246943920211338099)
        ·
          refine ⟨353223120370415880317007149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235482080246943920211338099 353223120370415880317007149)
          ·
            refine ⟨132458670138905955118877681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353223120370415880317007149 132458670138905955118877681)
            ·
              refine ⟨99344002604179466339158261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132458670138905955118877681 99344002604179466339158261)
              ·
                refine ⟨9313500244141824969296087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99344002604179466339158261 9313500244141824969296087)
                ·
                  refine ⟨13970250366212737453944131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313500244141824969296087 13970250366212737453944131)
                  ·
                    refine ⟨20955375549319106180916197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13970250366212737453944131 20955375549319106180916197)
                    ·
                      refine ⟨3929132915497332408921787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20955375549319106180916197 3929132915497332408921787)
                      ·
                        rfl

theorem cell23_7651959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_7651959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651959 prefixEnd_7651959 := by exact prefixLift 7651959
  have htrace : WordTrace (prefixWord ++ tailWord_7651959) baseStart_7651959 baseEnd_7651959 := by
    simpa [prefixWord, tailWord_7651959, baseEnd_7651959] using wordTrace_append hprefix tailTrace_7651959
  have hstable : (prefixWord ++ tailWord_7651959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651959).length < 2 ^ (prefixWord ++ tailWord_7651959).sum := by decide
  have hdescent : baseEnd_7651959 < baseStart_7651959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651986 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_7651986 : Nat := 118140960795 + 7651986 * 2 ^ 59
def prefixEnd_7651986 : Nat := 4983230072969 + 3 ^ 40 * 7651986 * 2
def baseEnd_7651986 : Nat := 1309715593158334601094721

theorem tailTrace_7651986 : CollatzResearch.WordTrace tailWord_7651986 prefixEnd_7651986 1309715593158334601094721 := by
  unfold tailWord_7651986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69772714414042263002463953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186060571770779368006570541 69772714414042263002463953)
  ·
    refine ⟨52329535810531697251847965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69772714414042263002463953 52329535810531697251847965)
    ·
      refine ⟨19623575928949386469442987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52329535810531697251847965 19623575928949386469442987)
      ·
        refine ⟨29435363893424079704164481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623575928949386469442987 29435363893424079704164481)
        ·
          refine ⟨22076522920068059778123361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29435363893424079704164481 22076522920068059778123361)
          ·
            refine ⟨16557392190051044833592521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22076522920068059778123361 16557392190051044833592521)
            ·
              refine ⟨12418044142538283625194391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16557392190051044833592521 12418044142538283625194391)
              ·
                refine ⟨18627066213807425437791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418044142538283625194391 18627066213807425437791587)
                ·
                  refine ⟨27940599320711138156687381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18627066213807425437791587 27940599320711138156687381)
                  ·
                    refine ⟨1309715593158334601094721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27940599320711138156687381 1309715593158334601094721)
                    ·
                      rfl

theorem cell23_7651986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_7651986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651986 prefixEnd_7651986 := by exact prefixLift 7651986
  have htrace : WordTrace (prefixWord ++ tailWord_7651986) baseStart_7651986 baseEnd_7651986 := by
    simpa [prefixWord, tailWord_7651986, baseEnd_7651986] using wordTrace_append hprefix tailTrace_7651986
  have hstable : (prefixWord ++ tailWord_7651986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651986).length < 2 ^ (prefixWord ++ tailWord_7651986).sum := by decide
  have hdescent : baseEnd_7651986 < baseStart_7651986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7651996 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7651996 : Nat := 118140960795 + 7651996 * 2 ^ 59
def prefixEnd_7651996 : Nat := 4983230072969 + 3 ^ 40 * 7651996 * 2
def baseEnd_7651996 : Nat := 3929151914281548764159117

theorem tailTrace_7651996 : CollatzResearch.WordTrace tailWord_7651996 prefixEnd_7651996 3929151914281548764159117 := by
  unfold tailWord_7651996
  simp only [CollatzResearch.WordTrace]
  refine ⟨139545611193066411858859921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186060814924088549145146561 139545611193066411858859921)
  ·
    refine ⟨104659208394799808894144941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139545611193066411858859921 104659208394799808894144941)
    ·
      refine ⟨39247203148049928335304353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104659208394799808894144941 39247203148049928335304353)
      ·
        refine ⟨29435402361037446251478265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39247203148049928335304353 29435402361037446251478265)
        ·
          refine ⟨22076551770778084688608699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29435402361037446251478265 22076551770778084688608699)
          ·
            refine ⟨33114827656167127032913049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076551770778084688608699 33114827656167127032913049)
            ·
              refine ⟨24836120742125345274684787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33114827656167127032913049 24836120742125345274684787)
              ·
                refine ⟨37254181113188017912027181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24836120742125345274684787 37254181113188017912027181)
                ·
                  refine ⟨13970317917445506717010193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37254181113188017912027181 13970317917445506717010193)
                  ·
                    refine ⟨10477738438084130037757645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13970317917445506717010193 10477738438084130037757645)
                    ·
                      refine ⟨3929151914281548764159117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477738438084130037757645 3929151914281548764159117)
                      ·
                        rfl

theorem cell23_7651996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7651996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7651996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7651996 prefixEnd_7651996 := by exact prefixLift 7651996
  have htrace : WordTrace (prefixWord ++ tailWord_7651996) baseStart_7651996 baseEnd_7651996 := by
    simpa [prefixWord, tailWord_7651996, baseEnd_7651996] using wordTrace_append hprefix tailTrace_7651996
  have hstable : (prefixWord ++ tailWord_7651996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7651996).length < 2 ^ (prefixWord ++ tailWord_7651996).sum := by decide
  have hdescent : baseEnd_7651996 < baseStart_7651996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7651996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652007 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7652007 : Nat := 118140960795 + 7652007 * 2 ^ 59
def prefixEnd_7652007 : Nat := 4983230072969 + 3 ^ 40 * 7652007 * 2
def baseEnd_7652007 : Nat := 1309719187522916073707189

theorem tailTrace_7652007 : CollatzResearch.WordTrace tailWord_7652007 prefixEnd_7652007 1309719187522916073707189 := by
  unfold tailWord_7652007
  simp only [CollatzResearch.WordTrace]
  refine ⟨279091623589092972596370275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186061082392728648397580183 279091623589092972596370275)
  ·
    refine ⟨418637435383639458894555413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279091623589092972596370275 418637435383639458894555413)
    ·
      refine ⟨19623629783608099635682285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418637435383639458894555413 19623629783608099635682285)
      ·
        refine ⟨7358861168853037363380857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19623629783608099635682285 7358861168853037363380857)
        ·
          refine ⟨5519145876639778022535643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7358861168853037363380857 5519145876639778022535643)
          ·
            refine ⟨8278718814959667033803465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519145876639778022535643 8278718814959667033803465)
            ·
              refine ⟨6209039111219750275352599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278718814959667033803465 6209039111219750275352599)
              ·
                refine ⟨9313558666829625413028899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209039111219750275352599 9313558666829625413028899)
                ·
                  refine ⟨13970338000244438119543349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313558666829625413028899 13970338000244438119543349)
                  ·
                    refine ⟨1309719187522916073707189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13970338000244438119543349 1309719187522916073707189)
                    ·
                      rfl

theorem cell23_7652007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7652007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652007 prefixEnd_7652007 := by exact prefixLift 7652007
  have htrace : WordTrace (prefixWord ++ tailWord_7652007) baseStart_7652007 baseEnd_7652007 := by
    simpa [prefixWord, tailWord_7652007, baseEnd_7652007] using wordTrace_append hprefix tailTrace_7652007
  have hstable : (prefixWord ++ tailWord_7652007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652007).length < 2 ^ (prefixWord ++ tailWord_7652007).sum := by decide
  have hdescent : baseEnd_7652007 < baseStart_7652007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652010 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7652010 : Nat := 118140960795 + 7652010 * 2 ^ 59
def prefixEnd_7652010 : Nat := 4983230072969 + 3 ^ 40 * 7652010 * 2
def baseEnd_7652010 : Nat := 3929159103010711709384053

theorem tailTrace_7652010 : CollatzResearch.WordTrace tailWord_7652010 prefixEnd_7652010 3929159103010711709384053 := by
  unfold tailWord_7652010
  simp only [CollatzResearch.WordTrace]
  refine ⟨69772933252020526027182371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186061155338721402739152989 69772933252020526027182371)
  ·
    refine ⟨104659399878030789040773557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69772933252020526027182371 104659399878030789040773557)
    ·
      refine ⟨9811818738565386472572521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104659399878030789040773557 9811818738565386472572521)
      ·
        refine ⟨7358864053924039854429391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9811818738565386472572521 7358864053924039854429391)
        ·
          refine ⟨11038296080886059781644087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358864053924039854429391 11038296080886059781644087)
          ·
            refine ⟨16557444121329089672466131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038296080886059781644087 16557444121329089672466131)
            ·
              refine ⟨24836166181993634508699197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16557444121329089672466131 24836166181993634508699197)
              ·
                refine ⟨9313562318247612940762199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24836166181993634508699197 9313562318247612940762199)
                ·
                  refine ⟨13970343477371419411143299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313562318247612940762199 13970343477371419411143299)
                  ·
                    refine ⟨20955515216057129116714949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13970343477371419411143299 20955515216057129116714949)
                    ·
                      refine ⟨3929159103010711709384053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20955515216057129116714949 3929159103010711709384053)
                      ·
                        rfl

theorem cell23_7652010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7652010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652010 prefixEnd_7652010 := by exact prefixLift 7652010
  have htrace : WordTrace (prefixWord ++ tailWord_7652010) baseStart_7652010 baseEnd_7652010 := by
    simpa [prefixWord, tailWord_7652010, baseEnd_7652010] using wordTrace_append hprefix tailTrace_7652010
  have hstable : (prefixWord ++ tailWord_7652010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652010).length < 2 ^ (prefixWord ++ tailWord_7652010).sum := by decide
  have hdescent : baseEnd_7652010 < baseStart_7652010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652013 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_7652013 : Nat := 118140960795 + 7652013 * 2 ^ 59
def prefixEnd_7652013 : Nat := 4983230072969 + 3 ^ 40 * 7652013 * 2
def baseEnd_7652013 : Nat := 3929160643452675197646539

theorem tailTrace_7652013 : CollatzResearch.WordTrace tailWord_7652013 prefixEnd_7652013 3929160643452675197646539 := by
  unfold tailWord_7652013
  simp only [CollatzResearch.WordTrace]
  refine ⟨279091842427071235621088693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186061228284714157080725795 279091842427071235621088693)
  ·
    refine ⟨26164860227537928339477065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279091842427071235621088693 26164860227537928339477065)
    ·
      refine ⟨19623645170653446254607799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26164860227537928339477065 19623645170653446254607799)
      ·
        refine ⟨29435467755980169381911699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623645170653446254607799 29435467755980169381911699)
        ·
          refine ⟨44153201633970254072867549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435467755980169381911699 44153201633970254072867549)
          ·
            refine ⟨16557450612738845277325331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44153201633970254072867549 16557450612738845277325331)
            ·
              refine ⟨24836175919108267915987997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16557450612738845277325331 24836175919108267915987997)
              ·
                refine ⟨9313565969665600468495499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24836175919108267915987997 9313565969665600468495499)
                ·
                  refine ⟨13970348954498400702743249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313565969665600468495499 13970348954498400702743249)
                  ·
                    refine ⟨10477761715873800527057437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13970348954498400702743249 10477761715873800527057437)
                    ·
                      refine ⟨3929160643452675197646539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477761715873800527057437 3929160643452675197646539)
                      ·
                        rfl

theorem cell23_7652013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_7652013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652013 prefixEnd_7652013 := by exact prefixLift 7652013
  have htrace : WordTrace (prefixWord ++ tailWord_7652013) baseStart_7652013 baseEnd_7652013 := by
    simpa [prefixWord, tailWord_7652013, baseEnd_7652013] using wordTrace_append hprefix tailTrace_7652013
  have hstable : (prefixWord ++ tailWord_7652013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652013).length < 2 ^ (prefixWord ++ tailWord_7652013).sum := by decide
  have hdescent : baseEnd_7652013 < baseStart_7652013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652026 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_7652026 : Nat := 118140960795 + 7652026 * 2 ^ 59
def prefixEnd_7652026 : Nat := 4983230072969 + 3 ^ 40 * 7652026 * 2
def baseEnd_7652026 : Nat := 3929167318701183646783979

theorem tailTrace_7652026 : CollatzResearch.WordTrace tailWord_7652026 prefixEnd_7652026 3929167318701183646783979 := by
  unfold tailWord_7652026
  simp only [CollatzResearch.WordTrace]
  refine ⟨69773079144006034710327983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186061544384016092560874621 69773079144006034710327983)
  ·
    refine ⟨104659618716009052065491975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69773079144006034710327983 104659618716009052065491975)
    ·
      refine ⟨156989428074013578098237963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104659618716009052065491975 156989428074013578098237963)
      ·
        refine ⟨235484142111020367147356945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156989428074013578098237963 235484142111020367147356945)
        ·
          refine ⟨176613106583265275360517709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235484142111020367147356945 176613106583265275360517709)
          ·
            refine ⟨66229914968724478260194141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176613106583265275360517709 66229914968724478260194141)
            ·
              refine ⟨24836218113271679347572803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66229914968724478260194141 24836218113271679347572803)
              ·
                refine ⟨37254327169907519021359205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24836218113271679347572803 37254327169907519021359205)
                ·
                  refine ⟨6985186344357659816504851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37254327169907519021359205 6985186344357659816504851)
                  ·
                    refine ⟨10477779516536489724757277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6985186344357659816504851 10477779516536489724757277)
                    ·
                      refine ⟨3929167318701183646783979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477779516536489724757277 3929167318701183646783979)
                      ·
                        rfl

theorem cell23_7652026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_7652026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652026 prefixEnd_7652026 := by exact prefixLift 7652026
  have htrace : WordTrace (prefixWord ++ tailWord_7652026) baseStart_7652026 baseEnd_7652026 := by
    simpa [prefixWord, tailWord_7652026, baseEnd_7652026] using wordTrace_append hprefix tailTrace_7652026
  have hstable : (prefixWord ++ tailWord_7652026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652026).length < 2 ^ (prefixWord ++ tailWord_7652026).sum := by decide
  have hdescent : baseEnd_7652026 < baseStart_7652026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652069 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7652069 : Nat := 118140960795 + 7652069 * 2 ^ 59
def prefixEnd_7652069 : Nat := 4983230072969 + 3 ^ 40 * 7652069 * 2
def baseEnd_7652069 : Nat := 3929189398369326978546281

theorem tailTrace_7652069 : CollatzResearch.WordTrace tailWord_7652069 prefixEnd_7652069 3929189398369326978546281 := by
  unfold tailWord_7652069
  simp only [CollatzResearch.WordTrace]
  refine ⟨279093884914868357185127261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186062589943245571456751507 279093884914868357185127261)
  ·
    refine ⟨104660206843075633944422723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279093884914868357185127261 104660206843075633944422723)
    ·
      refine ⟨156990310264613450916634085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104660206843075633944422723 156990310264613450916634085)
      ·
        refine ⟨29435683174615022046868891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156990310264613450916634085 29435683174615022046868891)
        ·
          refine ⟨44153524761922533070303337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435683174615022046868891 44153524761922533070303337)
          ·
            refine ⟨33115143571441899802727503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44153524761922533070303337 33115143571441899802727503)
            ·
              refine ⟨49672715357162849704091255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33115143571441899802727503 49672715357162849704091255)
              ·
                refine ⟨74509073035744274556136883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49672715357162849704091255 74509073035744274556136883)
                ·
                  refine ⟨111763609553616411834205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74509073035744274556136883 111763609553616411834205325)
                  ·
                    refine ⟨41911353582606154437826997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111763609553616411834205325 41911353582606154437826997)
                    ·
                      refine ⟨3929189398369326978546281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41911353582606154437826997 3929189398369326978546281)
                      ·
                        rfl

theorem cell23_7652069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7652069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652069 prefixEnd_7652069 := by exact prefixLift 7652069
  have htrace : WordTrace (prefixWord ++ tailWord_7652069) baseStart_7652069 baseEnd_7652069 := by
    simpa [prefixWord, tailWord_7652069, baseEnd_7652069] using wordTrace_append hprefix tailTrace_7652069
  have hstable : (prefixWord ++ tailWord_7652069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652069).length < 2 ^ (prefixWord ++ tailWord_7652069).sum := by decide
  have hdescent : baseEnd_7652069 < baseStart_7652069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652083 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 2, 2, 2]
def baseStart_7652083 : Nat := 118140960795 + 7652083 * 2 ^ 59
def prefixEnd_7652083 : Nat := 4983230072969 + 3 ^ 40 * 7652083 * 2
def baseEnd_7652083 : Nat := 3929196587098489923771217

theorem tailTrace_7652083 : CollatzResearch.WordTrace tailWord_7652083 prefixEnd_7652083 3929196587098489923771217 := by
  unfold tailWord_7652083
  simp only [CollatzResearch.WordTrace]
  refine ⟨279094395536817637576136903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186062930357878425050757935 279094395536817637576136903)
  ·
    refine ⟨418641593305226456364205355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279094395536817637576136903 418641593305226456364205355)
    ·
      refine ⟨627962389957839684546308033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418641593305226456364205355 627962389957839684546308033)
      ·
        refine ⟨470971792468379763409731025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627962389957839684546308033 470971792468379763409731025)
        ·
          refine ⟨353228844351284822557298269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470971792468379763409731025 353228844351284822557298269)
          ·
            refine ⟨132460816631731808458986851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353228844351284822557298269 132460816631731808458986851)
            ·
              refine ⟨198691224947597712688480277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132460816631731808458986851 198691224947597712688480277)
              ·
                refine ⟨9313651169418642782272513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198691224947597712688480277 9313651169418642782272513)
                ·
                  refine ⟨6985238377063982086704385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9313651169418642782272513 6985238377063982086704385)
                  ·
                    refine ⟨5238928782797986565028289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985238377063982086704385 5238928782797986565028289)
                    ·
                      refine ⟨3929196587098489923771217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238928782797986565028289 3929196587098489923771217)
                      ·
                        rfl

theorem cell23_7652083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2, 2].length) (baseStart_7652083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652083 prefixEnd_7652083 := by exact prefixLift 7652083
  have htrace : WordTrace (prefixWord ++ tailWord_7652083) baseStart_7652083 baseEnd_7652083 := by
    simpa [prefixWord, tailWord_7652083, baseEnd_7652083] using wordTrace_append hprefix tailTrace_7652083
  have hstable : (prefixWord ++ tailWord_7652083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652083).length < 2 ^ (prefixWord ++ tailWord_7652083).sum := by decide
  have hdescent : baseEnd_7652083 < baseStart_7652083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652086 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7652086 : Nat := 118140960795 + 7652086 * 2 ^ 59
def prefixEnd_7652086 : Nat := 4983230072969 + 3 ^ 40 * 7652086 * 2
def baseEnd_7652086 : Nat := 3929198127540453412033703

theorem tailTrace_7652086 : CollatzResearch.WordTrace tailWord_7652086 prefixEnd_7652086 3929198127540453412033703 := by
  unfold tailWord_7652086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443406559737923068031007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186063003303871179392330741 17443406559737923068031007)
  ·
    refine ⟨26165109839606884602046511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17443406559737923068031007 26165109839606884602046511)
    ·
      refine ⟨39247664759410326903069767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26165109839606884602046511 39247664759410326903069767)
      ·
        refine ⟨58871497139115490354604651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39247664759410326903069767 58871497139115490354604651)
        ·
          refine ⟨88307245708673235531906977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58871497139115490354604651 88307245708673235531906977)
          ·
            refine ⟨66230434281504926648930233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88307245708673235531906977 66230434281504926648930233)
            ·
              refine ⟨49672825711128694986697675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66230434281504926648930233 49672825711128694986697675)
              ·
                refine ⟨74509238566693042480046513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49672825711128694986697675 74509238566693042480046513)
                ·
                  refine ⟨55881928925019781860034885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74509238566693042480046513 55881928925019781860034885)
                  ·
                    refine ⟨10477861673441209098756541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55881928925019781860034885 10477861673441209098756541)
                    ·
                      refine ⟨3929198127540453412033703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477861673441209098756541 3929198127540453412033703)
                      ·
                        rfl

theorem cell23_7652086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7652086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652086 prefixEnd_7652086 := by exact prefixLift 7652086
  have htrace : WordTrace (prefixWord ++ tailWord_7652086) baseStart_7652086 baseEnd_7652086 := by
    simpa [prefixWord, tailWord_7652086, baseEnd_7652086] using wordTrace_append hprefix tailTrace_7652086
  have hstable : (prefixWord ++ tailWord_7652086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652086).length < 2 ^ (prefixWord ++ tailWord_7652086).sum := by decide
  have hdescent : baseEnd_7652086 < baseStart_7652086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652099 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3]
def baseStart_7652099 : Nat := 118140960795 + 7652099 * 2 ^ 59
def prefixEnd_7652099 : Nat := 4983230072969 + 3 ^ 40 * 7652099 * 2
def baseEnd_7652099 : Nat := 3929204802788961861171143

theorem tailTrace_7652099 : CollatzResearch.WordTrace tailWord_7652099 prefixEnd_7652099 3929204802788961861171143 := by
  unfold tailWord_7652099
  simp only [CollatzResearch.WordTrace]
  refine ⟨279094979104759672308719351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186063319403173114872479567 279094979104759672308719351)
  ·
    refine ⟨418642468657139508463079027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279094979104759672308719351 418642468657139508463079027)
    ·
      refine ⟨627963702985709262694618541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418642468657139508463079027 627963702985709262694618541)
      ·
        refine ⟨235486388619640973510481953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627963702985709262694618541 235486388619640973510481953)
        ·
          refine ⟨176614791464730730132861465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235486388619640973510481953 176614791464730730132861465)
          ·
            refine ⟨132461093598548047599646099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176614791464730730132861465 132461093598548047599646099)
            ·
              refine ⟨198691640397822071399469149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132461093598548047599646099 198691640397822071399469149)
              ·
                refine ⟨74509365149183276774800931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198691640397822071399469149 74509365149183276774800931)
                ·
                  refine ⟨111764047723774915162201397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74509365149183276774800931 111764047723774915162201397)
                  ·
                    refine ⟨10477879474103898296456381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111764047723774915162201397 10477879474103898296456381)
                    ·
                      refine ⟨3929204802788961861171143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477879474103898296456381 3929204802788961861171143)
                      ·
                        rfl

theorem cell23_7652099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_7652099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652099 prefixEnd_7652099 := by exact prefixLift 7652099
  have htrace : WordTrace (prefixWord ++ tailWord_7652099) baseStart_7652099 baseEnd_7652099 := by
    simpa [prefixWord, tailWord_7652099, baseEnd_7652099] using wordTrace_append hprefix tailTrace_7652099
  have hstable : (prefixWord ++ tailWord_7652099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652099).length < 2 ^ (prefixWord ++ tailWord_7652099).sum := by decide
  have hdescent : baseEnd_7652099 < baseStart_7652099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652100 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7652100 : Nat := 118140960795 + 7652100 * 2 ^ 59
def prefixEnd_7652100 : Nat := 4983230072969 + 3 ^ 40 * 7652100 * 2
def baseEnd_7652100 : Nat := 3929205316269616357258639

theorem tailTrace_7652100 : CollatzResearch.WordTrace tailWord_7652100 prefixEnd_7652100 3929205316269616357258639 := by
  unfold tailWord_7652100
  simp only [CollatzResearch.WordTrace]
  refine ⟨139547507788878024739752877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186063343718504032986337169 139547507788878024739752877)
  ·
    refine ⟨52330315420829259277407329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139547507788878024739752877 52330315420829259277407329)
    ·
      refine ⟨39247736565621944458055497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52330315420829259277407329 39247736565621944458055497)
      ·
        refine ⟨29435802424216458343541623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39247736565621944458055497 29435802424216458343541623)
        ·
          refine ⟨44153703636324687515312435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435802424216458343541623 44153703636324687515312435)
          ·
            refine ⟨66230555454487031272968653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44153703636324687515312435 66230555454487031272968653)
            ·
              refine ⟨24836458295432636727363245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66230555454487031272968653 24836458295432636727363245)
              ·
                refine ⟨9313671860787238772761217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24836458295432636727363245 9313671860787238772761217)
                ·
                  refine ⟨6985253895590429079570913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9313671860787238772761217 6985253895590429079570913)
                  ·
                    refine ⟨5238940421692821809678185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985253895590429079570913 5238940421692821809678185)
                    ·
                      refine ⟨3929205316269616357258639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5238940421692821809678185 3929205316269616357258639)
                      ·
                        rfl

theorem cell23_7652100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7652100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652100 prefixEnd_7652100 := by exact prefixLift 7652100
  have htrace : WordTrace (prefixWord ++ tailWord_7652100) baseStart_7652100 baseEnd_7652100 := by
    simpa [prefixWord, tailWord_7652100, baseEnd_7652100] using wordTrace_append hprefix tailTrace_7652100
  have hstable : (prefixWord ++ tailWord_7652100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652100).length < 2 ^ (prefixWord ++ tailWord_7652100).sum := by decide
  have hdescent : baseEnd_7652100 < baseStart_7652100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652129 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7652129 : Nat := 118140960795 + 7652129 * 2 ^ 59
def prefixEnd_7652129 : Nat := 4983230072969 + 3 ^ 40 * 7652129 * 2
def baseEnd_7652129 : Nat := 3929220207208596743796005

theorem tailTrace_7652129 : CollatzResearch.WordTrace tailWord_7652129 prefixEnd_7652129 3929220207208596743796005 := by
  unfold tailWord_7652129
  simp only [CollatzResearch.WordTrace]
  refine ⟨279096073294650987432311441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186064048863100658288207627 279096073294650987432311441)
  ·
    refine ⟨209322054970988240574233581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279096073294650987432311441 209322054970988240574233581)
    ·
      refine ⟨78495770614120590215337593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209322054970988240574233581 78495770614120590215337593)
      ·
        refine ⟨58871827960590442661503195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78495770614120590215337593 58871827960590442661503195)
        ·
          refine ⟨88307741940885663992254793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58871827960590442661503195 88307741940885663992254793)
          ·
            refine ⟨66230806455664247994191095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88307741940885663992254793 66230806455664247994191095)
            ·
              refine ⟨99346209683496371991286643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66230806455664247994191095 99346209683496371991286643)
              ·
                refine ⟨149019314525244557986929965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99346209683496371991286643 149019314525244557986929965)
                ·
                  refine ⟨55882242946966709245098737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149019314525244557986929965 55882242946966709245098737)
                  ·
                    refine ⟨41911682210225031933824053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55882242946966709245098737 41911682210225031933824053)
                    ·
                      refine ⟨3929220207208596743796005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41911682210225031933824053 3929220207208596743796005)
                      ·
                        rfl

theorem cell23_7652129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7652129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652129 prefixEnd_7652129 := by exact prefixLift 7652129
  have htrace : WordTrace (prefixWord ++ tailWord_7652129) baseStart_7652129 baseEnd_7652129 := by
    simpa [prefixWord, tailWord_7652129, baseEnd_7652129] using wordTrace_append hprefix tailTrace_7652129
  have hstable : (prefixWord ++ tailWord_7652129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652129).length < 2 ^ (prefixWord ++ tailWord_7652129).sum := by decide
  have hdescent : baseEnd_7652129 < baseStart_7652129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652136 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7652136 : Nat := 118140960795 + 7652136 * 2 ^ 59
def prefixEnd_7652136 : Nat := 4983230072969 + 3 ^ 40 * 7652136 * 2
def baseEnd_7652136 : Nat := 1309741267191059405469491

theorem tailTrace_7652136 : CollatzResearch.WordTrace tailWord_7652136 prefixEnd_7652136 1309741267191059405469491 := by
  unfold tailWord_7652136
  simp only [CollatzResearch.WordTrace]
  refine ⟨139548164302812813813908131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186064219070417085085210841 139548164302812813813908131)
  ·
    refine ⟨209322246454219220720862197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139548164302812813813908131 209322246454219220720862197)
    ·
      refine ⟨19623960605083051942580831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209322246454219220720862197 19623960605083051942580831)
      ·
        refine ⟨29435940907624577913871247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623960605083051942580831 29435940907624577913871247)
        ·
          refine ⟨44153911361436866870806871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435940907624577913871247 44153911361436866870806871)
          ·
            refine ⟨66230867042155300306210307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44153911361436866870806871 66230867042155300306210307)
            ·
              refine ⟨99346300563232950459315461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66230867042155300306210307 99346300563232950459315461)
              ·
                refine ⟨18627431355606178211121649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99346300563232950459315461 18627431355606178211121649)
                ·
                  refine ⟨13970573516704633658341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18627431355606178211121649 13970573516704633658341237)
                  ·
                    refine ⟨1309741267191059405469491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13970573516704633658341237 1309741267191059405469491)
                    ·
                      rfl

theorem cell23_7652136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7652136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652136 prefixEnd_7652136 := by exact prefixLift 7652136
  have htrace : WordTrace (prefixWord ++ tailWord_7652136) baseStart_7652136 baseEnd_7652136 := by
    simpa [prefixWord, tailWord_7652136, baseEnd_7652136] using wordTrace_append hprefix tailTrace_7652136
  have hstable : (prefixWord ++ tailWord_7652136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652136).length < 2 ^ (prefixWord ++ tailWord_7652136).sum := by decide
  have hdescent : baseEnd_7652136 < baseStart_7652136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652150 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7652150 : Nat := 118140960795 + 7652150 * 2 ^ 59
def prefixEnd_7652150 : Nat := 4983230072969 + 3 ^ 40 * 7652150 * 2
def baseEnd_7652150 : Nat := 3929230990302341161633409

theorem tailTrace_7652150 : CollatzResearch.WordTrace tailWord_7652150 prefixEnd_7652150 3929230990302341161633409 := by
  unfold tailWord_7652150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443552451723431751176619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186064559485049938679217269 17443552451723431751176619)
  ·
    refine ⟨26165328677585147626764929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17443552451723431751176619 26165328677585147626764929)
    ·
      refine ⟨19623996508188860720073697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26165328677585147626764929 19623996508188860720073697)
      ·
        refine ⟨14717997381141645540055273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19623996508188860720073697 14717997381141645540055273)
        ·
          refine ⟨11038498035856234155041455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14717997381141645540055273 11038498035856234155041455)
          ·
            refine ⟨16557747053784351232562183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038498035856234155041455 16557747053784351232562183)
            ·
              refine ⟨24836620580676526848843275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16557747053784351232562183 24836620580676526848843275)
              ·
                refine ⟨37254930871014790273264913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24836620580676526848843275 37254930871014790273264913)
                ·
                  refine ⟨27941198153261092704948685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37254930871014790273264913 27941198153261092704948685)
                  ·
                    refine ⟨10477949307472909764355757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27941198153261092704948685 10477949307472909764355757)
                    ·
                      refine ⟨3929230990302341161633409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10477949307472909764355757 3929230990302341161633409)
                      ·
                        rfl

theorem cell23_7652150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7652150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652150 prefixEnd_7652150 := by exact prefixLift 7652150
  have htrace : WordTrace (prefixWord ++ tailWord_7652150) baseStart_7652150 baseEnd_7652150 := by
    simpa [prefixWord, tailWord_7652150, baseEnd_7652150] using wordTrace_append hprefix tailTrace_7652150
  have hstable : (prefixWord ++ tailWord_7652150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652150).length < 2 ^ (prefixWord ++ tailWord_7652150).sum := by decide
  have hdescent : baseEnd_7652150 < baseStart_7652150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652196 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 8]
def baseStart_7652196 : Nat := 118140960795 + 7652196 * 2 ^ 59
def prefixEnd_7652196 : Nat := 4983230072969 + 3 ^ 40 * 7652196 * 2
def baseEnd_7652196 : Nat := 436583845601383109073133

theorem tailTrace_7652196 : CollatzResearch.WordTrace tailWord_7652196 prefixEnd_7652196 436583845601383109073133 := by
  unfold tailWord_7652196
  simp only [CollatzResearch.WordTrace]
  refine ⟨139549258492704128937500221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186065677990272171916666961 139549258492704128937500221)
  ·
    refine ⟨52330971934764048351562583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139549258492704128937500221 52330971934764048351562583)
    ·
      refine ⟨78496457902146072527343875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52330971934764048351562583 78496457902146072527343875)
      ·
        refine ⟨117744686853219108791015813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78496457902146072527343875 117744686853219108791015813)
        ·
          refine ⟨22077128784978582898315465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117744686853219108791015813 22077128784978582898315465)
          ·
            refine ⟨16557846588733937173736599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22077128784978582898315465 16557846588733937173736599)
            ·
              refine ⟨24836769883100905760604899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16557846588733937173736599 24836769883100905760604899)
              ·
                refine ⟨37255154824651358640907349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24836769883100905760604899 37255154824651358640907349)
                ·
                  refine ⟨436583845601383109073133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37255154824651358640907349 436583845601383109073133)
                  ·
                    rfl

theorem cell23_7652196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_7652196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652196 prefixEnd_7652196 := by exact prefixLift 7652196
  have htrace : WordTrace (prefixWord ++ tailWord_7652196) baseStart_7652196 baseEnd_7652196 := by
    simpa [prefixWord, tailWord_7652196, baseEnd_7652196] using wordTrace_append hprefix tailTrace_7652196
  have hstable : (prefixWord ++ tailWord_7652196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652196).length < 2 ^ (prefixWord ++ tailWord_7652196).sum := by decide
  have hdescent : baseEnd_7652196 < baseStart_7652196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652200 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 1, 4]
def baseStart_7652200 : Nat := 118140960795 + 7652200 * 2 ^ 59
def prefixEnd_7652200 : Nat := 4983230072969 + 3 ^ 40 * 7652200 * 2
def baseEnd_7652200 : Nat := 1309752221445021988669393

theorem tailTrace_7652200 : CollatzResearch.WordTrace tailWord_7652200 prefixEnd_7652200 1309752221445021988669393 := by
  unfold tailWord_7652200
  simp only [CollatzResearch.WordTrace]
  refine ⟨139549331438696883279073027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186065775251595844372097369 139549331438696883279073027)
  ·
    refine ⟨209323997158045324918609541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139549331438696883279073027 209323997158045324918609541)
    ·
      refine ⟨39248249467133498422239289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209323997158045324918609541 39248249467133498422239289)
      ·
        refine ⟨29436187100350123816679467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39248249467133498422239289 29436187100350123816679467)
        ·
          refine ⟨44154280650525185725019201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29436187100350123816679467 44154280650525185725019201)
          ·
            refine ⟨33115710487893889293764401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44154280650525185725019201 33115710487893889293764401)
            ·
              refine ⟨24836782865920416970323301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33115710487893889293764401 24836782865920416970323301)
              ·
                refine ⟨4656896787360078181935619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24836782865920416970323301 4656896787360078181935619)
                ·
                  refine ⟨6985345181040117272903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656896787360078181935619 6985345181040117272903429)
                  ·
                    refine ⟨1309752221445021988669393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6985345181040117272903429 1309752221445021988669393)
                    ·
                      rfl

theorem cell23_7652200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_7652200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652200 prefixEnd_7652200 := by exact prefixLift 7652200
  have htrace : WordTrace (prefixWord ++ tailWord_7652200) baseStart_7652200 baseEnd_7652200 := by
    simpa [prefixWord, tailWord_7652200, baseEnd_7652200] using wordTrace_append hprefix tailTrace_7652200
  have hstable : (prefixWord ++ tailWord_7652200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652200).length < 2 ^ (prefixWord ++ tailWord_7652200).sum := by decide
  have hdescent : baseEnd_7652200 < baseStart_7652200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652219 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_7652219 : Nat := 118140960795 + 7652219 * 2 ^ 59
def prefixEnd_7652219 : Nat := 4983230072969 + 3 ^ 40 * 7652219 * 2
def baseEnd_7652219 : Nat := 3929266420467501391670591

theorem tailTrace_7652219 : CollatzResearch.WordTrace tailWord_7652219 prefixEnd_7652219 3929266420467501391670591 := by
  unfold tailWord_7652219
  simp only [CollatzResearch.WordTrace]
  refine ⟨279099355864324932803087711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186066237242883288535391807 279099355864324932803087711)
  ·
    refine ⟨418649033796487399204631567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279099355864324932803087711 418649033796487399204631567)
    ·
      refine ⟨627973550694731098806947351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418649033796487399204631567 627973550694731098806947351)
      ·
        refine ⟨941960326042096648210421027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627973550694731098806947351 941960326042096648210421027)
        ·
          refine ⟨1412940489063144972315631541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941960326042096648210421027 1412940489063144972315631541)
          ·
            refine ⟨132463170849669841154590457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1412940489063144972315631541 132463170849669841154590457)
            ·
              refine ⟨99347378137252380865942843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132463170849669841154590457 99347378137252380865942843)
              ·
                refine ⟨149021067205878571298914265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99347378137252380865942843 149021067205878571298914265)
                ·
                  refine ⟨111765800404408928474185699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149021067205878571298914265 111765800404408928474185699)
                  ·
                    refine ⟨167648700606613392711278549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111765800404408928474185699 167648700606613392711278549)
                    ·
                      refine ⟨3929266420467501391670591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167648700606613392711278549 3929266420467501391670591)
                      ·
                        rfl

theorem cell23_7652219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_7652219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652219 prefixEnd_7652219 := by exact prefixLift 7652219
  have htrace : WordTrace (prefixWord ++ tailWord_7652219) baseStart_7652219 baseEnd_7652219 := by
    simpa [prefixWord, tailWord_7652219, baseEnd_7652219] using wordTrace_append hprefix tailTrace_7652219
  have hstable : (prefixWord ++ tailWord_7652219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652219).length < 2 ^ (prefixWord ++ tailWord_7652219).sum := by decide
  have hdescent : baseEnd_7652219 < baseStart_7652219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652223 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 3]
def baseStart_7652223 : Nat := 118140960795 + 7652223 * 2 ^ 59
def prefixEnd_7652223 : Nat := 4983230072969 + 3 ^ 40 * 7652223 * 2
def baseEnd_7652223 : Nat := 3929268474390119376020573

theorem tailTrace_7652223 : CollatzResearch.WordTrace tailWord_7652223 prefixEnd_7652223 3929268474390119376020573 := by
  unfold tailWord_7652223
  simp only [CollatzResearch.WordTrace]
  refine ⟨279099501756310441486233323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186066334504206960990822215 279099501756310441486233323)
  ·
    refine ⟨418649252634465662229349985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279099501756310441486233323 418649252634465662229349985)
    ·
      refine ⟨313986939475849246672012489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418649252634465662229349985 313986939475849246672012489)
      ·
        refine ⟨235490204606886935004009367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313986939475849246672012489 235490204606886935004009367)
        ·
          refine ⟨353235306910330402506014051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235490204606886935004009367 353235306910330402506014051)
          ·
            refine ⟨529852960365495603759021077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353235306910330402506014051 529852960365495603759021077)
            ·
              refine ⟨24836857517132606426204113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 529852960365495603759021077 24836857517132606426204113)
              ·
                refine ⟨18627643137849454819653085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24836857517132606426204113 18627643137849454819653085)
                ·
                  refine ⟨6985366176693545557369907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18627643137849454819653085 6985366176693545557369907)
                  ·
                    refine ⟨10478049265040318336054861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6985366176693545557369907 10478049265040318336054861)
                    ·
                      refine ⟨3929268474390119376020573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478049265040318336054861 3929268474390119376020573)
                      ·
                        rfl

theorem cell23_7652223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_7652223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652223 prefixEnd_7652223 := by exact prefixLift 7652223
  have htrace : WordTrace (prefixWord ++ tailWord_7652223) baseStart_7652223 baseEnd_7652223 := by
    simpa [prefixWord, tailWord_7652223, baseEnd_7652223] using wordTrace_append hprefix tailTrace_7652223
  have hstable : (prefixWord ++ tailWord_7652223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652223).length < 2 ^ (prefixWord ++ tailWord_7652223).sum := by decide
  have hdescent : baseEnd_7652223 < baseStart_7652223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652233 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 5, 2]
def baseStart_7652233 : Nat := 118140960795 + 7652233 * 2 ^ 59
def prefixEnd_7652233 : Nat := 4983230072969 + 3 ^ 40 * 7652233 * 2
def baseEnd_7652233 : Nat := 3929273609196664336895527

theorem tailTrace_7652233 : CollatzResearch.WordTrace tailWord_7652233 prefixEnd_7652233 3929273609196664336895527 := by
  unfold tailWord_7652233
  simp only [CollatzResearch.WordTrace]
  refine ⟨279099866486274213194097353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186066577657516142129398235 279099866486274213194097353)
  ·
    refine ⟨209324899864705659895573015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279099866486274213194097353 209324899864705659895573015)
    ·
      refine ⟨313987349797058489843359523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209324899864705659895573015 313987349797058489843359523)
      ·
        refine ⟨470981024695587734765039285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313987349797058489843359523 470981024695587734765039285)
        ·
          refine ⟨44154471065211350134222433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470981024695587734765039285 44154471065211350134222433)
          ·
            refine ⟨33115853298908512600666825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44154471065211350134222433 33115853298908512600666825)
            ·
              refine ⟨24836889974181384450500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33115853298908512600666825 24836889974181384450500119)
              ·
                refine ⟨37255334961272076675750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24836889974181384450500119 37255334961272076675750179)
                ·
                  refine ⟨55883002441908115013625269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37255334961272076675750179 55883002441908115013625269)
                  ·
                    refine ⟨5239031478928885782527369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55883002441908115013625269 5239031478928885782527369)
                    ·
                      refine ⟨3929273609196664336895527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239031478928885782527369 3929273609196664336895527)
                      ·
                        rfl

theorem cell23_7652233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5, 2].length) (baseStart_7652233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652233 prefixEnd_7652233 := by exact prefixLift 7652233
  have htrace : WordTrace (prefixWord ++ tailWord_7652233) baseStart_7652233 baseEnd_7652233 := by
    simpa [prefixWord, tailWord_7652233, baseEnd_7652233] using wordTrace_append hprefix tailTrace_7652233
  have hstable : (prefixWord ++ tailWord_7652233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652233).length < 2 ^ (prefixWord ++ tailWord_7652233).sum := by decide
  have hdescent : baseEnd_7652233 < baseStart_7652233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652257 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7652257 : Nat := 118140960795 + 7652257 * 2 ^ 59
def prefixEnd_7652257 : Nat := 4983230072969 + 3 ^ 40 * 7652257 * 2
def baseEnd_7652257 : Nat := 3929285932732372242995417

theorem tailTrace_7652257 : CollatzResearch.WordTrace tailWord_7652257 prefixEnd_7652257 3929285932732372242995417 := by
  unfold tailWord_7652257
  simp only [CollatzResearch.WordTrace]
  refine ⟨279100741838187265292971025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186067161225458176861980683 279100741838187265292971025)
  ·
    refine ⟨209325556378640448969728269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279100741838187265292971025 209325556378640448969728269)
    ·
      refine ⟨78497083641990168363648101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209325556378640448969728269 78497083641990168363648101)
      ·
        refine ⟨14718203182873156568184019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78497083641990168363648101 14718203182873156568184019)
        ·
          refine ⟨22077304774309734852276029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14718203182873156568184019 22077304774309734852276029)
          ·
            refine ⟨8278989290366150569603511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22077304774309734852276029 8278989290366150569603511)
            ·
              refine ⟨12418483935549225854405267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278989290366150569603511 12418483935549225854405267)
              ·
                refine ⟨18627725903323838781607901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418483935549225854405267 18627725903323838781607901)
                ·
                  refine ⟨6985397213746439543102963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18627725903323838781607901 6985397213746439543102963)
                  ·
                    refine ⟨10478095820619659314654445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6985397213746439543102963 10478095820619659314654445)
                    ·
                      refine ⟨3929285932732372242995417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478095820619659314654445 3929285932732372242995417)
                      ·
                        rfl

theorem cell23_7652257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7652257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652257 prefixEnd_7652257 := by exact prefixLift 7652257
  have htrace : WordTrace (prefixWord ++ tailWord_7652257) baseStart_7652257 baseEnd_7652257 := by
    simpa [prefixWord, tailWord_7652257, baseEnd_7652257] using wordTrace_append hprefix tailTrace_7652257
  have hstable : (prefixWord ++ tailWord_7652257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652257).length < 2 ^ (prefixWord ++ tailWord_7652257).sum := by decide
  have hdescent : baseEnd_7652257 < baseStart_7652257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652280 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_7652280 : Nat := 118140960795 + 7652280 * 2 ^ 59
def prefixEnd_7652280 : Nat := 4983230072969 + 3 ^ 40 * 7652280 * 2
def baseEnd_7652280 : Nat := 3929297742787425653007811

theorem tailTrace_7652280 : CollatzResearch.WordTrace tailWord_7652280 prefixEnd_7652280 3929297742787425653007811 := by
  unfold tailWord_7652280
  simp only [CollatzResearch.WordTrace]
  refine ⟨139550790358551970110529147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186067720478069293480705529 139550790358551970110529147)
  ·
    refine ⟨209326185537827955165793721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139550790358551970110529147 209326185537827955165793721)
    ·
      refine ⟨156994639153370966374345291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209326185537827955165793721 156994639153370966374345291)
      ·
        refine ⟨235491958730056449561517937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156994639153370966374345291 235491958730056449561517937)
        ·
          refine ⟨176618969047542337171138453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235491958730056449561517937 176618969047542337171138453)
          ·
            refine ⟨8279014174103547054897115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176618969047542337171138453 8279014174103547054897115)
            ·
              refine ⟨12418521261155320582345673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279014174103547054897115 12418521261155320582345673)
              ·
                refine ⟨9313890945866490436759255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12418521261155320582345673 9313890945866490436759255)
                ·
                  refine ⟨13970836418799735655138883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313890945866490436759255 13970836418799735655138883)
                  ·
                    refine ⟨20956254628199603482708325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13970836418799735655138883 20956254628199603482708325)
                    ·
                      refine ⟨3929297742787425653007811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20956254628199603482708325 3929297742787425653007811)
                      ·
                        rfl

theorem cell23_7652280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_7652280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652280 prefixEnd_7652280 := by exact prefixLift 7652280
  have htrace : WordTrace (prefixWord ++ tailWord_7652280) baseStart_7652280 baseEnd_7652280 := by
    simpa [prefixWord, tailWord_7652280, baseEnd_7652280] using wordTrace_append hprefix tailTrace_7652280
  have hstable : (prefixWord ++ tailWord_7652280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652280).length < 2 ^ (prefixWord ++ tailWord_7652280).sum := by decide
  have hdescent : baseEnd_7652280 < baseStart_7652280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652286 : List Nat := [4, 2, 1, 1, 1, 2, 1, 11]
def baseStart_7652286 : Nat := 118140960795 + 7652286 * 2 ^ 59
def prefixEnd_7652286 : Nat := 4983230072969 + 3 ^ 40 * 7652286 * 2
def baseEnd_7652286 : Nat := 145529660135976023316029

theorem tailTrace_7652286 : CollatzResearch.WordTrace tailWord_7652286 prefixEnd_7652286 145529660135976023316029 := by
  unfold tailWord_7652286
  simp only [CollatzResearch.WordTrace]
  refine ⟨34887724944385275405722089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186067866370054802163851141 34887724944385275405722089)
  ·
    refine ⟨26165793708288956554291567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34887724944385275405722089 26165793708288956554291567)
    ·
      refine ⟨39248690562433434831437351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26165793708288956554291567 39248690562433434831437351)
      ·
        refine ⟨58873035843650152247156027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39248690562433434831437351 58873035843650152247156027)
        ·
          refine ⟨88309553765475228370734041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58873035843650152247156027 88309553765475228370734041)
          ·
            refine ⟨66232165324106421278050531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88309553765475228370734041 66232165324106421278050531)
            ·
              refine ⟨99348247986159631917075797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66232165324106421278050531 99348247986159631917075797)
              ·
                refine ⟨145529660135976023316029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99348247986159631917075797 145529660135976023316029)
                ·
                  rfl

theorem cell23_7652286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_7652286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652286 prefixEnd_7652286 := by exact prefixLift 7652286
  have htrace : WordTrace (prefixWord ++ tailWord_7652286) baseStart_7652286 baseEnd_7652286 := by
    simpa [prefixWord, tailWord_7652286, baseEnd_7652286] using wordTrace_append hprefix tailTrace_7652286
  have hstable : (prefixWord ++ tailWord_7652286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652286).length < 2 ^ (prefixWord ++ tailWord_7652286).sum := by decide
  have hdescent : baseEnd_7652286 < baseStart_7652286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652314 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2]
def baseStart_7652314 : Nat := 118140960795 + 7652314 * 2 ^ 59
def prefixEnd_7652314 : Nat := 4983230072969 + 3 ^ 40 * 7652314 * 2
def baseEnd_7652314 : Nat := 3929315201129678519982655

theorem tailTrace_7652314 : CollatzResearch.WordTrace tailWord_7652314 prefixEnd_7652314 3929315201129678519982655 := by
  unfold tailWord_7652314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69775705199745191006948999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186068547199320509351863997 69775705199745191006948999)
  ·
    refine ⟨104663557799617786510423499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69775705199745191006948999 104663557799617786510423499)
    ·
      refine ⟨156995336699426679765635249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104663557799617786510423499 156995336699426679765635249)
      ·
        refine ⟨117746502524570009824226437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156995336699426679765635249 117746502524570009824226437)
        ·
          refine ⟨22077469223356876842042457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117746502524570009824226437 22077469223356876842042457)
          ·
            refine ⟨16558101917517657631531843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22077469223356876842042457 16558101917517657631531843)
            ·
              refine ⟨24837152876276486447297765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558101917517657631531843 24837152876276486447297765)
              ·
                refine ⟨4656966164301841208868331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24837152876276486447297765 4656966164301841208868331)
                ·
                  refine ⟨6985449246452761813302497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656966164301841208868331 6985449246452761813302497)
                  ·
                    refine ⟨5239086934839571359976873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985449246452761813302497 5239086934839571359976873)
                    ·
                      refine ⟨3929315201129678519982655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239086934839571359976873 3929315201129678519982655)
                      ·
                        rfl

theorem cell23_7652314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_7652314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652314 prefixEnd_7652314 := by exact prefixLift 7652314
  have htrace : WordTrace (prefixWord ++ tailWord_7652314) baseStart_7652314 baseEnd_7652314 := by
    simpa [prefixWord, tailWord_7652314, baseEnd_7652314] using wordTrace_append hprefix tailTrace_7652314
  have hstable : (prefixWord ++ tailWord_7652314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652314).length < 2 ^ (prefixWord ++ tailWord_7652314).sum := by decide
  have hdescent : baseEnd_7652314 < baseStart_7652314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652330 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_7652330 : Nat := 118140960795 + 7652330 * 2 ^ 59
def prefixEnd_7652330 : Nat := 4983230072969 + 3 ^ 40 * 7652330 * 2
def baseEnd_7652330 : Nat := 3929323416820150457382581

theorem tailTrace_7652330 : CollatzResearch.WordTrace tailWord_7652330 prefixEnd_7652330 3929323416820150457382581 := by
  unfold tailWord_7652330
  simp only [CollatzResearch.WordTrace]
  refine ⟨69775851091730699690094611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186068936244615199173585629 69775851091730699690094611)
  ·
    refine ⟨104663776637596049535141917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69775851091730699690094611 104663776637596049535141917)
    ·
      refine ⟨39248916239098518575678219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104663776637596049535141917 39248916239098518575678219)
      ·
        refine ⟨58873374358647777863517329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39248916239098518575678219 58873374358647777863517329)
        ·
          refine ⟨44155030768985833397637997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58873374358647777863517329 44155030768985833397637997)
          ·
            refine ⟨16558136538369687524114249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44155030768985833397637997 16558136538369687524114249)
            ·
              refine ⟨12418602403777265643085687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16558136538369687524114249 12418602403777265643085687)
              ·
                refine ⟨18627903605665898464628531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418602403777265643085687 18627903605665898464628531)
                ·
                  refine ⟨27941855408498847696942797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18627903605665898464628531 27941855408498847696942797)
                  ·
                    refine ⟨10478195778187067886353549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27941855408498847696942797 10478195778187067886353549)
                    ·
                      refine ⟨3929323416820150457382581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10478195778187067886353549 3929323416820150457382581)
                      ·
                        rfl

theorem cell23_7652330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_7652330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652330 prefixEnd_7652330 := by exact prefixLift 7652330
  have htrace : WordTrace (prefixWord ++ tailWord_7652330) baseStart_7652330 baseEnd_7652330 := by
    simpa [prefixWord, tailWord_7652330, baseEnd_7652330] using wordTrace_append hprefix tailTrace_7652330
  have hstable : (prefixWord ++ tailWord_7652330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652330).length < 2 ^ (prefixWord ++ tailWord_7652330).sum := by decide
  have hdescent : baseEnd_7652330 < baseStart_7652330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652336 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_7652336 : Nat := 118140960795 + 7652336 * 2 ^ 59
def prefixEnd_7652336 : Nat := 4983230072969 + 3 ^ 40 * 7652336 * 2
def baseEnd_7652336 : Nat := 3929326497704077433907553

theorem tailTrace_7652336 : CollatzResearch.WordTrace tailWord_7652336 prefixEnd_7652336 3929326497704077433907553 := by
  unfold tailWord_7652336
  simp only [CollatzResearch.WordTrace]
  refine ⟨139551811602450530892548431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186069082136600707856731241 139551811602450530892548431)
  ·
    refine ⟨209327717403675796338822647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139551811602450530892548431 209327717403675796338822647)
    ·
      refine ⟨313991576105513694508233971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209327717403675796338822647 313991576105513694508233971)
      ·
        refine ⟨470987364158270541762350957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313991576105513694508233971 470987364158270541762350957)
        ·
          refine ⟨176620261559351453160881609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470987364158270541762350957 176620261559351453160881609)
          ·
            refine ⟨132465196169513589870661207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176620261559351453160881609 132465196169513589870661207)
            ·
              refine ⟨198697794254270384805991811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132465196169513589870661207 198697794254270384805991811)
              ·
                refine ⟨298046691381405577208987717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198697794254270384805991811 298046691381405577208987717)
                ·
                  refine ⟨55883754634013545726685197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298046691381405577208987717 55883754634013545726685197)
                  ·
                    refine ⟨20956407987755079647506949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55883754634013545726685197 20956407987755079647506949)
                    ·
                      refine ⟨3929326497704077433907553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20956407987755079647506949 3929326497704077433907553)
                      ·
                        rfl

theorem cell23_7652336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_7652336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652336 prefixEnd_7652336 := by exact prefixLift 7652336
  have htrace : WordTrace (prefixWord ++ tailWord_7652336) baseStart_7652336 baseEnd_7652336 := by
    simpa [prefixWord, tailWord_7652336, baseEnd_7652336] using wordTrace_append hprefix tailTrace_7652336
  have hstable : (prefixWord ++ tailWord_7652336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652336).length < 2 ^ (prefixWord ++ tailWord_7652336).sum := by decide
  have hdescent : baseEnd_7652336 < baseStart_7652336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652383 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_7652383 : Nat := 118140960795 + 7652383 * 2 ^ 59
def prefixEnd_7652383 : Nat := 4983230072969 + 3 ^ 40 * 7652383 * 2
def baseEnd_7652383 : Nat := 3929350631294838750019837

theorem tailTrace_7652383 : CollatzResearch.WordTrace tailWord_7652383 prefixEnd_7652383 3929350631294838750019837 := by
  unfold tailWord_7652383
  simp only [CollatzResearch.WordTrace]
  refine ⟨279105337435730788812057803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186070224957153859208038535 279105337435730788812057803)
  ·
    refine ⟨418658006153596183218086705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279105337435730788812057803 418658006153596183218086705)
    ·
      refine ⟨313993504615197137413565029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418658006153596183218086705 313993504615197137413565029)
      ·
        refine ⟨58873782115349463265043443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313993504615197137413565029 58873782115349463265043443)
        ·
          refine ⟨88310673173024194897565165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58873782115349463265043443 88310673173024194897565165)
          ·
            refine ⟨33116502439884073086586937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88310673173024194897565165 33116502439884073086586937)
            ·
              refine ⟨24837376829913054814940203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33116502439884073086586937 24837376829913054814940203)
              ·
                refine ⟨37256065244869582222410305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24837376829913054814940203 37256065244869582222410305)
                ·
                  refine ⟨27942048933652186666807729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37256065244869582222410305 27942048933652186666807729)
                  ·
                    refine ⟨20956536700239140000105797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27942048933652186666807729 20956536700239140000105797)
                    ·
                      refine ⟨3929350631294838750019837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20956536700239140000105797 3929350631294838750019837)
                      ·
                        rfl

theorem cell23_7652383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_7652383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652383 prefixEnd_7652383 := by exact prefixLift 7652383
  have htrace : WordTrace (prefixWord ++ tailWord_7652383) baseStart_7652383 baseEnd_7652383 := by
    simpa [prefixWord, tailWord_7652383, baseEnd_7652383] using wordTrace_append hprefix tailTrace_7652383
  have hstable : (prefixWord ++ tailWord_7652383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652383).length < 2 ^ (prefixWord ++ tailWord_7652383).sum := by decide
  have hdescent : baseEnd_7652383 < baseStart_7652383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652387 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 1, 4, 2]
def baseStart_7652387 : Nat := 118140960795 + 7652387 * 2 ^ 59
def prefixEnd_7652387 : Nat := 4983230072969 + 3 ^ 40 * 7652387 * 2
def baseEnd_7652387 : Nat := 3929352685217456734369819

theorem tailTrace_7652387 : CollatzResearch.WordTrace tailWord_7652387 prefixEnd_7652387 3929352685217456734369819 := by
  unfold tailWord_7652387
  simp only [CollatzResearch.WordTrace]
  refine ⟨279105483327716297495203415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186070322218477531663468943 279105483327716297495203415)
  ·
    refine ⟨418658224991574446242805123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279105483327716297495203415 418658224991574446242805123)
    ·
      refine ⟨627987337487361669364207685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418658224991574446242805123 627987337487361669364207685)
      ·
        refine ⟨117747625778880313005788941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627987337487361669364207685 117747625778880313005788941)
        ·
          refine ⟨44155359667080117377170853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117747625778880313005788941 44155359667080117377170853)
          ·
            refine ⟨8279129937577522008219535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44155359667080117377170853 8279129937577522008219535)
            ·
              refine ⟨12418694906366283012329303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279129937577522008219535 12418694906366283012329303)
              ·
                refine ⟨18628042359549424518493955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12418694906366283012329303 18628042359549424518493955)
                ·
                  refine ⟨27942063539324136777740933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18628042359549424518493955 27942063539324136777740933)
                  ·
                    refine ⟨5239136913623275645826425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27942063539324136777740933 5239136913623275645826425)
                    ·
                      refine ⟨3929352685217456734369819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239136913623275645826425 3929352685217456734369819)
                      ·
                        rfl

theorem cell23_7652387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_7652387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652387 prefixEnd_7652387 := by exact prefixLift 7652387
  have htrace : WordTrace (prefixWord ++ tailWord_7652387) baseStart_7652387 baseEnd_7652387 := by
    simpa [prefixWord, tailWord_7652387, baseEnd_7652387] using wordTrace_append hprefix tailTrace_7652387
  have hstable : (prefixWord ++ tailWord_7652387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652387).length < 2 ^ (prefixWord ++ tailWord_7652387).sum := by decide
  have hdescent : baseEnd_7652387 < baseStart_7652387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652404 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7652404 : Nat := 118140960795 + 7652404 * 2 ^ 59
def prefixEnd_7652404 : Nat := 4983230072969 + 3 ^ 40 * 7652404 * 2
def baseEnd_7652404 : Nat := 3929361414388583167857241

theorem tailTrace_7652404 : CollatzResearch.WordTrace tailWord_7652404 prefixEnd_7652404 3929361414388583167857241 := by
  unfold tailWord_7652404
  simp only [CollatzResearch.WordTrace]
  refine ⟨139553051684327354699286133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186070735579103139599048177 139553051684327354699286133)
  ·
    refine ⟨13083098595405689503058075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139553051684327354699286133 13083098595405689503058075)
    ·
      refine ⟨19624647893108534254587113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13083098595405689503058075 19624647893108534254587113)
      ·
        refine ⟨14718485919831400690940335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19624647893108534254587113 14718485919831400690940335)
        ·
          refine ⟨22077728879747101036410503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14718485919831400690940335 22077728879747101036410503)
          ·
            refine ⟨33116593319620651554615755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22077728879747101036410503 33116593319620651554615755)
            ·
              refine ⟨49674889979430977331923633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33116593319620651554615755 49674889979430977331923633)
              ·
                refine ⟨37256167484573232998942725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49674889979430977331923633 37256167484573232998942725)
                ·
                  refine ⟨6985531403357481187301761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37256167484573232998942725 6985531403357481187301761)
                  ·
                    refine ⟨5239148552518110890476321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985531403357481187301761 5239148552518110890476321)
                    ·
                      refine ⟨3929361414388583167857241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239148552518110890476321 3929361414388583167857241)
                      ·
                        rfl

theorem cell23_7652404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7652404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652404 prefixEnd_7652404 := by exact prefixLift 7652404
  have htrace : WordTrace (prefixWord ++ tailWord_7652404) baseStart_7652404 baseEnd_7652404 := by
    simpa [prefixWord, tailWord_7652404, baseEnd_7652404] using wordTrace_append hprefix tailTrace_7652404
  have hstable : (prefixWord ++ tailWord_7652404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652404).length < 2 ^ (prefixWord ++ tailWord_7652404).sum := by decide
  have hdescent : baseEnd_7652404 < baseStart_7652404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652410 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 5]
def baseStart_7652410 : Nat := 118140960795 + 7652410 * 2 ^ 59
def prefixEnd_7652410 : Nat := 4983230072969 + 3 ^ 40 * 7652410 * 2
def baseEnd_7652410 : Nat := 436596055030278904931357

theorem tailTrace_7652410 : CollatzResearch.WordTrace tailWord_7652410 prefixEnd_7652410 436596055030278904931357 := by
  unfold tailWord_7652410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69776580551658243105822671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186070881471088648282193789 69776580551658243105822671)
  ·
    refine ⟨104664870827487364658734007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69776580551658243105822671 104664870827487364658734007)
    ·
      refine ⟨156997306241231046988101011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104664870827487364658734007 156997306241231046988101011)
      ·
        refine ⟨235495959361846570482151517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156997306241231046988101011 235495959361846570482151517)
        ·
          refine ⟨88310984760692463930806819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235495959361846570482151517 88310984760692463930806819)
          ·
            refine ⟨132466477141038695896210229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88310984760692463930806819 132466477141038695896210229)
            ·
              refine ⟨12418732231972377740269709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132466477141038695896210229 12418732231972377740269709)
              ·
                refine ⟨4657024586989641652601141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12418732231972377740269709 4657024586989641652601141)
                ·
                  refine ⟨436596055030278904931357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4657024586989641652601141 436596055030278904931357)
                  ·
                    rfl

theorem cell23_7652410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_7652410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652410 prefixEnd_7652410 := by exact prefixLift 7652410
  have htrace : WordTrace (prefixWord ++ tailWord_7652410) baseStart_7652410 baseEnd_7652410 := by
    simpa [prefixWord, tailWord_7652410, baseEnd_7652410] using wordTrace_append hprefix tailTrace_7652410
  have hstable : (prefixWord ++ tailWord_7652410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652410).length < 2 ^ (prefixWord ++ tailWord_7652410).sum := by decide
  have hdescent : baseEnd_7652410 < baseStart_7652410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652423 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 4, 5]
def baseStart_7652423 : Nat := 118140960795 + 7652423 * 2 ^ 59
def prefixEnd_7652423 : Nat := 4983230072969 + 3 ^ 40 * 7652423 * 2
def baseEnd_7652423 : Nat := 1309790390173672864506551

theorem tailTrace_7652423 : CollatzResearch.WordTrace tailWord_7652423 prefixEnd_7652423 1309790390173672864506551 := by
  unfold tailWord_7652423
  simp only [CollatzResearch.WordTrace]
  refine ⟨279106796355585875643513923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186071197570390583762342615 279106796355585875643513923)
  ·
    refine ⟨418660194533378813465270885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279106796355585875643513923 418660194533378813465270885)
    ·
      refine ⟨78498786475008527524738291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418660194533378813465270885 78498786475008527524738291)
      ·
        refine ⟨117748179712512791287107437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78498786475008527524738291 117748179712512791287107437)
        ·
          refine ⟨44155567392192296732665289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117748179712512791287107437 44155567392192296732665289)
          ·
            refine ⟨33116675544144222549498967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44155567392192296732665289 33116675544144222549498967)
            ·
              refine ⟨49675013316216333824248451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33116675544144222549498967 49675013316216333824248451)
              ·
                refine ⟨74512519974324500736372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49675013316216333824248451 74512519974324500736372677)
                ·
                  refine ⟨13971097495185843888069877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74512519974324500736372677 13971097495185843888069877)
                  ·
                    refine ⟨1309790390173672864506551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13971097495185843888069877 1309790390173672864506551)
                    ·
                      rfl

theorem cell23_7652423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_7652423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652423 prefixEnd_7652423 := by exact prefixLift 7652423
  have htrace : WordTrace (prefixWord ++ tailWord_7652423) baseStart_7652423 baseEnd_7652423 := by
    simpa [prefixWord, tailWord_7652423, baseEnd_7652423] using wordTrace_append hprefix tailTrace_7652423
  have hstable : (prefixWord ++ tailWord_7652423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652423).length < 2 ^ (prefixWord ++ tailWord_7652423).sum := by decide
  have hdescent : baseEnd_7652423 < baseStart_7652423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652430 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_7652430 : Nat := 118140960795 + 7652430 * 2 ^ 59
def prefixEnd_7652430 : Nat := 4983230072969 + 3 ^ 40 * 7652430 * 2
def baseEnd_7652430 : Nat := 3929374764885600066132121

theorem tailTrace_7652430 : CollatzResearch.WordTrace tailWord_7652430 prefixEnd_7652430 3929374764885600066132121 := by
  unfold tailWord_7652430
  simp only [CollatzResearch.WordTrace]
  refine ⟨34888381458320064479877343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186071367777707010559345829 34888381458320064479877343)
  ·
    refine ⟨52332572187480096719816015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34888381458320064479877343 52332572187480096719816015)
    ·
      refine ⟨78498858281220145079724023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52332572187480096719816015 78498858281220145079724023)
      ·
        refine ⟨117748287421830217619586035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78498858281220145079724023 117748287421830217619586035)
        ·
          refine ⟨176622431132745326429379053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117748287421830217619586035 176622431132745326429379053)
          ·
            refine ⟨66233411674779497411017145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176622431132745326429379053 66233411674779497411017145)
            ·
              refine ⟨49675058756084623058262859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66233411674779497411017145 49675058756084623058262859)
              ·
                refine ⟨74512588134126934587394289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49675058756084623058262859 74512588134126934587394289)
                ·
                  refine ⟨55884441100595200940545717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74512588134126934587394289 55884441100595200940545717)
                  ·
                    refine ⟨5239166353180800088176161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55884441100595200940545717 5239166353180800088176161)
                    ·
                      refine ⟨3929374764885600066132121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239166353180800088176161 3929374764885600066132121)
                      ·
                        rfl

theorem cell23_7652430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_7652430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652430 prefixEnd_7652430 := by exact prefixLift 7652430
  have htrace : WordTrace (prefixWord ++ tailWord_7652430) baseStart_7652430 baseEnd_7652430 := by
    simpa [prefixWord, tailWord_7652430, baseEnd_7652430] using wordTrace_append hprefix tailTrace_7652430
  have hstable : (prefixWord ++ tailWord_7652430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652430).length < 2 ^ (prefixWord ++ tailWord_7652430).sum := by decide
  have hdescent : baseEnd_7652430 < baseStart_7652430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7652438 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7652438 : Nat := 118140960795 + 7652438 * 2 ^ 59
def prefixEnd_7652438 : Nat := 4983230072969 + 3 ^ 40 * 7652438 * 2
def baseEnd_7652438 : Nat := 3929378872730836034832085

theorem tailTrace_7652438 : CollatzResearch.WordTrace tailWord_7652438 prefixEnd_7652438 3929378872730836034832085 := by
  unfold tailWord_7652438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444208965658220825331873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186071562300354355470206645 17444208965658220825331873)
  ·
    refine ⟨13083156724243665618998905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17444208965658220825331873 13083156724243665618998905)
    ·
      refine ⟨9812367543182749214249179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13083156724243665618998905 9812367543182749214249179)
      ·
        refine ⟨14718551314774123821373769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9812367543182749214249179 14718551314774123821373769)
        ·
          refine ⟨11038913486080592866030327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14718551314774123821373769 11038913486080592866030327)
          ·
            refine ⟨16558370229120889299045491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038913486080592866030327 16558370229120889299045491)
            ·
              refine ⟨24837555343681333948568237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558370229120889299045491 24837555343681333948568237)
              ·
                refine ⟨9314083253880500230713089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24837555343681333948568237 9314083253880500230713089)
                ·
                  refine ⟨6985562440410375173034817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9314083253880500230713089 6985562440410375173034817)
                  ·
                    refine ⟨5239171830307781379776113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6985562440410375173034817 5239171830307781379776113)
                    ·
                      refine ⟨3929378872730836034832085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5239171830307781379776113 3929378872730836034832085)
                      ·
                        rfl

theorem cell23_7652438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7652438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7652438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7652438 prefixEnd_7652438 := by exact prefixLift 7652438
  have htrace : WordTrace (prefixWord ++ tailWord_7652438) baseStart_7652438 baseEnd_7652438 := by
    simpa [prefixWord, tailWord_7652438, baseEnd_7652438] using wordTrace_append hprefix tailTrace_7652438
  have hstable : (prefixWord ++ tailWord_7652438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7652438).length < 2 ^ (prefixWord ++ tailWord_7652438).sum := by decide
  have hdescent : baseEnd_7652438 < baseStart_7652438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7652438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
