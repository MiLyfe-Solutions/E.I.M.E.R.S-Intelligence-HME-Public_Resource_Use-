import V185TrunkScan23Chunk0147

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_874992 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_874992 : Nat := 118140960795 + 874992 * 2 ^ 59
def prefixEnd_874992 : Nat := 4983230072969 + 3 ^ 40 * 874992 * 2
def baseEnd_874992 : Nat := 449291464838945823475991

theorem tailTrace_874992 : CollatzResearch.WordTrace tailWord_874992 prefixEnd_874992 449291464838945823475991 := by
  unfold tailWord_874992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956790023030447790721615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21275720030707263720962153 15956790023030447790721615)
  ·
    refine ⟨23935185034545671686082423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956790023030447790721615 23935185034545671686082423)
    ·
      refine ⟨35902777551818507529123635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23935185034545671686082423 35902777551818507529123635)
      ·
        refine ⟨53854166327727761293685453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35902777551818507529123635 53854166327727761293685453)
        ·
          refine ⟨20195312372897910485132045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53854166327727761293685453 20195312372897910485132045)
          ·
            refine ⟨7573242139836716431924517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20195312372897910485132045 7573242139836716431924517)
            ·
              refine ⟨1419982901219384330985847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7573242139836716431924517 1419982901219384330985847)
              ·
                refine ⟨2129974351829076496478771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419982901219384330985847 2129974351829076496478771)
                ·
                  refine ⟨3194961527743614744718157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129974351829076496478771 3194961527743614744718157)
                  ·
                    refine ⟨1198110572903855529269309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3194961527743614744718157 1198110572903855529269309)
                    ·
                      refine ⟨449291464838945823475991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198110572903855529269309 449291464838945823475991)
                      ·
                        rfl

theorem cell23_874992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_874992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_874992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_874992 prefixEnd_874992 := by exact prefixLift 874992
  have htrace : WordTrace (prefixWord ++ tailWord_874992) baseStart_874992 baseEnd_874992 := by
    simpa [prefixWord, tailWord_874992, baseEnd_874992] using wordTrace_append hprefix tailTrace_874992
  have hstable : (prefixWord ++ tailWord_874992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874992).length < 2 ^ (prefixWord ++ tailWord_874992).sum := by decide
  have hdescent : baseEnd_874992 < baseStart_874992 := by decide
  rcases family_descends (prefixWord ++ tailWord_874992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875005 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_875005 : Nat := 118140960795 + 875005 * 2 ^ 59
def prefixEnd_875005 : Nat := 4983230072969 + 3 ^ 40 * 875005 * 2
def baseEnd_875005 : Nat := 449298140087454272613431

theorem tailTrace_875005 : CollatzResearch.WordTrace tailWord_875005 prefixEnd_875005 449298140087454272613431 := by
  unfold tailWord_875005
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914054195013798801666469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21276036130009199201110979 31914054195013798801666469)
  ·
    refine ⟨5983885161565087275312463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31914054195013798801666469 5983885161565087275312463)
    ·
      refine ⟨8975827742347630912968695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5983885161565087275312463 8975827742347630912968695)
      ·
        refine ⟨13463741613521446369453043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8975827742347630912968695 13463741613521446369453043)
        ·
          refine ⟨20195612420282169554179565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13463741613521446369453043 20195612420282169554179565)
          ·
            refine ⟨7573354657605813582817337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20195612420282169554179565 7573354657605813582817337)
            ·
              refine ⟨5680015993204360187113003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573354657605813582817337 5680015993204360187113003)
              ·
                refine ⟨8520023989806540280669505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680015993204360187113003 8520023989806540280669505)
                ·
                  refine ⟨6390017992354905210502129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8520023989806540280669505 6390017992354905210502129)
                  ·
                    refine ⟨4792513494266178907876597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6390017992354905210502129 4792513494266178907876597)
                    ·
                      refine ⟨449298140087454272613431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4792513494266178907876597 449298140087454272613431)
                      ·
                        rfl

theorem cell23_875005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_875005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875005 prefixEnd_875005 := by exact prefixLift 875005
  have htrace : WordTrace (prefixWord ++ tailWord_875005) baseStart_875005 baseEnd_875005 := by
    simpa [prefixWord, tailWord_875005, baseEnd_875005] using wordTrace_append hprefix tailTrace_875005
  have hstable : (prefixWord ++ tailWord_875005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875005).length < 2 ^ (prefixWord ++ tailWord_875005).sum := by decide
  have hdescent : baseEnd_875005 < baseStart_875005 := by decide
  rcases family_descends (prefixWord ++ tailWord_875005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875010 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_875010 : Nat := 118140960795 + 875010 * 2 ^ 59
def prefixEnd_875010 : Nat := 4983230072969 + 3 ^ 40 * 875010 * 2
def baseEnd_875010 : Nat := 449300707490726753050909

theorem tailTrace_875010 : CollatzResearch.WordTrace tailWord_875010 prefixEnd_875010 449300707490726753050909 := by
  unfold tailWord_875010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978559139998921163899621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21276157706663789770398989 7978559139998921163899621)
  ·
    refine ⟨1495979838749797718231179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7978559139998921163899621 1495979838749797718231179)
    ·
      refine ⟨2243969758124696577346769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495979838749797718231179 2243969758124696577346769)
      ·
        refine ⟨1682977318593522433010077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2243969758124696577346769 1682977318593522433010077)
        ·
          refine ⟨631116494472570912378779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1682977318593522433010077 631116494472570912378779)
          ·
            refine ⟨946674741708856368568169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631116494472570912378779 946674741708856368568169)
            ·
              refine ⟨710006056281642276426127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946674741708856368568169 710006056281642276426127)
              ·
                refine ⟨1065009084422463414639191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710006056281642276426127 1065009084422463414639191)
                ·
                  refine ⟨1597513626633695121958787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065009084422463414639191 1597513626633695121958787)
                  ·
                    refine ⟨2396270439950542682938181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597513626633695121958787 2396270439950542682938181)
                    ·
                      refine ⟨449300707490726753050909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2396270439950542682938181 449300707490726753050909)
                      ·
                        rfl

theorem cell23_875010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_875010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875010 prefixEnd_875010 := by exact prefixLift 875010
  have htrace : WordTrace (prefixWord ++ tailWord_875010) baseStart_875010 baseEnd_875010 := by
    simpa [prefixWord, tailWord_875010, baseEnd_875010] using wordTrace_append hprefix tailTrace_875010
  have hstable : (prefixWord ++ tailWord_875010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875010).length < 2 ^ (prefixWord ++ tailWord_875010).sum := by decide
  have hdescent : baseEnd_875010 < baseStart_875010 := by decide
  rcases family_descends (prefixWord ++ tailWord_875010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875156 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_875156 : Nat := 118140960795 + 875156 * 2 ^ 59
def prefixEnd_875156 : Nat := 4983230072969 + 3 ^ 40 * 875156 * 2
def baseEnd_875156 : Nat := 449375675666283181825237

theorem tailTrace_875156 : CollatzResearch.WordTrace tailWord_875156 prefixEnd_875156 449375675666283181825237 := by
  unfold tailWord_875156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959780808733375795206661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21279707744977834393608881 15959780808733375795206661)
  ·
    refine ⟨2992458901637507961601249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15959780808733375795206661 2992458901637507961601249)
    ·
      refine ⟨2244344176228130971200937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2992458901637507961601249 2244344176228130971200937)
      ·
        refine ⟨1683258132171098228400703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2244344176228130971200937 1683258132171098228400703)
        ·
          refine ⟨2524887198256647342601055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683258132171098228400703 2524887198256647342601055)
          ·
            refine ⟨3787330797384971013901583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524887198256647342601055 3787330797384971013901583)
            ·
              refine ⟨5680996196077456520852375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787330797384971013901583 5680996196077456520852375)
              ·
                refine ⟨8521494294116184781278563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680996196077456520852375 8521494294116184781278563)
                ·
                  refine ⟨12782241441174277171917845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8521494294116184781278563 12782241441174277171917845)
                  ·
                    refine ⟨599167567555044242433649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12782241441174277171917845 599167567555044242433649)
                    ·
                      refine ⟨449375675666283181825237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599167567555044242433649 449375675666283181825237)
                      ·
                        rfl

theorem cell23_875156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_875156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875156 prefixEnd_875156 := by exact prefixLift 875156
  have htrace : WordTrace (prefixWord ++ tailWord_875156) baseStart_875156 baseEnd_875156 := by
    simpa [prefixWord, tailWord_875156, baseEnd_875156] using wordTrace_append hprefix tailTrace_875156
  have hstable : (prefixWord ++ tailWord_875156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875156).length < 2 ^ (prefixWord ++ tailWord_875156).sum := by decide
  have hdescent : baseEnd_875156 < baseStart_875156 := by decide
  rcases family_descends (prefixWord ++ tailWord_875156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875166 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_875166 : Nat := 118140960795 + 875166 * 2 ^ 59
def prefixEnd_875166 : Nat := 4983230072969 + 3 ^ 40 * 875166 * 2
def baseEnd_875166 : Nat := 149793603490942714233397

theorem tailTrace_875166 : CollatzResearch.WordTrace tailWord_875166 prefixEnd_875166 149793603490942714233397 := by
  unfold tailWord_875166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989990793428815412284669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21279950898287015532184901 3989990793428815412284669)
  ·
    refine ⟨1496246547535805779606751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3989990793428815412284669 1496246547535805779606751)
    ·
      refine ⟨2244369821303708669410127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496246547535805779606751 2244369821303708669410127)
      ·
        refine ⟨3366554731955563004115191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244369821303708669410127 3366554731955563004115191)
        ·
          refine ⟨5049832097933344506172787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366554731955563004115191 5049832097933344506172787)
          ·
            refine ⟨7574748146900016759259181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049832097933344506172787 7574748146900016759259181)
            ·
              refine ⟨2840530555087506284722193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7574748146900016759259181 2840530555087506284722193)
              ·
                refine ⟨2130397916315629713541645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840530555087506284722193 2130397916315629713541645)
                ·
                  refine ⟨798899218618361142578117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2130397916315629713541645 798899218618361142578117)
                  ·
                    refine ⟨149793603490942714233397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 798899218618361142578117 149793603490942714233397)
                    ·
                      rfl

theorem cell23_875166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_875166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875166 prefixEnd_875166 := by exact prefixLift 875166
  have htrace : WordTrace (prefixWord ++ tailWord_875166) baseStart_875166 baseEnd_875166 := by
    simpa [prefixWord, tailWord_875166, baseEnd_875166] using wordTrace_append hprefix tailTrace_875166
  have hstable : (prefixWord ++ tailWord_875166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875166).length < 2 ^ (prefixWord ++ tailWord_875166).sum := by decide
  have hdescent : baseEnd_875166 < baseStart_875166 := by decide
  rcases family_descends (prefixWord ++ tailWord_875166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875232 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_875232 : Nat := 118140960795 + 875232 * 2 ^ 59
def prefixEnd_875232 : Nat := 4983230072969 + 3 ^ 40 * 875232 * 2
def baseEnd_875232 : Nat := 449414700196024884474887

theorem tailTrace_875232 : CollatzResearch.WordTrace tailWord_875232 prefixEnd_875232 449414700196024884474887 := by
  unfold tailWord_875232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15961166782595708285089975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21281555710127611046786633 15961166782595708285089975)
  ·
    refine ⟨23941750173893562427634963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15961166782595708285089975 23941750173893562427634963)
    ·
      refine ⟨35912625260840343641452445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23941750173893562427634963 35912625260840343641452445)
      ·
        refine ⟨13467234472815128865544667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35912625260840343641452445 13467234472815128865544667)
        ·
          refine ⟨20200851709222693298317001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13467234472815128865544667 20200851709222693298317001)
          ·
            refine ⟨15150638781917019973737751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20200851709222693298317001 15150638781917019973737751)
            ·
              refine ⟨22725958172875529960606627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15150638781917019973737751 22725958172875529960606627)
              ·
                refine ⟨34088937259313294940909941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22725958172875529960606627 34088937259313294940909941)
                ·
                  refine ⟨3195837868060621400710307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34088937259313294940909941 3195837868060621400710307)
                  ·
                    refine ⟨4793756802090932101065461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195837868060621400710307 4793756802090932101065461)
                    ·
                      refine ⟨449414700196024884474887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4793756802090932101065461 449414700196024884474887)
                      ·
                        rfl

theorem cell23_875232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_875232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875232 prefixEnd_875232 := by exact prefixLift 875232
  have htrace : WordTrace (prefixWord ++ tailWord_875232) baseStart_875232 baseEnd_875232 := by
    simpa [prefixWord, tailWord_875232, baseEnd_875232] using wordTrace_append hprefix tailTrace_875232
  have hstable : (prefixWord ++ tailWord_875232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875232).length < 2 ^ (prefixWord ++ tailWord_875232).sum := by decide
  have hdescent : baseEnd_875232 < baseStart_875232 := by decide
  rcases family_descends (prefixWord ++ tailWord_875232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875246 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_875246 : Nat := 118140960795 + 875246 * 2 ^ 59
def prefixEnd_875246 : Nat := 4983230072969 + 3 ^ 40 * 875246 * 2
def baseEnd_875246 : Nat := 449421888925187829699823

theorem tailTrace_875246 : CollatzResearch.WordTrace tailWord_875246 prefixEnd_875246 449421888925187829699823 := by
  unfold tailWord_875246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990355523392587120148699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21281896124760464640793061 3990355523392587120148699)
  ·
    refine ⟨5985533285088880680223049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990355523392587120148699 5985533285088880680223049)
    ·
      refine ⟨4489149963816660510167287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5985533285088880680223049 4489149963816660510167287)
      ·
        refine ⟨6733724945724990765250931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489149963816660510167287 6733724945724990765250931)
        ·
          refine ⟨10100587418587486147876397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733724945724990765250931 10100587418587486147876397)
          ·
            refine ⟨3787720281970307305453649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10100587418587486147876397 3787720281970307305453649)
            ·
              refine ⟨2840790211477730479090237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787720281970307305453649 2840790211477730479090237)
              ·
                refine ⟨1065296329304148929658839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2840790211477730479090237 1065296329304148929658839)
                ·
                  refine ⟨1597944493956223394488259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065296329304148929658839 1597944493956223394488259)
                  ·
                    refine ⟨2396916740934335091732389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1597944493956223394488259 2396916740934335091732389)
                    ·
                      refine ⟨449421888925187829699823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2396916740934335091732389 449421888925187829699823)
                      ·
                        rfl

theorem cell23_875246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_875246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875246 prefixEnd_875246 := by exact prefixLift 875246
  have htrace : WordTrace (prefixWord ++ tailWord_875246) baseStart_875246 baseEnd_875246 := by
    simpa [prefixWord, tailWord_875246, baseEnd_875246] using wordTrace_append hprefix tailTrace_875246
  have hstable : (prefixWord ++ tailWord_875246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875246).length < 2 ^ (prefixWord ++ tailWord_875246).sum := by decide
  have hdescent : baseEnd_875246 < baseStart_875246 := by decide
  rcases family_descends (prefixWord ++ tailWord_875246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875249 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_875249 : Nat := 118140960795 + 875249 * 2 ^ 59
def prefixEnd_875249 : Nat := 4983230072969 + 3 ^ 40 * 875249 * 2
def baseEnd_875249 : Nat := 449423429367151317962309

theorem tailTrace_875249 : CollatzResearch.WordTrace tailWord_875249 prefixEnd_875249 449423429367151317962309 := by
  unfold tailWord_875249
  simp only [CollatzResearch.WordTrace]
  refine ⟨31922953606129828473548801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21281969070753218982365867 31922953606129828473548801)
  ·
    refine ⟨23942215204597371355161601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31922953606129828473548801 23942215204597371355161601)
    ·
      refine ⟨17956661403448028516371201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23942215204597371355161601 17956661403448028516371201)
      ·
        refine ⟨13467496052586021387278401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17956661403448028516371201 13467496052586021387278401)
        ·
          refine ⟨10100622039439516040458801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13467496052586021387278401 10100622039439516040458801)
          ·
            refine ⟨7575466529579637030344101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10100622039439516040458801 7575466529579637030344101)
            ·
              refine ⟨1420399974296181943189519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7575466529579637030344101 1420399974296181943189519)
              ·
                refine ⟨2130599961444272914784279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420399974296181943189519 2130599961444272914784279)
                ·
                  refine ⟨3195899942166409372176419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130599961444272914784279 3195899942166409372176419)
                  ·
                    refine ⟨4793849913249614058264629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195899942166409372176419 4793849913249614058264629)
                    ·
                      refine ⟨449423429367151317962309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4793849913249614058264629 449423429367151317962309)
                      ·
                        rfl

theorem cell23_875249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_875249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875249 prefixEnd_875249 := by exact prefixLift 875249
  have htrace : WordTrace (prefixWord ++ tailWord_875249) baseStart_875249 baseEnd_875249 := by
    simpa [prefixWord, tailWord_875249, baseEnd_875249] using wordTrace_append hprefix tailTrace_875249
  have hstable : (prefixWord ++ tailWord_875249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875249).length < 2 ^ (prefixWord ++ tailWord_875249).sum := by decide
  have hdescent : baseEnd_875249 < baseStart_875249 := by decide
  rcases family_descends (prefixWord ++ tailWord_875249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875266 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_875266 : Nat := 118140960795 + 875266 * 2 ^ 59
def prefixEnd_875266 : Nat := 4983230072969 + 3 ^ 40 * 875266 * 2
def baseEnd_875266 : Nat := 449432158538277751449731

theorem tailTrace_875266 : CollatzResearch.WordTrace tailWord_875266 prefixEnd_875266 449432158538277751449731 := by
  unfold tailWord_875266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980893411767060094229413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21282382431378826917945101 7980893411767060094229413)
  ·
    refine ⟨1496417514706323767668015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7980893411767060094229413 1496417514706323767668015)
    ·
      refine ⟨2244626272059485651502023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496417514706323767668015 2244626272059485651502023)
      ·
        refine ⟨3366939408089228477253035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244626272059485651502023 3366939408089228477253035)
        ·
          refine ⟨5050409112133842715879553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366939408089228477253035 5050409112133842715879553)
          ·
            refine ⟨3787806834100382036909665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5050409112133842715879553 3787806834100382036909665)
            ·
              refine ⟨2840855125575286527682249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787806834100382036909665 2840855125575286527682249)
              ·
                refine ⟨2130641344181464895761687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840855125575286527682249 2130641344181464895761687)
                ·
                  refine ⟨3195962016272197343642531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130641344181464895761687 3195962016272197343642531)
                  ·
                    refine ⟨4793943024408296015463797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195962016272197343642531 4793943024408296015463797)
                    ·
                      refine ⟨449432158538277751449731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4793943024408296015463797 449432158538277751449731)
                      ·
                        rfl

theorem cell23_875266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_875266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875266 prefixEnd_875266 := by exact prefixLift 875266
  have htrace : WordTrace (prefixWord ++ tailWord_875266) baseStart_875266 baseEnd_875266 := by
    simpa [prefixWord, tailWord_875266, baseEnd_875266] using wordTrace_append hprefix tailTrace_875266
  have hstable : (prefixWord ++ tailWord_875266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875266).length < 2 ^ (prefixWord ++ tailWord_875266).sum := by decide
  have hdescent : baseEnd_875266 < baseStart_875266 := by decide
  rcases family_descends (prefixWord ++ tailWord_875266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875279 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_875279 : Nat := 118140960795 + 875279 * 2 ^ 59
def prefixEnd_875279 : Nat := 4983230072969 + 3 ^ 40 * 875279 * 2
def baseEnd_875279 : Nat := 449438833786786200587171

theorem tailTrace_875279 : CollatzResearch.WordTrace tailWord_875279 prefixEnd_875279 449438833786786200587171 := by
  unfold tailWord_875279
  simp only [CollatzResearch.WordTrace]
  refine ⟨31924047796021143597140891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21282698530680762398093927 31924047796021143597140891)
  ·
    refine ⟨47886071694031715395711337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31924047796021143597140891 47886071694031715395711337)
    ·
      refine ⟨35914553770523786546783503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47886071694031715395711337 35914553770523786546783503)
      ·
        refine ⟨53871830655785679820175255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35914553770523786546783503 53871830655785679820175255)
        ·
          refine ⟨80807745983678519730262883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53871830655785679820175255 80807745983678519730262883)
          ·
            refine ⟨121211618975517779595394325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80807745983678519730262883 121211618975517779595394325)
            ·
              refine ⟨5681794639477395918534109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121211618975517779595394325 5681794639477395918534109)
              ·
                refine ⟨2130672989804023469450291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5681794639477395918534109 2130672989804023469450291)
                ·
                  refine ⟨3196009484706035204175437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130672989804023469450291 3196009484706035204175437)
                  ·
                    refine ⟨1198503556764763201565789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196009484706035204175437 1198503556764763201565789)
                    ·
                      refine ⟨449438833786786200587171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198503556764763201565789 449438833786786200587171)
                      ·
                        rfl

theorem cell23_875279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_875279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875279 prefixEnd_875279 := by exact prefixLift 875279
  have htrace : WordTrace (prefixWord ++ tailWord_875279) baseStart_875279 baseEnd_875279 := by
    simpa [prefixWord, tailWord_875279, baseEnd_875279] using wordTrace_append hprefix tailTrace_875279
  have hstable : (prefixWord ++ tailWord_875279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875279).length < 2 ^ (prefixWord ++ tailWord_875279).sum := by decide
  have hdescent : baseEnd_875279 < baseStart_875279 := by decide
  rcases family_descends (prefixWord ++ tailWord_875279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875293 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_875293 : Nat := 118140960795 + 875293 * 2 ^ 59
def prefixEnd_875293 : Nat := 4983230072969 + 3 ^ 40 * 875293 * 2
def baseEnd_875293 : Nat := 449446022515949145812107

theorem tailTrace_875293 : CollatzResearch.WordTrace tailWord_875293 prefixEnd_875293 449446022515949145812107 := by
  unfold tailWord_875293
  simp only [CollatzResearch.WordTrace]
  refine ⟨31924558417970423988150533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21283038945313615992100355 31924558417970423988150533)
  ·
    refine ⟨5985854703369454497778225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31924558417970423988150533 5985854703369454497778225)
    ·
      refine ⟨4489391027527090873333669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5985854703369454497778225 4489391027527090873333669)
      ·
        refine ⟨841760817661329538750063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4489391027527090873333669 841760817661329538750063)
        ·
          refine ⟨1262641226491994308125095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841760817661329538750063 1262641226491994308125095)
          ·
            refine ⟨1893961839737991462187643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262641226491994308125095 1893961839737991462187643)
            ·
              refine ⟨2840942759606987193281465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893961839737991462187643 2840942759606987193281465)
              ·
                refine ⟨2130707069705240394961099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840942759606987193281465 2130707069705240394961099)
                ·
                  refine ⟨3196060604557860592441649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130707069705240394961099 3196060604557860592441649)
                  ·
                    refine ⟨2397045453418395444331237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3196060604557860592441649 2397045453418395444331237)
                    ·
                      refine ⟨449446022515949145812107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2397045453418395444331237 449446022515949145812107)
                      ·
                        rfl

theorem cell23_875293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_875293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875293 prefixEnd_875293 := by exact prefixLift 875293
  have htrace : WordTrace (prefixWord ++ tailWord_875293) baseStart_875293 baseEnd_875293 := by
    simpa [prefixWord, tailWord_875293, baseEnd_875293] using wordTrace_append hprefix tailTrace_875293
  have hstable : (prefixWord ++ tailWord_875293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875293).length < 2 ^ (prefixWord ++ tailWord_875293).sum := by decide
  have hdescent : baseEnd_875293 < baseStart_875293 := by decide
  rcases family_descends (prefixWord ++ tailWord_875293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875296 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_875296 : Nat := 118140960795 + 875296 * 2 ^ 59
def prefixEnd_875296 : Nat := 4983230072969 + 3 ^ 40 * 875296 * 2
def baseEnd_875296 : Nat := 449447562957912634074593

theorem tailTrace_875296 : CollatzResearch.WordTrace tailWord_875296 prefixEnd_875296 449447562957912634074593 := by
  unfold tailWord_875296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15962333918479777750254871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21283111891306370333673161 15962333918479777750254871)
  ·
    refine ⟨23943500877719666625382307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15962333918479777750254871 23943500877719666625382307)
    ·
      refine ⟨35915251316579499938073461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23943500877719666625382307 35915251316579499938073461)
      ·
        refine ⟨3367054810929328119194387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35915251316579499938073461 3367054810929328119194387)
        ·
          refine ⟨5050582216393992178791581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367054810929328119194387 5050582216393992178791581)
          ·
            refine ⟨1893968331147747067046843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5050582216393992178791581 1893968331147747067046843)
            ·
              refine ⟨2840952496721620600570265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893968331147747067046843 2840952496721620600570265)
              ·
                refine ⟨2130714372541215450427699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840952496721620600570265 2130714372541215450427699)
                ·
                  refine ⟨3196071558811823175641549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130714372541215450427699 3196071558811823175641549)
                  ·
                    refine ⟨1198526834554433690865581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3196071558811823175641549 1198526834554433690865581)
                    ·
                      refine ⟨449447562957912634074593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198526834554433690865581 449447562957912634074593)
                      ·
                        rfl

theorem cell23_875296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_875296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875296 prefixEnd_875296 := by exact prefixLift 875296
  have htrace : WordTrace (prefixWord ++ tailWord_875296) baseStart_875296 baseEnd_875296 := by
    simpa [prefixWord, tailWord_875296, baseEnd_875296] using wordTrace_append hprefix tailTrace_875296
  have hstable : (prefixWord ++ tailWord_875296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875296).length < 2 ^ (prefixWord ++ tailWord_875296).sum := by decide
  have hdescent : baseEnd_875296 < baseStart_875296 := by decide
  rcases family_descends (prefixWord ++ tailWord_875296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875300 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_875300 : Nat := 118140960795 + 875300 * 2 ^ 59
def prefixEnd_875300 : Nat := 4983230072969 + 3 ^ 40 * 875300 * 2
def baseEnd_875300 : Nat := 449449616880530618424575

theorem tailTrace_875300 : CollatzResearch.WordTrace tailWord_875300 prefixEnd_875300 449449616880530618424575 := by
  unfold tailWord_875300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15962406864472532091827677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21283209152630042789103569 15962406864472532091827677)
  ·
    refine ⟨5985902574177199534435379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15962406864472532091827677 5985902574177199534435379)
    ·
      refine ⟨8978853861265799301653069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985902574177199534435379 8978853861265799301653069)
      ·
        refine ⟨3367070197974674738119901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8978853861265799301653069 3367070197974674738119901)
        ·
          refine ⟨1262651324240503026794963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3367070197974674738119901 1262651324240503026794963)
          ·
            refine ⟨1893976986360754540192445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262651324240503026794963 1893976986360754540192445)
            ·
              refine ⟨710241369885282952572167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1893976986360754540192445 710241369885282952572167)
              ·
                refine ⟨1065362054827924428858251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710241369885282952572167 1065362054827924428858251)
                ·
                  refine ⟨1598043082241886643287377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065362054827924428858251 1598043082241886643287377)
                  ·
                    refine ⟨1198532311681414982465533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1598043082241886643287377 1198532311681414982465533)
                    ·
                      refine ⟨449449616880530618424575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198532311681414982465533 449449616880530618424575)
                      ·
                        rfl

theorem cell23_875300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_875300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875300 prefixEnd_875300 := by exact prefixLift 875300
  have htrace : WordTrace (prefixWord ++ tailWord_875300) baseStart_875300 baseEnd_875300 := by
    simpa [prefixWord, tailWord_875300, baseEnd_875300] using wordTrace_append hprefix tailTrace_875300
  have hstable : (prefixWord ++ tailWord_875300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875300).length < 2 ^ (prefixWord ++ tailWord_875300).sum := by decide
  have hdescent : baseEnd_875300 < baseStart_875300 := by decide
  rcases family_descends (prefixWord ++ tailWord_875300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875312 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_875312 : Nat := 118140960795 + 875312 * 2 ^ 59
def prefixEnd_875312 : Nat := 4983230072969 + 3 ^ 40 * 875312 * 2
def baseEnd_875312 : Nat := 149818592882794857158173

theorem tailTrace_875312 : CollatzResearch.WordTrace tailWord_875312 prefixEnd_875312 149818592882794857158173 := by
  unfold tailWord_875312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15962625702450795116546095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21283500936601060155394793 15962625702450795116546095)
  ·
    refine ⟨23943938553676192674819143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15962625702450795116546095 23943938553676192674819143)
    ·
      refine ⟨35915907830514289012228715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23943938553676192674819143 35915907830514289012228715)
      ·
        refine ⟨53873861745771433518343073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35915907830514289012228715 53873861745771433518343073)
        ·
          refine ⟨40405396309328575138757305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53873861745771433518343073 40405396309328575138757305)
          ·
            refine ⟨30304047231996431354067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40405396309328575138757305 30304047231996431354067979)
            ·
              refine ⟨45456070847994647031101969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30304047231996431354067979 45456070847994647031101969)
              ·
                refine ⟨34092053135995985273326477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45456070847994647031101969 34092053135995985273326477)
                ·
                  refine ⟨12784519925998494477497429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34092053135995985273326477 12784519925998494477497429)
                  ·
                    refine ⟨149818592882794857158173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12784519925998494477497429 149818592882794857158173)
                    ·
                      rfl

theorem cell23_875312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_875312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875312 prefixEnd_875312 := by exact prefixLift 875312
  have htrace : WordTrace (prefixWord ++ tailWord_875312) baseStart_875312 baseEnd_875312 := by
    simpa [prefixWord, tailWord_875312, baseEnd_875312] using wordTrace_append hprefix tailTrace_875312
  have hstable : (prefixWord ++ tailWord_875312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875312).length < 2 ^ (prefixWord ++ tailWord_875312).sum := by decide
  have hdescent : baseEnd_875312 < baseStart_875312 := by decide
  rcases family_descends (prefixWord ++ tailWord_875312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875313 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_875313 : Nat := 118140960795 + 875313 * 2 ^ 59
def prefixEnd_875313 : Nat := 4983230072969 + 3 ^ 40 * 875313 * 2
def baseEnd_875313 : Nat := 449456292129039067562015

theorem tailTrace_875313 : CollatzResearch.WordTrace tailWord_875313 prefixEnd_875313 449456292129039067562015 := by
  unfold tailWord_875313
  simp only [CollatzResearch.WordTrace]
  refine ⟨31925287877897967403878593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21283525251931978269252395 31925287877897967403878593)
  ·
    refine ⟨23943965908423475552908945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31925287877897967403878593 23943965908423475552908945)
    ·
      refine ⟨17957974431317606664681709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23943965908423475552908945 17957974431317606664681709)
      ·
        refine ⟨6734240411744102499255641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17957974431317606664681709 6734240411744102499255641)
        ·
          refine ⟨5050680308808076874441731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6734240411744102499255641 5050680308808076874441731)
          ·
            refine ⟨7576020463212115311662597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050680308808076874441731 7576020463212115311662597)
            ·
              refine ⟨1420503836852271620936737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7576020463212115311662597 1420503836852271620936737)
              ·
                refine ⟨1065377877639203715702553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420503836852271620936737 1065377877639203715702553)
                ·
                  refine ⟨799033408229402786776915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065377877639203715702553 799033408229402786776915)
                  ·
                    refine ⟨1198550112344104180165373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799033408229402786776915 1198550112344104180165373)
                    ·
                      refine ⟨449456292129039067562015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198550112344104180165373 449456292129039067562015)
                      ·
                        rfl

theorem cell23_875313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_875313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875313 prefixEnd_875313 := by exact prefixLift 875313
  have htrace : WordTrace (prefixWord ++ tailWord_875313) baseStart_875313 baseEnd_875313 := by
    simpa [prefixWord, tailWord_875313, baseEnd_875313] using wordTrace_append hprefix tailTrace_875313
  have hstable : (prefixWord ++ tailWord_875313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875313).length < 2 ^ (prefixWord ++ tailWord_875313).sum := by decide
  have hdescent : baseEnd_875313 < baseStart_875313 := by decide
  rcases family_descends (prefixWord ++ tailWord_875313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875349 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_875349 : Nat := 118140960795 + 875349 * 2 ^ 59
def prefixEnd_875349 : Nat := 4983230072969 + 3 ^ 40 * 875349 * 2
def baseEnd_875349 : Nat := 449474777432600926711849

theorem tailTrace_875349 : CollatzResearch.WordTrace tailWord_875349 prefixEnd_875349 449474777432600926711849 := by
  unfold tailWord_875349
  simp only [CollatzResearch.WordTrace]
  refine ⟨31926600905767545552189101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21284400603845030368126067 31926600905767545552189101)
  ·
    refine ⟨11972475339662829582070913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31926600905767545552189101 11972475339662829582070913)
    ·
      refine ⟨8979356504747122186553185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11972475339662829582070913 8979356504747122186553185)
      ·
        refine ⟨6734517378560341639914889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8979356504747122186553185 6734517378560341639914889)
        ·
          refine ⟨5050888033920256229936167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6734517378560341639914889 5050888033920256229936167)
          ·
            refine ⟨7576332050880384344904251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050888033920256229936167 7576332050880384344904251)
            ·
              refine ⟨11364498076320576517356377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576332050880384344904251 11364498076320576517356377)
              ·
                refine ⟨8523373557240432388017283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364498076320576517356377 8523373557240432388017283)
                ·
                  refine ⟨12785060335860648582025925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523373557240432388017283 12785060335860648582025925)
                  ·
                    refine ⟨2397198812973871609129861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12785060335860648582025925 2397198812973871609129861)
                    ·
                      refine ⟨449474777432600926711849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2397198812973871609129861 449474777432600926711849)
                      ·
                        rfl

theorem cell23_875349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_875349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875349 prefixEnd_875349 := by exact prefixLift 875349
  have htrace : WordTrace (prefixWord ++ tailWord_875349) baseStart_875349 baseEnd_875349 := by
    simpa [prefixWord, tailWord_875349, baseEnd_875349] using wordTrace_append hprefix tailTrace_875349
  have hstable : (prefixWord ++ tailWord_875349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875349).length < 2 ^ (prefixWord ++ tailWord_875349).sum := by decide
  have hdescent : baseEnd_875349 < baseStart_875349 := by decide
  rcases family_descends (prefixWord ++ tailWord_875349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875376 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 5]
def baseStart_875376 : Nat := 118140960795 + 875376 * 2 ^ 59
def prefixEnd_875376 : Nat := 4983230072969 + 3 ^ 40 * 875376 * 2
def baseEnd_875376 : Nat := 49943182378919146786025

theorem tailTrace_875376 : CollatzResearch.WordTrace tailWord_875376 prefixEnd_875376 49943182378919146786025 := by
  unfold tailWord_875376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963792838334864581710991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21285057117779819442281321 15963792838334864581710991)
  ·
    refine ⟨23945689257502296872566487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15963792838334864581710991 23945689257502296872566487)
    ·
      refine ⟨35918533886253445308849731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23945689257502296872566487 35918533886253445308849731)
      ·
        refine ⟨53877800829380167963274597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35918533886253445308849731 53877800829380167963274597)
        ·
          refine ⟨10102087655508781493113987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53877800829380167963274597 10102087655508781493113987)
          ·
            refine ⟨15153131483263172239670981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102087655508781493113987 15153131483263172239670981)
            ·
              refine ⟨2841212153111844794938309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15153131483263172239670981 2841212153111844794938309)
              ·
                refine ⟨532727278708470899050933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2841212153111844794938309 532727278708470899050933)
                ·
                  refine ⟨49943182378919146786025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532727278708470899050933 49943182378919146786025)
                  ·
                    rfl

theorem cell23_875376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 5].length) (baseStart_875376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875376 prefixEnd_875376 := by exact prefixLift 875376
  have htrace : WordTrace (prefixWord ++ tailWord_875376) baseStart_875376 baseEnd_875376 := by
    simpa [prefixWord, tailWord_875376, baseEnd_875376] using wordTrace_append hprefix tailTrace_875376
  have hstable : (prefixWord ++ tailWord_875376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875376).length < 2 ^ (prefixWord ++ tailWord_875376).sum := by decide
  have hdescent : baseEnd_875376 < baseStart_875376 := by decide
  rcases family_descends (prefixWord ++ tailWord_875376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875389 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_875389 : Nat := 118140960795 + 875389 * 2 ^ 59
def prefixEnd_875389 : Nat := 4983230072969 + 3 ^ 40 * 875389 * 2
def baseEnd_875389 : Nat := 149831772219593590070555

theorem tailTrace_875389 : CollatzResearch.WordTrace tailWord_875389 prefixEnd_875389 149831772219593590070555 := by
  unfold tailWord_875389
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928059825622632383645221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21285373217081754922430147 31928059825622632383645221)
  ·
    refine ⟨5986511217304243571933479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31928059825622632383645221 5986511217304243571933479)
    ·
      refine ⟨8979766825956365357900219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986511217304243571933479 8979766825956365357900219)
      ·
        refine ⟨13469650238934548036850329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8979766825956365357900219 13469650238934548036850329)
        ·
          refine ⟨10102237679200911027637747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13469650238934548036850329 10102237679200911027637747)
          ·
            refine ⟨15153356518801366541456621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102237679200911027637747 15153356518801366541456621)
            ·
              refine ⟨5682508694550512453046233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15153356518801366541456621 5682508694550512453046233)
              ·
                refine ⟨4261881520912884339784675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682508694550512453046233 4261881520912884339784675)
                ·
                  refine ⟨6392822281369326509677013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261881520912884339784675 6392822281369326509677013)
                  ·
                    refine ⟨149831772219593590070555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6392822281369326509677013 149831772219593590070555)
                    ·
                      rfl

theorem cell23_875389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_875389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875389 prefixEnd_875389 := by exact prefixLift 875389
  have htrace : WordTrace (prefixWord ++ tailWord_875389) baseStart_875389 baseEnd_875389 := by
    simpa [prefixWord, tailWord_875389, baseEnd_875389] using wordTrace_append hprefix tailTrace_875389
  have hstable : (prefixWord ++ tailWord_875389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875389).length < 2 ^ (prefixWord ++ tailWord_875389).sum := by decide
  have hdescent : baseEnd_875389 < baseStart_875389 := by decide
  rcases family_descends (prefixWord ++ tailWord_875389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875439 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_875439 : Nat := 118140960795 + 875439 * 2 ^ 59
def prefixEnd_875439 : Nat := 4983230072969 + 3 ^ 40 * 875439 * 2
def baseEnd_875439 : Nat := 449520990691505574586435

theorem tailTrace_875439 : CollatzResearch.WordTrace tailWord_875439 prefixEnd_875439 449520990691505574586435 := by
  unfold tailWord_875439
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929883475441490922965371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21286588983627660615310247 31929883475441490922965371)
  ·
    refine ⟨47894825213162236384448057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31929883475441490922965371 47894825213162236384448057)
    ·
      refine ⟨35921118909871677288336043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47894825213162236384448057 35921118909871677288336043)
      ·
        refine ⟨53881678364807515932504065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35921118909871677288336043 53881678364807515932504065)
        ·
          refine ⟨40411258773605636949378049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53881678364807515932504065 40411258773605636949378049)
          ·
            refine ⟨30308444080204227712033537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40411258773605636949378049 30308444080204227712033537)
            ·
              refine ⟨22731333060153170784025153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30308444080204227712033537 22731333060153170784025153)
              ·
                refine ⟨17048499795114878088018865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731333060153170784025153 17048499795114878088018865)
                ·
                  refine ⟨12786374846336158566014149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17048499795114878088018865 12786374846336158566014149)
                  ·
                    refine ⟨2397445283688029731127653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12786374846336158566014149 2397445283688029731127653)
                    ·
                      refine ⟨449520990691505574586435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2397445283688029731127653 449520990691505574586435)
                      ·
                        rfl

theorem cell23_875439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_875439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875439 prefixEnd_875439 := by exact prefixLift 875439
  have htrace : WordTrace (prefixWord ++ tailWord_875439) baseStart_875439 baseEnd_875439 := by
    simpa [prefixWord, tailWord_875439, baseEnd_875439] using wordTrace_append hprefix tailTrace_875439
  have hstable : (prefixWord ++ tailWord_875439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875439).length < 2 ^ (prefixWord ++ tailWord_875439).sum := by decide
  have hdescent : baseEnd_875439 < baseStart_875439 := by decide
  rcases family_descends (prefixWord ++ tailWord_875439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875496 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_875496 : Nat := 118140960795 + 875496 * 2 ^ 59
def prefixEnd_875496 : Nat := 4983230072969 + 3 ^ 40 * 875496 * 2
def baseEnd_875496 : Nat := 149850086362937283857891

theorem tailTrace_875496 : CollatzResearch.WordTrace tailWord_875496 prefixEnd_875496 149850086362937283857891 := by
  unfold tailWord_875496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965981218117494828895171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21287974957489993105193561 15965981218117494828895171)
  ·
    refine ⟨23948971827176242243342757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15965981218117494828895171 23948971827176242243342757)
    ·
      refine ⟨4490432217595545420626767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23948971827176242243342757 4490432217595545420626767)
      ·
        refine ⟨6735648326393318130940151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490432217595545420626767 6735648326393318130940151)
        ·
          refine ⟨10103472489589977196410227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735648326393318130940151 10103472489589977196410227)
          ·
            refine ⟨15155208734384965794615341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103472489589977196410227 15155208734384965794615341)
            ·
              refine ⟨5683203275394362172980753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15155208734384965794615341 5683203275394362172980753)
              ·
                refine ⟨4262402456545771629735565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683203275394362172980753 4262402456545771629735565)
                ·
                  refine ⟨1598400921204664361150837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4262402456545771629735565 1598400921204664361150837)
                  ·
                    refine ⟨149850086362937283857891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1598400921204664361150837 149850086362937283857891)
                    ·
                      rfl

theorem cell23_875496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_875496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875496 prefixEnd_875496 := by exact prefixLift 875496
  have htrace : WordTrace (prefixWord ++ tailWord_875496) baseStart_875496 baseEnd_875496 := by
    simpa [prefixWord, tailWord_875496, baseEnd_875496] using wordTrace_append hprefix tailTrace_875496
  have hstable : (prefixWord ++ tailWord_875496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875496).length < 2 ^ (prefixWord ++ tailWord_875496).sum := by decide
  have hdescent : baseEnd_875496 < baseStart_875496 := by decide
  rcases family_descends (prefixWord ++ tailWord_875496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875510 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_875510 : Nat := 118140960795 + 875510 * 2 ^ 59
def prefixEnd_875510 : Nat := 4983230072969 + 3 ^ 40 * 875510 * 2
def baseEnd_875510 : Nat := 449557447817974796798609

theorem tailTrace_875510 : CollatzResearch.WordTrace tailWord_875510 prefixEnd_875510 449557447817974796798609 := by
  unfold tailWord_875510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995779566136516878049999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21288315372122846699199989 1995779566136516878049999)
  ·
    refine ⟨2993669349204775317074999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995779566136516878049999 2993669349204775317074999)
    ·
      refine ⟨4490504023807162975612499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993669349204775317074999 4490504023807162975612499)
      ·
        refine ⟨6735756035710744463418749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490504023807162975612499 6735756035710744463418749)
        ·
          refine ⟨2525908513391529173782031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6735756035710744463418749 2525908513391529173782031)
          ·
            refine ⟨3788862770087293760673047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525908513391529173782031 3788862770087293760673047)
            ·
              refine ⟨5683294155130940641009571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788862770087293760673047 5683294155130940641009571)
              ·
                refine ⟨8524941232696410961514357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683294155130940641009571 8524941232696410961514357)
                ·
                  refine ⟨799213240565288527641971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8524941232696410961514357 799213240565288527641971)
                  ·
                    refine ⟨1198819860847932791462957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799213240565288527641971 1198819860847932791462957)
                    ·
                      refine ⟨449557447817974796798609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198819860847932791462957 449557447817974796798609)
                      ·
                        rfl

theorem cell23_875510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_875510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875510 prefixEnd_875510 := by exact prefixLift 875510
  have htrace : WordTrace (prefixWord ++ tailWord_875510) baseStart_875510 baseEnd_875510 := by
    simpa [prefixWord, tailWord_875510, baseEnd_875510] using wordTrace_append hprefix tailTrace_875510
  have hstable : (prefixWord ++ tailWord_875510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875510).length < 2 ^ (prefixWord ++ tailWord_875510).sum := by decide
  have hdescent : baseEnd_875510 < baseStart_875510 := by decide
  rcases family_descends (prefixWord ++ tailWord_875510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875527 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_875527 : Nat := 118140960795 + 875527 * 2 ^ 59
def prefixEnd_875527 : Nat := 4983230072969 + 3 ^ 40 * 875527 * 2
def baseEnd_875527 : Nat := 449566176989101230286031

theorem tailTrace_875527 : CollatzResearch.WordTrace tailWord_875527 prefixEnd_875527 449566176989101230286031 := by
  unfold tailWord_875527
  simp only [CollatzResearch.WordTrace]
  refine ⟨31933093099122681952168835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21288728732748454634779223 31933093099122681952168835)
  ·
    refine ⟨47899639648684022928253253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31933093099122681952168835 47899639648684022928253253)
    ·
      refine ⟨8981182434128254299047485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47899639648684022928253253 8981182434128254299047485)
      ·
        refine ⟨3367943412798095362142807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8981182434128254299047485 3367943412798095362142807)
        ·
          refine ⟨5051915119197143043214211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367943412798095362142807 5051915119197143043214211)
          ·
            refine ⟨7577872678795714564821317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051915119197143043214211 7577872678795714564821317)
            ·
              refine ⟨1420851127274196480903997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7577872678795714564821317 1420851127274196480903997)
              ·
                refine ⟨532819172727823680338999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420851127274196480903997 532819172727823680338999)
                ·
                  refine ⟨799228759091735520508499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532819172727823680338999 799228759091735520508499)
                  ·
                    refine ⟨1198843138637603280762749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799228759091735520508499 1198843138637603280762749)
                    ·
                      refine ⟨449566176989101230286031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198843138637603280762749 449566176989101230286031)
                      ·
                        rfl

theorem cell23_875527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_875527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875527 prefixEnd_875527 := by exact prefixLift 875527
  have htrace : WordTrace (prefixWord ++ tailWord_875527) baseStart_875527 baseEnd_875527 := by
    simpa [prefixWord, tailWord_875527, baseEnd_875527] using wordTrace_append hprefix tailTrace_875527
  have hstable : (prefixWord ++ tailWord_875527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875527).length < 2 ^ (prefixWord ++ tailWord_875527).sum := by decide
  have hdescent : baseEnd_875527 < baseStart_875527 := by decide
  rcases family_descends (prefixWord ++ tailWord_875527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875530 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_875530 : Nat := 118140960795 + 875530 * 2 ^ 59
def prefixEnd_875530 : Nat := 4983230072969 + 3 ^ 40 * 875530 * 2
def baseEnd_875530 : Nat := 149855905810354906182839

theorem tailTrace_875530 : CollatzResearch.WordTrace tailWord_875530 prefixEnd_875530 149855905810354906182839 := by
  unfold tailWord_875530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983300629527953366132011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21288801678741208976352029 7983300629527953366132011)
  ·
    refine ⟨11974950944291930049198017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7983300629527953366132011 11974950944291930049198017)
    ·
      refine ⟨8981213208218947536898513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11974950944291930049198017 8981213208218947536898513)
      ·
        refine ⟨6735909906164210652673885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8981213208218947536898513 6735909906164210652673885)
        ·
          refine ⟨2525966214811578994752707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6735909906164210652673885 2525966214811578994752707)
          ·
            refine ⟨3788949322217368492129061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525966214811578994752707 3788949322217368492129061)
            ·
              refine ⟨710427997915756592274199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3788949322217368492129061 710427997915756592274199)
              ·
                refine ⟨1065641996873634888411299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710427997915756592274199 1065641996873634888411299)
                ·
                  refine ⟨1598462995310452332616949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065641996873634888411299 1598462995310452332616949)
                  ·
                    refine ⟨149855905810354906182839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1598462995310452332616949 149855905810354906182839)
                    ·
                      rfl

theorem cell23_875530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_875530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875530 prefixEnd_875530 := by exact prefixLift 875530
  have htrace : WordTrace (prefixWord ++ tailWord_875530) baseStart_875530 baseEnd_875530 := by
    simpa [prefixWord, tailWord_875530, baseEnd_875530] using wordTrace_append hprefix tailTrace_875530
  have hstable : (prefixWord ++ tailWord_875530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875530).length < 2 ^ (prefixWord ++ tailWord_875530).sum := by decide
  have hdescent : baseEnd_875530 < baseStart_875530 := by decide
  rcases family_descends (prefixWord ++ tailWord_875530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875546 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_875546 : Nat := 118140960795 + 875546 * 2 ^ 59
def prefixEnd_875546 : Nat := 4983230072969 + 3 ^ 40 * 875546 * 2
def baseEnd_875546 : Nat := 449575933121536655948443

theorem tailTrace_875546 : CollatzResearch.WordTrace tailWord_875546 prefixEnd_875546 449575933121536655948443 := by
  unfold tailWord_875546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983446521513462049277623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21289190724035898798073661 7983446521513462049277623)
  ·
    refine ⟨11975169782270193073916435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7983446521513462049277623 11975169782270193073916435)
    ·
      refine ⟨17962754673405289610874653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11975169782270193073916435 17962754673405289610874653)
      ·
        refine ⟨6736033002526983604077995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17962754673405289610874653 6736033002526983604077995)
        ·
          refine ⟨10104049503790475406116993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736033002526983604077995 10104049503790475406116993)
          ·
            refine ⟨7578037127842856554587745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104049503790475406116993 7578037127842856554587745)
            ·
              refine ⟨5683527845882142415940809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7578037127842856554587745 5683527845882142415940809)
              ·
                refine ⟨4262645884411606811955607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683527845882142415940809 4262645884411606811955607)
                ·
                  refine ⟨6393968826617410217933411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262645884411606811955607 6393968826617410217933411)
                  ·
                    refine ⟨9590953239926115326900117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6393968826617410217933411 9590953239926115326900117)
                    ·
                      refine ⟨449575933121536655948443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9590953239926115326900117 449575933121536655948443)
                      ·
                        rfl

theorem cell23_875546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_875546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875546 prefixEnd_875546 := by exact prefixLift 875546
  have htrace : WordTrace (prefixWord ++ tailWord_875546) baseStart_875546 baseEnd_875546 := by
    simpa [prefixWord, tailWord_875546, baseEnd_875546] using wordTrace_append hprefix tailTrace_875546
  have hstable : (prefixWord ++ tailWord_875546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875546).length < 2 ^ (prefixWord ++ tailWord_875546).sum := by decide
  have hdescent : baseEnd_875546 < baseStart_875546 := by decide
  rcases family_descends (prefixWord ++ tailWord_875546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875553 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_875553 : Nat := 118140960795 + 875553 * 2 ^ 59
def prefixEnd_875553 : Nat := 4983230072969 + 3 ^ 40 * 875553 * 2
def baseEnd_875553 : Nat := 449579527486118128560911

theorem tailTrace_875553 : CollatzResearch.WordTrace tailWord_875553 prefixEnd_875553 449579527486118128560911 := by
  unfold tailWord_875553
  simp only [CollatzResearch.WordTrace]
  refine ⟨31934041397028488392615313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21289360931352325595076875 31934041397028488392615313)
  ·
    refine ⟨23950531047771366294461485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31934041397028488392615313 23950531047771366294461485)
    ·
      refine ⟨8981449142914262360423057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23950531047771366294461485 8981449142914262360423057)
      ·
        refine ⟨6736086857185696770317293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8981449142914262360423057 6736086857185696770317293)
        ·
          refine ⟨2526032571444636288868985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6736086857185696770317293 2526032571444636288868985)
          ·
            refine ⟨1894524428583477216651739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2526032571444636288868985 1894524428583477216651739)
            ·
              refine ⟨2841786642875215824977609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894524428583477216651739 2841786642875215824977609)
              ·
                refine ⟨2131339982156411868733207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841786642875215824977609 2131339982156411868733207)
                ·
                  refine ⟨3197009973234617803099811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131339982156411868733207 3197009973234617803099811)
                  ·
                    refine ⟨4795514959851926704649717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3197009973234617803099811 4795514959851926704649717)
                    ·
                      refine ⟨449579527486118128560911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4795514959851926704649717 449579527486118128560911)
                      ·
                        rfl

theorem cell23_875553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_875553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875553 prefixEnd_875553 := by exact prefixLift 875553
  have htrace : WordTrace (prefixWord ++ tailWord_875553) baseStart_875553 baseEnd_875553 := by
    simpa [prefixWord, tailWord_875553, baseEnd_875553] using wordTrace_append hprefix tailTrace_875553
  have hstable : (prefixWord ++ tailWord_875553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875553).length < 2 ^ (prefixWord ++ tailWord_875553).sum := by decide
  have hdescent : baseEnd_875553 < baseStart_875553 := by decide
  rcases family_descends (prefixWord ++ tailWord_875553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875570 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_875570 : Nat := 118140960795 + 875570 * 2 ^ 59
def prefixEnd_875570 : Nat := 4983230072969 + 3 ^ 40 * 875570 * 2
def baseEnd_875570 : Nat := 449588256657244562048333

theorem tailTrace_875570 : CollatzResearch.WordTrace tailWord_875570 prefixEnd_875570 449588256657244562048333 := by
  unfold tailWord_875570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983665359491725073996041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21289774291977933530656109 7983665359491725073996041)
  ·
    refine ⟨5987749019618793805497031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7983665359491725073996041 5987749019618793805497031)
    ·
      refine ⟨8981623529428190708245547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987749019618793805497031 8981623529428190708245547)
      ·
        refine ⟨13472435294142286062368321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981623529428190708245547 13472435294142286062368321)
        ·
          refine ⟨10104326470606714546776241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13472435294142286062368321 10104326470606714546776241)
          ·
            refine ⟨7578244852955035910082181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104326470606714546776241 7578244852955035910082181)
            ·
              refine ⟨1420920909929069233140409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7578244852955035910082181 1420920909929069233140409)
              ·
                refine ⟨1065690682446801924855307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420920909929069233140409 1065690682446801924855307)
                ·
                  refine ⟨1598536023670202887282961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065690682446801924855307 1598536023670202887282961)
                  ·
                    refine ⟨1198902017752652165462221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1598536023670202887282961 1198902017752652165462221)
                    ·
                      refine ⟨449588256657244562048333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198902017752652165462221 449588256657244562048333)
                      ·
                        rfl

theorem cell23_875570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_875570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875570 prefixEnd_875570 := by exact prefixLift 875570
  have htrace : WordTrace (prefixWord ++ tailWord_875570) baseStart_875570 baseEnd_875570 := by
    simpa [prefixWord, tailWord_875570, baseEnd_875570] using wordTrace_append hprefix tailTrace_875570
  have hstable : (prefixWord ++ tailWord_875570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875570).length < 2 ^ (prefixWord ++ tailWord_875570).sum := by decide
  have hdescent : baseEnd_875570 < baseStart_875570 := by decide
  rcases family_descends (prefixWord ++ tailWord_875570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875590 : List Nat := [6, 1, 1, 1, 1, 4, 9]
def baseStart_875590 : Nat := 118140960795 + 875590 * 2 ^ 59
def prefixEnd_875590 : Nat := 4983230072969 + 3 ^ 40 * 875590 * 2
def baseEnd_875590 : Nat := 5550599089757215849361

theorem tailTrace_875590 : CollatzResearch.WordTrace tailWord_875590 prefixEnd_875590 5550599089757215849361 := by
  unfold tailWord_875590
  simp only [CollatzResearch.WordTrace]
  refine ⟨997980965559201365991007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21290260598596295807808149 997980965559201365991007)
  ·
    refine ⟨1496971448338802048986511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997980965559201365991007 1496971448338802048986511)
    ·
      refine ⟨2245457172508203073479767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496971448338802048986511 2245457172508203073479767)
      ·
        refine ⟨3368185758762304610219651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245457172508203073479767 3368185758762304610219651)
        ·
          refine ⟨5052278638143456915329477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368185758762304610219651 5052278638143456915329477)
          ·
            refine ⟨947302244651898171624277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5052278638143456915329477 947302244651898171624277)
            ·
              refine ⟨5550599089757215849361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 947302244651898171624277 5550599089757215849361)
              ·
                rfl

theorem cell23_875590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 9].length) (baseStart_875590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875590 prefixEnd_875590 := by exact prefixLift 875590
  have htrace : WordTrace (prefixWord ++ tailWord_875590) baseStart_875590 baseEnd_875590 := by
    simpa [prefixWord, tailWord_875590, baseEnd_875590] using wordTrace_append hprefix tailTrace_875590
  have hstable : (prefixWord ++ tailWord_875590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875590).length < 2 ^ (prefixWord ++ tailWord_875590).sum := by decide
  have hdescent : baseEnd_875590 < baseStart_875590 := by decide
  rcases family_descends (prefixWord ++ tailWord_875590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875596 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_875596 : Nat := 118140960795 + 875596 * 2 ^ 59
def prefixEnd_875596 : Nat := 4983230072969 + 3 ^ 40 * 875596 * 2
def baseEnd_875596 : Nat := 449601607154261460323213

theorem tailTrace_875596 : CollatzResearch.WordTrace tailWord_875596 prefixEnd_875596 449601607154261460323213 := by
  unfold tailWord_875596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967804867936353368215321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21290406490581804490953761 15967804867936353368215321)
  ·
    refine ⟨11975853650952265026161491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15967804867936353368215321 11975853650952265026161491)
    ·
      refine ⟨17963780476428397539242237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11975853650952265026161491 17963780476428397539242237)
      ·
        refine ⟨6736417678660649077215839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17963780476428397539242237 6736417678660649077215839)
        ·
          refine ⟨10104626517990973615823759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736417678660649077215839 10104626517990973615823759)
          ·
            refine ⟨15156939776986460423735639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104626517990973615823759 15156939776986460423735639)
            ·
              refine ⟨22735409665479690635603459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156939776986460423735639 22735409665479690635603459)
              ·
                refine ⟨34103114498219535953405189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22735409665479690635603459 34103114498219535953405189)
                ·
                  refine ⟨6394333968416162991263473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34103114498219535953405189 6394333968416162991263473)
                  ·
                    refine ⟨4795750476312122243447605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6394333968416162991263473 4795750476312122243447605)
                    ·
                      refine ⟨449601607154261460323213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4795750476312122243447605 449601607154261460323213)
                      ·
                        rfl

theorem cell23_875596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_875596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875596 prefixEnd_875596 := by exact prefixLift 875596
  have htrace : WordTrace (prefixWord ++ tailWord_875596) baseStart_875596 baseEnd_875596 := by
    simpa [prefixWord, tailWord_875596, baseEnd_875596] using wordTrace_append hprefix tailTrace_875596
  have hstable : (prefixWord ++ tailWord_875596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875596).length < 2 ^ (prefixWord ++ tailWord_875596).sum := by decide
  have hdescent : baseEnd_875596 < baseStart_875596 := by decide
  rcases family_descends (prefixWord ++ tailWord_875596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875616 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_875616 : Nat := 118140960795 + 875616 * 2 ^ 59
def prefixEnd_875616 : Nat := 4983230072969 + 3 ^ 40 * 875616 * 2
def baseEnd_875616 : Nat := 149870625589117127357707

theorem tailTrace_875616 : CollatzResearch.WordTrace tailWord_875616 prefixEnd_875616 149870625589117127357707 := by
  unfold tailWord_875616
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968169597900125076079351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21290892797200166768105801 15968169597900125076079351)
  ·
    refine ⟨23952254396850187614119027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15968169597900125076079351 23952254396850187614119027)
    ·
      refine ⟨35928381595275281421178541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23952254396850187614119027 35928381595275281421178541)
      ·
        refine ⟨13473143098228230532941953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35928381595275281421178541 13473143098228230532941953)
        ·
          refine ⟨10104857323671172899706465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13473143098228230532941953 10104857323671172899706465)
          ·
            refine ⟨7578642992753379674779849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104857323671172899706465 7578642992753379674779849)
            ·
              refine ⟨5683982244565034756084887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7578642992753379674779849 5683982244565034756084887)
              ·
                refine ⟨8525973366847552134127331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683982244565034756084887 8525973366847552134127331)
                ·
                  refine ⟨12788960050271328201190997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525973366847552134127331 12788960050271328201190997)
                  ·
                    refine ⟨149870625589117127357707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12788960050271328201190997 149870625589117127357707)
                    ·
                      rfl

theorem cell23_875616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_875616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875616 prefixEnd_875616 := by exact prefixLift 875616
  have htrace : WordTrace (prefixWord ++ tailWord_875616) baseStart_875616 baseEnd_875616 := by
    simpa [prefixWord, tailWord_875616, baseEnd_875616] using wordTrace_append hprefix tailTrace_875616
  have hstable : (prefixWord ++ tailWord_875616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875616).length < 2 ^ (prefixWord ++ tailWord_875616).sum := by decide
  have hdescent : baseEnd_875616 < baseStart_875616 := by decide
  rcases family_descends (prefixWord ++ tailWord_875616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875617 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_875617 : Nat := 118140960795 + 875617 * 2 ^ 59
def prefixEnd_875617 : Nat := 4983230072969 + 3 ^ 40 * 875617 * 2
def baseEnd_875617 : Nat := 449612390248005878160617

theorem tailTrace_875617 : CollatzResearch.WordTrace tailWord_875617 prefixEnd_875617 449612390248005878160617 := by
  unfold tailWord_875617
  simp only [CollatzResearch.WordTrace]
  refine ⟨31936375668796627322945105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21290917112531084881963403 31936375668796627322945105)
  ·
    refine ⟨23952281751597470492208829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31936375668796627322945105 23952281751597470492208829)
    ·
      refine ⟨8982105656849051434578311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23952281751597470492208829 8982105656849051434578311)
      ·
        refine ⟨13473158485273577151867467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982105656849051434578311 13473158485273577151867467)
        ·
          refine ⟨20209737727910365727801201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473158485273577151867467 20209737727910365727801201)
          ·
            refine ⟨15157303295932774295850901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20209737727910365727801201 15157303295932774295850901)
            ·
              refine ⟨710498591996848795118011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15157303295932774295850901 710498591996848795118011)
              ·
                refine ⟨1065747887995273192677017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710498591996848795118011 1065747887995273192677017)
                ·
                  refine ⟨799310915996454894507763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065747887995273192677017 799310915996454894507763)
                  ·
                    refine ⟨1198966373994682341761645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799310915996454894507763 1198966373994682341761645)
                    ·
                      refine ⟨449612390248005878160617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1198966373994682341761645 449612390248005878160617)
                      ·
                        rfl

theorem cell23_875617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_875617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875617 prefixEnd_875617 := by exact prefixLift 875617
  have htrace : WordTrace (prefixWord ++ tailWord_875617) baseStart_875617 baseEnd_875617 := by
    simpa [prefixWord, tailWord_875617, baseEnd_875617] using wordTrace_append hprefix tailTrace_875617
  have hstable : (prefixWord ++ tailWord_875617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875617).length < 2 ^ (prefixWord ++ tailWord_875617).sum := by decide
  have hdescent : baseEnd_875617 < baseStart_875617 := by decide
  rcases family_descends (prefixWord ++ tailWord_875617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875640 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_875640 : Nat := 118140960795 + 875640 * 2 ^ 59
def prefixEnd_875640 : Nat := 4983230072969 + 3 ^ 40 * 875640 * 2
def baseEnd_875640 : Nat := 449624200303059288173011

theorem tailTrace_875640 : CollatzResearch.WordTrace tailWord_875640 prefixEnd_875640 449624200303059288173011 := by
  unfold tailWord_875640
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968607273856651125516187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21291476365142201500688249 15968607273856651125516187)
  ·
    refine ⟨23952910910784976688274281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15968607273856651125516187 23952910910784976688274281)
    ·
      refine ⟨17964683183088732516205711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23952910910784976688274281 17964683183088732516205711)
      ·
        refine ⟨26947024774633098774308567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17964683183088732516205711 26947024774633098774308567)
        ·
          refine ⟨40420537161949648161462851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26947024774633098774308567 40420537161949648161462851)
          ·
            refine ⟨60630805742924472242194277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40420537161949648161462851 60630805742924472242194277)
            ·
              refine ⟨11368276076798338545411427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60630805742924472242194277 11368276076798338545411427)
              ·
                refine ⟨17052414115197507818117141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11368276076798338545411427 17052414115197507818117141)
                ·
                  refine ⟨799331911649883178974241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17052414115197507818117141 799331911649883178974241)
                  ·
                    refine ⟨599498933737412384230681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799331911649883178974241 599498933737412384230681)
                    ·
                      refine ⟨449624200303059288173011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599498933737412384230681 449624200303059288173011)
                      ·
                        rfl

theorem cell23_875640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_875640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875640 prefixEnd_875640 := by exact prefixLift 875640
  have htrace : WordTrace (prefixWord ++ tailWord_875640) baseStart_875640 baseEnd_875640 := by
    simpa [prefixWord, tailWord_875640, baseEnd_875640] using wordTrace_append hprefix tailTrace_875640
  have hstable : (prefixWord ++ tailWord_875640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875640).length < 2 ^ (prefixWord ++ tailWord_875640).sum := by decide
  have hdescent : baseEnd_875640 < baseStart_875640 := by decide
  rcases family_descends (prefixWord ++ tailWord_875640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875657 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 2, 2, 2]
def baseStart_875657 : Nat := 118140960795 + 875657 * 2 ^ 59
def prefixEnd_875657 : Nat := 4983230072969 + 3 ^ 40 * 875657 * 2
def baseEnd_875657 : Nat := 449632929474185721660433

theorem tailTrace_875657 : CollatzResearch.WordTrace tailWord_875657 prefixEnd_875657 449632929474185721660433 := by
  unfold tailWord_875657
  simp only [CollatzResearch.WordTrace]
  refine ⟨31937834588651714154401225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21291889725767809436267483 31937834588651714154401225)
  ·
    refine ⟨23953375941488785615800919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31937834588651714154401225 23953375941488785615800919)
    ·
      refine ⟨35930063912233178423701379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23953375941488785615800919 35930063912233178423701379)
      ·
        refine ⟨53895095868349767635552069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35930063912233178423701379 53895095868349767635552069)
        ·
          refine ⟨10105330475315581431666013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53895095868349767635552069 10105330475315581431666013)
          ·
            refine ⟨3789498928243343036874755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10105330475315581431666013 3789498928243343036874755)
            ·
              refine ⟨5684248392365014555312133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789498928243343036874755 5684248392365014555312133)
              ·
                refine ⟨1065796573568440229121025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5684248392365014555312133 1065796573568440229121025)
                ·
                  refine ⟨799347430176330171840769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065796573568440229121025 799347430176330171840769)
                  ·
                    refine ⟨599510572632247628880577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799347430176330171840769 599510572632247628880577)
                    ·
                      refine ⟨449632929474185721660433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599510572632247628880577 449632929474185721660433)
                      ·
                        rfl

theorem cell23_875657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2, 2].length) (baseStart_875657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875657 prefixEnd_875657 := by exact prefixLift 875657
  have htrace : WordTrace (prefixWord ++ tailWord_875657) baseStart_875657 baseEnd_875657 := by
    simpa [prefixWord, tailWord_875657, baseEnd_875657] using wordTrace_append hprefix tailTrace_875657
  have hstable : (prefixWord ++ tailWord_875657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875657).length < 2 ^ (prefixWord ++ tailWord_875657).sum := by decide
  have hdescent : baseEnd_875657 < baseStart_875657 := by decide
  rcases family_descends (prefixWord ++ tailWord_875657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875674 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_875674 : Nat := 118140960795 + 875674 * 2 ^ 59
def prefixEnd_875674 : Nat := 4983230072969 + 3 ^ 40 * 875674 * 2
def baseEnd_875674 : Nat := 449641658645312155147855

theorem tailTrace_875674 : CollatzResearch.WordTrace tailWord_875674 prefixEnd_875674 449641658645312155147855 := by
  unfold tailWord_875674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984613657397531514442519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21292303086393417371846717 7984613657397531514442519)
  ·
    refine ⟨11976920486096297271663779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7984613657397531514442519 11976920486096297271663779)
    ·
      refine ⟨17965380729144445907495669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11976920486096297271663779 17965380729144445907495669)
      ·
        refine ⟨1684254443357291803827719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17965380729144445907495669 1684254443357291803827719)
        ·
          refine ⟨2526381665035937705741579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684254443357291803827719 2526381665035937705741579)
          ·
            refine ⟨3789572497553906558612369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526381665035937705741579 3789572497553906558612369)
            ·
              refine ⟨2842179373165429918959277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789572497553906558612369 2842179373165429918959277)
              ·
                refine ⟨1065817264937036219609729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842179373165429918959277 1065817264937036219609729)
                ·
                  refine ⟨799362948702777164707297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065817264937036219609729 799362948702777164707297)
                  ·
                    refine ⟨599522211527082873530473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799362948702777164707297 599522211527082873530473)
                    ·
                      refine ⟨449641658645312155147855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599522211527082873530473 449641658645312155147855)
                      ·
                        rfl

theorem cell23_875674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_875674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875674 prefixEnd_875674 := by exact prefixLift 875674
  have htrace : WordTrace (prefixWord ++ tailWord_875674) baseStart_875674 baseEnd_875674 := by
    simpa [prefixWord, tailWord_875674, baseEnd_875674] using wordTrace_append hprefix tailTrace_875674
  have hstable : (prefixWord ++ tailWord_875674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875674).length < 2 ^ (prefixWord ++ tailWord_875674).sum := by decide
  have hdescent : baseEnd_875674 < baseStart_875674 := by decide
  rcases family_descends (prefixWord ++ tailWord_875674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875697 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 5]
def baseStart_875697 : Nat := 118140960795 + 875697 * 2 ^ 59
def prefixEnd_875697 : Nat := 4983230072969 + 3 ^ 40 * 875697 * 2
def baseEnd_875697 : Nat := 49961496522262840573361

theorem tailTrace_875697 : CollatzResearch.WordTrace tailWord_875697 prefixEnd_875697 49961496522262840573361 := by
  unfold tailWord_875697
  simp only [CollatzResearch.WordTrace]
  refine ⟨31939293508506800985857345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21292862339004533990571563 31939293508506800985857345)
  ·
    refine ⟨23954470131380100739393009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31939293508506800985857345 23954470131380100739393009)
    ·
      refine ⟨17965852598535075554544757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23954470131380100739393009 17965852598535075554544757)
      ·
        refine ⟨1684298681112663333238571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17965852598535075554544757 1684298681112663333238571)
        ·
          refine ⟨2526448021668994999857857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684298681112663333238571 2526448021668994999857857)
          ·
            refine ⟨1894836016251746249893393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2526448021668994999857857 1894836016251746249893393)
            ·
              refine ⟨1421127012188809687420045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894836016251746249893393 1421127012188809687420045)
              ·
                refine ⟨532922629570803632782517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421127012188809687420045 532922629570803632782517)
                ·
                  refine ⟨49961496522262840573361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532922629570803632782517 49961496522262840573361)
                  ·
                    rfl

theorem cell23_875697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 5].length) (baseStart_875697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875697 prefixEnd_875697 := by exact prefixLift 875697
  have htrace : WordTrace (prefixWord ++ tailWord_875697) baseStart_875697 baseEnd_875697 := by
    simpa [prefixWord, tailWord_875697, baseEnd_875697] using wordTrace_append hprefix tailTrace_875697
  have hstable : (prefixWord ++ tailWord_875697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875697).length < 2 ^ (prefixWord ++ tailWord_875697).sum := by decide
  have hdescent : baseEnd_875697 < baseStart_875697 := by decide
  rcases family_descends (prefixWord ++ tailWord_875697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875714 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_875714 : Nat := 118140960795 + 875714 * 2 ^ 59
def prefixEnd_875714 : Nat := 4983230072969 + 3 ^ 40 * 875714 * 2
def baseEnd_875714 : Nat := 49962466430165777627519

theorem tailTrace_875714 : CollatzResearch.WordTrace tailWord_875714 prefixEnd_875714 49962466430165777627519 := by
  unfold tailWord_875714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984978387361303222306549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21293275699630141926150797 7984978387361303222306549)
  ·
    refine ⟨748591723815122177091239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7984978387361303222306549 748591723815122177091239)
    ·
      refine ⟨1122887585722683265636859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 748591723815122177091239 1122887585722683265636859)
      ·
        refine ⟨1684331378584024898455289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122887585722683265636859 1684331378584024898455289)
        ·
          refine ⟨1263248533938018673841467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1684331378584024898455289 1263248533938018673841467)
          ·
            refine ⟨1894872800907028010762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263248533938018673841467 1894872800907028010762201)
            ·
              refine ⟨1421154600680271008071651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894872800907028010762201 1421154600680271008071651)
              ·
                refine ⟨2131731901020406512107477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421154600680271008071651 2131731901020406512107477)
                ·
                  refine ⟨49962466430165777627519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2131731901020406512107477 49962466430165777627519)
                  ·
                    rfl

theorem cell23_875714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_875714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875714 prefixEnd_875714 := by exact prefixLift 875714
  have htrace : WordTrace (prefixWord ++ tailWord_875714) baseStart_875714 baseEnd_875714 := by
    simpa [prefixWord, tailWord_875714, baseEnd_875714] using wordTrace_append hprefix tailTrace_875714
  have hstable : (prefixWord ++ tailWord_875714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875714).length < 2 ^ (prefixWord ++ tailWord_875714).sum := by decide
  have hdescent : baseEnd_875714 < baseStart_875714 := by decide
  rcases family_descends (prefixWord ++ tailWord_875714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875725 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_875725 : Nat := 118140960795 + 875725 * 2 ^ 59
def prefixEnd_875725 : Nat := 4983230072969 + 3 ^ 40 * 875725 * 2
def baseEnd_875725 : Nat := 449667846158691455610121

theorem tailTrace_875725 : CollatzResearch.WordTrace tailWord_875725 prefixEnd_875725 449667846158691455610121 := by
  unfold tailWord_875725
  simp only [CollatzResearch.WordTrace]
  refine ⟨31940314752405361767876629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21293543168270241178584419 31940314752405361767876629)
  ·
    refine ⟨1497202254019001332869217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31940314752405361767876629 1497202254019001332869217)
    ·
      refine ⟨1122901690514250999651913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1497202254019001332869217 1122901690514250999651913)
      ·
        refine ⟨842176267885688249738935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122901690514250999651913 842176267885688249738935)
        ·
          refine ⟨1263264401828532374608403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842176267885688249738935 1263264401828532374608403)
          ·
            refine ⟨1894896602742798561912605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263264401828532374608403 1894896602742798561912605)
            ·
              refine ⟨710586226028549460717227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1894896602742798561912605 710586226028549460717227)
              ·
                refine ⟨1065879339042824191075841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710586226028549460717227 1065879339042824191075841)
                ·
                  refine ⟨799409504282118143306881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065879339042824191075841 799409504282118143306881)
                  ·
                    refine ⟨599557128211588607480161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799409504282118143306881 599557128211588607480161)
                    ·
                      refine ⟨449667846158691455610121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599557128211588607480161 449667846158691455610121)
                      ·
                        rfl

theorem cell23_875725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_875725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875725 prefixEnd_875725 := by exact prefixLift 875725
  have htrace : WordTrace (prefixWord ++ tailWord_875725) baseStart_875725 baseEnd_875725 := by
    simpa [prefixWord, tailWord_875725, baseEnd_875725] using wordTrace_append hprefix tailTrace_875725
  have hstable : (prefixWord ++ tailWord_875725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875725).length < 2 ^ (prefixWord ++ tailWord_875725).sum := by decide
  have hdescent : baseEnd_875725 < baseStart_875725 := by decide
  rcases family_descends (prefixWord ++ tailWord_875725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875774 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_875774 : Nat := 118140960795 + 875774 * 2 ^ 59
def prefixEnd_875774 : Nat := 4983230072969 + 3 ^ 40 * 875774 * 2
def baseEnd_875774 : Nat := 149897668903587254632465

theorem tailTrace_875774 : CollatzResearch.WordTrace tailWord_875774 prefixEnd_875774 149897668903587254632465 := by
  unfold tailWord_875774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992762741153480392051297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21294734619485228757606917 3992762741153480392051297)
  ·
    refine ⟨2994572055865110294038473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992762741153480392051297 2994572055865110294038473)
    ·
      refine ⟨2245929041898832720528855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2994572055865110294038473 2245929041898832720528855)
      ·
        refine ⟨3368893562848249080793283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245929041898832720528855 3368893562848249080793283)
        ·
          refine ⟨5053340344272373621189925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368893562848249080793283 5053340344272373621189925)
          ·
            refine ⟨947501314551070053973111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5053340344272373621189925 947501314551070053973111)
            ·
              refine ⟨1421251971826605080959667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947501314551070053973111 1421251971826605080959667)
              ·
                refine ⟨2131877957739907621439501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421251971826605080959667 2131877957739907621439501)
                ·
                  refine ⟨799454234152465358039813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2131877957739907621439501 799454234152465358039813)
                  ·
                    refine ⟨149897668903587254632465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799454234152465358039813 149897668903587254632465)
                    ·
                      rfl

theorem cell23_875774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_875774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875774 prefixEnd_875774 := by exact prefixLift 875774
  have htrace : WordTrace (prefixWord ++ tailWord_875774) baseStart_875774 baseEnd_875774 := by
    simpa [prefixWord, tailWord_875774, baseEnd_875774] using wordTrace_append hprefix tailTrace_875774
  have hstable : (prefixWord ++ tailWord_875774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875774).length < 2 ^ (prefixWord ++ tailWord_875774).sum := by decide
  have hdescent : baseEnd_875774 < baseStart_875774 := by decide
  rcases family_descends (prefixWord ++ tailWord_875774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875787 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 6]
def baseStart_875787 : Nat := 118140960795 + 875787 * 2 ^ 59
def prefixEnd_875787 : Nat := 4983230072969 + 3 ^ 40 * 875787 * 2
def baseEnd_875787 : Nat := 49966631328807801448315

theorem tailTrace_875787 : CollatzResearch.WordTrace tailWord_875787 prefixEnd_875787 49966631328807801448315 := by
  unfold tailWord_875787
  simp only [CollatzResearch.WordTrace]
  refine ⟨31942576078180746356633615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21295050718787164237755743 31942576078180746356633615)
  ·
    refine ⟨47913864117271119534950423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31942576078180746356633615 47913864117271119534950423)
    ·
      refine ⟨71870796175906679302425635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47913864117271119534950423 71870796175906679302425635)
      ·
        refine ⟨107806194263860018953638453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71870796175906679302425635 107806194263860018953638453)
        ·
          refine ⟨10106830712236876776903605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107806194263860018953638453 10106830712236876776903605)
          ·
            refine ⟨947515379272207197834713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10106830712236876776903605 947515379272207197834713)
            ·
              refine ⟨710636534454155398376035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947515379272207197834713 710636534454155398376035)
              ·
                refine ⟨1065954801681233097564053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710636534454155398376035 1065954801681233097564053)
                ·
                  refine ⟨49966631328807801448315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1065954801681233097564053 49966631328807801448315)
                  ·
                    rfl

theorem cell23_875787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 6].length) (baseStart_875787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875787 prefixEnd_875787 := by exact prefixLift 875787
  have htrace : WordTrace (prefixWord ++ tailWord_875787) baseStart_875787 baseEnd_875787 := by
    simpa [prefixWord, tailWord_875787, baseEnd_875787] using wordTrace_append hprefix tailTrace_875787
  have hstable : (prefixWord ++ tailWord_875787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875787).length < 2 ^ (prefixWord ++ tailWord_875787).sum := by decide
  have hdescent : baseEnd_875787 < baseStart_875787 := by decide
  rcases family_descends (prefixWord ++ tailWord_875787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875800 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_875800 : Nat := 118140960795 + 875800 * 2 ^ 59
def prefixEnd_875800 : Nat := 4983230072969 + 3 ^ 40 * 875800 * 2
def baseEnd_875800 : Nat := 149902119069259554057425

theorem tailTrace_875800 : CollatzResearch.WordTrace tailWord_875800 prefixEnd_875800 149902119069259554057425 := by
  unfold tailWord_875800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971525113566824788428427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21295366818089099717904569 15971525113566824788428427)
  ·
    refine ⟨23957287670350237182642641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15971525113566824788428427 23957287670350237182642641)
    ·
      refine ⟨17967965752762677886981981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23957287670350237182642641 17967965752762677886981981)
      ·
        refine ⟨6737987157286004207618243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17967965752762677886981981 6737987157286004207618243)
        ·
          refine ⟨10106980735929006311427365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737987157286004207618243 10106980735929006311427365)
          ·
            refine ⟨1895058887986688683392631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10106980735929006311427365 1895058887986688683392631)
            ·
              refine ⟨2842588331980033025088947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895058887986688683392631 2842588331980033025088947)
              ·
                refine ⟨4263882497970049537633421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842588331980033025088947 4263882497970049537633421)
                ·
                  refine ⟨1598955936738768576612533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4263882497970049537633421 1598955936738768576612533)
                  ·
                    refine ⟨149902119069259554057425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1598955936738768576612533 149902119069259554057425)
                    ·
                      rfl

theorem cell23_875800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_875800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875800 prefixEnd_875800 := by exact prefixLift 875800
  have htrace : WordTrace (prefixWord ++ tailWord_875800) baseStart_875800 baseEnd_875800 := by
    simpa [prefixWord, tailWord_875800, baseEnd_875800] using wordTrace_append hprefix tailTrace_875800
  have hstable : (prefixWord ++ tailWord_875800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875800).length < 2 ^ (prefixWord ++ tailWord_875800).sum := by decide
  have hdescent : baseEnd_875800 < baseStart_875800 := by decide
  rcases family_descends (prefixWord ++ tailWord_875800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875840 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_875840 : Nat := 118140960795 + 875840 * 2 ^ 59
def prefixEnd_875840 : Nat := 4983230072969 + 3 ^ 40 * 875840 * 2
def baseEnd_875840 : Nat := 449726896433958505672091

theorem tailTrace_875840 : CollatzResearch.WordTrace tailWord_875840 prefixEnd_875840 449726896433958505672091 := by
  unfold tailWord_875840
  simp only [CollatzResearch.WordTrace]
  refine ⟨15972254573494368204156487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21296339431325824272208649 15972254573494368204156487)
  ·
    refine ⟨23958381860241552306234731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15972254573494368204156487 23958381860241552306234731)
    ·
      refine ⟨35937572790362328459352097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23958381860241552306234731 35937572790362328459352097)
      ·
        refine ⟨26953179592771746344514073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35937572790362328459352097 26953179592771746344514073)
        ·
          refine ⟨20214884694578809758385555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26953179592771746344514073 20214884694578809758385555)
          ·
            refine ⟨30322327041868214637578333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20214884694578809758385555 30322327041868214637578333)
            ·
              refine ⟨11370872640700580489091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30322327041868214637578333 11370872640700580489091875)
              ·
                refine ⟨17056308961050870733637813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370872640700580489091875 17056308961050870733637813)
                ·
                  refine ⟨1599028965098519131278545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17056308961050870733637813 1599028965098519131278545)
                  ·
                    refine ⟨1199271723823889348458909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1599028965098519131278545 1199271723823889348458909)
                    ·
                      refine ⟨449726896433958505672091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1199271723823889348458909 449726896433958505672091)
                      ·
                        rfl

theorem cell23_875840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_875840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875840 prefixEnd_875840 := by exact prefixLift 875840
  have htrace : WordTrace (prefixWord ++ tailWord_875840) baseStart_875840 baseEnd_875840 := by
    simpa [prefixWord, tailWord_875840, baseEnd_875840] using wordTrace_append hprefix tailTrace_875840
  have hstable : (prefixWord ++ tailWord_875840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875840).length < 2 ^ (prefixWord ++ tailWord_875840).sum := by decide
  have hdescent : baseEnd_875840 < baseStart_875840 := by decide
  rcases family_descends (prefixWord ++ tailWord_875840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875847 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 2, 4]
def baseStart_875847 : Nat := 118140960795 + 875847 * 2 ^ 59
def prefixEnd_875847 : Nat := 4983230072969 + 3 ^ 40 * 875847 * 2
def baseEnd_875847 : Nat := 149910163599513326094853

theorem tailTrace_875847 : CollatzResearch.WordTrace tailWord_875847 prefixEnd_875847 149910163599513326094853 := by
  unfold tailWord_875847
  simp only [CollatzResearch.WordTrace]
  refine ⟨31944764457963376603817795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21296509638642251069211863 31944764457963376603817795)
  ·
    refine ⟨47917146686945064905726693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31944764457963376603817795 47917146686945064905726693)
    ·
      refine ⟨8984465003802199669823755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47917146686945064905726693 8984465003802199669823755)
      ·
        refine ⟨13476697505703299504735633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984465003802199669823755 13476697505703299504735633)
        ·
          refine ⟨10107523129277474628551725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13476697505703299504735633 10107523129277474628551725)
          ·
            refine ⟨3790321173479052985706897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10107523129277474628551725 3790321173479052985706897)
            ·
              refine ⟨2842740880109289739280173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790321173479052985706897 2842740880109289739280173)
              ·
                refine ⟨1066027830040983652230065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842740880109289739280173 1066027830040983652230065)
                ·
                  refine ⟨799520872530737739172549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066027830040983652230065 799520872530737739172549)
                  ·
                    refine ⟨149910163599513326094853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799520872530737739172549 149910163599513326094853)
                    ·
                      rfl

theorem cell23_875847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_875847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875847 prefixEnd_875847 := by exact prefixLift 875847
  have htrace : WordTrace (prefixWord ++ tailWord_875847) baseStart_875847 baseEnd_875847 := by
    simpa [prefixWord, tailWord_875847, baseEnd_875847] using wordTrace_append hprefix tailTrace_875847
  have hstable : (prefixWord ++ tailWord_875847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875847).length < 2 ^ (prefixWord ++ tailWord_875847).sum := by decide
  have hdescent : baseEnd_875847 < baseStart_875847 := by decide
  rcases family_descends (prefixWord ++ tailWord_875847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875854 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_875854 : Nat := 118140960795 + 875854 * 2 ^ 59
def prefixEnd_875854 : Nat := 4983230072969 + 3 ^ 40 * 875854 * 2
def baseEnd_875854 : Nat := 449734085163121450897027

theorem tailTrace_875854 : CollatzResearch.WordTrace tailWord_875854 prefixEnd_875854 449734085163121450897027 := by
  unfold tailWord_875854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993127471117252099915327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21296679845958677866215077 3993127471117252099915327)
  ·
    refine ⟨5989691206675878149872991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993127471117252099915327 5989691206675878149872991)
    ·
      refine ⟨8984536810013817224809487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989691206675878149872991 8984536810013817224809487)
      ·
        refine ⟨13476805215020725837214231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984536810013817224809487 13476805215020725837214231)
        ·
          refine ⟨20215207822531088755821347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13476805215020725837214231 20215207822531088755821347)
          ·
            refine ⟨30322811733796633133732021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20215207822531088755821347 30322811733796633133732021)
            ·
              refine ⟨2842763600043434356287377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30322811733796633133732021 2842763600043434356287377)
              ·
                refine ⟨2132072700032575767215533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842763600043434356287377 2132072700032575767215533)
                ·
                  refine ⟨799527262512215912705825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2132072700032575767215533 799527262512215912705825)
                  ·
                    refine ⟨599645446884161934529369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799527262512215912705825 599645446884161934529369)
                    ·
                      refine ⟨449734085163121450897027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599645446884161934529369 449734085163121450897027)
                      ·
                        rfl

theorem cell23_875854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_875854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875854 prefixEnd_875854 := by exact prefixLift 875854
  have htrace : WordTrace (prefixWord ++ tailWord_875854) baseStart_875854 baseEnd_875854 := by
    simpa [prefixWord, tailWord_875854, baseEnd_875854] using wordTrace_append hprefix tailTrace_875854
  have hstable : (prefixWord ++ tailWord_875854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875854).length < 2 ^ (prefixWord ++ tailWord_875854).sum := by decide
  have hdescent : baseEnd_875854 < baseStart_875854 := by decide
  rcases family_descends (prefixWord ++ tailWord_875854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875857 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_875857 : Nat := 118140960795 + 875857 * 2 ^ 59
def prefixEnd_875857 : Nat := 4983230072969 + 3 ^ 40 * 875857 * 2
def baseEnd_875857 : Nat := 449735625605084939159513

theorem tailTrace_875857 : CollatzResearch.WordTrace tailWord_875857 prefixEnd_875857 449735625605084939159513 := by
  unfold tailWord_875857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31945129187927148311681825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21296752791951432207787883 31945129187927148311681825)
  ·
    refine ⟨23958846890945361233761369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31945129187927148311681825 23958846890945361233761369)
    ·
      refine ⟨17969135168209020925321027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23958846890945361233761369 17969135168209020925321027)
      ·
        refine ⟨26953702752313531387981541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17969135168209020925321027 26953702752313531387981541)
        ·
          refine ⟨5053819266058787135246539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26953702752313531387981541 5053819266058787135246539)
          ·
            refine ⟨7580728899088180702869809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053819266058787135246539 7580728899088180702869809)
            ·
              refine ⟨5685546674316135527152357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7580728899088180702869809 5685546674316135527152357)
              ·
                refine ⟨1066040001434275411341067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5685546674316135527152357 1066040001434275411341067)
                ·
                  refine ⟨1599060002151413117011601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066040001434275411341067 1599060002151413117011601)
                  ·
                    refine ⟨1199295001613559837758701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1599060002151413117011601 1199295001613559837758701)
                    ·
                      refine ⟨449735625605084939159513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1199295001613559837758701 449735625605084939159513)
                      ·
                        rfl

theorem cell23_875857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_875857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875857 prefixEnd_875857 := by exact prefixLift 875857
  have htrace : WordTrace (prefixWord ++ tailWord_875857) baseStart_875857 baseEnd_875857 := by
    simpa [prefixWord, tailWord_875857, baseEnd_875857] using wordTrace_append hprefix tailTrace_875857
  have hstable : (prefixWord ++ tailWord_875857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875857).length < 2 ^ (prefixWord ++ tailWord_875857).sum := by decide
  have hdescent : baseEnd_875857 < baseStart_875857 := by decide
  rcases family_descends (prefixWord ++ tailWord_875857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875874 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_875874 : Nat := 118140960795 + 875874 * 2 ^ 59
def prefixEnd_875874 : Nat := 4983230072969 + 3 ^ 40 * 875874 * 2
def baseEnd_875874 : Nat := 449744354776211372646935

theorem tailTrace_875874 : CollatzResearch.WordTrace tailWord_875874 prefixEnd_875874 449744354776211372646935 := by
  unfold tailWord_875874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986437307216390053762669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21297166152577040143367117 7986437307216390053762669)
  ·
    refine ⟨2994913990206146270161001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7986437307216390053762669 2994913990206146270161001)
    ·
      refine ⟨2246185492654609702620751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2994913990206146270161001 2246185492654609702620751)
      ·
        refine ⟨3369278238981914553931127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246185492654609702620751 3369278238981914553931127)
        ·
          refine ⟨5053917358472871830896691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369278238981914553931127 5053917358472871830896691)
          ·
            refine ⟨7580876037709307746345037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053917358472871830896691 7580876037709307746345037)
            ·
              refine ⟨2842828514140990404879389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7580876037709307746345037 2842828514140990404879389)
              ·
                refine ⟨1066060692802871401829771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842828514140990404879389 1066060692802871401829771)
                ·
                  refine ⟨1599091039204307102744657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066060692802871401829771 1599091039204307102744657)
                  ·
                    refine ⟨1199318279403230327058493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1599091039204307102744657 1199318279403230327058493)
                    ·
                      refine ⟨449744354776211372646935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1199318279403230327058493 449744354776211372646935)
                      ·
                        rfl

theorem cell23_875874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_875874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875874 prefixEnd_875874 := by exact prefixLift 875874
  have htrace : WordTrace (prefixWord ++ tailWord_875874) baseStart_875874 baseEnd_875874 := by
    simpa [prefixWord, tailWord_875874, baseEnd_875874] using wordTrace_append hprefix tailTrace_875874
  have hstable : (prefixWord ++ tailWord_875874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875874).length < 2 ^ (prefixWord ++ tailWord_875874).sum := by decide
  have hdescent : baseEnd_875874 < baseStart_875874 := by decide
  rcases family_descends (prefixWord ++ tailWord_875874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875883 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7]
def baseStart_875883 : Nat := 118140960795 + 875883 * 2 ^ 59
def prefixEnd_875883 : Nat := 4983230072969 + 3 ^ 40 * 875883 * 2
def baseEnd_875883 : Nat := 449748976102101837434393

theorem tailTrace_875883 : CollatzResearch.WordTrace tailWord_875883 prefixEnd_875883 449748976102101837434393 := by
  unfold tailWord_875883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946077485832954752128303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21297384990555303168085535 31946077485832954752128303)
  ·
    refine ⟨47919116228749432128192455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31946077485832954752128303 47919116228749432128192455)
    ·
      refine ⟨71878674343124148192288683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47919116228749432128192455 71878674343124148192288683)
      ·
        refine ⟨107818011514686222288433025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71878674343124148192288683 107818011514686222288433025)
        ·
          refine ⟨80863508636014666716324769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107818011514686222288433025 80863508636014666716324769)
          ·
            refine ⟨60647631477011000037243577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80863508636014666716324769 60647631477011000037243577)
            ·
              refine ⟨45485723607758250027932683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60647631477011000037243577 45485723607758250027932683)
              ·
                refine ⟨68228585411637375041899025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45485723607758250027932683 68228585411637375041899025)
                ·
                  refine ⟨51171439058728031281424269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68228585411637375041899025 51171439058728031281424269)
                  ·
                    refine ⟨19189289647023011730534101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51171439058728031281424269 19189289647023011730534101)
                    ·
                      refine ⟨449748976102101837434393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19189289647023011730534101 449748976102101837434393)
                      ·
                        rfl

theorem cell23_875883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_875883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875883 prefixEnd_875883 := by exact prefixLift 875883
  have htrace : WordTrace (prefixWord ++ tailWord_875883) baseStart_875883 baseEnd_875883 := by
    simpa [prefixWord, tailWord_875883, baseEnd_875883] using wordTrace_append hprefix tailTrace_875883
  have hstable : (prefixWord ++ tailWord_875883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875883).length < 2 ^ (prefixWord ++ tailWord_875883).sum := by decide
  have hdescent : baseEnd_875883 < baseStart_875883 := by decide
  rcases family_descends (prefixWord ++ tailWord_875883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875887 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 3]
def baseStart_875887 : Nat := 118140960795 + 875887 * 2 ^ 59
def prefixEnd_875887 : Nat := 4983230072969 + 3 ^ 40 * 875887 * 2
def baseEnd_875887 : Nat := 449751030024719821784375

theorem tailTrace_875887 : CollatzResearch.WordTrace tailWord_875887 prefixEnd_875887 449751030024719821784375 := by
  unfold tailWord_875887
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946223377818463435273915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21297482251878975623515943 31946223377818463435273915)
  ·
    refine ⟨47919335066727695152910873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31946223377818463435273915 47919335066727695152910873)
    ·
      refine ⟨35939501300045771364683155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47919335066727695152910873 35939501300045771364683155)
      ·
        refine ⟨53909251950068657047024733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35939501300045771364683155 53909251950068657047024733)
        ·
          refine ⟨20215969481275746392634275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53909251950068657047024733 20215969481275746392634275)
          ·
            refine ⟨30323954221913619588951413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20215969481275746392634275 30323954221913619588951413)
            ·
              refine ⟨2842870708304401836464195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30323954221913619588951413 2842870708304401836464195)
              ·
                refine ⟨4264306062456602754696293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842870708304401836464195 4264306062456602754696293)
                ·
                  refine ⟨799557386710613016505555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4264306062456602754696293 799557386710613016505555)
                  ·
                    refine ⟨1199336080065919524758333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799557386710613016505555 1199336080065919524758333)
                    ·
                      refine ⟨449751030024719821784375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1199336080065919524758333 449751030024719821784375)
                      ·
                        rfl

theorem cell23_875887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_875887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875887 prefixEnd_875887 := by exact prefixLift 875887
  have htrace : WordTrace (prefixWord ++ tailWord_875887) baseStart_875887 baseEnd_875887 := by
    simpa [prefixWord, tailWord_875887, baseEnd_875887] using wordTrace_append hprefix tailTrace_875887
  have hstable : (prefixWord ++ tailWord_875887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875887).length < 2 ^ (prefixWord ++ tailWord_875887).sum := by decide
  have hdescent : baseEnd_875887 < baseStart_875887 := by decide
  rcases family_descends (prefixWord ++ tailWord_875887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875897 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 5, 3, 2]
def baseStart_875897 : Nat := 118140960795 + 875897 * 2 ^ 59
def prefixEnd_875897 : Nat := 4983230072969 + 3 ^ 40 * 875897 * 2
def baseEnd_875897 : Nat := 449756164831264782659329

theorem tailTrace_875897 : CollatzResearch.WordTrace tailWord_875897 prefixEnd_875897 449756164831264782659329 := by
  unfold tailWord_875897
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946588107782235143137945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21297725405188156762091963 31946588107782235143137945)
  ·
    refine ⟨23959941080836676357353459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31946588107782235143137945 23959941080836676357353459)
    ·
      refine ⟨35939911621255014536030189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23959941080836676357353459 35939911621255014536030189)
      ·
        refine ⟨13477466857970630451011321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35939911621255014536030189 13477466857970630451011321)
        ·
          refine ⟨10108100143477972838258491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13477466857970630451011321 10108100143477972838258491)
          ·
            refine ⟨15162150215216959257387737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10108100143477972838258491 15162150215216959257387737)
            ·
              refine ⟨11371612661412719443040803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15162150215216959257387737 11371612661412719443040803)
              ·
                refine ⟨17057418992119079164561205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371612661412719443040803 17057418992119079164561205)
                ·
                  refine ⟨1599133030511163671677613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17057418992119079164561205 1599133030511163671677613)
                  ·
                    refine ⟨599674886441686376879105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599133030511163671677613 599674886441686376879105)
                    ·
                      refine ⟨449756164831264782659329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599674886441686376879105 449756164831264782659329)
                      ·
                        rfl

theorem cell23_875897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_875897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875897 prefixEnd_875897 := by exact prefixLift 875897
  have htrace : WordTrace (prefixWord ++ tailWord_875897) baseStart_875897 baseEnd_875897 := by
    simpa [prefixWord, tailWord_875897, baseEnd_875897] using wordTrace_append hprefix tailTrace_875897
  have hstable : (prefixWord ++ tailWord_875897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875897).length < 2 ^ (prefixWord ++ tailWord_875897).sum := by decide
  have hdescent : baseEnd_875897 < baseStart_875897 := by decide
  rcases family_descends (prefixWord ++ tailWord_875897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875922 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_875922 : Nat := 118140960795 + 875922 * 2 ^ 59
def prefixEnd_875922 : Nat := 4983230072969 + 3 ^ 40 * 875922 * 2
def baseEnd_875922 : Nat := 449769001847627184846715

theorem tailTrace_875922 : CollatzResearch.WordTrace tailWord_875922 prefixEnd_875922 449769001847627184846715 := by
  unfold tailWord_875922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986874983172916103199505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21298333288461109608532013 7986874983172916103199505)
  ·
    refine ⟨5990156237379687077399629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7986874983172916103199505 5990156237379687077399629)
    ·
      refine ⟨2246308589017382654024861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5990156237379687077399629 2246308589017382654024861)
      ·
        refine ⟨842365720881518495259323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2246308589017382654024861 842365720881518495259323)
        ·
          refine ⟨1263548581322277742888985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842365720881518495259323 1263548581322277742888985)
          ·
            refine ⟨947661435991708307166739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263548581322277742888985 947661435991708307166739)
            ·
              refine ⟨1421492153987562460750109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947661435991708307166739 1421492153987562460750109)
              ·
                refine ⟨533059557745335922781291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421492153987562460750109 533059557745335922781291)
                ·
                  refine ⟨799589336618003884171937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533059557745335922781291 799589336618003884171937)
                  ·
                    refine ⟨599692002463502913128953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 799589336618003884171937 599692002463502913128953)
                    ·
                      refine ⟨449769001847627184846715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599692002463502913128953 449769001847627184846715)
                      ·
                        rfl

theorem cell23_875922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_875922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875922 prefixEnd_875922 := by exact prefixLift 875922
  have htrace : WordTrace (prefixWord ++ tailWord_875922) baseStart_875922 baseEnd_875922 := by
    simpa [prefixWord, tailWord_875922, baseEnd_875922] using wordTrace_append hprefix tailTrace_875922
  have hstable : (prefixWord ++ tailWord_875922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875922).length < 2 ^ (prefixWord ++ tailWord_875922).sum := by decide
  have hdescent : baseEnd_875922 < baseStart_875922 := by decide
  rcases family_descends (prefixWord ++ tailWord_875922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875927 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_875927 : Nat := 118140960795 + 875927 * 2 ^ 59
def prefixEnd_875927 : Nat := 4983230072969 + 3 ^ 40 * 875927 * 2
def baseEnd_875927 : Nat := 449771569250899665284191

theorem tailTrace_875927 : CollatzResearch.WordTrace tailWord_875927 prefixEnd_875927 449771569250899665284191 := by
  unfold tailWord_875927
  simp only [CollatzResearch.WordTrace]
  refine ⟨31947682297673550266730035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21298454865115700177820023 31947682297673550266730035)
  ·
    refine ⟨47921523446510325400095053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31947682297673550266730035 47921523446510325400095053)
    ·
      refine ⟨17970571292441372025035645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47921523446510325400095053 17970571292441372025035645)
      ·
        refine ⟨6738964234665514509388367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17970571292441372025035645 6738964234665514509388367)
        ·
          refine ⟨10108446351998271764082551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6738964234665514509388367 10108446351998271764082551)
          ·
            refine ⟨15162669527997407646123827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10108446351998271764082551 15162669527997407646123827)
            ·
              refine ⟨22744004291996111469185741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15162669527997407646123827 22744004291996111469185741)
              ·
                refine ⟨8529001609498541800944653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22744004291996111469185741 8529001609498541800944653)
                ·
                  refine ⟨3198375603561953175354245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8529001609498541800944653 3198375603561953175354245)
                  ·
                    refine ⟨599695425667866220378921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3198375603561953175354245 599695425667866220378921)
                    ·
                      refine ⟨449771569250899665284191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599695425667866220378921 449771569250899665284191)
                      ·
                        rfl

theorem cell23_875927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_875927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_875927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_875927 prefixEnd_875927 := by exact prefixLift 875927
  have htrace : WordTrace (prefixWord ++ tailWord_875927) baseStart_875927 baseEnd_875927 := by
    simpa [prefixWord, tailWord_875927, baseEnd_875927] using wordTrace_append hprefix tailTrace_875927
  have hstable : (prefixWord ++ tailWord_875927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875927).length < 2 ^ (prefixWord ++ tailWord_875927).sum := by decide
  have hdescent : baseEnd_875927 < baseStart_875927 := by decide
  rcases family_descends (prefixWord ++ tailWord_875927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876001 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 5]
def baseStart_876001 : Nat := 118140960795 + 876001 * 2 ^ 59
def prefixEnd_876001 : Nat := 4983230072969 + 3 ^ 40 * 876001 * 2
def baseEnd_876001 : Nat := 49978840757703597306539

theorem tailTrace_876001 : CollatzResearch.WordTrace tailWord_876001 prefixEnd_876001 49978840757703597306539 := by
  unfold tailWord_876001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31950381299405460904923857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21300254199603640603282571 31950381299405460904923857)
  ·
    refine ⟨23962785974554095678692893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31950381299405460904923857 23962785974554095678692893)
    ·
      refine ⟨8986044740457785879509835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23962785974554095678692893 8986044740457785879509835)
      ·
        refine ⟨13479067110686678819264753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986044740457785879509835 13479067110686678819264753)
        ·
          refine ⟨10109300333015009114448565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13479067110686678819264753 10109300333015009114448565)
          ·
            refine ⟨947746906220157104479553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10109300333015009114448565 947746906220157104479553)
            ·
              refine ⟨710810179665117828359665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947746906220157104479553 710810179665117828359665)
              ·
                refine ⟨533107634748838371269749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710810179665117828359665 533107634748838371269749)
                ·
                  refine ⟨49978840757703597306539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 533107634748838371269749 49978840757703597306539)
                  ·
                    rfl

theorem cell23_876001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 5].length) (baseStart_876001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876001 prefixEnd_876001 := by exact prefixLift 876001
  have htrace : WordTrace (prefixWord ++ tailWord_876001) baseStart_876001 baseEnd_876001 := by
    simpa [prefixWord, tailWord_876001, baseEnd_876001] using wordTrace_append hprefix tailTrace_876001
  have hstable : (prefixWord ++ tailWord_876001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876001).length < 2 ^ (prefixWord ++ tailWord_876001).sum := by decide
  have hdescent : baseEnd_876001 < baseStart_876001 := by decide
  rcases family_descends (prefixWord ++ tailWord_876001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876007 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_876007 : Nat := 118140960795 + 876007 * 2 ^ 59
def prefixEnd_876007 : Nat := 4983230072969 + 3 ^ 40 * 876007 * 2
def baseEnd_876007 : Nat := 449812647703259352283823

theorem tailTrace_876007 : CollatzResearch.WordTrace tailWord_876007 prefixEnd_876007 449812647703259352283823 := by
  unfold tailWord_876007
  simp only [CollatzResearch.WordTrace]
  refine ⟨31950600137383723929642275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21300400091589149286428183 31950600137383723929642275)
  ·
    refine ⟨47925900206075585894463413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31950600137383723929642275 47925900206075585894463413)
    ·
      refine ⟨4493053144319586177605945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47925900206075585894463413 4493053144319586177605945)
      ·
        refine ⟨3369789858239689633204459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493053144319586177605945 3369789858239689633204459)
        ·
          refine ⟨5054684787359534449806689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369789858239689633204459 5054684787359534449806689)
          ·
            refine ⟨3791013590519650837355017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054684787359534449806689 3791013590519650837355017)
            ·
              refine ⟨2843260192889738128016263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791013590519650837355017 2843260192889738128016263)
              ·
                refine ⟨4264890289334607192024395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843260192889738128016263 4264890289334607192024395)
                ·
                  refine ⟨6397335434001910788036593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264890289334607192024395 6397335434001910788036593)
                  ·
                    refine ⟨4798001575501433091027445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6397335434001910788036593 4798001575501433091027445)
                    ·
                      refine ⟨449812647703259352283823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4798001575501433091027445 449812647703259352283823)
                      ·
                        rfl

theorem cell23_876007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_876007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876007 prefixEnd_876007 := by exact prefixLift 876007
  have htrace : WordTrace (prefixWord ++ tailWord_876007) baseStart_876007 baseEnd_876007 := by
    simpa [prefixWord, tailWord_876007, baseEnd_876007] using wordTrace_append hprefix tailTrace_876007
  have hstable : (prefixWord ++ tailWord_876007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876007).length < 2 ^ (prefixWord ++ tailWord_876007).sum := by decide
  have hdescent : baseEnd_876007 < baseStart_876007 := by decide
  rcases family_descends (prefixWord ++ tailWord_876007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876027 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 3, 4]
def baseStart_876027 : Nat := 118140960795 + 876027 * 2 ^ 59
def prefixEnd_876027 : Nat := 4983230072969 + 3 ^ 40 * 876027 * 2
def baseEnd_876027 : Nat := 149940972438783091344577

theorem tailTrace_876027 : CollatzResearch.WordTrace tailWord_876027 prefixEnd_876027 149940972438783091344577 := by
  unfold tailWord_876027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31951329597311267345370335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21300886398207511563580223 31951329597311267345370335)
  ·
    refine ⟨47926994395966901018055503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31951329597311267345370335 47926994395966901018055503)
    ·
      refine ⟨71890491593950351527083255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47926994395966901018055503 71890491593950351527083255)
      ·
        refine ⟨107835737390925527290624883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71890491593950351527083255 107835737390925527290624883)
        ·
          refine ⟨161753606086388290935937325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107835737390925527290624883 161753606086388290935937325)
          ·
            refine ⟨60657602282395609100976497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161753606086388290935937325 60657602282395609100976497)
            ·
              refine ⟨45493201711796706825732373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60657602282395609100976497 45493201711796706825732373)
              ·
                refine ⟨2132493830240470632456205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45493201711796706825732373 2132493830240470632456205)
                ·
                  refine ⟨799685186340176487171077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2132493830240470632456205 799685186340176487171077)
                  ·
                    refine ⟨149940972438783091344577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799685186340176487171077 149940972438783091344577)
                    ·
                      rfl

theorem cell23_876027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 4].length) (baseStart_876027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876027 prefixEnd_876027 := by exact prefixLift 876027
  have htrace : WordTrace (prefixWord ++ tailWord_876027) baseStart_876027 baseEnd_876027 := by
    simpa [prefixWord, tailWord_876027, baseEnd_876027] using wordTrace_append hprefix tailTrace_876027
  have hstable : (prefixWord ++ tailWord_876027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876027).length < 2 ^ (prefixWord ++ tailWord_876027).sum := by decide
  have hdescent : baseEnd_876027 < baseStart_876027 := by decide
  rcases family_descends (prefixWord ++ tailWord_876027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876061 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_876061 : Nat := 118140960795 + 876061 * 2 ^ 59
def prefixEnd_876061 : Nat := 4983230072969 + 3 ^ 40 * 876061 * 2
def baseEnd_876061 : Nat := 149946791886200713669525

theorem tailTrace_876061 : CollatzResearch.WordTrace tailWord_876061 prefixEnd_876061 149946791886200713669525 := by
  unfold tailWord_876061
  simp only [CollatzResearch.WordTrace]
  refine ⟨31952569679188091152108037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21301713119458727434738691 31952569679188091152108037)
  ·
    refine ⟨5991106814847767091020257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31952569679188091152108037 5991106814847767091020257)
    ·
      refine ⟨4493330111135825318265193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991106814847767091020257 4493330111135825318265193)
      ·
        refine ⟨3369997583351868988698895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493330111135825318265193 3369997583351868988698895)
        ·
          refine ⟨5054996375027803483048343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369997583351868988698895 5054996375027803483048343)
          ·
            refine ⟨7582494562541705224572515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054996375027803483048343 7582494562541705224572515)
            ·
              refine ⟨11373741843812557836858773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582494562541705224572515 11373741843812557836858773)
              ·
                refine ⟨533144148928713648602755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11373741843812557836858773 533144148928713648602755)
                ·
                  refine ⟨799716223393070472904133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533144148928713648602755 799716223393070472904133)
                  ·
                    refine ⟨149946791886200713669525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799716223393070472904133 149946791886200713669525)
                    ·
                      rfl

theorem cell23_876061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_876061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876061 prefixEnd_876061 := by exact prefixLift 876061
  have htrace : WordTrace (prefixWord ++ tailWord_876061) baseStart_876061 baseEnd_876061 := by
    simpa [prefixWord, tailWord_876061, baseEnd_876061] using wordTrace_append hprefix tailTrace_876061
  have hstable : (prefixWord ++ tailWord_876061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876061).length < 2 ^ (prefixWord ++ tailWord_876061).sum := by decide
  have hdescent : baseEnd_876061 < baseStart_876061 := by decide
  rcases family_descends (prefixWord ++ tailWord_876061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876107 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4]
def baseStart_876107 : Nat := 118140960795 + 876107 * 2 ^ 59
def prefixEnd_876107 : Nat := 4983230072969 + 3 ^ 40 * 876107 * 2
def baseEnd_876107 : Nat := 449863995768708961033363

theorem tailTrace_876107 : CollatzResearch.WordTrace tailWord_876107 prefixEnd_876107 449863995768708961033363 := by
  unfold tailWord_876107
  simp only [CollatzResearch.WordTrace]
  refine ⟨31954247437021441008282575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21302831624680960672188383 31954247437021441008282575)
  ·
    refine ⟨47931371155532161512423863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31954247437021441008282575 47931371155532161512423863)
    ·
      refine ⟨71897056733298242268635795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47931371155532161512423863 71897056733298242268635795)
      ·
        refine ⟨107845585099947363402953693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71897056733298242268635795 107845585099947363402953693)
        ·
          refine ⟨40442094412480261276107635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107845585099947363402953693 40442094412480261276107635)
          ·
            refine ⟨60663141618720391914161453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40442094412480261276107635 60663141618720391914161453)
            ·
              refine ⟨22748678107020146967810545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60663141618720391914161453 22748678107020146967810545)
              ·
                refine ⟨17061508580265110225857909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22748678107020146967810545 17061508580265110225857909)
                ·
                  refine ⟨1599516429399854083674179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17061508580265110225857909 1599516429399854083674179)
                  ·
                    refine ⟨2399274644099781125511269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599516429399854083674179 2399274644099781125511269)
                    ·
                      refine ⟨449863995768708961033363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2399274644099781125511269 449863995768708961033363)
                      ·
                        rfl

theorem cell23_876107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4].length) (baseStart_876107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876107 prefixEnd_876107 := by exact prefixLift 876107
  have htrace : WordTrace (prefixWord ++ tailWord_876107) baseStart_876107 baseEnd_876107 := by
    simpa [prefixWord, tailWord_876107, baseEnd_876107] using wordTrace_append hprefix tailTrace_876107
  have hstable : (prefixWord ++ tailWord_876107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876107).length < 2 ^ (prefixWord ++ tailWord_876107).sum := by decide
  have hdescent : baseEnd_876107 < baseStart_876107 := by decide
  rcases family_descends (prefixWord ++ tailWord_876107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876125 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 6]
def baseStart_876125 : Nat := 118140960795 + 876125 * 2 ^ 59
def prefixEnd_876125 : Nat := 4983230072969 + 3 ^ 40 * 876125 * 2
def baseEnd_876125 : Nat := 49985915380054432289809

theorem tailTrace_876125 : CollatzResearch.WordTrace tailWord_876125 prefixEnd_876125 49985915380054432289809 := by
  unfold tailWord_876125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31954903950956230082437829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21303269300637486721625219 31954903950956230082437829)
  ·
    refine ⟨5991544490804293140457093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31954903950956230082437829 5991544490804293140457093)
    ·
      refine ⟨1123414592025804963835705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5991544490804293140457093 1123414592025804963835705)
      ·
        refine ⟨842560944019353722876779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1123414592025804963835705 842560944019353722876779)
        ·
          refine ⟨1263841416029030584315169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842560944019353722876779 1263841416029030584315169)
          ·
            refine ⟨947881062021772938236377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263841416029030584315169 947881062021772938236377)
            ·
              refine ⟨710910796516329703677283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947881062021772938236377 710910796516329703677283)
              ·
                refine ⟨1066366194774494555515925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710910796516329703677283 1066366194774494555515925)
                ·
                  refine ⟨49985915380054432289809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1066366194774494555515925 49985915380054432289809)
                  ·
                    rfl

theorem cell23_876125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_876125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876125 prefixEnd_876125 := by exact prefixLift 876125
  have htrace : WordTrace (prefixWord ++ tailWord_876125) baseStart_876125 baseEnd_876125 := by
    simpa [prefixWord, tailWord_876125, baseEnd_876125] using wordTrace_append hprefix tailTrace_876125
  have hstable : (prefixWord ++ tailWord_876125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876125).length < 2 ^ (prefixWord ++ tailWord_876125).sum := by decide
  have hdescent : baseEnd_876125 < baseStart_876125 := by decide
  rcases family_descends (prefixWord ++ tailWord_876125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876127 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_876127 : Nat := 118140960795 + 876127 * 2 ^ 59
def prefixEnd_876127 : Nat := 4983230072969 + 3 ^ 40 * 876127 * 2
def baseEnd_876127 : Nat := 449874265381798882783271

theorem tailTrace_876127 : CollatzResearch.WordTrace tailWord_876127 prefixEnd_876127 449874265381798882783271 := by
  unfold tailWord_876127
  simp only [CollatzResearch.WordTrace]
  refine ⟨31954976896948984424010635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21303317931299322949340423 31954976896948984424010635)
  ·
    refine ⟨47932465345423476636015953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31954976896948984424010635 47932465345423476636015953)
    ·
      refine ⟨35949349009067607477011965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47932465345423476636015953 35949349009067607477011965)
      ·
        refine ⟨13481005878400352803879487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35949349009067607477011965 13481005878400352803879487)
        ·
          refine ⟨20221508817600529205819231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481005878400352803879487 20221508817600529205819231)
          ·
            refine ⟨30332263226400793808728847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20221508817600529205819231 30332263226400793808728847)
            ·
              refine ⟨45498394839601190713093271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30332263226400793808728847 45498394839601190713093271)
              ·
                refine ⟨68247592259401786069639907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45498394839601190713093271 68247592259401786069639907)
                ·
                  refine ⟨102371388389102679104459861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68247592259401786069639907 102371388389102679104459861)
                  ·
                    refine ⟨1199664707684797020755389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102371388389102679104459861 1199664707684797020755389)
                    ·
                      refine ⟨449874265381798882783271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1199664707684797020755389 449874265381798882783271)
                      ·
                        rfl

theorem cell23_876127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_876127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876127 prefixEnd_876127 := by exact prefixLift 876127
  have htrace : WordTrace (prefixWord ++ tailWord_876127) baseStart_876127 baseEnd_876127 := by
    simpa [prefixWord, tailWord_876127, baseEnd_876127] using wordTrace_append hprefix tailTrace_876127
  have hstable : (prefixWord ++ tailWord_876127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876127).length < 2 ^ (prefixWord ++ tailWord_876127).sum := by decide
  have hdescent : baseEnd_876127 < baseStart_876127 := by decide
  rcases family_descends (prefixWord ++ tailWord_876127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876137 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_876137 : Nat := 118140960795 + 876137 * 2 ^ 59
def prefixEnd_876137 : Nat := 4983230072969 + 3 ^ 40 * 876137 * 2
def baseEnd_876137 : Nat := 449879400188343843658225

theorem tailTrace_876137 : CollatzResearch.WordTrace tailWord_876137 prefixEnd_876137 449879400188343843658225 := by
  unfold tailWord_876137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31955341626912756131874665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21303561084608504087916443 31955341626912756131874665)
  ·
    refine ⟨23966506220184567098905999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31955341626912756131874665 23966506220184567098905999)
    ·
      refine ⟨35949759330276850648358999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23966506220184567098905999 35949759330276850648358999)
      ·
        refine ⟨53924638995415275972538499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35949759330276850648358999 53924638995415275972538499)
        ·
          refine ⟨80886958493122913958807749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53924638995415275972538499 80886958493122913958807749)
          ·
            refine ⟨15166304717460546367276453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80886958493122913958807749 15166304717460546367276453)
            ·
              refine ⟨2843682134523852443864335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15166304717460546367276453 2843682134523852443864335)
              ·
                refine ⟨4265523201785778665796503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843682134523852443864335 4265523201785778665796503)
                ·
                  refine ⟨6398284802678667998694755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265523201785778665796503 6398284802678667998694755)
                  ·
                    refine ⟨9597427204018001998042133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398284802678667998694755 9597427204018001998042133)
                    ·
                      refine ⟨449879400188343843658225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9597427204018001998042133 449879400188343843658225)
                      ·
                        rfl

theorem cell23_876137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_876137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876137 prefixEnd_876137 := by exact prefixLift 876137
  have htrace : WordTrace (prefixWord ++ tailWord_876137) baseStart_876137 baseEnd_876137 := by
    simpa [prefixWord, tailWord_876137, baseEnd_876137] using wordTrace_append hprefix tailTrace_876137
  have hstable : (prefixWord ++ tailWord_876137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876137).length < 2 ^ (prefixWord ++ tailWord_876137).sum := by decide
  have hdescent : baseEnd_876137 < baseStart_876137 := by decide
  rcases family_descends (prefixWord ++ tailWord_876137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876141 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_876141 : Nat := 118140960795 + 876141 * 2 ^ 59
def prefixEnd_876141 : Nat := 4983230072969 + 3 ^ 40 * 876141 * 2
def baseEnd_876141 : Nat := 449881454110961828008207

theorem tailTrace_876141 : CollatzResearch.WordTrace tailWord_876141 prefixEnd_876141 449881454110961828008207 := by
  unfold tailWord_876141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31955487518898264815020277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21303658345932176543346851 31955487518898264815020277)
  ·
    refine ⟨2995826954896712326408151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31955487518898264815020277 2995826954896712326408151)
    ·
      refine ⟨4493740432345068489612227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995826954896712326408151 4493740432345068489612227)
      ·
        refine ⟨6740610648517602734418341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493740432345068489612227 6740610648517602734418341)
        ·
          refine ⟨1263864496597050512703439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6740610648517602734418341 1263864496597050512703439)
          ·
            refine ⟨1895796744895575769055159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263864496597050512703439 1895796744895575769055159)
            ·
              refine ⟨2843695117343363653582739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895796744895575769055159 2843695117343363653582739)
              ·
                refine ⟨4265542676015045480374109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843695117343363653582739 4265542676015045480374109)
                ·
                  refine ⟨1599578503505642055140291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4265542676015045480374109 1599578503505642055140291)
                  ·
                    refine ⟨2399367755258463082710437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599578503505642055140291 2399367755258463082710437)
                    ·
                      refine ⟨449881454110961828008207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2399367755258463082710437 449881454110961828008207)
                      ·
                        rfl

theorem cell23_876141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_876141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876141 prefixEnd_876141 := by exact prefixLift 876141
  have htrace : WordTrace (prefixWord ++ tailWord_876141) baseStart_876141 baseEnd_876141 := by
    simpa [prefixWord, tailWord_876141, baseEnd_876141] using wordTrace_append hprefix tailTrace_876141
  have hstable : (prefixWord ++ tailWord_876141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876141).length < 2 ^ (prefixWord ++ tailWord_876141).sum := by decide
  have hdescent : baseEnd_876141 < baseStart_876141 := by decide
  rcases family_descends (prefixWord ++ tailWord_876141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876161 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_876161 : Nat := 118140960795 + 876161 * 2 ^ 59
def prefixEnd_876161 : Nat := 4983230072969 + 3 ^ 40 * 876161 * 2
def baseEnd_876161 : Nat := 449891723724051749758115

theorem tailTrace_876161 : CollatzResearch.WordTrace tailWord_876161 prefixEnd_876161 449891723724051749758115 := by
  unfold tailWord_876161
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956216978825808230748337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21304144652550538820498891 31956216978825808230748337)
  ·
    refine ⟨23967162734119356173061253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31956216978825808230748337 23967162734119356173061253)
    ·
      refine ⟨4493843012647379282448985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23967162734119356173061253 4493843012647379282448985)
      ·
        refine ⟨3370382259485534461836739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493843012647379282448985 3370382259485534461836739)
        ·
          refine ⟨5055573389228301692755109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370382259485534461836739 5055573389228301692755109)
          ·
            refine ⟨947920010480306567391583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5055573389228301692755109 947920010480306567391583)
            ·
              refine ⟨1421880015720459851087375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947920010480306567391583 1421880015720459851087375)
              ·
                refine ⟨2132820023580689776631063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421880015720459851087375 2132820023580689776631063)
                ·
                  refine ⟨3199230035371034664946595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132820023580689776631063 3199230035371034664946595)
                  ·
                    refine ⟨4798845053056551997419893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3199230035371034664946595 4798845053056551997419893)
                    ·
                      refine ⟨449891723724051749758115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4798845053056551997419893 449891723724051749758115)
                      ·
                        rfl

theorem cell23_876161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_876161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876161 prefixEnd_876161 := by exact prefixLift 876161
  have htrace : WordTrace (prefixWord ++ tailWord_876161) baseStart_876161 baseEnd_876161 := by
    simpa [prefixWord, tailWord_876161, baseEnd_876161] using wordTrace_append hprefix tailTrace_876161
  have hstable : (prefixWord ++ tailWord_876161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876161).length < 2 ^ (prefixWord ++ tailWord_876161).sum := by decide
  have hdescent : baseEnd_876161 < baseStart_876161 := by decide
  rcases family_descends (prefixWord ++ tailWord_876161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876164 : List Nat := [2, 3, 2, 1, 5, 10]
def baseStart_876164 : Nat := 118140960795 + 876164 * 2 ^ 59
def prefixEnd_876164 : Nat := 4983230072969 + 3 ^ 40 * 876164 * 2
def baseEnd_876164 : Nat := 1851412609736688222307

theorem tailTrace_876164 : CollatzResearch.WordTrace tailWord_876164 prefixEnd_876164 1851412609736688222307 := by
  unfold tailWord_876164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978163198907469871553773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21304217598543293162071697 15978163198907469871553773)
  ·
    refine ⟨5991811199590301201832665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15978163198907469871553773 5991811199590301201832665)
    ·
      refine ⟨4493858399692725901374499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991811199590301201832665 4493858399692725901374499)
      ·
        refine ⟨6740787599539088852061749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493858399692725901374499 6740787599539088852061749)
        ·
          refine ⟨631948837456789579880789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6740787599539088852061749 631948837456789579880789)
          ·
            refine ⟨1851412609736688222307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 631948837456789579880789 1851412609736688222307)
            ·
              rfl

theorem cell23_876164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 10].length) (baseStart_876164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876164 prefixEnd_876164 := by exact prefixLift 876164
  have htrace : WordTrace (prefixWord ++ tailWord_876164) baseStart_876164 baseEnd_876164 := by
    simpa [prefixWord, tailWord_876164, baseEnd_876164] using wordTrace_append hprefix tailTrace_876164
  have hstable : (prefixWord ++ tailWord_876164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876164).length < 2 ^ (prefixWord ++ tailWord_876164).sum := by decide
  have hdescent : baseEnd_876164 < baseStart_876164 := by decide
  rcases family_descends (prefixWord ++ tailWord_876164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876207 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 8]
def baseStart_876207 : Nat := 118140960795 + 876207 * 2 ^ 59
def prefixEnd_876207 : Nat := 4983230072969 + 3 ^ 40 * 876207 * 2
def baseEnd_876207 : Nat := 149971781278052856594301

theorem tailTrace_876207 : CollatzResearch.WordTrace tailWord_876207 prefixEnd_876207 149971781278052856594301 := by
  unfold tailWord_876207
  simp only [CollatzResearch.WordTrace]
  refine ⟨31957894736659158086922875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21305263157772772057948583 31957894736659158086922875)
  ·
    refine ⟨47936842104988737130384313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31957894736659158086922875 47936842104988737130384313)
    ·
      refine ⟨35952631578741552847788235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47936842104988737130384313 35952631578741552847788235)
      ·
        refine ⟨53928947368112329271682353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35952631578741552847788235 53928947368112329271682353)
        ·
          refine ⟨40446710526084246953761765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53928947368112329271682353 40446710526084246953761765)
          ·
            refine ⟨7583758223640796303830331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40446710526084246953761765 7583758223640796303830331)
            ·
              refine ⟨11375637335461194455745497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583758223640796303830331 11375637335461194455745497)
              ·
                refine ⟨8531728001595895841809123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375637335461194455745497 8531728001595895841809123)
                ·
                  refine ⟨12797592002393843762713685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531728001595895841809123 12797592002393843762713685)
                  ·
                    refine ⟨149971781278052856594301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12797592002393843762713685 149971781278052856594301)
                    ·
                      rfl

theorem cell23_876207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_876207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876207 prefixEnd_876207 := by exact prefixLift 876207
  have htrace : WordTrace (prefixWord ++ tailWord_876207) baseStart_876207 baseEnd_876207 := by
    simpa [prefixWord, tailWord_876207, baseEnd_876207] using wordTrace_append hprefix tailTrace_876207
  have hstable : (prefixWord ++ tailWord_876207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876207).length < 2 ^ (prefixWord ++ tailWord_876207).sum := by decide
  have hdescent : baseEnd_876207 < baseStart_876207 := by decide
  rcases family_descends (prefixWord ++ tailWord_876207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876218 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_876218 : Nat := 118140960795 + 876218 * 2 ^ 59
def prefixEnd_876218 : Nat := 4983230072969 + 3 ^ 40 * 876218 * 2
def baseEnd_876218 : Nat := 449920992121358026745353

theorem tailTrace_876218 : CollatzResearch.WordTrace tailWord_876218 prefixEnd_876218 449920992121358026745353 := by
  unfold tailWord_876218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7989573984904826741393327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21305530626412871310382205 7989573984904826741393327)
  ·
    refine ⟨11984360977357240112089991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7989573984904826741393327 11984360977357240112089991)
    ·
      refine ⟨17976541466035860168134987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984360977357240112089991 17976541466035860168134987)
      ·
        refine ⟨26964812199053790252202481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17976541466035860168134987 26964812199053790252202481)
        ·
          refine ⟨20223609149290342689151861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26964812199053790252202481 20223609149290342689151861)
          ·
            refine ⟨1895963357745969627107987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20223609149290342689151861 1895963357745969627107987)
            ·
              refine ⟨2843945036618954440661981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895963357745969627107987 2843945036618954440661981)
              ·
                refine ⟨1066479388732107915248243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843945036618954440661981 1066479388732107915248243)
                ·
                  refine ⟨1599719083098161872872365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066479388732107915248243 1599719083098161872872365)
                  ·
                    refine ⟨599894656161810702327137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599719083098161872872365 599894656161810702327137)
                    ·
                      refine ⟨449920992121358026745353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599894656161810702327137 449920992121358026745353)
                      ·
                        rfl

theorem cell23_876218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_876218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876218 prefixEnd_876218 := by exact prefixLift 876218
  have htrace : WordTrace (prefixWord ++ tailWord_876218) baseStart_876218 baseEnd_876218 := by
    simpa [prefixWord, tailWord_876218, baseEnd_876218] using wordTrace_append hprefix tailTrace_876218
  have hstable : (prefixWord ++ tailWord_876218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876218).length < 2 ^ (prefixWord ++ tailWord_876218).sum := by decide
  have hdescent : baseEnd_876218 < baseStart_876218 := by decide
  rcases family_descends (prefixWord ++ tailWord_876218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876252 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_876252 : Nat := 118140960795 + 876252 * 2 ^ 59
def prefixEnd_876252 : Nat := 4983230072969 + 3 ^ 40 * 876252 * 2
def baseEnd_876252 : Nat := 449938450463610893720197

theorem tailTrace_876252 : CollatzResearch.WordTrace tailWord_876252 prefixEnd_876252 449938450463610893720197 := by
  unfold tailWord_876252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15979768010748065386155505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21306357347664087181540673 15979768010748065386155505)
  ·
    refine ⟨11984826008061049039616629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15979768010748065386155505 11984826008061049039616629)
    ·
      refine ⟨1123577438255723347464059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11984826008061049039616629 1123577438255723347464059)
      ·
        refine ⟨1685366157383585021196089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123577438255723347464059 1685366157383585021196089)
        ·
          refine ⟨1264024618037688765897067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685366157383585021196089 1264024618037688765897067)
          ·
            refine ⟨1896036927056533148845601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264024618037688765897067 1896036927056533148845601)
            ·
              refine ⟨1422027695292399861634201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1896036927056533148845601 1422027695292399861634201)
              ·
                refine ⟨1066520771469299896225651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422027695292399861634201 1066520771469299896225651)
                ·
                  refine ⟨1599781157203949844338477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066520771469299896225651 1599781157203949844338477)
                  ·
                    refine ⟨599917933951481191626929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599781157203949844338477 599917933951481191626929)
                    ·
                      refine ⟨449938450463610893720197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 599917933951481191626929 449938450463610893720197)
                      ·
                        rfl

theorem cell23_876252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_876252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876252 prefixEnd_876252 := by exact prefixLift 876252
  have htrace : WordTrace (prefixWord ++ tailWord_876252) baseStart_876252 baseEnd_876252 := by
    simpa [prefixWord, tailWord_876252, baseEnd_876252] using wordTrace_append hprefix tailTrace_876252
  have hstable : (prefixWord ++ tailWord_876252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876252).length < 2 ^ (prefixWord ++ tailWord_876252).sum := by decide
  have hdescent : baseEnd_876252 < baseStart_876252 := by decide
  rcases family_descends (prefixWord ++ tailWord_876252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876321 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_876321 : Nat := 118140960795 + 876321 * 2 ^ 59
def prefixEnd_876321 : Nat := 4983230072969 + 3 ^ 40 * 876321 * 2
def baseEnd_876321 : Nat := 449973880628771123757379

theorem tailTrace_876321 : CollatzResearch.WordTrace tailWord_876321 prefixEnd_876321 449973880628771123757379 := by
  unfold tailWord_876321
  simp only [CollatzResearch.WordTrace]
  refine ⟨31962052658246155556572817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21308035105497437037715211 31962052658246155556572817)
  ·
    refine ⟨23971539493684616667429613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31962052658246155556572817 23971539493684616667429613)
    ·
      refine ⟨8989327310131731250286105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23971539493684616667429613 8989327310131731250286105)
      ·
        refine ⟨6741995482598798437714579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8989327310131731250286105 6741995482598798437714579)
        ·
          refine ⟨10112993223898197656571869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741995482598798437714579 10112993223898197656571869)
          ·
            refine ⟨3792372458961824121214451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10112993223898197656571869 3792372458961824121214451)
            ·
              refine ⟨5688558688442736181821677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792372458961824121214451 5688558688442736181821677)
              ·
                refine ⟨2133209508166026068183129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5688558688442736181821677 2133209508166026068183129)
                ·
                  refine ⟨1599907131124519551137347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2133209508166026068183129 1599907131124519551137347)
                  ·
                    refine ⟨2399860696686779326706021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1599907131124519551137347 2399860696686779326706021)
                    ·
                      refine ⟨449973880628771123757379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2399860696686779326706021 449973880628771123757379)
                      ·
                        rfl

theorem cell23_876321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_876321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876321 prefixEnd_876321 := by exact prefixLift 876321
  have htrace : WordTrace (prefixWord ++ tailWord_876321) baseStart_876321 baseEnd_876321 := by
    simpa [prefixWord, tailWord_876321, baseEnd_876321] using wordTrace_append hprefix tailTrace_876321
  have hstable : (prefixWord ++ tailWord_876321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876321).length < 2 ^ (prefixWord ++ tailWord_876321).sum := by decide
  have hdescent : baseEnd_876321 < baseStart_876321 := by decide
  rcases family_descends (prefixWord ++ tailWord_876321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876365 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_876365 : Nat := 118140960795 + 876365 * 2 ^ 59
def prefixEnd_876365 : Nat := 4983230072969 + 3 ^ 40 * 876365 * 2
def baseEnd_876365 : Nat := 149998824592522983869059

theorem tailTrace_876365 : CollatzResearch.WordTrace tailWord_876365 prefixEnd_876365 149998824592522983869059 := by
  unfold tailWord_876365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31963657470086751071174549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21309104980057834047449699 31963657470086751071174549)
  ·
    refine ⟨1498296443910316456461307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31963657470086751071174549 1498296443910316456461307)
    ·
      refine ⟨2247444665865474684691961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1498296443910316456461307 2247444665865474684691961)
      ·
        refine ⟨1685583499399106013518971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247444665865474684691961 1685583499399106013518971)
        ·
          refine ⟨2528375249098659020278457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685583499399106013518971 2528375249098659020278457)
          ·
            refine ⟨1896281436823994265208843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528375249098659020278457 1896281436823994265208843)
            ·
              refine ⟨2844422155235991397813265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896281436823994265208843 2844422155235991397813265)
              ·
                refine ⟨2133316616426993548359949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844422155235991397813265 2133316616426993548359949)
                ·
                  refine ⟨799993731160122580634981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2133316616426993548359949 799993731160122580634981)
                  ·
                    refine ⟨149998824592522983869059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 799993731160122580634981 149998824592522983869059)
                    ·
                      rfl

theorem cell23_876365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_876365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876365 prefixEnd_876365 := by exact prefixLift 876365
  have htrace : WordTrace (prefixWord ++ tailWord_876365) baseStart_876365 baseEnd_876365 := by
    simpa [prefixWord, tailWord_876365, baseEnd_876365] using wordTrace_append hprefix tailTrace_876365
  have hstable : (prefixWord ++ tailWord_876365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876365).length < 2 ^ (prefixWord ++ tailWord_876365).sum := by decide
  have hdescent : baseEnd_876365 < baseStart_876365 := by decide
  rcases family_descends (prefixWord ++ tailWord_876365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876375 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_876375 : Nat := 118140960795 + 876375 * 2 ^ 59
def prefixEnd_876375 : Nat := 4983230072969 + 3 ^ 40 * 876375 * 2
def baseEnd_876375 : Nat := 450001608584113912482131

theorem tailTrace_876375 : CollatzResearch.WordTrace tailWord_876375 prefixEnd_876375 450001608584113912482131 := by
  unfold tailWord_876375
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964022200050522779038579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21309348133367015186025719 31964022200050522779038579)
  ·
    refine ⟨47946033300075784168557869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31964022200050522779038579 47946033300075784168557869)
    ·
      refine ⟨17979762487528419063209201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47946033300075784168557869 17979762487528419063209201)
      ·
        refine ⟨13484821865646314297406901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17979762487528419063209201 13484821865646314297406901)
        ·
          refine ⟨1264202049904341965381897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13484821865646314297406901 1264202049904341965381897)
          ·
            refine ⟨948151537428256474036423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264202049904341965381897 948151537428256474036423)
            ·
              refine ⟨1422227306142384711054635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948151537428256474036423 1422227306142384711054635)
              ·
                refine ⟨2133340959213577066581953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422227306142384711054635 2133340959213577066581953)
                ·
                  refine ⟨1600005719410182799936465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2133340959213577066581953 1600005719410182799936465)
                  ·
                    refine ⟨1200004289557637099952349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1600005719410182799936465 1200004289557637099952349)
                    ·
                      refine ⟨450001608584113912482131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200004289557637099952349 450001608584113912482131)
                      ·
                        rfl

theorem cell23_876375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_876375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876375 prefixEnd_876375 := by exact prefixLift 876375
  have htrace : WordTrace (prefixWord ++ tailWord_876375) baseStart_876375 baseEnd_876375 := by
    simpa [prefixWord, tailWord_876375, baseEnd_876375] using wordTrace_append hprefix tailTrace_876375
  have hstable : (prefixWord ++ tailWord_876375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876375).length < 2 ^ (prefixWord ++ tailWord_876375).sum := by decide
  have hdescent : baseEnd_876375 < baseStart_876375 := by decide
  rcases family_descends (prefixWord ++ tailWord_876375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876405 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_876405 : Nat := 118140960795 + 876405 * 2 ^ 59
def prefixEnd_876405 : Nat := 4983230072969 + 3 ^ 40 * 876405 * 2
def baseEnd_876405 : Nat := 450017013003748795106993

theorem tailTrace_876405 : CollatzResearch.WordTrace tailWord_876405 prefixEnd_876405 450017013003748795106993 := by
  unfold tailWord_876405
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965116389941837902630669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21310077593294558601753779 31965116389941837902630669)
  ·
    refine ⟨11986918646228189213486501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31965116389941837902630669 11986918646228189213486501)
    ·
      refine ⟨2247547246167785477528719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11986918646228189213486501 2247547246167785477528719)
      ·
        refine ⟨3371320869251678216293079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247547246167785477528719 3371320869251678216293079)
        ·
          refine ⟨5056981303877517324439619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371320869251678216293079 5056981303877517324439619)
          ·
            refine ⟨7585471955816275986659429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056981303877517324439619 7585471955816275986659429)
            ·
              refine ⟨1422275991715551747498643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7585471955816275986659429 1422275991715551747498643)
              ·
                refine ⟨2133413987573327621247965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422275991715551747498643 2133413987573327621247965)
                ·
                  refine ⟨800030245339997857967987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2133413987573327621247965 800030245339997857967987)
                  ·
                    refine ⟨1200045368009996786951981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 800030245339997857967987 1200045368009996786951981)
                    ·
                      refine ⟨450017013003748795106993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200045368009996786951981 450017013003748795106993)
                      ·
                        rfl

theorem cell23_876405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_876405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876405 prefixEnd_876405 := by exact prefixLift 876405
  have htrace : WordTrace (prefixWord ++ tailWord_876405) baseStart_876405 baseEnd_876405 := by
    simpa [prefixWord, tailWord_876405, baseEnd_876405] using wordTrace_append hprefix tailTrace_876405
  have hstable : (prefixWord ++ tailWord_876405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876405).length < 2 ^ (prefixWord ++ tailWord_876405).sum := by decide
  have hdescent : baseEnd_876405 < baseStart_876405 := by decide
  rcases family_descends (prefixWord ++ tailWord_876405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876431 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_876431 : Nat := 118140960795 + 876431 * 2 ^ 59
def prefixEnd_876431 : Nat := 4983230072969 + 3 ^ 40 * 876431 * 2
def baseEnd_876431 : Nat := 450030363500765693381873

theorem tailTrace_876431 : CollatzResearch.WordTrace tailWord_876431 prefixEnd_876431 450030363500765693381873 := by
  unfold tailWord_876431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31966064687847644343077147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21310709791898429562051431 31966064687847644343077147)
  ·
    refine ⟨47949097031771466514615721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31966064687847644343077147 47949097031771466514615721)
    ·
      refine ⟨35961822773828599885961791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47949097031771466514615721 35961822773828599885961791)
      ·
        refine ⟨53942734160742899828942687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35961822773828599885961791 53942734160742899828942687)
        ·
          refine ⟨80914101241114349743414031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53942734160742899828942687 80914101241114349743414031)
          ·
            refine ⟨121371151861671524615121047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80914101241114349743414031 121371151861671524615121047)
            ·
              refine ⟨182056727792507286922681571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121371151861671524615121047 182056727792507286922681571)
              ·
                refine ⟨273085091688760930384022357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182056727792507286922681571 273085091688760930384022357)
                ·
                  refine ⟨1600107959113833576468881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 273085091688760930384022357 1600107959113833576468881)
                  ·
                    refine ⟨1200080969335375182351661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1600107959113833576468881 1200080969335375182351661)
                    ·
                      refine ⟨450030363500765693381873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200080969335375182351661 450030363500765693381873)
                      ·
                        rfl

theorem cell23_876431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_876431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876431 prefixEnd_876431 := by exact prefixLift 876431
  have htrace : WordTrace (prefixWord ++ tailWord_876431) baseStart_876431 baseEnd_876431 := by
    simpa [prefixWord, tailWord_876431, baseEnd_876431] using wordTrace_append hprefix tailTrace_876431
  have hstable : (prefixWord ++ tailWord_876431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876431).length < 2 ^ (prefixWord ++ tailWord_876431).sum := by decide
  have hdescent : baseEnd_876431 < baseStart_876431 := by decide
  rcases family_descends (prefixWord ++ tailWord_876431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876441 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_876441 : Nat := 118140960795 + 876441 * 2 ^ 59
def prefixEnd_876441 : Nat := 4983230072969 + 3 ^ 40 * 876441 * 2
def baseEnd_876441 : Nat := 450035498307310654256827

theorem tailTrace_876441 : CollatzResearch.WordTrace tailWord_876441 prefixEnd_876441 450035498307310654256827 := by
  unfold tailWord_876441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31966429417811416050941177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21310952945207610700627451 31966429417811416050941177)
  ·
    refine ⟨23974822063358562038205883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31966429417811416050941177 23974822063358562038205883)
    ·
      refine ⟨35962233095037843057308825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23974822063358562038205883 35962233095037843057308825)
      ·
        refine ⟨26971674821278382292981619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35962233095037843057308825 26971674821278382292981619)
        ·
          refine ⟨40457512231917573439472429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26971674821278382292981619 40457512231917573439472429)
          ·
            refine ⟨15171567086969090039802161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40457512231917573439472429 15171567086969090039802161)
            ·
              refine ⟨11378675315226817529851621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15171567086969090039802161 11378675315226817529851621)
              ·
                refine ⟨2133501621605028286847179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11378675315226817529851621 2133501621605028286847179)
                ·
                  refine ⟨3200252432407542430270769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133501621605028286847179 3200252432407542430270769)
                  ·
                    refine ⟨2400189324305656822703077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3200252432407542430270769 2400189324305656822703077)
                    ·
                      refine ⟨450035498307310654256827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2400189324305656822703077 450035498307310654256827)
                      ·
                        rfl

theorem cell23_876441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_876441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876441 prefixEnd_876441 := by exact prefixLift 876441
  have htrace : WordTrace (prefixWord ++ tailWord_876441) baseStart_876441 baseEnd_876441 := by
    simpa [prefixWord, tailWord_876441, baseEnd_876441] using wordTrace_append hprefix tailTrace_876441
  have hstable : (prefixWord ++ tailWord_876441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876441).length < 2 ^ (prefixWord ++ tailWord_876441).sum := by decide
  have hdescent : baseEnd_876441 < baseStart_876441 := by decide
  rcases family_descends (prefixWord ++ tailWord_876441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876456 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_876456 : Nat := 118140960795 + 876456 * 2 ^ 59
def prefixEnd_876456 : Nat := 4983230072969 + 3 ^ 40 * 876456 * 2
def baseEnd_876456 : Nat := 450043200517128095569259

theorem tailTrace_876456 : CollatzResearch.WordTrace tailWord_876456 prefixEnd_876456 450043200517128095569259 := by
  unfold tailWord_876456
  simp only [CollatzResearch.WordTrace]
  refine ⟨15983488256378536806368611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21311317675171382408491481 15983488256378536806368611)
  ·
    refine ⟨23975232384567805209552917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15983488256378536806368611 23975232384567805209552917)
    ·
      refine ⟨1123839018026615869197793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23975232384567805209552917 1123839018026615869197793)
      ·
        refine ⟨842879263519961901898345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1123839018026615869197793 842879263519961901898345)
        ·
          refine ⟨632159447639971426423759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842879263519961901898345 632159447639971426423759)
          ·
            refine ⟨948239171459957139635639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632159447639971426423759 948239171459957139635639)
            ·
              refine ⟨1422358757189935709453459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948239171459957139635639 1422358757189935709453459)
              ·
                refine ⟨2133538135784903564180189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422358757189935709453459 2133538135784903564180189)
                ·
                  refine ⟨800076800919338836567571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2133538135784903564180189 800076800919338836567571)
                  ·
                    refine ⟨1200115201379008254851357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 800076800919338836567571 1200115201379008254851357)
                    ·
                      refine ⟨450043200517128095569259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200115201379008254851357 450043200517128095569259)
                      ·
                        rfl

theorem cell23_876456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_876456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876456 prefixEnd_876456 := by exact prefixLift 876456
  have htrace : WordTrace (prefixWord ++ tailWord_876456) baseStart_876456 baseEnd_876456 := by
    simpa [prefixWord, tailWord_876456, baseEnd_876456] using wordTrace_append hprefix tailTrace_876456
  have hstable : (prefixWord ++ tailWord_876456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876456).length < 2 ^ (prefixWord ++ tailWord_876456).sum := by decide
  have hdescent : baseEnd_876456 < baseStart_876456 := by decide
  rcases family_descends (prefixWord ++ tailWord_876456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876541 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 9]
def baseStart_876541 : Nat := 118140960795 + 876541 * 2 ^ 59
def prefixEnd_876541 : Nat := 4983230072969 + 3 ^ 40 * 876541 * 2
def baseEnd_876541 : Nat := 50009649596973362556263

theorem tailTrace_876541 : CollatzResearch.WordTrace tailWord_876541 prefixEnd_876541 50009649596973362556263 := by
  unfold tailWord_876541
  simp only [CollatzResearch.WordTrace]
  refine ⟨31970076717449133129581477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21313384478299422086387651 31970076717449133129581477)
  ·
    refine ⟨5994389384521712461796527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31970076717449133129581477 5994389384521712461796527)
    ·
      refine ⟨8991584076782568692694791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5994389384521712461796527 8991584076782568692694791)
      ·
        refine ⟨13487376115173853039042187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991584076782568692694791 13487376115173853039042187)
        ·
          refine ⟨20231064172760779558563281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487376115173853039042187 20231064172760779558563281)
          ·
            refine ⟨15173298129570584668922461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231064172760779558563281 15173298129570584668922461)
            ·
              refine ⟨5689986798588969250845923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15173298129570584668922461 5689986798588969250845923)
              ·
                refine ⟨8534980197883453876268885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689986798588969250845923 8534980197883453876268885)
                ·
                  refine ⟨50009649596973362556263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8534980197883453876268885 50009649596973362556263)
                  ·
                    rfl

theorem cell23_876541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_876541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876541 prefixEnd_876541 := by exact prefixLift 876541
  have htrace : WordTrace (prefixWord ++ tailWord_876541) baseStart_876541 baseEnd_876541 := by
    simpa [prefixWord, tailWord_876541, baseEnd_876541] using wordTrace_append hprefix tailTrace_876541
  have hstable : (prefixWord ++ tailWord_876541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876541).length < 2 ^ (prefixWord ++ tailWord_876541).sum := by decide
  have hdescent : baseEnd_876541 < baseStart_876541 := by decide
  rcases family_descends (prefixWord ++ tailWord_876541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876550 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_876550 : Nat := 118140960795 + 876550 * 2 ^ 59
def prefixEnd_876550 : Nat := 4983230072969 + 3 ^ 40 * 876550 * 2
def baseEnd_876550 : Nat := 450091467698650727793827

theorem tailTrace_876550 : CollatzResearch.WordTrace tailWord_876550 prefixEnd_876550 450091467698650727793827 := by
  unfold tailWord_876550
  simp only [CollatzResearch.WordTrace]
  refine ⟨999075155450516489583097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21313603316277685111106069 999075155450516489583097)
  ·
    refine ⟨749306366587887367187323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 999075155450516489583097 749306366587887367187323)
    ·
      refine ⟨1123959549881831050780985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749306366587887367187323 1123959549881831050780985)
      ·
        refine ⟨842969662411373288085739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1123959549881831050780985 842969662411373288085739)
        ·
          refine ⟨1264454493617059932128609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842969662411373288085739 1264454493617059932128609)
          ·
            refine ⟨948340870212794949096457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264454493617059932128609 948340870212794949096457)
            ·
              refine ⟨711255652659596211822343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948340870212794949096457 711255652659596211822343)
              ·
                refine ⟨1066883478989394317733515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711255652659596211822343 1066883478989394317733515)
                ·
                  refine ⟨1600325218484091476600273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066883478989394317733515 1600325218484091476600273)
                  ·
                    refine ⟨1200243913863068607450205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1600325218484091476600273 1200243913863068607450205)
                    ·
                      refine ⟨450091467698650727793827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200243913863068607450205 450091467698650727793827)
                      ·
                        rfl

theorem cell23_876550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_876550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876550 prefixEnd_876550 := by exact prefixLift 876550
  have htrace : WordTrace (prefixWord ++ tailWord_876550) baseStart_876550 baseEnd_876550 := by
    simpa [prefixWord, tailWord_876550, baseEnd_876550] using wordTrace_append hprefix tailTrace_876550
  have hstable : (prefixWord ++ tailWord_876550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876550).length < 2 ^ (prefixWord ++ tailWord_876550).sum := by decide
  have hdescent : baseEnd_876550 < baseStart_876550 := by decide
  rcases family_descends (prefixWord ++ tailWord_876550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876568 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_876568 : Nat := 118140960795 + 876568 * 2 ^ 59
def prefixEnd_876568 : Nat := 4983230072969 + 3 ^ 40 * 876568 * 2
def baseEnd_876568 : Nat := 450100710350431657368743

theorem tailTrace_876568 : CollatzResearch.WordTrace tailWord_876568 prefixEnd_876568 450100710350431657368743 := by
  unfold tailWord_876568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985530744175658370407179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21314040992234211160542905 15985530744175658370407179)
  ·
    refine ⟨23978296116263487555610769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15985530744175658370407179 23978296116263487555610769)
    ·
      refine ⟨17983722087197615666708077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23978296116263487555610769 17983722087197615666708077)
      ·
        refine ⟨6743895782699105875015529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17983722087197615666708077 6743895782699105875015529)
        ·
          refine ⟨5057921837024329406261647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6743895782699105875015529 5057921837024329406261647)
          ·
            refine ⟨7586882755536494109392471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057921837024329406261647 7586882755536494109392471)
            ·
              refine ⟨11380324133304741164088707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586882755536494109392471 11380324133304741164088707)
              ·
                refine ⟨17070486199957111746133061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11380324133304741164088707 17070486199957111746133061)
                ·
                  refine ⟨3200716162491958452399949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17070486199957111746133061 3200716162491958452399949)
                  ·
                    refine ⟨1200268560934484419649981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3200716162491958452399949 1200268560934484419649981)
                    ·
                      refine ⟨450100710350431657368743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200268560934484419649981 450100710350431657368743)
                      ·
                        rfl

theorem cell23_876568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_876568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876568 prefixEnd_876568 := by exact prefixLift 876568
  have htrace : WordTrace (prefixWord ++ tailWord_876568) baseStart_876568 baseEnd_876568 := by
    simpa [prefixWord, tailWord_876568, baseEnd_876568] using wordTrace_append hprefix tailTrace_876568
  have hstable : (prefixWord ++ tailWord_876568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876568).length < 2 ^ (prefixWord ++ tailWord_876568).sum := by decide
  have hdescent : baseEnd_876568 < baseStart_876568 := by decide
  rcases family_descends (prefixWord ++ tailWord_876568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876586 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_876586 : Nat := 118140960795 + 876586 * 2 ^ 59
def prefixEnd_876586 : Nat := 4983230072969 + 3 ^ 40 * 876586 * 2
def baseEnd_876586 : Nat := 450109953002212586943661

theorem tailTrace_876586 : CollatzResearch.WordTrace tailWord_876586 prefixEnd_876586 450109953002212586943661 := by
  unfold tailWord_876586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992929500571526453742403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21314478668190737209979741 7992929500571526453742403)
  ·
    refine ⟨11989394250857289680613605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7992929500571526453742403 11989394250857289680613605)
    ·
      refine ⟨2248011422035741815115051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11989394250857289680613605 2248011422035741815115051)
      ·
        refine ⟨3372017133053612722672577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248011422035741815115051 3372017133053612722672577)
        ·
          refine ⟨2529012849790209542004433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3372017133053612722672577 2529012849790209542004433)
          ·
            refine ⟨1896759637342657156503325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2529012849790209542004433 1896759637342657156503325)
            ·
              refine ⟨711284864003496433688747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1896759637342657156503325 711284864003496433688747)
              ·
                refine ⟨1066927296005244650533121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711284864003496433688747 1066927296005244650533121)
                ·
                  refine ⟨800195472003933487899841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066927296005244650533121 800195472003933487899841)
                  ·
                    refine ⟨600146604002950115924881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800195472003933487899841 600146604002950115924881)
                    ·
                      refine ⟨450109953002212586943661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600146604002950115924881 450109953002212586943661)
                      ·
                        rfl

theorem cell23_876586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_876586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876586 prefixEnd_876586 := by exact prefixLift 876586
  have htrace : WordTrace (prefixWord ++ tailWord_876586) baseStart_876586 baseEnd_876586 := by
    simpa [prefixWord, tailWord_876586, baseEnd_876586] using wordTrace_append hprefix tailTrace_876586
  have hstable : (prefixWord ++ tailWord_876586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876586).length < 2 ^ (prefixWord ++ tailWord_876586).sum := by decide
  have hdescent : baseEnd_876586 < baseStart_876586 := by decide
  rcases family_descends (prefixWord ++ tailWord_876586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876608 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_876608 : Nat := 118140960795 + 876608 * 2 ^ 59
def prefixEnd_876608 : Nat := 4983230072969 + 3 ^ 40 * 876608 * 2
def baseEnd_876608 : Nat := 450121249576611500868559

theorem tailTrace_876608 : CollatzResearch.WordTrace tailWord_876608 prefixEnd_876608 450121249576611500868559 := by
  unfold tailWord_876608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15986260204103201786135239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21315013605470935714846985 15986260204103201786135239)
  ·
    refine ⟨23979390306154802679202859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15986260204103201786135239 23979390306154802679202859)
    ·
      refine ⟨35969085459232204018804289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23979390306154802679202859 35969085459232204018804289)
      ·
        refine ⟨26976814094424153014103217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35969085459232204018804289 26976814094424153014103217)
        ·
          refine ⟨20232610570818114760577413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26976814094424153014103217 20232610570818114760577413)
          ·
            refine ⟨3793614482028396517608265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20232610570818114760577413 3793614482028396517608265)
            ·
              refine ⟨2845210861521297388206199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3793614482028396517608265 2845210861521297388206199)
              ·
                refine ⟨4267816292281946082309299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845210861521297388206199 4267816292281946082309299)
                ·
                  refine ⟨6401724438422919123463949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267816292281946082309299 6401724438422919123463949)
                  ·
                    refine ⟨2400646664408594671298981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6401724438422919123463949 2400646664408594671298981)
                    ·
                      refine ⟨450121249576611500868559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2400646664408594671298981 450121249576611500868559)
                      ·
                        rfl

theorem cell23_876608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_876608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876608 prefixEnd_876608 := by exact prefixLift 876608
  have htrace : WordTrace (prefixWord ++ tailWord_876608) baseStart_876608 baseEnd_876608 := by
    simpa [prefixWord, tailWord_876608, baseEnd_876608] using wordTrace_append hprefix tailTrace_876608
  have hstable : (prefixWord ++ tailWord_876608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876608).length < 2 ^ (prefixWord ++ tailWord_876608).sum := by decide
  have hdescent : baseEnd_876608 < baseStart_876608 := by decide
  rcases family_descends (prefixWord ++ tailWord_876608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876662 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_876662 : Nat := 118140960795 + 876662 * 2 ^ 59
def prefixEnd_876662 : Nat := 4983230072969 + 3 ^ 40 * 876662 * 2
def baseEnd_876662 : Nat := 450148977531954289593311

theorem tailTrace_876662 : CollatzResearch.WordTrace tailWord_876662 prefixEnd_876662 450148977531954289593311 := by
  unfold tailWord_876662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998405621875673174671015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21316326633340513863157493 1998405621875673174671015)
  ·
    refine ⟨2997608432813509762006523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1998405621875673174671015 2997608432813509762006523)
    ·
      refine ⟨4496412649220264643009785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997608432813509762006523 4496412649220264643009785)
      ·
        refine ⟨3372309486915198482257339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4496412649220264643009785 3372309486915198482257339)
        ·
          refine ⟨5058464230372797723386009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372309486915198482257339 5058464230372797723386009)
          ·
            refine ⟨3793848172779598292539507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5058464230372797723386009 3793848172779598292539507)
            ·
              refine ⟨5690772259169397438809261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3793848172779598292539507 5690772259169397438809261)
              ·
                refine ⟨2134039597188524039553473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5690772259169397438809261 2134039597188524039553473)
                ·
                  refine ⟨1600529697891393029665105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2134039597188524039553473 1600529697891393029665105)
                  ·
                    refine ⟨1200397273418544772248829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1600529697891393029665105 1200397273418544772248829)
                    ·
                      refine ⟨450148977531954289593311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200397273418544772248829 450148977531954289593311)
                      ·
                        rfl

theorem cell23_876662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_876662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876662 prefixEnd_876662 := by exact prefixLift 876662
  have htrace : WordTrace (prefixWord ++ tailWord_876662) baseStart_876662 baseEnd_876662 := by
    simpa [prefixWord, tailWord_876662, baseEnd_876662] using wordTrace_append hprefix tailTrace_876662
  have hstable : (prefixWord ++ tailWord_876662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876662).length < 2 ^ (prefixWord ++ tailWord_876662).sum := by decide
  have hdescent : baseEnd_876662 < baseStart_876662 := by decide
  rcases family_descends (prefixWord ++ tailWord_876662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876783 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 1, 2, 2]
def baseStart_876783 : Nat := 118140960795 + 876783 * 2 ^ 59
def prefixEnd_876783 : Nat := 4983230072969 + 3 ^ 40 * 876783 * 2
def baseEnd_876783 : Nat := 450211108691148316180255

theorem tailTrace_876783 : CollatzResearch.WordTrace tailWord_876783 prefixEnd_876783 450211108691148316180255 := by
  unfold tailWord_876783
  simp only [CollatzResearch.WordTrace]
  refine ⟨31978903182572408459891003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21319268788381605639927335 31978903182572408459891003)
  ·
    refine ⟨47968354773858612689836505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31978903182572408459891003 47968354773858612689836505)
    ·
      refine ⟨35976266080393959517377379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47968354773858612689836505 35976266080393959517377379)
      ·
        refine ⟨53964399120590939276066069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35976266080393959517377379 53964399120590939276066069)
        ·
          refine ⟨2529581208777700278565597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53964399120590939276066069 2529581208777700278565597)
          ·
            refine ⟨948592953291637604462099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2529581208777700278565597 948592953291637604462099)
            ·
              refine ⟨1422889429937456406693149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948592953291637604462099 1422889429937456406693149)
              ·
                refine ⟨533583536226546152509931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422889429937456406693149 533583536226546152509931)
                ·
                  refine ⟨800375304339819228764897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533583536226546152509931 800375304339819228764897)
                  ·
                    refine ⟨600281478254864421573673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800375304339819228764897 600281478254864421573673)
                    ·
                      refine ⟨450211108691148316180255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600281478254864421573673 450211108691148316180255)
                      ·
                        rfl

theorem cell23_876783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 2, 2].length) (baseStart_876783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876783 prefixEnd_876783 := by exact prefixLift 876783
  have htrace : WordTrace (prefixWord ++ tailWord_876783) baseStart_876783 baseEnd_876783 := by
    simpa [prefixWord, tailWord_876783, baseEnd_876783] using wordTrace_append hprefix tailTrace_876783
  have hstable : (prefixWord ++ tailWord_876783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876783).length < 2 ^ (prefixWord ++ tailWord_876783).sum := by decide
  have hdescent : baseEnd_876783 < baseStart_876783 := by decide
  rcases family_descends (prefixWord ++ tailWord_876783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876855 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_876855 : Nat := 118140960795 + 876855 * 2 ^ 59
def prefixEnd_876855 : Nat := 4983230072969 + 3 ^ 40 * 876855 * 2
def baseEnd_876855 : Nat := 450248079298272034479923

theorem tailTrace_876855 : CollatzResearch.WordTrace tailWord_876855 prefixEnd_876855 450248079298272034479923 := by
  unfold tailWord_876855
  simp only [CollatzResearch.WordTrace]
  refine ⟨31981529238311564756512019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21321019492207709837674679 31981529238311564756512019)
  ·
    refine ⟨47972293857467347134768029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31981529238311564756512019 47972293857467347134768029)
    ·
      refine ⟨17989610196550255175538011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47972293857467347134768029 17989610196550255175538011)
      ·
        refine ⟨26984415294825382763307017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17989610196550255175538011 26984415294825382763307017)
        ·
          refine ⟨20238311471119037072480263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26984415294825382763307017 20238311471119037072480263)
          ·
            refine ⟨30357467206678555608720395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20238311471119037072480263 30357467206678555608720395)
            ·
              refine ⟨45536200810017833413080593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30357467206678555608720395 45536200810017833413080593)
              ·
                refine ⟨34152150607513375059810445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45536200810017833413080593 34152150607513375059810445)
                ·
                  refine ⟨12807056477817515647428917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34152150607513375059810445 12807056477817515647428917)
                  ·
                    refine ⟨1200661544795392091946461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12807056477817515647428917 1200661544795392091946461)
                    ·
                      refine ⟨450248079298272034479923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200661544795392091946461 450248079298272034479923)
                      ·
                        rfl

theorem cell23_876855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_876855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876855 prefixEnd_876855 := by exact prefixLift 876855
  have htrace : WordTrace (prefixWord ++ tailWord_876855) baseStart_876855 baseEnd_876855 := by
    simpa [prefixWord, tailWord_876855, baseEnd_876855] using wordTrace_append hprefix tailTrace_876855
  have hstable : (prefixWord ++ tailWord_876855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876855).length < 2 ^ (prefixWord ++ tailWord_876855).sum := by decide
  have hdescent : baseEnd_876855 < baseStart_876855 := by decide
  rcases family_descends (prefixWord ++ tailWord_876855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876932 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_876932 : Nat := 118140960795 + 876932 * 2 ^ 59
def prefixEnd_876932 : Nat := 4983230072969 + 3 ^ 40 * 876932 * 2
def baseEnd_876932 : Nat := 450287617308668233217069

theorem tailTrace_876932 : CollatzResearch.WordTrace tailWord_876932 prefixEnd_876932 450287617308668233217069 := by
  unfold tailWord_876932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992168829516303453532525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21322891772688404604710033 15992168829516303453532525)
  ·
    refine ⟨5997063311068613795074697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15992168829516303453532525 5997063311068613795074697)
    ·
      refine ⟨4497797483301460346306023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5997063311068613795074697 4497797483301460346306023)
      ·
        refine ⟨6746696224952190519459035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497797483301460346306023 6746696224952190519459035)
        ·
          refine ⟨10120044337428285779188553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746696224952190519459035 10120044337428285779188553)
          ·
            refine ⟨7590033253071214334391415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10120044337428285779188553 7590033253071214334391415)
            ·
              refine ⟨11385049879606821501587123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7590033253071214334391415 11385049879606821501587123)
              ·
                refine ⟨17077574819410232252380685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11385049879606821501587123 17077574819410232252380685)
                ·
                  refine ⟨6404090557278837094642757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17077574819410232252380685 6404090557278837094642757)
                  ·
                    refine ⟨1200766979489781955245517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6404090557278837094642757 1200766979489781955245517)
                    ·
                      refine ⟨450287617308668233217069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1200766979489781955245517 450287617308668233217069)
                      ·
                        rfl

theorem cell23_876932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_876932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876932 prefixEnd_876932 := by exact prefixLift 876932
  have htrace : WordTrace (prefixWord ++ tailWord_876932) baseStart_876932 baseEnd_876932 := by
    simpa [prefixWord, tailWord_876932, baseEnd_876932] using wordTrace_append hprefix tailTrace_876932
  have hstable : (prefixWord ++ tailWord_876932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876932).length < 2 ^ (prefixWord ++ tailWord_876932).sum := by decide
  have hdescent : baseEnd_876932 < baseStart_876932 := by decide
  rcases family_descends (prefixWord ++ tailWord_876932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876952 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 8]
def baseStart_876952 : Nat := 118140960795 + 876952 * 2 ^ 59
def prefixEnd_876952 : Nat := 4983230072969 + 3 ^ 40 * 876952 * 2
def baseEnd_876952 : Nat := 50033098546862017218553

theorem tailTrace_876952 : CollatzResearch.WordTrace tailWord_876952 prefixEnd_876952 50033098546862017218553 := by
  unfold tailWord_876952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992533559480075161396555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21323378079306766881862073 15992533559480075161396555)
  ·
    refine ⟨23988800339220112742094833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15992533559480075161396555 23988800339220112742094833)
    ·
      refine ⟨17991600254415084556571125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23988800339220112742094833 17991600254415084556571125)
      ·
        refine ⟨1686712523851414177178543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17991600254415084556571125 1686712523851414177178543)
        ·
          refine ⟨2530068785777121265767815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686712523851414177178543 2530068785777121265767815)
          ·
            refine ⟨3795103178665681898651723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530068785777121265767815 3795103178665681898651723)
            ·
              refine ⟨5692654767998522847977585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795103178665681898651723 5692654767998522847977585)
              ·
                refine ⟨4269491075998892135983189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692654767998522847977585 4269491075998892135983189)
                ·
                  refine ⟨50033098546862017218553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4269491075998892135983189 50033098546862017218553)
                  ·
                    rfl

theorem cell23_876952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_876952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876952 prefixEnd_876952 := by exact prefixLift 876952
  have htrace : WordTrace (prefixWord ++ tailWord_876952) baseStart_876952 baseEnd_876952 := by
    simpa [prefixWord, tailWord_876952, baseEnd_876952] using wordTrace_append hprefix tailTrace_876952
  have hstable : (prefixWord ++ tailWord_876952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876952).length < 2 ^ (prefixWord ++ tailWord_876952).sum := by decide
  have hdescent : baseEnd_876952 < baseStart_876952 := by decide
  rcases family_descends (prefixWord ++ tailWord_876952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876973 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_876973 : Nat := 118140960795 + 876973 * 2 ^ 59
def prefixEnd_876973 : Nat := 4983230072969 + 3 ^ 40 * 876973 * 2
def baseEnd_876973 : Nat := 150102890005167524268127

theorem tailTrace_876973 : CollatzResearch.WordTrace tailWord_876973 prefixEnd_876973 150102890005167524268127 := by
  unfold tailWord_876973
  simp only [CollatzResearch.WordTrace]
  refine ⟨31985833051884070909307573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21323888701256047272871715 31985833051884070909307573)
  ·
    refine ⟨2998671848614131647747585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31985833051884070909307573 2998671848614131647747585)
    ·
      refine ⟨2249003886460598735810689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2998671848614131647747585 2249003886460598735810689)
      ·
        refine ⟨1686752914845449051858017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2249003886460598735810689 1686752914845449051858017)
        ·
          refine ⟨1265064686134086788893513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1686752914845449051858017 1265064686134086788893513)
          ·
            refine ⟨948798514600565091670135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265064686134086788893513 948798514600565091670135)
            ·
              refine ⟨1423197771900847637505203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948798514600565091670135 1423197771900847637505203)
              ·
                refine ⟨2134796657851271456257805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423197771900847637505203 2134796657851271456257805)
                ·
                  refine ⟨800548746694226796096677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2134796657851271456257805 800548746694226796096677)
                  ·
                    refine ⟨150102890005167524268127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 800548746694226796096677 150102890005167524268127)
                    ·
                      rfl

theorem cell23_876973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_876973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876973 prefixEnd_876973 := by exact prefixLift 876973
  have htrace : WordTrace (prefixWord ++ tailWord_876973) baseStart_876973 baseEnd_876973 := by
    simpa [prefixWord, tailWord_876973, baseEnd_876973] using wordTrace_append hprefix tailTrace_876973
  have hstable : (prefixWord ++ tailWord_876973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876973).length < 2 ^ (prefixWord ++ tailWord_876973).sum := by decide
  have hdescent : baseEnd_876973 < baseStart_876973 := by decide
  rcases family_descends (prefixWord ++ tailWord_876973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876975 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_876975 : Nat := 118140960795 + 876975 * 2 ^ 59
def prefixEnd_876975 : Nat := 4983230072969 + 3 ^ 40 * 876975 * 2
def baseEnd_876975 : Nat := 450309696976811564979371

theorem tailTrace_876975 : CollatzResearch.WordTrace tailWord_876975 prefixEnd_876975 450309696976811564979371 := by
  unfold tailWord_876975
  simp only [CollatzResearch.WordTrace]
  refine ⟨31985905997876825250880379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21323937331917883500586919 31985905997876825250880379)
  ·
    refine ⟨47978858996815237876320569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31985905997876825250880379 47978858996815237876320569)
    ·
      refine ⟨35984144247611428407240427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47978858996815237876320569 35984144247611428407240427)
      ·
        refine ⟨53976216371417142610860641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35984144247611428407240427 53976216371417142610860641)
        ·
          refine ⟨40482162278562856958145481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53976216371417142610860641 40482162278562856958145481)
          ·
            refine ⟨30361621708922142718609111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40482162278562856958145481 30361621708922142718609111)
            ·
              refine ⟨45542432563383214077913667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30361621708922142718609111 45542432563383214077913667)
              ·
                refine ⟨68313648845074821116870501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45542432563383214077913667 68313648845074821116870501)
                ·
                  refine ⟨12808809158451528959413219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68313648845074821116870501 12808809158451528959413219)
                  ·
                    refine ⟨19213213737677293439119829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12808809158451528959413219 19213213737677293439119829)
                    ·
                      refine ⟨450309696976811564979371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19213213737677293439119829 450309696976811564979371)
                      ·
                        rfl

theorem cell23_876975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_876975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876975 prefixEnd_876975 := by exact prefixLift 876975
  have htrace : WordTrace (prefixWord ++ tailWord_876975) baseStart_876975 baseEnd_876975 := by
    simpa [prefixWord, tailWord_876975, baseEnd_876975] using wordTrace_append hprefix tailTrace_876975
  have hstable : (prefixWord ++ tailWord_876975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876975).length < 2 ^ (prefixWord ++ tailWord_876975).sum := by decide
  have hdescent : baseEnd_876975 < baseStart_876975 := by decide
  rcases family_descends (prefixWord ++ tailWord_876975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876999 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 1, 5]
def baseStart_876999 : Nat := 118140960795 + 876999 * 2 ^ 59
def prefixEnd_876999 : Nat := 4983230072969 + 3 ^ 40 * 876999 * 2
def baseEnd_876999 : Nat := 150107340170839823693087

theorem tailTrace_876999 : CollatzResearch.WordTrace tailWord_876999 prefixEnd_876999 150107340170839823693087 := by
  unfold tailWord_876999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31986781349789877349754051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21324520899859918233169367 31986781349789877349754051)
  ·
    refine ⟨47980172024684816024631077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31986781349789877349754051 47980172024684816024631077)
    ·
      refine ⟨8996282254628403004618327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47980172024684816024631077 8996282254628403004618327)
      ·
        refine ⟨13494423381942604506927491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996282254628403004618327 13494423381942604506927491)
        ·
          refine ⟨20241635072913906760391237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13494423381942604506927491 20241635072913906760391237)
          ·
            refine ⟨3795306576171357517573357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20241635072913906760391237 3795306576171357517573357)
            ·
              refine ⟨1423239966064259069090009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3795306576171357517573357 1423239966064259069090009)
              ·
                refine ⟨1067429974548194301817507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423239966064259069090009 1067429974548194301817507)
                ·
                  refine ⟨1601144961822291452726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067429974548194301817507 1601144961822291452726261)
                  ·
                    refine ⟨150107340170839823693087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1601144961822291452726261 150107340170839823693087)
                    ·
                      rfl

theorem cell23_876999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_876999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_876999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_876999 prefixEnd_876999 := by exact prefixLift 876999
  have htrace : WordTrace (prefixWord ++ tailWord_876999) baseStart_876999 baseEnd_876999 := by
    simpa [prefixWord, tailWord_876999, baseEnd_876999] using wordTrace_append hprefix tailTrace_876999
  have hstable : (prefixWord ++ tailWord_876999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876999).length < 2 ^ (prefixWord ++ tailWord_876999).sum := by decide
  have hdescent : baseEnd_876999 < baseStart_876999 := by decide
  rcases family_descends (prefixWord ++ tailWord_876999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877036 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_877036 : Nat := 118140960795 + 877036 * 2 ^ 59
def prefixEnd_877036 : Nat := 4983230072969 + 3 ^ 40 * 877036 * 2
def baseEnd_877036 : Nat := 450341019296735826316591

theorem tailTrace_877036 : CollatzResearch.WordTrace tailWord_877036 prefixEnd_877036 450341019296735826316591 := by
  unfold tailWord_877036
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994065425327916334425481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21325420567103888445900641 15994065425327916334425481)
  ·
    refine ⟨11995549068995937250819111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15994065425327916334425481 11995549068995937250819111)
    ·
      refine ⟨17993323603493905876228667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11995549068995937250819111 17993323603493905876228667)
      ·
        refine ⟨26989985405240858814343001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17993323603493905876228667 26989985405240858814343001)
        ·
          refine ⟨20242489053930644110757251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26989985405240858814343001 20242489053930644110757251)
          ·
            refine ⟨30363733580895966166135877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20242489053930644110757251 30363733580895966166135877)
            ·
              refine ⟨5693200046417993656150477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30363733580895966166135877 5693200046417993656150477)
              ·
                refine ⟨2134950017406747621056429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5693200046417993656150477 2134950017406747621056429)
                ·
                  refine ⟨800606256527530357896161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2134950017406747621056429 800606256527530357896161)
                  ·
                    refine ⟨600454692395647768422121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800606256527530357896161 600454692395647768422121)
                    ·
                      refine ⟨450341019296735826316591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600454692395647768422121 450341019296735826316591)
                      ·
                        rfl

theorem cell23_877036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_877036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877036 prefixEnd_877036 := by exact prefixLift 877036
  have htrace : WordTrace (prefixWord ++ tailWord_877036) baseStart_877036 baseEnd_877036 := by
    simpa [prefixWord, tailWord_877036, baseEnd_877036] using wordTrace_append hprefix tailTrace_877036
  have hstable : (prefixWord ++ tailWord_877036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877036).length < 2 ^ (prefixWord ++ tailWord_877036).sum := by decide
  have hdescent : baseEnd_877036 < baseStart_877036 := by decide
  rcases family_descends (prefixWord ++ tailWord_877036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877046 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_877046 : Nat := 118140960795 + 877046 * 2 ^ 59
def prefixEnd_877046 : Nat := 4983230072969 + 3 ^ 40 * 877046 * 2
def baseEnd_877046 : Nat := 150115384701093595730515

theorem tailTrace_877046 : CollatzResearch.WordTrace tailWord_877046 prefixEnd_877046 150115384701093595730515 := by
  unfold tailWord_877046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999280973788725273544687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21325663720413069584476661 1999280973788725273544687)
  ·
    refine ⟨2998921460683087910317031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1999280973788725273544687 2998921460683087910317031)
    ·
      refine ⟨4498382191024631865475547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998921460683087910317031 4498382191024631865475547)
      ·
        refine ⟨6747573286536947798213321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498382191024631865475547 6747573286536947798213321)
        ·
          refine ⟨5060679964902710848659991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6747573286536947798213321 5060679964902710848659991)
          ·
            refine ⟨7591019947354066272989987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060679964902710848659991 7591019947354066272989987)
            ·
              refine ⟨11386529921031099409484981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7591019947354066272989987 11386529921031099409484981)
              ·
                refine ⟨1067487180096665569639217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11386529921031099409484981 1067487180096665569639217)
                ·
                  refine ⟨800615385072499177229413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067487180096665569639217 800615385072499177229413)
                  ·
                    refine ⟨150115384701093595730515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 800615385072499177229413 150115384701093595730515)
                    ·
                      rfl

theorem cell23_877046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_877046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877046 prefixEnd_877046 := by exact prefixLift 877046
  have htrace : WordTrace (prefixWord ++ tailWord_877046) baseStart_877046 baseEnd_877046 := by
    simpa [prefixWord, tailWord_877046, baseEnd_877046] using wordTrace_append hprefix tailTrace_877046
  have hstable : (prefixWord ++ tailWord_877046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877046).length < 2 ^ (prefixWord ++ tailWord_877046).sum := by decide
  have hdescent : baseEnd_877046 < baseStart_877046 := by decide
  rcases family_descends (prefixWord ++ tailWord_877046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877070 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_877070 : Nat := 118140960795 + 877070 * 2 ^ 59
def prefixEnd_877070 : Nat := 4983230072969 + 3 ^ 40 * 877070 * 2
def baseEnd_877070 : Nat := 450358477638988693291435

theorem tailTrace_877070 : CollatzResearch.WordTrace tailWord_877070 prefixEnd_877070 450358477638988693291435 := by
  unfold tailWord_877070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998671366566582059448583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21326247288355104317059109 3998671366566582059448583)
  ·
    refine ⟨5998007049849873089172875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998671366566582059448583 5998007049849873089172875)
    ·
      refine ⟨8997010574774809633759313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998007049849873089172875 8997010574774809633759313)
      ·
        refine ⟨6747757931081107225319485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997010574774809633759313 6747757931081107225319485)
        ·
          refine ⟨2530409224155415209494807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6747757931081107225319485 2530409224155415209494807)
          ·
            refine ⟨3795613836233122814242211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530409224155415209494807 3795613836233122814242211)
            ·
              refine ⟨5693420754349684221363317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795613836233122814242211 5693420754349684221363317)
              ·
                refine ⟨533758195720282895752811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5693420754349684221363317 533758195720282895752811)
                ·
                  refine ⟨800637293580424343629217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533758195720282895752811 800637293580424343629217)
                  ·
                    refine ⟨600477970185318257721913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800637293580424343629217 600477970185318257721913)
                    ·
                      refine ⟨450358477638988693291435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600477970185318257721913 450358477638988693291435)
                      ·
                        rfl

theorem cell23_877070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_877070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877070 prefixEnd_877070 := by exact prefixLift 877070
  have htrace : WordTrace (prefixWord ++ tailWord_877070) baseStart_877070 baseEnd_877070 := by
    simpa [prefixWord, tailWord_877070, baseEnd_877070] using wordTrace_append hprefix tailTrace_877070
  have hstable : (prefixWord ++ tailWord_877070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877070).length < 2 ^ (prefixWord ++ tailWord_877070).sum := by decide
  have hdescent : baseEnd_877070 < baseStart_877070 := by decide
  rcases family_descends (prefixWord ++ tailWord_877070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877113 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 1, 3, 2]
def baseStart_877113 : Nat := 118140960795 + 877113 * 2 ^ 59
def prefixEnd_877113 : Nat := 4983230072969 + 3 ^ 40 * 877113 * 2
def baseEnd_877113 : Nat := 450380557307132025053737

theorem tailTrace_877113 : CollatzResearch.WordTrace tailWord_877113 prefixEnd_877113 450380557307132025053737 := by
  unfold tailWord_877113
  simp only [CollatzResearch.WordTrace]
  refine ⟨31990939271376874819403993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21327292847584583212935995 31990939271376874819403993)
  ·
    refine ⟨23993204453532656114552995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31990939271376874819403993 23993204453532656114552995)
    ·
      refine ⟨35989806680298984171829493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23993204453532656114552995 35989806680298984171829493)
      ·
        refine ⟨3374044376278029766109015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35989806680298984171829493 3374044376278029766109015)
        ·
          refine ⟨5061066564417044649163523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374044376278029766109015 5061066564417044649163523)
          ·
            refine ⟨7591599846625566973745285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061066564417044649163523 7591599846625566973745285)
            ·
              refine ⟨1423424971242293807577241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7591599846625566973745285 1423424971242293807577241)
              ·
                refine ⟨1067568728431720355682931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423424971242293807577241 1067568728431720355682931)
                ·
                  refine ⟨1601353092647580533524397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067568728431720355682931 1601353092647580533524397)
                  ·
                    refine ⟨600507409742842700071649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601353092647580533524397 600507409742842700071649)
                    ·
                      refine ⟨450380557307132025053737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600507409742842700071649 450380557307132025053737)
                      ·
                        rfl

theorem cell23_877113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_877113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877113 prefixEnd_877113 := by exact prefixLift 877113
  have htrace : WordTrace (prefixWord ++ tailWord_877113) baseStart_877113 baseEnd_877113 := by
    simpa [prefixWord, tailWord_877113, baseEnd_877113] using wordTrace_append hprefix tailTrace_877113
  have hstable : (prefixWord ++ tailWord_877113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877113).length < 2 ^ (prefixWord ++ tailWord_877113).sum := by decide
  have hdescent : baseEnd_877113 < baseStart_877113 := by decide
  rcases family_descends (prefixWord ++ tailWord_877113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877143 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_877143 : Nat := 118140960795 + 877143 * 2 ^ 59
def prefixEnd_877143 : Nat := 4983230072969 + 3 ^ 40 * 877143 * 2
def baseEnd_877143 : Nat := 450395961726766907678599

theorem tailTrace_877143 : CollatzResearch.WordTrace tailWord_877143 prefixEnd_877143 450395961726766907678599 := by
  unfold tailWord_877143
  simp only [CollatzResearch.WordTrace]
  refine ⟨31992033461268189942996083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21328022307512126628664055 31992033461268189942996083)
  ·
    refine ⟨47988050191902284914494125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31992033461268189942996083 47988050191902284914494125)
    ·
      refine ⟨17995518821963356842935297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47988050191902284914494125 17995518821963356842935297)
      ·
        refine ⟨13496639116472517632201473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17995518821963356842935297 13496639116472517632201473)
        ·
          refine ⟨10122479337354388224151105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13496639116472517632201473 10122479337354388224151105)
          ·
            refine ⟨7591859503015791168113329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10122479337354388224151105 7591859503015791168113329)
            ·
              refine ⟨5693894627261843376084997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591859503015791168113329 5693894627261843376084997)
              ·
                refine ⟨1067605242611595633015937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5693894627261843376084997 1067605242611595633015937)
                ·
                  refine ⟨800703931958696724761953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067605242611595633015937 800703931958696724761953)
                  ·
                    refine ⟨600527948969022543571465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 800703931958696724761953 600527948969022543571465)
                    ·
                      refine ⟨450395961726766907678599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600527948969022543571465 450395961726766907678599)
                      ·
                        rfl

theorem cell23_877143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_877143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877143 prefixEnd_877143 := by exact prefixLift 877143
  have htrace : WordTrace (prefixWord ++ tailWord_877143) baseStart_877143 baseEnd_877143 := by
    simpa [prefixWord, tailWord_877143, baseEnd_877143] using wordTrace_append hprefix tailTrace_877143
  have hstable : (prefixWord ++ tailWord_877143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877143).length < 2 ^ (prefixWord ++ tailWord_877143).sum := by decide
  have hdescent : baseEnd_877143 < baseStart_877143 := by decide
  rcases family_descends (prefixWord ++ tailWord_877143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877154 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_877154 : Nat := 118140960795 + 877154 * 2 ^ 59
def prefixEnd_877154 : Nat := 4983230072969 + 3 ^ 40 * 877154 * 2
def baseEnd_877154 : Nat := 450401610013966364641049

theorem tailTrace_877154 : CollatzResearch.WordTrace tailWord_877154 prefixEnd_877154 450401610013966364641049 := by
  unfold tailWord_877154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998108666057084705411629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21328289776152225881097677 7998108666057084705411629)
  ·
    refine ⟨2999290749771406764529361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7998108666057084705411629 2999290749771406764529361)
    ·
      refine ⟨2249468062328555073397021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2999290749771406764529361 2249468062328555073397021)
      ·
        refine ⟨843550523373208152523883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2249468062328555073397021 843550523373208152523883)
        ·
          refine ⟨1265325785059812228785825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843550523373208152523883 1265325785059812228785825)
          ·
            refine ⟨948994338794859171589369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265325785059812228785825 948994338794859171589369)
            ·
              refine ⟨711745754096144378692027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948994338794859171589369 711745754096144378692027)
              ·
                refine ⟨1067618631144216568038041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711745754096144378692027 1067618631144216568038041)
                ·
                  refine ⟨800713973358162426028531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067618631144216568038041 800713973358162426028531)
                  ·
                    refine ⟨1201070960037243639042797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 800713973358162426028531 1201070960037243639042797)
                    ·
                      refine ⟨450401610013966364641049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201070960037243639042797 450401610013966364641049)
                      ·
                        rfl

theorem cell23_877154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_877154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877154 prefixEnd_877154 := by exact prefixLift 877154
  have htrace : WordTrace (prefixWord ++ tailWord_877154) baseStart_877154 baseEnd_877154 := by
    simpa [prefixWord, tailWord_877154, baseEnd_877154] using wordTrace_append hprefix tailTrace_877154
  have hstable : (prefixWord ++ tailWord_877154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877154).length < 2 ^ (prefixWord ++ tailWord_877154).sum := by decide
  have hdescent : baseEnd_877154 < baseStart_877154 := by decide
  rcases family_descends (prefixWord ++ tailWord_877154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877159 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_877159 : Nat := 118140960795 + 877159 * 2 ^ 59
def prefixEnd_877159 : Nat := 4983230072969 + 3 ^ 40 * 877159 * 2
def baseEnd_877159 : Nat := 450404177417238845078525

theorem tailTrace_877159 : CollatzResearch.WordTrace tailWord_877159 prefixEnd_877159 450404177417238845078525 := by
  unfold tailWord_877159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31992617029210224675578531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21328411352806816450385687 31992617029210224675578531)
  ·
    refine ⟨47988925543815337013367797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31992617029210224675578531 47988925543815337013367797)
    ·
      refine ⟨4498961769732687845003231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47988925543815337013367797 4498961769732687845003231)
      ·
        refine ⟨6748442654599031767504847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498961769732687845003231 6748442654599031767504847)
        ·
          refine ⟨10122663981898547651257271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748442654599031767504847 10122663981898547651257271)
          ·
            refine ⟨15183995972847821476885907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122663981898547651257271 15183995972847821476885907)
            ·
              refine ⟨22775993959271732215328861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15183995972847821476885907 22775993959271732215328861)
              ·
                refine ⟨8540997734726899580748323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22775993959271732215328861 8540997734726899580748323)
                ·
                  refine ⟨12811496602090349371122485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8540997734726899580748323 12811496602090349371122485)
                  ·
                    refine ⟨1201077806445970253542733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12811496602090349371122485 1201077806445970253542733)
                    ·
                      refine ⟨450404177417238845078525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201077806445970253542733 450404177417238845078525)
                      ·
                        rfl

theorem cell23_877159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_877159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877159 prefixEnd_877159 := by exact prefixLift 877159
  have htrace : WordTrace (prefixWord ++ tailWord_877159) baseStart_877159 baseEnd_877159 := by
    simpa [prefixWord, tailWord_877159, baseEnd_877159] using wordTrace_append hprefix tailTrace_877159
  have hstable : (prefixWord ++ tailWord_877159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877159).length < 2 ^ (prefixWord ++ tailWord_877159).sum := by decide
  have hdescent : baseEnd_877159 < baseStart_877159 := by decide
  rcases family_descends (prefixWord ++ tailWord_877159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877189 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_877189 : Nat := 118140960795 + 877189 * 2 ^ 59
def prefixEnd_877189 : Nat := 4983230072969 + 3 ^ 40 * 877189 * 2
def baseEnd_877189 : Nat := 450419581836873727703387

theorem tailTrace_877189 : CollatzResearch.WordTrace tailWord_877189 prefixEnd_877189 450419581836873727703387 := by
  unfold tailWord_877189
  simp only [CollatzResearch.WordTrace]
  refine ⟨31993711219101539799170621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21329140812734359866113747 31993711219101539799170621)
  ·
    refine ⟨11997641707163077424688983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31993711219101539799170621 11997641707163077424688983)
    ·
      refine ⟨17996462560744616137033475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11997641707163077424688983 17996462560744616137033475)
      ·
        refine ⟨26994693841116924205550213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17996462560744616137033475 26994693841116924205550213)
        ·
          refine ⟨5061505095209423288540665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26994693841116924205550213 5061505095209423288540665)
          ·
            refine ⟨3796128821407067466405499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061505095209423288540665 3796128821407067466405499)
            ·
              refine ⟨5694193232110601199608249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796128821407067466405499 5694193232110601199608249)
              ·
                refine ⟨4270644924082950899706187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5694193232110601199608249 4270644924082950899706187)
                ·
                  refine ⟨6405967386124426349559281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270644924082950899706187 6405967386124426349559281)
                  ·
                    refine ⟨4804475539593319762169461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6405967386124426349559281 4804475539593319762169461)
                    ·
                      refine ⟨450419581836873727703387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4804475539593319762169461 450419581836873727703387)
                      ·
                        rfl

theorem cell23_877189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_877189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877189 prefixEnd_877189 := by exact prefixLift 877189
  have htrace : WordTrace (prefixWord ++ tailWord_877189) baseStart_877189 baseEnd_877189 := by
    simpa [prefixWord, tailWord_877189, baseEnd_877189] using wordTrace_append hprefix tailTrace_877189
  have hstable : (prefixWord ++ tailWord_877189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877189).length < 2 ^ (prefixWord ++ tailWord_877189).sum := by decide
  have hdescent : baseEnd_877189 < baseStart_877189 := by decide
  rcases family_descends (prefixWord ++ tailWord_877189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877230 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_877230 : Nat := 118140960795 + 877230 * 2 ^ 59
def prefixEnd_877230 : Nat := 4983230072969 + 3 ^ 40 * 877230 * 2
def baseEnd_877230 : Nat := 150146878181236022430233

theorem tailTrace_877230 : CollatzResearch.WordTrace tailWord_877230 prefixEnd_877230 150146878181236022430233 := by
  unfold tailWord_877230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999400826494125475176643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21330137741302002534275429 3999400826494125475176643)
  ·
    refine ⟨5999101239741188212764965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3999400826494125475176643 5999101239741188212764965)
    ·
      refine ⟨1124831482451472789893431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5999101239741188212764965 1124831482451472789893431)
      ·
        refine ⟨1687247223677209184840147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124831482451472789893431 1687247223677209184840147)
        ·
          refine ⟨2530870835515813777260221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687247223677209184840147 2530870835515813777260221)
          ·
            refine ⟨949076563318430166472583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2530870835515813777260221 949076563318430166472583)
            ·
              refine ⟨1423614844977645249708875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949076563318430166472583 1423614844977645249708875)
              ·
                refine ⟨2135422267466467874563313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423614844977645249708875 2135422267466467874563313)
                ·
                  refine ⟨1601566700599850905922485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135422267466467874563313 1601566700599850905922485)
                  ·
                    refine ⟨150146878181236022430233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1601566700599850905922485 150146878181236022430233)
                    ·
                      rfl

theorem cell23_877230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_877230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877230 prefixEnd_877230 := by exact prefixLift 877230
  have htrace : WordTrace (prefixWord ++ tailWord_877230) baseStart_877230 baseEnd_877230 := by
    simpa [prefixWord, tailWord_877230, baseEnd_877230] using wordTrace_append hprefix tailTrace_877230
  have hstable : (prefixWord ++ tailWord_877230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877230).length < 2 ^ (prefixWord ++ tailWord_877230).sum := by decide
  have hdescent : baseEnd_877230 < baseStart_877230 := by decide
  rcases family_descends (prefixWord ++ tailWord_877230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877233 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_877233 : Nat := 118140960795 + 877233 * 2 ^ 59
def prefixEnd_877233 : Nat := 4983230072969 + 3 ^ 40 * 877233 * 2
def baseEnd_877233 : Nat := 450442174985671555553185

theorem tailTrace_877233 : CollatzResearch.WordTrace tailWord_877233 prefixEnd_877233 450442174985671555553185 := by
  unfold tailWord_877233
  simp only [CollatzResearch.WordTrace]
  refine ⟨31995316030942135313772353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21330210687294756875848235 31995316030942135313772353)
  ·
    refine ⟨23996487023206601485329265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31995316030942135313772353 23996487023206601485329265)
    ·
      refine ⟨17997365267404951113996949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23996487023206601485329265 17997365267404951113996949)
      ·
        refine ⟨843626496909607083468607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17997365267404951113996949 843626496909607083468607)
        ·
          refine ⟨1265439745364410625202911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843626496909607083468607 1265439745364410625202911)
          ·
            refine ⟨1898159618046615937804367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265439745364410625202911 1898159618046615937804367)
            ·
              refine ⟨2847239427069923906706551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898159618046615937804367 2847239427069923906706551)
              ·
                refine ⟨4270859140604885860059827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847239427069923906706551 4270859140604885860059827)
                ·
                  refine ⟨6406288710907328790089741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4270859140604885860059827 6406288710907328790089741)
                  ·
                    refine ⟨2402358266590248296283653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6406288710907328790089741 2402358266590248296283653)
                    ·
                      refine ⟨450442174985671555553185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2402358266590248296283653 450442174985671555553185)
                      ·
                        rfl

theorem cell23_877233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_877233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877233 prefixEnd_877233 := by exact prefixLift 877233
  have htrace : WordTrace (prefixWord ++ tailWord_877233) baseStart_877233 baseEnd_877233 := by
    simpa [prefixWord, tailWord_877233, baseEnd_877233] using wordTrace_append hprefix tailTrace_877233
  have hstable : (prefixWord ++ tailWord_877233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877233).length < 2 ^ (prefixWord ++ tailWord_877233).sum := by decide
  have hdescent : baseEnd_877233 < baseStart_877233 := by decide
  rcases family_descends (prefixWord ++ tailWord_877233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877256 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 6]
def baseStart_877256 : Nat := 118140960795 + 877256 * 2 ^ 59
def prefixEnd_877256 : Nat := 4983230072969 + 3 ^ 40 * 877256 * 2
def baseEnd_877256 : Nat := 50050442782302773951731

theorem tailTrace_877256 : CollatzResearch.WordTrace tailWord_877256 prefixEnd_877256 50050442782302773951731 := by
  unfold tailWord_877256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15998077454929405120929811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21330769939905873494573081 15998077454929405120929811)
  ·
    refine ⟨23997116182394107681394717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15998077454929405120929811 23997116182394107681394717)
    ·
      refine ⟨8998918568397790380523019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23997116182394107681394717 8998918568397790380523019)
      ·
        refine ⟨13498377852596685570784529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8998918568397790380523019 13498377852596685570784529)
        ·
          refine ⟨10123783389447514178088397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13498377852596685570784529 10123783389447514178088397)
          ·
            refine ⟨3796418771042817816783149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10123783389447514178088397 3796418771042817816783149)
            ·
              refine ⟨1423657039141056681293681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3796418771042817816783149 1423657039141056681293681)
              ·
                refine ⟨1067742779355792510970261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423657039141056681293681 1067742779355792510970261)
                ·
                  refine ⟨50050442782302773951731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1067742779355792510970261 50050442782302773951731)
                  ·
                    rfl

theorem cell23_877256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_877256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877256 prefixEnd_877256 := by exact prefixLift 877256
  have htrace : WordTrace (prefixWord ++ tailWord_877256) baseStart_877256 baseEnd_877256 := by
    simpa [prefixWord, tailWord_877256, baseEnd_877256] using wordTrace_append hprefix tailTrace_877256
  have hstable : (prefixWord ++ tailWord_877256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877256).length < 2 ^ (prefixWord ++ tailWord_877256).sum := by decide
  have hdescent : baseEnd_877256 < baseStart_877256 := by decide
  rcases family_descends (prefixWord ++ tailWord_877256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877260 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_877260 : Nat := 118140960795 + 877260 * 2 ^ 59
def prefixEnd_877260 : Nat := 4983230072969 + 3 ^ 40 * 877260 * 2
def baseEnd_877260 : Nat := 150152012987780983305187

theorem tailTrace_877260 : CollatzResearch.WordTrace tailWord_877260 prefixEnd_877260 150152012987780983305187 := by
  unfold tailWord_877260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15998150400922159462502617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21330867201229545950003489 15998150400922159462502617)
  ·
    refine ⟨11998612800691619596876963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15998150400922159462502617 11998612800691619596876963)
    ·
      refine ⟨17997919201037429395315445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998612800691619596876963 17997919201037429395315445)
      ·
        refine ⟨1687304925097259005810823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17997919201037429395315445 1687304925097259005810823)
        ·
          refine ⟨2530957387645888508716235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687304925097259005810823 2530957387645888508716235)
          ·
            refine ⟨3796436081468832763074353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530957387645888508716235 3796436081468832763074353)
            ·
              refine ⟨2847327061101624572305765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796436081468832763074353 2847327061101624572305765)
              ·
                refine ⟨533873823956554607307331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847327061101624572305765 533873823956554607307331)
                ·
                  refine ⟨800810735934831910960997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533873823956554607307331 800810735934831910960997)
                  ·
                    refine ⟨150152012987780983305187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 800810735934831910960997 150152012987780983305187)
                    ·
                      rfl

theorem cell23_877260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_877260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877260 prefixEnd_877260 := by exact prefixLift 877260
  have htrace : WordTrace (prefixWord ++ tailWord_877260) baseStart_877260 baseEnd_877260 := by
    simpa [prefixWord, tailWord_877260, baseEnd_877260] using wordTrace_append hprefix tailTrace_877260
  have hstable : (prefixWord ++ tailWord_877260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877260).length < 2 ^ (prefixWord ++ tailWord_877260).sum := by decide
  have hdescent : baseEnd_877260 < baseStart_877260 := by decide
  rcases family_descends (prefixWord ++ tailWord_877260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877293 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_877293 : Nat := 118140960795 + 877293 * 2 ^ 59
def prefixEnd_877293 : Nat := 4983230072969 + 3 ^ 40 * 877293 * 2
def baseEnd_877293 : Nat := 450472983824941320802909

theorem tailTrace_877293 : CollatzResearch.WordTrace tailWord_877293 prefixEnd_877293 450472983824941320802909 := by
  unfold tailWord_877293
  simp only [CollatzResearch.WordTrace]
  refine ⟨31997504410724765560956533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21331669607149843707304355 31997504410724765560956533)
  ·
    refine ⟨2999766038505446771339675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31997504410724765560956533 2999766038505446771339675)
    ·
      refine ⟨4499649057758170157009513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2999766038505446771339675 4499649057758170157009513)
      ·
        refine ⟨3374736793318627617757135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4499649057758170157009513 3374736793318627617757135)
        ·
          refine ⟨5062105189977941426635703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374736793318627617757135 5062105189977941426635703)
          ·
            refine ⟨7593157784966912139953555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062105189977941426635703 7593157784966912139953555)
            ·
              refine ⟨11389736677450368209930333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593157784966912139953555 11389736677450368209930333)
              ·
                refine ⟨4271151254043888078723875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11389736677450368209930333 4271151254043888078723875)
                ·
                  refine ⟨6406726881065832118085813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271151254043888078723875 6406726881065832118085813)
                  ·
                    refine ⟨600630645099921761070545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6406726881065832118085813 600630645099921761070545)
                    ·
                      refine ⟨450472983824941320802909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600630645099921761070545 450472983824941320802909)
                      ·
                        rfl

theorem cell23_877293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_877293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877293 prefixEnd_877293 := by exact prefixLift 877293
  have htrace : WordTrace (prefixWord ++ tailWord_877293) baseStart_877293 baseEnd_877293 := by
    simpa [prefixWord, tailWord_877293, baseEnd_877293] using wordTrace_append hprefix tailTrace_877293
  have hstable : (prefixWord ++ tailWord_877293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877293).length < 2 ^ (prefixWord ++ tailWord_877293).sum := by decide
  have hdescent : baseEnd_877293 < baseStart_877293 := by decide
  rcases family_descends (prefixWord ++ tailWord_877293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877299 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 3, 6]
def baseStart_877299 : Nat := 118140960795 + 877299 * 2 ^ 59
def prefixEnd_877299 : Nat := 4983230072969 + 3 ^ 40 * 877299 * 2
def baseEnd_877299 : Nat := 150158688236289432442627

theorem tailTrace_877299 : CollatzResearch.WordTrace tailWord_877299 prefixEnd_877299 150158688236289432442627 := by
  unfold tailWord_877299
  simp only [CollatzResearch.WordTrace]
  refine ⟨31997723248703028585674951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21331815499135352390449967 31997723248703028585674951)
  ·
    refine ⟨47996584873054542878512427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31997723248703028585674951 47996584873054542878512427)
    ·
      refine ⟨71994877309581814317768641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47996584873054542878512427 71994877309581814317768641)
      ·
        refine ⟨53996157982186360738326481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71994877309581814317768641 53996157982186360738326481)
        ·
          refine ⟨40497118486639770553744861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53996157982186360738326481 40497118486639770553744861)
          ·
            refine ⟨15186419432489913957654323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40497118486639770553744861 15186419432489913957654323)
            ·
              refine ⟨22779629148734870936481485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15186419432489913957654323 22779629148734870936481485)
              ·
                refine ⟨8542360930775576601180557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22779629148734870936481485 8542360930775576601180557)
                ·
                  refine ⟨3203385349040841225442709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8542360930775576601180557 3203385349040841225442709)
                  ·
                    refine ⟨150158688236289432442627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3203385349040841225442709 150158688236289432442627)
                    ·
                      rfl

theorem cell23_877299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 6].length) (baseStart_877299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877299 prefixEnd_877299 := by exact prefixLift 877299
  have htrace : WordTrace (prefixWord ++ tailWord_877299) baseStart_877299 baseEnd_877299 := by
    simpa [prefixWord, tailWord_877299, baseEnd_877299] using wordTrace_append hprefix tailTrace_877299
  have hstable : (prefixWord ++ tailWord_877299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877299).length < 2 ^ (prefixWord ++ tailWord_877299).sum := by decide
  have hdescent : baseEnd_877299 < baseStart_877299 := by decide
  rcases family_descends (prefixWord ++ tailWord_877299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877310 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_877310 : Nat := 118140960795 + 877310 * 2 ^ 59
def prefixEnd_877310 : Nat := 4983230072969 + 3 ^ 40 * 877310 * 2
def baseEnd_877310 : Nat := 450481712996067754290331

theorem tailTrace_877310 : CollatzResearch.WordTrace tailWord_877310 prefixEnd_877310 450481712996067754290331 := by
  unfold tailWord_877310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999765556457897183040673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21332082967775451642883589 3999765556457897183040673)
  ·
    refine ⟨2999824167343422887280505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3999765556457897183040673 2999824167343422887280505)
    ·
      refine ⟨2249868125507567165460379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2999824167343422887280505 2249868125507567165460379)
      ·
        refine ⟨3374802188261350748190569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249868125507567165460379 3374802188261350748190569)
        ·
          refine ⟨2531101641196013061142927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3374802188261350748190569 2531101641196013061142927)
          ·
            refine ⟨3796652461794019591714391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531101641196013061142927 3796652461794019591714391)
            ·
              refine ⟨5694978692691029387571587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796652461794019591714391 5694978692691029387571587)
              ·
                refine ⟨8542468039036544081357381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694978692691029387571587 8542468039036544081357381)
                ·
                  refine ⟨1601712757319352015254509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8542468039036544081357381 1601712757319352015254509)
                  ·
                    refine ⟨600642283994757005720441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601712757319352015254509 600642283994757005720441)
                    ·
                      refine ⟨450481712996067754290331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600642283994757005720441 450481712996067754290331)
                      ·
                        rfl

theorem cell23_877310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_877310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877310 prefixEnd_877310 := by exact prefixLift 877310
  have htrace : WordTrace (prefixWord ++ tailWord_877310) baseStart_877310 baseEnd_877310 := by
    simpa [prefixWord, tailWord_877310, baseEnd_877310] using wordTrace_append hprefix tailTrace_877310
  have hstable : (prefixWord ++ tailWord_877310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877310).length < 2 ^ (prefixWord ++ tailWord_877310).sum := by decide
  have hdescent : baseEnd_877310 < baseStart_877310 := by decide
  rcases family_descends (prefixWord ++ tailWord_877310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877326 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_877326 : Nat := 118140960795 + 877326 * 2 ^ 59
def prefixEnd_877326 : Nat := 4983230072969 + 3 ^ 40 * 877326 * 2
def baseEnd_877326 : Nat := 450489928686539691690257

theorem tailTrace_877326 : CollatzResearch.WordTrace tailWord_877326 prefixEnd_877326 450489928686539691690257 := by
  unfold tailWord_877326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999838502450651524613479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21332472013070141464605221 3999838502450651524613479)
  ·
    refine ⟨5999757753675977286920219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3999838502450651524613479 5999757753675977286920219)
    ·
      refine ⟨8999636630513965930380329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5999757753675977286920219 8999636630513965930380329)
      ·
        refine ⟨6749727472885474447785247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8999636630513965930380329 6749727472885474447785247)
        ·
          refine ⟨10124591209328211671677871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749727472885474447785247 10124591209328211671677871)
          ·
            refine ⟨15186886813992317507516807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124591209328211671677871 15186886813992317507516807)
            ·
              refine ⟨22780330220988476261275211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15186886813992317507516807 22780330220988476261275211)
              ·
                refine ⟨34170495331482714391912817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22780330220988476261275211 34170495331482714391912817)
                ·
                  refine ⟨25627871498612035793934613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34170495331482714391912817 25627871498612035793934613)
                  ·
                    refine ⟨1201306476497439177840685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25627871498612035793934613 1201306476497439177840685)
                    ·
                      refine ⟨450489928686539691690257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201306476497439177840685 450489928686539691690257)
                      ·
                        rfl

theorem cell23_877326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_877326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877326 prefixEnd_877326 := by exact prefixLift 877326
  have htrace : WordTrace (prefixWord ++ tailWord_877326) baseStart_877326 baseEnd_877326 := by
    simpa [prefixWord, tailWord_877326, baseEnd_877326] using wordTrace_append hprefix tailTrace_877326
  have hstable : (prefixWord ++ tailWord_877326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877326).length < 2 ^ (prefixWord ++ tailWord_877326).sum := by decide
  have hdescent : baseEnd_877326 < baseStart_877326 := by decide
  rcases family_descends (prefixWord ++ tailWord_877326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877329 : List Nat := [1, 2, 2, 1, 1, 3, 3, 10]
def baseStart_877329 : Nat := 118140960795 + 877329 * 2 ^ 59
def prefixEnd_877329 : Nat := 4983230072969 + 3 ^ 40 * 877329 * 2
def baseEnd_877329 : Nat := 16684869226981599257509

theorem tailTrace_877329 : CollatzResearch.WordTrace tailWord_877329 prefixEnd_877329 16684869226981599257509 := by
  unfold tailWord_877329
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998817438594343709267041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21332544959062895806178027 31998817438594343709267041)
  ·
    refine ⟨23999113078945757781950281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31998817438594343709267041 23999113078945757781950281)
    ·
      refine ⟨17999334809209318336462711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23999113078945757781950281 17999334809209318336462711)
      ·
        refine ⟨26999002213813977504694067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17999334809209318336462711 26999002213813977504694067)
        ·
          refine ⟨40498503320720966257041101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26999002213813977504694067 40498503320720966257041101)
          ·
            refine ⟨15186938745270362346390413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40498503320720966257041101 15186938745270362346390413)
            ·
              refine ⟨5695102029476385879896405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15186938745270362346390413 5695102029476385879896405)
              ·
                refine ⟨16684869226981599257509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5695102029476385879896405 16684869226981599257509)
                ·
                  rfl

theorem cell23_877329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 10].length) (baseStart_877329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877329 prefixEnd_877329 := by exact prefixLift 877329
  have htrace : WordTrace (prefixWord ++ tailWord_877329) baseStart_877329 baseEnd_877329 := by
    simpa [prefixWord, tailWord_877329, baseEnd_877329] using wordTrace_append hprefix tailTrace_877329
  have hstable : (prefixWord ++ tailWord_877329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877329).length < 2 ^ (prefixWord ++ tailWord_877329).sum := by decide
  have hdescent : baseEnd_877329 < baseStart_877329 := by decide
  rcases family_descends (prefixWord ++ tailWord_877329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877333 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_877333 : Nat := 118140960795 + 877333 * 2 ^ 59
def prefixEnd_877333 : Nat := 4983230072969 + 3 ^ 40 * 877333 * 2
def baseEnd_877333 : Nat := 150164507683707054767575

theorem tailTrace_877333 : CollatzResearch.WordTrace tailWord_877333 prefixEnd_877333 150164507683707054767575 := by
  unfold tailWord_877333
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998963330579852392412653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21332642220386568261608435 31998963330579852392412653)
  ·
    refine ⟨11999611248967444647154745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31998963330579852392412653 11999611248967444647154745)
    ·
      refine ⟨8999708436725583485366059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11999611248967444647154745 8999708436725583485366059)
      ·
        refine ⟨13499562655088375228049089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999708436725583485366059 13499562655088375228049089)
        ·
          refine ⟨10124671991316281421036817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13499562655088375228049089 10124671991316281421036817)
          ·
            refine ⟨7593503993487211065777613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124671991316281421036817 7593503993487211065777613)
            ·
              refine ⟨2847563997557704149666605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7593503993487211065777613 2847563997557704149666605)
              ·
                refine ⟨1067836499084139056124977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2847563997557704149666605 1067836499084139056124977)
                ·
                  refine ⟨800877374313104292093733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067836499084139056124977 800877374313104292093733)
                  ·
                    refine ⟨150164507683707054767575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 800877374313104292093733 150164507683707054767575)
                    ·
                      rfl

theorem cell23_877333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_877333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877333 prefixEnd_877333 := by exact prefixLift 877333
  have htrace : WordTrace (prefixWord ++ tailWord_877333) baseStart_877333 baseEnd_877333 := by
    simpa [prefixWord, tailWord_877333, baseEnd_877333] using wordTrace_append hprefix tailTrace_877333
  have hstable : (prefixWord ++ tailWord_877333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877333).length < 2 ^ (prefixWord ++ tailWord_877333).sum := by decide
  have hdescent : baseEnd_877333 < baseStart_877333 := by decide
  rcases family_descends (prefixWord ++ tailWord_877333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877336 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_877336 : Nat := 118140960795 + 877336 * 2 ^ 59
def prefixEnd_877336 : Nat := 4983230072969 + 3 ^ 40 * 877336 * 2
def baseEnd_877336 : Nat := 450495063493084652565211

theorem tailTrace_877336 : CollatzResearch.WordTrace tailWord_877336 prefixEnd_877336 450495063493084652565211 := by
  unfold tailWord_877336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999536374784491952385931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21332715166379322603181241 15999536374784491952385931)
  ·
    refine ⟨23999304562176737928578897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15999536374784491952385931 23999304562176737928578897)
    ·
      refine ⟨17999478421632553446434173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23999304562176737928578897 17999478421632553446434173)
      ·
        refine ⟨6749804408112207542412815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17999478421632553446434173 6749804408112207542412815)
        ·
          refine ⟨10124706612168311313619223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749804408112207542412815 10124706612168311313619223)
          ·
            refine ⟨15187059918252466970428835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124706612168311313619223 15187059918252466970428835)
            ·
              refine ⟨22780589877378700455643253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15187059918252466970428835 22780589877378700455643253)
              ·
                refine ⟨2135680301004253167716555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22780589877378700455643253 2135680301004253167716555)
                ·
                  refine ⟨3203520451506379751574833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135680301004253167716555 3203520451506379751574833)
                  ·
                    refine ⟨2402640338629784813681125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3203520451506379751574833 2402640338629784813681125)
                    ·
                      refine ⟨450495063493084652565211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2402640338629784813681125 450495063493084652565211)
                      ·
                        rfl

theorem cell23_877336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_877336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877336 prefixEnd_877336 := by exact prefixLift 877336
  have htrace : WordTrace (prefixWord ++ tailWord_877336) baseStart_877336 baseEnd_877336 := by
    simpa [prefixWord, tailWord_877336, baseEnd_877336] using wordTrace_append hprefix tailTrace_877336
  have hstable : (prefixWord ++ tailWord_877336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877336).length < 2 ^ (prefixWord ++ tailWord_877336).sum := by decide
  have hdescent : baseEnd_877336 < baseStart_877336 := by decide
  rcases family_descends (prefixWord ++ tailWord_877336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877340 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_877340 : Nat := 118140960795 + 877340 * 2 ^ 59
def prefixEnd_877340 : Nat := 4983230072969 + 3 ^ 40 * 877340 * 2
def baseEnd_877340 : Nat := 450497117415702636915193

theorem tailTrace_877340 : CollatzResearch.WordTrace tailWord_877340 prefixEnd_877340 450497117415702636915193 := by
  unfold tailWord_877340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999609320777246293958737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21332812427702995058611649 15999609320777246293958737)
  ·
    refine ⟨11999706990582934720469053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15999609320777246293958737 11999706990582934720469053)
    ·
      refine ⟨4499890121468600520175895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11999706990582934720469053 4499890121468600520175895)
      ·
        refine ⟨6749835182202900780263843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499890121468600520175895 6749835182202900780263843)
        ·
          refine ⟨10124752773304351170395765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6749835182202900780263843 10124752773304351170395765)
          ·
            refine ⟨949195572497282922224603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10124752773304351170395765 949195572497282922224603)
            ·
              refine ⟨1423793358745924383336905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949195572497282922224603 1423793358745924383336905)
              ·
                refine ⟨1067845019059443287502679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423793358745924383336905 1067845019059443287502679)
                ·
                  refine ⟨1601767528589164931254019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067845019059443287502679 1601767528589164931254019)
                  ·
                    refine ⟨2402651292883747396881029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1601767528589164931254019 2402651292883747396881029)
                    ·
                      refine ⟨450497117415702636915193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2402651292883747396881029 450497117415702636915193)
                      ·
                        rfl

theorem cell23_877340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_877340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877340 prefixEnd_877340 := by exact prefixLift 877340
  have htrace : WordTrace (prefixWord ++ tailWord_877340) baseStart_877340 baseEnd_877340 := by
    simpa [prefixWord, tailWord_877340, baseEnd_877340] using wordTrace_append hprefix tailTrace_877340
  have hstable : (prefixWord ++ tailWord_877340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877340).length < 2 ^ (prefixWord ++ tailWord_877340).sum := by decide
  have hdescent : baseEnd_877340 < baseStart_877340 := by decide
  rcases family_descends (prefixWord ++ tailWord_877340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877343 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_877343 : Nat := 118140960795 + 877343 * 2 ^ 59
def prefixEnd_877343 : Nat := 4983230072969 + 3 ^ 40 * 877343 * 2
def baseEnd_877343 : Nat := 450498657857666125177679

theorem tailTrace_877343 : CollatzResearch.WordTrace tailWord_877343 prefixEnd_877343 450498657857666125177679 := by
  unfold tailWord_877343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31999328060543624100276683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21332885373695749400184455 31999328060543624100276683)
  ·
    refine ⟨47998992090815436150415025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31999328060543624100276683 47998992090815436150415025)
    ·
      refine ⟨35999244068111577112811269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47998992090815436150415025 35999244068111577112811269)
      ·
        refine ⟨6749858262770920708652113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35999244068111577112811269 6749858262770920708652113)
        ·
          refine ⟨5062393697078190531489085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6749858262770920708652113 5062393697078190531489085)
          ·
            refine ⟨1898397636404321449308407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5062393697078190531489085 1898397636404321449308407)
            ·
              refine ⟨2847596454606482173962611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898397636404321449308407 2847596454606482173962611)
              ·
                refine ⟨4271394681909723260943917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847596454606482173962611 4271394681909723260943917)
                ·
                  refine ⟨1601773005716146222853969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4271394681909723260943917 1601773005716146222853969)
                  ·
                    refine ⟨1201329754287109667140477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1601773005716146222853969 1201329754287109667140477)
                    ·
                      refine ⟨450498657857666125177679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201329754287109667140477 450498657857666125177679)
                      ·
                        rfl

theorem cell23_877343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_877343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877343 prefixEnd_877343 := by exact prefixLift 877343
  have htrace : WordTrace (prefixWord ++ tailWord_877343) baseStart_877343 baseEnd_877343 := by
    simpa [prefixWord, tailWord_877343, baseEnd_877343] using wordTrace_append hprefix tailTrace_877343
  have hstable : (prefixWord ++ tailWord_877343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877343).length < 2 ^ (prefixWord ++ tailWord_877343).sum := by decide
  have hdescent : baseEnd_877343 < baseStart_877343 := by decide
  rcases family_descends (prefixWord ++ tailWord_877343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877346 : List Nat := [3, 3, 1, 1, 2, 2, 2, 9]
def baseStart_877346 : Nat := 118140960795 + 877346 * 2 ^ 59
def prefixEnd_877346 : Nat := 4983230072969 + 3 ^ 40 * 877346 * 2
def baseEnd_877346 : Nat := 16685192529615911608895

theorem tailTrace_877346 : CollatzResearch.WordTrace tailWord_877346 prefixEnd_877346 16685192529615911608895 := by
  unfold tailWord_877346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999859369883188903158973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21332958319688503741757261 7999859369883188903158973)
  ·
    refine ⟨2999947263706195838684615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7999859369883188903158973 2999947263706195838684615)
    ·
      refine ⟨4499920895559293758026923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2999947263706195838684615 4499920895559293758026923)
      ·
        refine ⟨6749881343338940637040385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499920895559293758026923 6749881343338940637040385)
        ·
          refine ⟨5062411007504205477780289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6749881343338940637040385 5062411007504205477780289)
          ·
            refine ⟨3796808255628154108335217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5062411007504205477780289 3796808255628154108335217)
            ·
              refine ⟨2847606191721115581251413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796808255628154108335217 2847606191721115581251413)
              ·
                refine ⟨16685192529615911608895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2847606191721115581251413 16685192529615911608895)
                ·
                  rfl

theorem cell23_877346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_877346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877346 prefixEnd_877346 := by exact prefixLift 877346
  have htrace : WordTrace (prefixWord ++ tailWord_877346) baseStart_877346 baseEnd_877346 := by
    simpa [prefixWord, tailWord_877346, baseEnd_877346] using wordTrace_append hprefix tailTrace_877346
  have hstable : (prefixWord ++ tailWord_877346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877346).length < 2 ^ (prefixWord ++ tailWord_877346).sum := by decide
  have hdescent : baseEnd_877346 < baseStart_877346 := by decide
  rcases family_descends (prefixWord ++ tailWord_877346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877359 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 9]
def baseStart_877359 : Nat := 118140960795 + 877359 * 2 ^ 59
def prefixEnd_877359 : Nat := 4983230072969 + 3 ^ 40 * 877359 * 2
def baseEnd_877359 : Nat := 150168957849379354192535

theorem tailTrace_877359 : CollatzResearch.WordTrace tailWord_877359 prefixEnd_877359 150168957849379354192535 := by
  unfold tailWord_877359
  simp only [CollatzResearch.WordTrace]
  refine ⟨31999911628485658832859131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21333274418990439221906087 31999911628485658832859131)
  ·
    refine ⟨47999867442728488249288697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31999911628485658832859131 47999867442728488249288697)
    ·
      refine ⟨35999900582046366186966523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47999867442728488249288697 35999900582046366186966523)
      ·
        refine ⟨53999850873069549280449785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35999900582046366186966523 53999850873069549280449785)
        ·
          refine ⟨40499888154802161960337339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53999850873069549280449785 40499888154802161960337339)
          ·
            refine ⟨60749832232203242940506009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40499888154802161960337339 60749832232203242940506009)
            ·
              refine ⟨45562374174152432205379507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60749832232203242940506009 45562374174152432205379507)
              ·
                refine ⟨68343561261228648308069261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45562374174152432205379507 68343561261228648308069261)
                ·
                  refine ⟨25628835472960743115525973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68343561261228648308069261 25628835472960743115525973)
                  ·
                    refine ⟨150168957849379354192535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25628835472960743115525973 150168957849379354192535)
                    ·
                      rfl

theorem cell23_877359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_877359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877359 prefixEnd_877359 := by exact prefixLift 877359
  have htrace : WordTrace (prefixWord ++ tailWord_877359) baseStart_877359 baseEnd_877359 := by
    simpa [prefixWord, tailWord_877359, baseEnd_877359] using wordTrace_append hprefix tailTrace_877359
  have hstable : (prefixWord ++ tailWord_877359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877359).length < 2 ^ (prefixWord ++ tailWord_877359).sum := by decide
  have hdescent : baseEnd_877359 < baseStart_877359 := by decide
  rcases family_descends (prefixWord ++ tailWord_877359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877447 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_877447 : Nat := 118140960795 + 877447 * 2 ^ 59
def prefixEnd_877447 : Nat := 4983230072969 + 3 ^ 40 * 877447 * 2
def baseEnd_877447 : Nat := 450552059845733718277201

theorem tailTrace_877447 : CollatzResearch.WordTrace tailWord_877447 prefixEnd_877447 450552059845733718277201 := by
  unfold tailWord_877447
  simp only [CollatzResearch.WordTrace]
  refine ⟨32003121252166849862062595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21335414168111233241375063 32003121252166849862062595)
  ·
    refine ⟨48004681878250274793093893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32003121252166849862062595 48004681878250274793093893)
    ·
      refine ⟨9000877852171926523705105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48004681878250274793093893 9000877852171926523705105)
      ·
        refine ⟨6750658389128944892778829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9000877852171926523705105 6750658389128944892778829)
        ·
          refine ⟨2531496895923354334792061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6750658389128944892778829 2531496895923354334792061)
          ·
            refine ⟨949311335971257875547023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2531496895923354334792061 949311335971257875547023)
            ·
              refine ⟨1423967003956886813320535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949311335971257875547023 1423967003956886813320535)
              ·
                refine ⟨2135950505935330219980803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423967003956886813320535 2135950505935330219980803)
                ·
                  refine ⟨3203925758902995329971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135950505935330219980803 3203925758902995329971205)
                  ·
                    refine ⟨600736079794311624369601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203925758902995329971205 600736079794311624369601)
                    ·
                      refine ⟨450552059845733718277201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600736079794311624369601 450552059845733718277201)
                      ·
                        rfl

theorem cell23_877447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_877447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877447 prefixEnd_877447 := by exact prefixLift 877447
  have htrace : WordTrace (prefixWord ++ tailWord_877447) baseStart_877447 baseEnd_877447 := by
    simpa [prefixWord, tailWord_877447, baseEnd_877447] using wordTrace_append hprefix tailTrace_877447
  have hstable : (prefixWord ++ tailWord_877447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877447).length < 2 ^ (prefixWord ++ tailWord_877447).sum := by decide
  have hdescent : baseEnd_877447 < baseStart_877447 := by decide
  rcases family_descends (prefixWord ++ tailWord_877447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877493 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_877493 : Nat := 118140960795 + 877493 * 2 ^ 59
def prefixEnd_877493 : Nat := 4983230072969 + 3 ^ 40 * 877493 * 2
def baseEnd_877493 : Nat := 450575679955840538301989

theorem tailTrace_877493 : CollatzResearch.WordTrace tailWord_877493 prefixEnd_877493 450575679955840538301989 := by
  unfold tailWord_877493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32004799010000199718237133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21336532673333466478824755 32004799010000199718237133)
  ·
    refine ⟨12001799628750074894338925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32004799010000199718237133 12001799628750074894338925)
    ·
      refine ⟨4500674860781278085377097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12001799628750074894338925 4500674860781278085377097)
      ·
        refine ⟨3375506145585958564032823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500674860781278085377097 3375506145585958564032823)
        ·
          refine ⟨5063259218378937846049235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375506145585958564032823 5063259218378937846049235)
          ·
            refine ⟨7594888827568406769073853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5063259218378937846049235 7594888827568406769073853)
            ·
              refine ⟨2848083310338152538402695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7594888827568406769073853 2848083310338152538402695)
              ·
                refine ⟨4272124965507228807604043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848083310338152538402695 4272124965507228807604043)
                ·
                  refine ⟨6408187448260843211406065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272124965507228807604043 6408187448260843211406065)
                  ·
                    refine ⟨4806140586195632408554549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6408187448260843211406065 4806140586195632408554549)
                    ·
                      refine ⟨450575679955840538301989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4806140586195632408554549 450575679955840538301989)
                      ·
                        rfl

theorem cell23_877493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_877493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877493 prefixEnd_877493 := by exact prefixLift 877493
  have htrace : WordTrace (prefixWord ++ tailWord_877493) baseStart_877493 baseEnd_877493 := by
    simpa [prefixWord, tailWord_877493, baseEnd_877493] using wordTrace_append hprefix tailTrace_877493
  have hstable : (prefixWord ++ tailWord_877493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877493).length < 2 ^ (prefixWord ++ tailWord_877493).sum := by decide
  have hdescent : baseEnd_877493 < baseStart_877493 := by decide
  rcases family_descends (prefixWord ++ tailWord_877493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877554 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_877554 : Nat := 118140960795 + 877554 * 2 ^ 59
def prefixEnd_877554 : Nat := 4983230072969 + 3 ^ 40 * 877554 * 2
def baseEnd_877554 : Nat := 450607002275764799639209

theorem tailTrace_877554 : CollatzResearch.WordTrace tailWord_877554 prefixEnd_877554 450607002275764799639209 := by
  unfold tailWord_877554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001755965694801784051929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21338015908519471424138477 8001755965694801784051929)
  ·
    refine ⟨6001316974271101338038947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8001755965694801784051929 6001316974271101338038947)
    ·
      refine ⟨9001975461406652007058421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001316974271101338038947 9001975461406652007058421)
      ·
        refine ⟨843935199506873625661727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9001975461406652007058421 843935199506873625661727)
        ·
          refine ⟨1265902799260310438492591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843935199506873625661727 1265902799260310438492591)
          ·
            refine ⟨1898854198890465657738887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265902799260310438492591 1898854198890465657738887)
            ·
              refine ⟨2848281298335698486608331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898854198890465657738887 2848281298335698486608331)
              ·
                refine ⟨4272421947503547729912497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848281298335698486608331 4272421947503547729912497)
                ·
                  refine ⟨3204316460627660797434373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4272421947503547729912497 3204316460627660797434373)
                  ·
                    refine ⟨600809336367686399518945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204316460627660797434373 600809336367686399518945)
                    ·
                      refine ⟨450607002275764799639209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600809336367686399518945 450607002275764799639209)
                      ·
                        rfl

theorem cell23_877554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_877554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877554 prefixEnd_877554 := by exact prefixLift 877554
  have htrace : WordTrace (prefixWord ++ tailWord_877554) baseStart_877554 baseEnd_877554 := by
    simpa [prefixWord, tailWord_877554, baseEnd_877554] using wordTrace_append hprefix tailTrace_877554
  have hstable : (prefixWord ++ tailWord_877554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877554).length < 2 ^ (prefixWord ++ tailWord_877554).sum := by decide
  have hdescent : baseEnd_877554 < baseStart_877554 := by decide
  rcases family_descends (prefixWord ++ tailWord_877554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877573 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_877573 : Nat := 118140960795 + 877573 * 2 ^ 59
def prefixEnd_877573 : Nat := 4983230072969 + 3 ^ 40 * 877573 * 2
def baseEnd_877573 : Nat := 150205586136066741767207

theorem tailTrace_877573 : CollatzResearch.WordTrace tailWord_877573 prefixEnd_877573 150205586136066741767207 := by
  unfold tailWord_877573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32007716849710373381149373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21338477899806915587432915 32007716849710373381149373)
  ·
    refine ⟨12002893818641390017931015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32007716849710373381149373 12002893818641390017931015)
    ·
      refine ⟨18004340727962085026896523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002893818641390017931015 18004340727962085026896523)
      ·
        refine ⟨27006511091943127540344785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18004340727962085026896523 27006511091943127540344785)
        ·
          refine ⟨20254883318957345655258589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27006511091943127540344785 20254883318957345655258589)
          ·
            refine ⟨7595581244609004620721971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20254883318957345655258589 7595581244609004620721971)
            ·
              refine ⟨11393371866913506931082957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7595581244609004620721971 11393371866913506931082957)
              ·
                refine ⟨4272514450092565099156109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11393371866913506931082957 4272514450092565099156109)
                ·
                  refine ⟨1602192918784711912183541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4272514450092565099156109 1602192918784711912183541)
                  ·
                    refine ⟨150205586136066741767207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1602192918784711912183541 150205586136066741767207)
                    ·
                      rfl

theorem cell23_877573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_877573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877573 prefixEnd_877573 := by exact prefixLift 877573
  have htrace : WordTrace (prefixWord ++ tailWord_877573) baseStart_877573 baseEnd_877573 := by
    simpa [prefixWord, tailWord_877573, baseEnd_877573] using wordTrace_append hprefix tailTrace_877573
  have hstable : (prefixWord ++ tailWord_877573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877573).length < 2 ^ (prefixWord ++ tailWord_877573).sum := by decide
  have hdescent : baseEnd_877573 < baseStart_877573 := by decide
  rcases family_descends (prefixWord ++ tailWord_877573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877604 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_877604 : Nat := 118140960795 + 877604 * 2 ^ 59
def prefixEnd_877604 : Nat := 4983230072969 + 3 ^ 40 * 877604 * 2
def baseEnd_877604 : Nat := 450632676308489604013979

theorem tailTrace_877604 : CollatzResearch.WordTrace tailWord_877604 prefixEnd_877604 450632676308489604013979 := by
  unfold tailWord_877604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004423756299032837763933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21339231675065377117018577 16004423756299032837763933)
  ·
    refine ⟨6001658908612137314161475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16004423756299032837763933 6001658908612137314161475)
    ·
      refine ⟨9002488362918205971242213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001658908612137314161475 9002488362918205971242213)
      ·
        refine ⟨1687966568047163619607915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9002488362918205971242213 1687966568047163619607915)
        ·
          refine ⟨2531949852070745429411873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687966568047163619607915 2531949852070745429411873)
          ·
            refine ⟨1898962389053059072058905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531949852070745429411873 1898962389053059072058905)
            ·
              refine ⟨1424221791789794304044179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898962389053059072058905 1424221791789794304044179)
              ·
                refine ⟨2136332687684691456066269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424221791789794304044179 2136332687684691456066269)
                ·
                  refine ⟨801124757881759296024851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2136332687684691456066269 801124757881759296024851)
                  ·
                    refine ⟨1201687136822638944037277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 801124757881759296024851 1201687136822638944037277)
                    ·
                      refine ⟨450632676308489604013979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201687136822638944037277 450632676308489604013979)
                      ·
                        rfl

theorem cell23_877604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_877604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877604 prefixEnd_877604 := by exact prefixLift 877604
  have htrace : WordTrace (prefixWord ++ tailWord_877604) baseStart_877604 baseEnd_877604 := by
    simpa [prefixWord, tailWord_877604, baseEnd_877604] using wordTrace_append hprefix tailTrace_877604
  have hstable : (prefixWord ++ tailWord_877604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877604).length < 2 ^ (prefixWord ++ tailWord_877604).sum := by decide
  have hdescent : baseEnd_877604 < baseStart_877604 := by decide
  rcases family_descends (prefixWord ++ tailWord_877604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877638 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_877638 : Nat := 118140960795 + 877638 * 2 ^ 59
def prefixEnd_877638 : Nat := 4983230072969 + 3 ^ 40 * 877638 * 2
def baseEnd_877638 : Nat := 450650134650742470988823

theorem tailTrace_877638 : CollatzResearch.WordTrace tailWord_877638 prefixEnd_877638 450650134650742470988823 := by
  unfold tailWord_877638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000315237327340296320799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21340058396316592988177045 1000315237327340296320799)
  ·
    refine ⟨1500472855991010444481199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000315237327340296320799 1500472855991010444481199)
    ·
      refine ⟨2250709283986515666721799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500472855991010444481199 2250709283986515666721799)
      ·
        refine ⟨3376063925979773500082699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250709283986515666721799 3376063925979773500082699)
        ·
          refine ⟨5064095888969660250124049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376063925979773500082699 5064095888969660250124049)
          ·
            refine ⟨3798071916727245187593037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064095888969660250124049 3798071916727245187593037)
            ·
              refine ⟨1424276968772716945347389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3798071916727245187593037 1424276968772716945347389)
              ·
                refine ⟨534103863289768854505271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1424276968772716945347389 534103863289768854505271)
                ·
                  refine ⟨801155794934653281757907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534103863289768854505271 801155794934653281757907)
                  ·
                    refine ⟨1201733692401979922636861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 801155794934653281757907 1201733692401979922636861)
                    ·
                      refine ⟨450650134650742470988823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201733692401979922636861 450650134650742470988823)
                      ·
                        rfl

theorem cell23_877638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_877638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877638 prefixEnd_877638 := by exact prefixLift 877638
  have htrace : WordTrace (prefixWord ++ tailWord_877638) baseStart_877638 baseEnd_877638 := by
    simpa [prefixWord, tailWord_877638, baseEnd_877638] using wordTrace_append hprefix tailTrace_877638
  have hstable : (prefixWord ++ tailWord_877638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877638).length < 2 ^ (prefixWord ++ tailWord_877638).sum := by decide
  have hdescent : baseEnd_877638 < baseStart_877638 := by decide
  rcases family_descends (prefixWord ++ tailWord_877638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877650 : List Nat := [3, 2, 2, 1, 3, 3, 9]
def baseStart_877650 : Nat := 118140960795 + 877650 * 2 ^ 59
def prefixEnd_877650 : Nat := 4983230072969 + 3 ^ 40 * 877650 * 2
def baseEnd_877650 : Nat := 5563657980476499062207

theorem tailTrace_877650 : CollatzResearch.WordTrace tailWord_877650 prefixEnd_877650 5563657980476499062207 := by
  unfold tailWord_877650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002631317607853882925601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21340350180287610354468269 8002631317607853882925601)
  ·
    refine ⟨6001973488205890412194201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8002631317607853882925601 6001973488205890412194201)
    ·
      refine ⟨4501480116154417809145651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6001973488205890412194201 4501480116154417809145651)
      ·
        refine ⟨6752220174231626713718477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501480116154417809145651 6752220174231626713718477)
        ·
          refine ⟨2532082565336860017644429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6752220174231626713718477 2532082565336860017644429)
          ·
            refine ⟨949530962001322506616661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2532082565336860017644429 949530962001322506616661)
            ·
              refine ⟨5563657980476499062207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 949530962001322506616661 5563657980476499062207)
              ·
                rfl

theorem cell23_877650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 9].length) (baseStart_877650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877650 prefixEnd_877650 := by exact prefixLift 877650
  have htrace : WordTrace (prefixWord ++ tailWord_877650) baseStart_877650 baseEnd_877650 := by
    simpa [prefixWord, tailWord_877650, baseEnd_877650] using wordTrace_append hprefix tailTrace_877650
  have hstable : (prefixWord ++ tailWord_877650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877650).length < 2 ^ (prefixWord ++ tailWord_877650).sum := by decide
  have hdescent : baseEnd_877650 < baseStart_877650 := by decide
  rcases family_descends (prefixWord ++ tailWord_877650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877663 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 7]
def baseStart_877663 : Nat := 118140960795 + 877663 * 2 ^ 59
def prefixEnd_877663 : Nat := 4983230072969 + 3 ^ 40 * 877663 * 2
def baseEnd_877663 : Nat := 150220990555701624392069

theorem tailTrace_877663 : CollatzResearch.WordTrace tailWord_877663 prefixEnd_877663 150220990555701624392069 := by
  unfold tailWord_877663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32010999419384318751925643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21340666279589545834617095 32010999419384318751925643)
  ·
    refine ⟨48016499129076478127888465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32010999419384318751925643 48016499129076478127888465)
    ·
      refine ⟨36012374346807358595916349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48016499129076478127888465 36012374346807358595916349)
      ·
        refine ⟨13504640380052759473468631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36012374346807358595916349 13504640380052759473468631)
        ·
          refine ⟨20256960570079139210202947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504640380052759473468631 20256960570079139210202947)
          ·
            refine ⟨30385440855118708815304421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256960570079139210202947 30385440855118708815304421)
            ·
              refine ⟨5697270160334757902869579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30385440855118708815304421 5697270160334757902869579)
              ·
                refine ⟨8545905240502136854304369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697270160334757902869579 8545905240502136854304369)
                ·
                  refine ⟨6409428930376602640728277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545905240502136854304369 6409428930376602640728277)
                  ·
                    refine ⟨150220990555701624392069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6409428930376602640728277 150220990555701624392069)
                    ·
                      rfl

theorem cell23_877663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_877663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877663 prefixEnd_877663 := by exact prefixLift 877663
  have htrace : WordTrace (prefixWord ++ tailWord_877663) baseStart_877663 baseEnd_877663 := by
    simpa [prefixWord, tailWord_877663, baseEnd_877663] using wordTrace_append hprefix tailTrace_877663
  have hstable : (prefixWord ++ tailWord_877663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877663).length < 2 ^ (prefixWord ++ tailWord_877663).sum := by decide
  have hdescent : baseEnd_877663 < baseStart_877663 := by decide
  rcases family_descends (prefixWord ++ tailWord_877663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877687 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_877687 : Nat := 118140960795 + 877687 * 2 ^ 59
def prefixEnd_877687 : Nat := 4983230072969 + 3 ^ 40 * 877687 * 2
def baseEnd_877687 : Nat := 450675295202812779276097

theorem tailTrace_877687 : CollatzResearch.WordTrace tailWord_877687 prefixEnd_877687 450675295202812779276097 := by
  unfold tailWord_877687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011874771297370850799315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21341249847531580567199543 32011874771297370850799315)
  ·
    refine ⟨48017812156946056276198973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011874771297370850799315 48017812156946056276198973)
    ·
      refine ⟨18006679558854771103574615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48017812156946056276198973 18006679558854771103574615)
      ·
        refine ⟨27010019338282156655361923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18006679558854771103574615 27010019338282156655361923)
        ·
          refine ⟨40515029007423234983042885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27010019338282156655361923 40515029007423234983042885)
          ·
            refine ⟨7596567938891856559320541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40515029007423234983042885 7596567938891856559320541)
            ·
              refine ⟨2848712977084446209745203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7596567938891856559320541 2848712977084446209745203)
              ·
                refine ⟨4273069465626669314617805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848712977084446209745203 4273069465626669314617805)
                ·
                  refine ⟨1602401049610000992981677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4273069465626669314617805 1602401049610000992981677)
                  ·
                    refine ⟨600900393603750372368129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1602401049610000992981677 600900393603750372368129)
                    ·
                      refine ⟨450675295202812779276097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 600900393603750372368129 450675295202812779276097)
                      ·
                        rfl

theorem cell23_877687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_877687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877687 prefixEnd_877687 := by exact prefixLift 877687
  have htrace : WordTrace (prefixWord ++ tailWord_877687) baseStart_877687 baseEnd_877687 := by
    simpa [prefixWord, tailWord_877687, baseEnd_877687] using wordTrace_append hprefix tailTrace_877687
  have hstable : (prefixWord ++ tailWord_877687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877687).length < 2 ^ (prefixWord ++ tailWord_877687).sum := by decide
  have hdescent : baseEnd_877687 < baseStart_877687 := by decide
  rcases family_descends (prefixWord ++ tailWord_877687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877727 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 2, 6]
def baseStart_877727 : Nat := 118140960795 + 877727 * 2 ^ 59
def prefixEnd_877727 : Nat := 4983230072969 + 3 ^ 40 * 877727 * 2
def baseEnd_877727 : Nat := 150231944809664207591971

theorem tailTrace_877727 : CollatzResearch.WordTrace tailWord_877727 prefixEnd_877727 150231944809664207591971 := by
  unfold tailWord_877727
  simp only [CollatzResearch.WordTrace]
  refine ⟨32013333691152457682255435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21342222460768305121503623 32013333691152457682255435)
  ·
    refine ⟨48020000536728686523383153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32013333691152457682255435 48020000536728686523383153)
    ·
      refine ⟨36015000402546514892537365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48020000536728686523383153 36015000402546514892537365)
      ·
        refine ⟨1688203143869367885587689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36015000402546514892537365 1688203143869367885587689)
        ·
          refine ⟨1266152357902025914190767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688203143869367885587689 1266152357902025914190767)
          ·
            refine ⟨1899228536853038871286151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266152357902025914190767 1899228536853038871286151)
            ·
              refine ⟨2848842805279558306929227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899228536853038871286151 2848842805279558306929227)
              ·
                refine ⟨4273264207919337460393841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848842805279558306929227 4273264207919337460393841)
                ·
                  refine ⟨3204948155939503095295381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273264207919337460393841 3204948155939503095295381)
                  ·
                    refine ⟨150231944809664207591971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3204948155939503095295381 150231944809664207591971)
                    ·
                      rfl

theorem cell23_877727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_877727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877727 prefixEnd_877727 := by exact prefixLift 877727
  have htrace : WordTrace (prefixWord ++ tailWord_877727) baseStart_877727 baseEnd_877727 := by
    simpa [prefixWord, tailWord_877727, baseEnd_877727] using wordTrace_append hprefix tailTrace_877727
  have hstable : (prefixWord ++ tailWord_877727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877727).length < 2 ^ (prefixWord ++ tailWord_877727).sum := by decide
  have hdescent : baseEnd_877727 < baseStart_877727 := by decide
  rcases family_descends (prefixWord ++ tailWord_877727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877757 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 5]
def baseStart_877757 : Nat := 118140960795 + 877757 * 2 ^ 59
def prefixEnd_877757 : Nat := 4983230072969 + 3 ^ 40 * 877757 * 2
def baseEnd_877757 : Nat := 50079026538736389488975

theorem tailTrace_877757 : CollatzResearch.WordTrace tailWord_877757 prefixEnd_877757 50079026538736389488975 := by
  unfold tailWord_877757
  simp only [CollatzResearch.WordTrace]
  refine ⟨32014427881043772805847525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21342951920695848537231683 32014427881043772805847525)
  ·
    refine ⟨6002705227695707401096411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32014427881043772805847525 6002705227695707401096411)
    ·
      refine ⟨9004057841543561101644617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6002705227695707401096411 9004057841543561101644617)
      ·
        refine ⟨6753043381157670826233463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9004057841543561101644617 6753043381157670826233463)
        ·
          refine ⟨10129565071736506239350195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753043381157670826233463 10129565071736506239350195)
          ·
            refine ⟨15194347607604759359025293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10129565071736506239350195 15194347607604759359025293)
            ·
              refine ⟨5697880352851784759634485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15194347607604759359025293 5697880352851784759634485)
              ·
                refine ⟨534176283079854821215733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5697880352851784759634485 534176283079854821215733)
                ·
                  refine ⟨50079026538736389488975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534176283079854821215733 50079026538736389488975)
                  ·
                    rfl

theorem cell23_877757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_877757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877757 prefixEnd_877757 := by exact prefixLift 877757
  have htrace : WordTrace (prefixWord ++ tailWord_877757) baseStart_877757 baseEnd_877757 := by
    simpa [prefixWord, tailWord_877757, baseEnd_877757] using wordTrace_append hprefix tailTrace_877757
  have hstable : (prefixWord ++ tailWord_877757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877757).length < 2 ^ (prefixWord ++ tailWord_877757).sum := by decide
  have hdescent : baseEnd_877757 < baseStart_877757 := by decide
  rcases family_descends (prefixWord ++ tailWord_877757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877762 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_877762 : Nat := 118140960795 + 877762 * 2 ^ 59
def prefixEnd_877762 : Nat := 4983230072969 + 3 ^ 40 * 877762 * 2
def baseEnd_877762 : Nat := 450713806251899985838253

theorem tailTrace_877762 : CollatzResearch.WordTrace tailWord_877762 prefixEnd_877762 450713806251899985838253 := by
  unfold tailWord_877762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003652561506414664944885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21343073497350439106519693 8003652561506414664944885)
  ·
    refine ⟨750342427641226374838583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8003652561506414664944885 750342427641226374838583)
    ·
      refine ⟨1125513641461839562257875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750342427641226374838583 1125513641461839562257875)
      ·
        refine ⟨1688270462192759343386813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125513641461839562257875 1688270462192759343386813)
        ·
          refine ⟨633101423322284753770055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688270462192759343386813 633101423322284753770055)
          ·
            refine ⟨949652134983427130655083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633101423322284753770055 949652134983427130655083)
            ·
              refine ⟨1424478202475140695982625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949652134983427130655083 1424478202475140695982625)
              ·
                refine ⟨1068358651856355521986969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424478202475140695982625 1068358651856355521986969)
                ·
                  refine ⟨801268988892266641490227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068358651856355521986969 801268988892266641490227)
                  ·
                    refine ⟨1201903483338399962235341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 801268988892266641490227 1201903483338399962235341)
                    ·
                      refine ⟨450713806251899985838253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201903483338399962235341 450713806251899985838253)
                      ·
                        rfl

theorem cell23_877762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_877762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877762 prefixEnd_877762 := by exact prefixLift 877762
  have htrace : WordTrace (prefixWord ++ tailWord_877762) baseStart_877762 baseEnd_877762 := by
    simpa [prefixWord, tailWord_877762, baseEnd_877762] using wordTrace_append hprefix tailTrace_877762
  have hstable : (prefixWord ++ tailWord_877762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877762).length < 2 ^ (prefixWord ++ tailWord_877762).sum := by decide
  have hdescent : baseEnd_877762 < baseStart_877762 := by decide
  rcases family_descends (prefixWord ++ tailWord_877762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877800 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_877800 : Nat := 118140960795 + 877800 * 2 ^ 59
def prefixEnd_877800 : Nat := 4983230072969 + 3 ^ 40 * 877800 * 2
def baseEnd_877800 : Nat := 150244439505590279054359

theorem tailTrace_877800 : CollatzResearch.WordTrace tailWord_877800 prefixEnd_877800 150244439505590279054359 := by
  unfold tailWord_877800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007998109943995574831427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21343997479925327433108569 16007998109943995574831427)
  ·
    refine ⟨24011997164915993362247141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16007998109943995574831427 24011997164915993362247141)
    ·
      refine ⟨4502249468421748755421339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24011997164915993362247141 4502249468421748755421339)
      ·
        refine ⟨6753374202632623133132009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502249468421748755421339 6753374202632623133132009)
        ·
          refine ⟨5065030651974467349849007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6753374202632623133132009 5065030651974467349849007)
          ·
            refine ⟨7597545977961701024773511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065030651974467349849007 7597545977961701024773511)
            ·
              refine ⟨11396318966942551537160267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597545977961701024773511 11396318966942551537160267)
              ·
                refine ⟨17094478450413827305740401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396318966942551537160267 17094478450413827305740401)
                ·
                  refine ⟨12820858837810370479305301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17094478450413827305740401 12820858837810370479305301)
                  ·
                    refine ⟨150244439505590279054359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12820858837810370479305301 150244439505590279054359)
                    ·
                      rfl

theorem cell23_877800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_877800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877800 prefixEnd_877800 := by exact prefixLift 877800
  have htrace : WordTrace (prefixWord ++ tailWord_877800) baseStart_877800 baseEnd_877800 := by
    simpa [prefixWord, tailWord_877800, baseEnd_877800] using wordTrace_append hprefix tailTrace_877800
  have hstable : (prefixWord ++ tailWord_877800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877800).length < 2 ^ (prefixWord ++ tailWord_877800).sum := by decide
  have hdescent : baseEnd_877800 < baseStart_877800 := by decide
  rcases family_descends (prefixWord ++ tailWord_877800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877827 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3]
def baseStart_877827 : Nat := 118140960795 + 877827 * 2 ^ 59
def prefixEnd_877827 : Nat := 4983230072969 + 3 ^ 40 * 877827 * 2
def baseEnd_877827 : Nat := 450747182494442231525453

theorem tailTrace_877827 : CollatzResearch.WordTrace tailWord_877827 prefixEnd_877827 450747182494442231525453 := by
  unfold tailWord_877827
  simp only [CollatzResearch.WordTrace]
  refine ⟨32016980990790174760895735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21344653993860116507263823 32016980990790174760895735)
  ·
    refine ⟨48025471486185262141343603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32016980990790174760895735 48025471486185262141343603)
    ·
      refine ⟨72038207229277893212015405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48025471486185262141343603 72038207229277893212015405)
      ·
        refine ⟨27014327710979209954505777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72038207229277893212015405 27014327710979209954505777)
        ·
          refine ⟨20260745783234407465879333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27014327710979209954505777 20260745783234407465879333)
          ·
            refine ⟨3798889834356451399852375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20260745783234407465879333 3798889834356451399852375)
            ·
              refine ⟨5698334751534677099778563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798889834356451399852375 5698334751534677099778563)
              ·
                refine ⟨8547502127302015649667845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698334751534677099778563 8547502127302015649667845)
                ·
                  refine ⟨1602656648869127934312721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8547502127302015649667845 1602656648869127934312721)
                  ·
                    refine ⟨1201992486651845950734541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1602656648869127934312721 1201992486651845950734541)
                    ·
                      refine ⟨450747182494442231525453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1201992486651845950734541 450747182494442231525453)
                      ·
                        rfl

theorem cell23_877827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_877827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877827 prefixEnd_877827 := by exact prefixLift 877827
  have htrace : WordTrace (prefixWord ++ tailWord_877827) baseStart_877827 baseEnd_877827 := by
    simpa [prefixWord, tailWord_877827, baseEnd_877827] using wordTrace_append hprefix tailTrace_877827
  have hstable : (prefixWord ++ tailWord_877827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877827).length < 2 ^ (prefixWord ++ tailWord_877827).sum := by decide
  have hdescent : baseEnd_877827 < baseStart_877827 := by decide
  rcases family_descends (prefixWord ++ tailWord_877827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877847 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 6]
def baseStart_877847 : Nat := 118140960795 + 877847 * 2 ^ 59
def prefixEnd_877847 : Nat := 4983230072969 + 3 ^ 40 * 877847 * 2
def baseEnd_877847 : Nat := 50084161345281350363929

theorem tailTrace_877847 : CollatzResearch.WordTrace tailWord_877847 prefixEnd_877847 50084161345281350363929 := by
  unfold tailWord_877847
  simp only [CollatzResearch.WordTrace]
  refine ⟨32017710450717718176623795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21345140300478478784415863 32017710450717718176623795)
  ·
    refine ⟨48026565676076577264935693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32017710450717718176623795 48026565676076577264935693)
    ·
      refine ⟨18009962128528716474350885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48026565676076577264935693 18009962128528716474350885)
      ·
        refine ⟨3376867899099134338940791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18009962128528716474350885 3376867899099134338940791)
        ·
          refine ⟨5065301848648701508411187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376867899099134338940791 5065301848648701508411187)
          ·
            refine ⟨7597952772973052262616781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065301848648701508411187 7597952772973052262616781)
            ·
              refine ⟨2849232289864894598481293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7597952772973052262616781 2849232289864894598481293)
              ·
                refine ⟨1068462108699335474430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2849232289864894598481293 1068462108699335474430485)
                ·
                  refine ⟨50084161345281350363929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1068462108699335474430485 50084161345281350363929)
                  ·
                    rfl

theorem cell23_877847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 6].length) (baseStart_877847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877847 prefixEnd_877847 := by exact prefixLift 877847
  have htrace : WordTrace (prefixWord ++ tailWord_877847) baseStart_877847 baseEnd_877847 := by
    simpa [prefixWord, tailWord_877847, baseEnd_877847] using wordTrace_append hprefix tailTrace_877847
  have hstable : (prefixWord ++ tailWord_877847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877847).length < 2 ^ (prefixWord ++ tailWord_877847).sum := by decide
  have hdescent : baseEnd_877847 < baseStart_877847 := by decide
  rcases family_descends (prefixWord ++ tailWord_877847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877897 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_877897 : Nat := 118140960795 + 877897 * 2 ^ 59
def prefixEnd_877897 : Nat := 4983230072969 + 3 ^ 40 * 877897 * 2
def baseEnd_877897 : Nat := 450783126140256957650131

theorem tailTrace_877897 : CollatzResearch.WordTrace tailWord_877897 prefixEnd_877897 450783126140256957650131 := by
  unfold tailWord_877897
  simp only [CollatzResearch.WordTrace]
  refine ⟨32019534100536576715943945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21346356067024384477295963 32019534100536576715943945)
  ·
    refine ⟨24014650575402432536957959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32019534100536576715943945 24014650575402432536957959)
    ·
      refine ⟨36021975863103648805436939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24014650575402432536957959 36021975863103648805436939)
      ·
        refine ⟨54032963794655473208155409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36021975863103648805436939 54032963794655473208155409)
        ·
          refine ⟨40524722845991604906116557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54032963794655473208155409 40524722845991604906116557)
          ·
            refine ⟨15196771067246851839793709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40524722845991604906116557 15196771067246851839793709)
            ·
              refine ⟨5698789150217569439922641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15196771067246851839793709 5698789150217569439922641)
              ·
                refine ⟨4274091862663177079941981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5698789150217569439922641 4274091862663177079941981)
                ·
                  refine ⟨1602784448498691404978243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4274091862663177079941981 1602784448498691404978243)
                  ·
                    refine ⟨2404176672748037107467365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1602784448498691404978243 2404176672748037107467365)
                    ·
                      refine ⟨450783126140256957650131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2404176672748037107467365 450783126140256957650131)
                      ·
                        rfl

theorem cell23_877897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_877897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877897 prefixEnd_877897 := by exact prefixLift 877897
  have htrace : WordTrace (prefixWord ++ tailWord_877897) baseStart_877897 baseEnd_877897 := by
    simpa [prefixWord, tailWord_877897, baseEnd_877897] using wordTrace_append hprefix tailTrace_877897
  have hstable : (prefixWord ++ tailWord_877897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877897).length < 2 ^ (prefixWord ++ tailWord_877897).sum := by decide
  have hdescent : baseEnd_877897 < baseStart_877897 := by decide
  rcases family_descends (prefixWord ++ tailWord_877897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877907 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 1, 6]
def baseStart_877907 : Nat := 118140960795 + 877907 * 2 ^ 59
def prefixEnd_877907 : Nat := 4983230072969 + 3 ^ 40 * 877907 * 2
def baseEnd_877907 : Nat := 150262753648933972841695

theorem tailTrace_877907 : CollatzResearch.WordTrace tailWord_877907 prefixEnd_877907 150262753648933972841695 := by
  unfold tailWord_877907
  simp only [CollatzResearch.WordTrace]
  refine ⟨32019898830500348423807975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21346599220333565615871983 32019898830500348423807975)
  ·
    refine ⟨48029848245750522635711963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32019898830500348423807975 48029848245750522635711963)
    ·
      refine ⟨72044772368625783953567945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48029848245750522635711963 72044772368625783953567945)
      ·
        refine ⟨54033579276469337965175959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72044772368625783953567945 54033579276469337965175959)
        ·
          refine ⟨81050368914704006947763939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54033579276469337965175959 81050368914704006947763939)
          ·
            refine ⟨121575553372056010421645909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81050368914704006947763939 121575553372056010421645909)
            ·
              refine ⟨1424713516078781372128663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 121575553372056010421645909 1424713516078781372128663)
              ·
                refine ⟨2137070274118172058192995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424713516078781372128663 2137070274118172058192995)
                ·
                  refine ⟨3205605411177258087289493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137070274118172058192995 3205605411177258087289493)
                  ·
                    refine ⟨150262753648933972841695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3205605411177258087289493 150262753648933972841695)
                    ·
                      rfl

theorem cell23_877907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 6].length) (baseStart_877907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877907 prefixEnd_877907 := by exact prefixLift 877907
  have htrace : WordTrace (prefixWord ++ tailWord_877907) baseStart_877907 baseEnd_877907 := by
    simpa [prefixWord, tailWord_877907, baseEnd_877907] using wordTrace_append hprefix tailTrace_877907
  have hstable : (prefixWord ++ tailWord_877907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877907).length < 2 ^ (prefixWord ++ tailWord_877907).sum := by decide
  have hdescent : baseEnd_877907 < baseStart_877907 := by decide
  rcases family_descends (prefixWord ++ tailWord_877907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877928 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 1, 5]
def baseStart_877928 : Nat := 118140960795 + 877928 * 2 ^ 59
def prefixEnd_877928 : Nat := 4983230072969 + 3 ^ 40 * 877928 * 2
def baseEnd_877928 : Nat := 150266348013515445454163

theorem tailTrace_877928 : CollatzResearch.WordTrace tailWord_877928 prefixEnd_877928 150266348013515445454163 := by
  unfold tailWord_877928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010332381712134505161219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21347109842282846006881625 16010332381712134505161219)
  ·
    refine ⟨24015498572568201757741829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16010332381712134505161219 24015498572568201757741829)
    ·
      refine ⟨4502905982356537829576593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24015498572568201757741829 4502905982356537829576593)
      ·
        refine ⟨3377179486767403372182445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4502905982356537829576593 3377179486767403372182445)
        ·
          refine ⟨1266442307537776264568417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3377179486767403372182445 1266442307537776264568417)
          ·
            refine ⟨949831730653332198426313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266442307537776264568417 949831730653332198426313)
            ·
              refine ⟨712373797989999148819735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949831730653332198426313 712373797989999148819735)
              ·
                refine ⟨1068560696984998723229603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712373797989999148819735 1068560696984998723229603)
                ·
                  refine ⟨1602841045477498084844405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068560696984998723229603 1602841045477498084844405)
                  ·
                    refine ⟨150266348013515445454163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1602841045477498084844405 150266348013515445454163)
                    ·
                      rfl

theorem cell23_877928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_877928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877928 prefixEnd_877928 := by exact prefixLift 877928
  have htrace : WordTrace (prefixWord ++ tailWord_877928) baseStart_877928 baseEnd_877928 := by
    simpa [prefixWord, tailWord_877928, baseEnd_877928] using wordTrace_append hprefix tailTrace_877928
  have hstable : (prefixWord ++ tailWord_877928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877928).length < 2 ^ (prefixWord ++ tailWord_877928).sum := by decide
  have hdescent : baseEnd_877928 < baseStart_877928 := by decide
  rcases family_descends (prefixWord ++ tailWord_877928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877941 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_877941 : Nat := 118140960795 + 877941 * 2 ^ 59
def prefixEnd_877941 : Nat := 4983230072969 + 3 ^ 40 * 877941 * 2
def baseEnd_877941 : Nat := 150268573096351595166643

theorem tailTrace_877941 : CollatzResearch.WordTrace tailWord_877941 prefixEnd_877941 150268573096351595166643 := by
  unfold tailWord_877941
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021138912377172230545677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21347425941584781487030451 32021138912377172230545677)
  ·
    refine ⟨12007927092141439586454629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32021138912377172230545677 12007927092141439586454629)
    ·
      refine ⟨2251486329776519922460243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12007927092141439586454629 2251486329776519922460243)
      ·
        refine ⟨3377229494664779883690365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251486329776519922460243 3377229494664779883690365)
        ·
          refine ⟨1266461060499292456383887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3377229494664779883690365 1266461060499292456383887)
          ·
            refine ⟨1899691590748938684575831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266461060499292456383887 1899691590748938684575831)
            ·
              refine ⟨2849537386123408026863747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899691590748938684575831 2849537386123408026863747)
              ·
                refine ⟨4274306079185112040295621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849537386123408026863747 4274306079185112040295621)
                ·
                  refine ⟨801432389847208507555429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4274306079185112040295621 801432389847208507555429)
                  ·
                    refine ⟨150268573096351595166643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 801432389847208507555429 150268573096351595166643)
                    ·
                      rfl

theorem cell23_877941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_877941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877941 prefixEnd_877941 := by exact prefixLift 877941
  have htrace : WordTrace (prefixWord ++ tailWord_877941) baseStart_877941 baseEnd_877941 := by
    simpa [prefixWord, tailWord_877941, baseEnd_877941] using wordTrace_append hprefix tailTrace_877941
  have hstable : (prefixWord ++ tailWord_877941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877941).length < 2 ^ (prefixWord ++ tailWord_877941).sum := by decide
  have hdescent : baseEnd_877941 < baseStart_877941 := by decide
  rcases family_descends (prefixWord ++ tailWord_877941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877948 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_877948 : Nat := 118140960795 + 877948 * 2 ^ 59
def prefixEnd_877948 : Nat := 4983230072969 + 3 ^ 40 * 877948 * 2
def baseEnd_877948 : Nat := 450809313653636258112397

theorem tailTrace_877948 : CollatzResearch.WordTrace tailWord_877948 prefixEnd_877948 450809313653636258112397 := by
  unfold tailWord_877948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010697111675906213025249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21347596148901208284033665 16010697111675906213025249)
  ·
    refine ⟨12008022833756929659768937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16010697111675906213025249 12008022833756929659768937)
    ·
      refine ⟨9006017125317697244826703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12008022833756929659768937 9006017125317697244826703)
      ·
        refine ⟨13509025687976545867240055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9006017125317697244826703 13509025687976545867240055)
        ·
          refine ⟨20263538531964818800860083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13509025687976545867240055 20263538531964818800860083)
          ·
            refine ⟨30395307797947228201290125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20263538531964818800860083 30395307797947228201290125)
            ·
              refine ⟨11398240424230210575483797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30395307797947228201290125 11398240424230210575483797)
              ·
                refine ⟨534292519885791120725803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11398240424230210575483797 534292519885791120725803)
                ·
                  refine ⟨801438779828686681088705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534292519885791120725803 801438779828686681088705)
                  ·
                    refine ⟨601079084871515010816529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801438779828686681088705 601079084871515010816529)
                    ·
                      refine ⟨450809313653636258112397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601079084871515010816529 450809313653636258112397)
                      ·
                        rfl

theorem cell23_877948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_877948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877948 prefixEnd_877948 := by exact prefixLift 877948
  have htrace : WordTrace (prefixWord ++ tailWord_877948) baseStart_877948 baseEnd_877948 := by
    simpa [prefixWord, tailWord_877948, baseEnd_877948] using wordTrace_append hprefix tailTrace_877948
  have hstable : (prefixWord ++ tailWord_877948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877948).length < 2 ^ (prefixWord ++ tailWord_877948).sum := by decide
  have hdescent : baseEnd_877948 < baseStart_877948 := by decide
  rcases family_descends (prefixWord ++ tailWord_877948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877961 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_877961 : Nat := 118140960795 + 877961 * 2 ^ 59
def prefixEnd_877961 : Nat := 4983230072969 + 3 ^ 40 * 877961 * 2
def baseEnd_877961 : Nat := 450815988902144707249837

theorem tailTrace_877961 : CollatzResearch.WordTrace tailWord_877961 prefixEnd_877961 450815988902144707249837 := by
  unfold tailWord_877961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021868372304715646273737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21347912248203143764182491 32021868372304715646273737)
  ·
    refine ⟨24016401279228536734705303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32021868372304715646273737 24016401279228536734705303)
    ·
      refine ⟨36024601918842805102057955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24016401279228536734705303 36024601918842805102057955)
      ·
        refine ⟨54036902878264207653086933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36024601918842805102057955 54036902878264207653086933)
        ·
          refine ⟨1266489911209317366869225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54036902878264207653086933 1266489911209317366869225)
          ·
            refine ⟨949867433406988025151919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266489911209317366869225 949867433406988025151919)
            ·
              refine ⟨1424801150110482037727879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949867433406988025151919 1424801150110482037727879)
              ·
                refine ⟨2137201725165723056591819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424801150110482037727879 2137201725165723056591819)
                ·
                  refine ⟨3205802587748584584887729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137201725165723056591819 3205802587748584584887729)
                  ·
                    refine ⟨2404351940811438438665797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3205802587748584584887729 2404351940811438438665797)
                    ·
                      refine ⟨450815988902144707249837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2404351940811438438665797 450815988902144707249837)
                      ·
                        rfl

theorem cell23_877961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_877961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877961 prefixEnd_877961 := by exact prefixLift 877961
  have htrace : WordTrace (prefixWord ++ tailWord_877961) baseStart_877961 baseEnd_877961 := by
    simpa [prefixWord, tailWord_877961, baseEnd_877961] using wordTrace_append hprefix tailTrace_877961
  have hstable : (prefixWord ++ tailWord_877961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877961).length < 2 ^ (prefixWord ++ tailWord_877961).sum := by decide
  have hdescent : baseEnd_877961 < baseStart_877961 := by decide
  rcases family_descends (prefixWord ++ tailWord_877961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877977 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_877977 : Nat := 118140960795 + 877977 * 2 ^ 59
def prefixEnd_877977 : Nat := 4983230072969 + 3 ^ 40 * 877977 * 2
def baseEnd_877977 : Nat := 450824204592616644649763

theorem tailTrace_877977 : CollatzResearch.WordTrace tailWord_877977 prefixEnd_877977 450824204592616644649763 := by
  unfold tailWord_877977
  simp only [CollatzResearch.WordTrace]
  refine ⟨32022451940246750378856185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21348301293497833585904123 32022451940246750378856185)
  ·
    refine ⟨24016838955185062784142139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32022451940246750378856185 24016838955185062784142139)
    ·
      refine ⟨36025258432777594176213209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24016838955185062784142139 36025258432777594176213209)
      ·
        refine ⟨27018943824583195632159907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36025258432777594176213209 27018943824583195632159907)
        ·
          refine ⟨40528415736874793448239861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27018943824583195632159907 40528415736874793448239861)
          ·
            refine ⟨3799538975332011885772487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40528415736874793448239861 3799538975332011885772487)
            ·
              refine ⟨5699308462998017828658731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799538975332011885772487 5699308462998017828658731)
              ·
                refine ⟨8548962694497026742988097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699308462998017828658731 8548962694497026742988097)
                ·
                  refine ⟨6411722020872770057241073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8548962694497026742988097 6411722020872770057241073)
                  ·
                    refine ⟨4808791515654577542930805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6411722020872770057241073 4808791515654577542930805)
                    ·
                      refine ⟨450824204592616644649763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4808791515654577542930805 450824204592616644649763)
                      ·
                        rfl

theorem cell23_877977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_877977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877977 prefixEnd_877977 := by exact prefixLift 877977
  have htrace : WordTrace (prefixWord ++ tailWord_877977) baseStart_877977 baseEnd_877977 := by
    simpa [prefixWord, tailWord_877977, baseEnd_877977] using wordTrace_append hprefix tailTrace_877977
  have hstable : (prefixWord ++ tailWord_877977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877977).length < 2 ^ (prefixWord ++ tailWord_877977).sum := by decide
  have hdescent : baseEnd_877977 < baseStart_877977 := by decide
  rcases family_descends (prefixWord ++ tailWord_877977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877981 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_877981 : Nat := 118140960795 + 877981 * 2 ^ 59
def prefixEnd_877981 : Nat := 4983230072969 + 3 ^ 40 * 877981 * 2
def baseEnd_877981 : Nat := 450826258515234628999745

theorem tailTrace_877981 : CollatzResearch.WordTrace tailWord_877981 prefixEnd_877981 450826258515234628999745 := by
  unfold tailWord_877981
  simp only [CollatzResearch.WordTrace]
  refine ⟨32022597832232259062001797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21348398554821506041334531 32022597832232259062001797)
  ·
    refine ⟨6004237093543548574125337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32022597832232259062001797 6004237093543548574125337)
    ·
      refine ⟨4503177820157661430594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6004237093543548574125337 4503177820157661430594003)
      ·
        refine ⟨6754766730236492145891005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503177820157661430594003 6754766730236492145891005)
        ·
          refine ⟨2533037523838684554709127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6754766730236492145891005 2533037523838684554709127)
          ·
            refine ⟨3799556285758026832063691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533037523838684554709127 3799556285758026832063691)
            ·
              refine ⟨5699334428637040248095537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799556285758026832063691 5699334428637040248095537)
              ·
                refine ⟨4274500821477780186071653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5699334428637040248095537 4274500821477780186071653)
                ·
                  refine ⟨801468904027083784888435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4274500821477780186071653 801468904027083784888435)
                  ·
                    refine ⟨1202203356040625677332653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 801468904027083784888435 1202203356040625677332653)
                    ·
                      refine ⟨450826258515234628999745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1202203356040625677332653 450826258515234628999745)
                      ·
                        rfl

theorem cell23_877981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_877981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_877981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_877981 prefixEnd_877981 := by exact prefixLift 877981
  have htrace : WordTrace (prefixWord ++ tailWord_877981) baseStart_877981 baseEnd_877981 := by
    simpa [prefixWord, tailWord_877981, baseEnd_877981] using wordTrace_append hprefix tailTrace_877981
  have hstable : (prefixWord ++ tailWord_877981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877981).length < 2 ^ (prefixWord ++ tailWord_877981).sum := by decide
  have hdescent : baseEnd_877981 < baseStart_877981 := by decide
  rcases family_descends (prefixWord ++ tailWord_877981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878007 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_878007 : Nat := 118140960795 + 878007 * 2 ^ 59
def prefixEnd_878007 : Nat := 4983230072969 + 3 ^ 40 * 878007 * 2
def baseEnd_878007 : Nat := 450839609012251527274625

theorem tailTrace_878007 : CollatzResearch.WordTrace tailWord_878007 prefixEnd_878007 450839609012251527274625 := by
  unfold tailWord_878007
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023546130138065502448275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21349030753425377001632183 32023546130138065502448275)
  ·
    refine ⟨48035319195207098253672413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32023546130138065502448275 48035319195207098253672413)
    ·
      refine ⟨18013244698202661845127155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48035319195207098253672413 18013244698202661845127155)
      ·
        refine ⟨27019867047303992767690733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18013244698202661845127155 27019867047303992767690733)
        ·
          refine ⟨10132450142738997287884025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27019867047303992767690733 10132450142738997287884025)
          ·
            refine ⟨7599337607054247965913019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10132450142738997287884025 7599337607054247965913019)
            ·
              refine ⟨11399006410581371948869529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599337607054247965913019 11399006410581371948869529)
              ·
                refine ⟨8549254807936028961652147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11399006410581371948869529 8549254807936028961652147)
                ·
                  refine ⟨12823882211904043442478221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549254807936028961652147 12823882211904043442478221)
                  ·
                    refine ⟨4808955829464016290929333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12823882211904043442478221 4808955829464016290929333)
                    ·
                      refine ⟨450839609012251527274625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4808955829464016290929333 450839609012251527274625)
                      ·
                        rfl

theorem cell23_878007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_878007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878007 prefixEnd_878007 := by exact prefixLift 878007
  have htrace : WordTrace (prefixWord ++ tailWord_878007) baseStart_878007 baseEnd_878007 := by
    simpa [prefixWord, tailWord_878007, baseEnd_878007] using wordTrace_append hprefix tailTrace_878007
  have hstable : (prefixWord ++ tailWord_878007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878007).length < 2 ^ (prefixWord ++ tailWord_878007).sum := by decide
  have hdescent : baseEnd_878007 < baseStart_878007 := by decide
  rcases family_descends (prefixWord ++ tailWord_878007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878027 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 7]
def baseStart_878027 : Nat := 118140960795 + 878027 * 2 ^ 59
def prefixEnd_878027 : Nat := 4983230072969 + 3 ^ 40 * 878027 * 2
def baseEnd_878027 : Nat := 50094430958371272113837

theorem tailTrace_878027 : CollatzResearch.WordTrace tailWord_878027 prefixEnd_878027 50094430958371272113837 := by
  unfold tailWord_878027
  simp only [CollatzResearch.WordTrace]
  refine ⟨32024275590065608918176335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21349517060043739278784223 32024275590065608918176335)
  ·
    refine ⟨48036413385098413377264503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32024275590065608918176335 48036413385098413377264503)
    ·
      refine ⟨72054620077647620065896755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48036413385098413377264503 72054620077647620065896755)
      ·
        refine ⟨108081930116471430098845133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72054620077647620065896755 108081930116471430098845133)
        ·
          refine ⟨40530723793676786287066925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108081930116471430098845133 40530723793676786287066925)
          ·
            refine ⟨15199021422628794857650097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40530723793676786287066925 15199021422628794857650097)
            ·
              refine ⟨11399266066971596143237573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15199021422628794857650097 11399266066971596143237573)
              ·
                refine ⟨2137362387557174276857045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11399266066971596143237573 2137362387557174276857045)
                ·
                  refine ⟨50094430958371272113837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2137362387557174276857045 50094430958371272113837)
                  ·
                    rfl

theorem cell23_878027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 7].length) (baseStart_878027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878027 prefixEnd_878027 := by exact prefixLift 878027
  have htrace : WordTrace (prefixWord ++ tailWord_878027) baseStart_878027 baseEnd_878027 := by
    simpa [prefixWord, tailWord_878027, baseEnd_878027] using wordTrace_append hprefix tailTrace_878027
  have hstable : (prefixWord ++ tailWord_878027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878027).length < 2 ^ (prefixWord ++ tailWord_878027).sum := by decide
  have hdescent : baseEnd_878027 < baseStart_878027 := by decide
  rcases family_descends (prefixWord ++ tailWord_878027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878038 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_878038 : Nat := 118140960795 + 878038 * 2 ^ 59
def prefixEnd_878038 : Nat := 4983230072969 + 3 ^ 40 * 878038 * 2
def baseEnd_878038 : Nat := 450855526912540905986983

theorem tailTrace_878038 : CollatzResearch.WordTrace tailWord_878038 prefixEnd_878038 450855526912540905986983 := by
  unfold tailWord_878038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001542299564109862301673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21349784528683838531217845 2001542299564109862301673)
  ·
    refine ⟨1501156724673082396726255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2001542299564109862301673 1501156724673082396726255)
    ·
      refine ⟨2251735087009623595089383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501156724673082396726255 2251735087009623595089383)
      ·
        refine ⟨3377602630514435392634075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251735087009623595089383 3377602630514435392634075)
        ·
          refine ⟨5066403945771653088951113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377602630514435392634075 5066403945771653088951113)
          ·
            refine ⟨3799802959328739816713335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5066403945771653088951113 3799802959328739816713335)
            ·
              refine ⟨5699704438993109725070003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3799802959328739816713335 5699704438993109725070003)
              ·
                refine ⟨8549556658489664587605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699704438993109725070003 8549556658489664587605005)
                ·
                  refine ⟨3206083746933624220351877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8549556658489664587605005 3206083746933624220351877)
                  ·
                    refine ⟨601140702550054541315977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206083746933624220351877 601140702550054541315977)
                    ·
                      refine ⟨450855526912540905986983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601140702550054541315977 450855526912540905986983)
                      ·
                        rfl

theorem cell23_878038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_878038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878038 prefixEnd_878038 := by exact prefixLift 878038
  have htrace : WordTrace (prefixWord ++ tailWord_878038) baseStart_878038 baseEnd_878038 := by
    simpa [prefixWord, tailWord_878038, baseEnd_878038] using wordTrace_append hprefix tailTrace_878038
  have hstable : (prefixWord ++ tailWord_878038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878038).length < 2 ^ (prefixWord ++ tailWord_878038).sum := by decide
  have hdescent : baseEnd_878038 < baseStart_878038 := by decide
  rcases family_descends (prefixWord ++ tailWord_878038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878055 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_878055 : Nat := 118140960795 + 878055 * 2 ^ 59
def prefixEnd_878055 : Nat := 4983230072969 + 3 ^ 40 * 878055 * 2
def baseEnd_878055 : Nat := 450864256083667339474405

theorem tailTrace_878055 : CollatzResearch.WordTrace tailWord_878055 prefixEnd_878055 450864256083667339474405 := by
  unfold tailWord_878055
  simp only [CollatzResearch.WordTrace]
  refine ⟨32025296833964169700195619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21350197889309446466797079 32025296833964169700195619)
  ·
    refine ⟨48037945250946254550293429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32025296833964169700195619 48037945250946254550293429)
    ·
      refine ⟨4503557367276211364090009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48037945250946254550293429 4503557367276211364090009)
      ·
        refine ⟨3377668025457158523067507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4503557367276211364090009 3377668025457158523067507)
        ·
          refine ⟨5066502038185737784601261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377668025457158523067507 5066502038185737784601261)
          ·
            refine ⟨1899938264319651669225473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5066502038185737784601261 1899938264319651669225473)
            ·
              refine ⟨1424953698239738751919105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899938264319651669225473 1424953698239738751919105)
              ·
                refine ⟨1068715273679804063939329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424953698239738751919105 1068715273679804063939329)
                ·
                  refine ⟨801536455259853047954497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068715273679804063939329 801536455259853047954497)
                  ·
                    refine ⟨601152341444889785965873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801536455259853047954497 601152341444889785965873)
                    ·
                      refine ⟨450864256083667339474405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601152341444889785965873 450864256083667339474405)
                      ·
                        rfl

theorem cell23_878055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_878055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878055 prefixEnd_878055 := by exact prefixLift 878055
  have htrace : WordTrace (prefixWord ++ tailWord_878055) baseStart_878055 baseEnd_878055 := by
    simpa [prefixWord, tailWord_878055, baseEnd_878055] using wordTrace_append hprefix tailTrace_878055
  have hstable : (prefixWord ++ tailWord_878055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878055).length < 2 ^ (prefixWord ++ tailWord_878055).sum := by decide
  have hdescent : baseEnd_878055 < baseStart_878055 := by decide
  rcases family_descends (prefixWord ++ tailWord_878055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878067 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_878067 : Nat := 118140960795 + 878067 * 2 ^ 59
def prefixEnd_878067 : Nat := 4983230072969 + 3 ^ 40 * 878067 * 2
def baseEnd_878067 : Nat := 450870417851521292524349

theorem tailTrace_878067 : CollatzResearch.WordTrace tailWord_878067 prefixEnd_878067 450870417851521292524349 := by
  unfold tailWord_878067
  simp only [CollatzResearch.WordTrace]
  refine ⟨32025734509920695749632455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21350489673280463833088303 32025734509920695749632455)
  ·
    refine ⟨48038601764881043624448683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32025734509920695749632455 48038601764881043624448683)
    ·
      refine ⟨72057902647321565436673025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48038601764881043624448683 72057902647321565436673025)
      ·
        refine ⟨54043426985491174077504769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72057902647321565436673025 54043426985491174077504769)
        ·
          refine ⟨40532570239118380558128577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54043426985491174077504769 40532570239118380558128577)
          ·
            refine ⟨30399427679338785418596433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40532570239118380558128577 30399427679338785418596433)
            ·
              refine ⟨22799570759504089063947325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30399427679338785418596433 22799570759504089063947325)
              ·
                refine ⟨8549839034814033398980247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22799570759504089063947325 8549839034814033398980247)
                ·
                  refine ⟨12824758552221050098470371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549839034814033398980247 12824758552221050098470371)
                  ·
                    refine ⟨19237137828331575147705557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12824758552221050098470371 19237137828331575147705557)
                    ·
                      refine ⟨450870417851521292524349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19237137828331575147705557 450870417851521292524349)
                      ·
                        rfl

theorem cell23_878067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_878067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878067 prefixEnd_878067 := by exact prefixLift 878067
  have htrace : WordTrace (prefixWord ++ tailWord_878067) baseStart_878067 baseEnd_878067 := by
    simpa [prefixWord, tailWord_878067, baseEnd_878067] using wordTrace_append hprefix tailTrace_878067
  have hstable : (prefixWord ++ tailWord_878067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878067).length < 2 ^ (prefixWord ++ tailWord_878067).sum := by decide
  have hdescent : baseEnd_878067 < baseStart_878067 := by decide
  rcases family_descends (prefixWord ++ tailWord_878067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878078 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_878078 : Nat := 118140960795 + 878078 * 2 ^ 59
def prefixEnd_878078 : Nat := 4983230072969 + 3 ^ 40 * 878078 * 2
def baseEnd_878078 : Nat := 50097340682080083276311

theorem tailTrace_878078 : CollatzResearch.WordTrace tailWord_878078 prefixEnd_878078 50097340682080083276311 := by
  unfold tailWord_878078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003266964110105578535361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21350757141920563085521925 4003266964110105578535361)
  ·
    refine ⟨3002450223082579183901521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4003266964110105578535361 3002450223082579183901521)
    ·
      refine ⟨2251837667311934387926141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3002450223082579183901521 2251837667311934387926141)
      ·
        refine ⟨844439125241975395472303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2251837667311934387926141 844439125241975395472303)
        ·
          refine ⟨1266658687862963093208455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844439125241975395472303 1266658687862963093208455)
          ·
            refine ⟨1899988031794444639812683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266658687862963093208455 1899988031794444639812683)
            ·
              refine ⟨2849982047691666959719025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899988031794444639812683 2849982047691666959719025)
              ·
                refine ⟨2137486535768750219789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849982047691666959719025 2137486535768750219789269)
                ·
                  refine ⟨50097340682080083276311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2137486535768750219789269 50097340682080083276311)
                  ·
                    rfl

theorem cell23_878078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_878078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878078 prefixEnd_878078 := by exact prefixLift 878078
  have htrace : WordTrace (prefixWord ++ tailWord_878078) baseStart_878078 baseEnd_878078 := by
    simpa [prefixWord, tailWord_878078, baseEnd_878078] using wordTrace_append hprefix tailTrace_878078
  have hstable : (prefixWord ++ tailWord_878078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878078).length < 2 ^ (prefixWord ++ tailWord_878078).sum := by decide
  have hdescent : baseEnd_878078 < baseStart_878078 := by decide
  rcases family_descends (prefixWord ++ tailWord_878078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878111 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 2, 4, 2]
def baseStart_878111 : Nat := 118140960795 + 878111 * 2 ^ 59
def prefixEnd_878111 : Nat := 4983230072969 + 3 ^ 40 * 878111 * 2
def baseEnd_878111 : Nat := 450893011000319120374147

theorem tailTrace_878111 : CollatzResearch.WordTrace tailWord_878111 prefixEnd_878111 450893011000319120374147 := by
  unfold tailWord_878111
  simp only [CollatzResearch.WordTrace]
  refine ⟨32027339321761291264234187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21351559547840860842822791 32027339321761291264234187)
  ·
    refine ⟨48041008982641936896351281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32027339321761291264234187 48041008982641936896351281)
    ·
      refine ⟨36030756736981452672263461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48041008982641936896351281 36030756736981452672263461)
      ·
        refine ⟨6755766888184022376049399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36030756736981452672263461 6755766888184022376049399)
        ·
          refine ⟨10133650332276033564074099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755766888184022376049399 10133650332276033564074099)
          ·
            refine ⟨15200475498414050346111149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133650332276033564074099 15200475498414050346111149)
            ·
              refine ⟨5700178311905268879791681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15200475498414050346111149 5700178311905268879791681)
              ·
                refine ⟨4275133733928951659843761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5700178311905268879791681 4275133733928951659843761)
                ·
                  refine ⟨3206350300446713744882821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4275133733928951659843761 3206350300446713744882821)
                  ·
                    refine ⟨601190681333758827165529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206350300446713744882821 601190681333758827165529)
                    ·
                      refine ⟨450893011000319120374147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601190681333758827165529 450893011000319120374147)
                      ·
                        rfl

theorem cell23_878111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_878111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878111 prefixEnd_878111 := by exact prefixLift 878111
  have htrace : WordTrace (prefixWord ++ tailWord_878111) baseStart_878111 baseEnd_878111 := by
    simpa [prefixWord, tailWord_878111, baseEnd_878111] using wordTrace_append hprefix tailTrace_878111
  have hstable : (prefixWord ++ tailWord_878111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878111).length < 2 ^ (prefixWord ++ tailWord_878111).sum := by decide
  have hdescent : baseEnd_878111 < baseStart_878111 := by decide
  rcases family_descends (prefixWord ++ tailWord_878111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878114 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_878114 : Nat := 118140960795 + 878114 * 2 ^ 59
def prefixEnd_878114 : Nat := 4983230072969 + 3 ^ 40 * 878114 * 2
def baseEnd_878114 : Nat := 450894551442282608636633

theorem tailTrace_878114 : CollatzResearch.WordTrace tailWord_878114 prefixEnd_878114 450894551442282608636633 := by
  unfold tailWord_878114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006862185187605694148349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21351632493833615184395597 8006862185187605694148349)
  ·
    refine ⟨3002573319445352135305631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8006862185187605694148349 3002573319445352135305631)
    ·
      refine ⟨4503859979168028202958447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002573319445352135305631 4503859979168028202958447)
      ·
        refine ⟨6755789968752042304437671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503859979168028202958447 6755789968752042304437671)
        ·
          refine ⟨10133684953128063456656507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755789968752042304437671 10133684953128063456656507)
          ·
            refine ⟨15200527429692095184984761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133684953128063456656507 15200527429692095184984761)
            ·
              refine ⟨11400395572269071388738571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15200527429692095184984761 11400395572269071388738571)
              ·
                refine ⟨17100593358403607083107857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11400395572269071388738571 17100593358403607083107857)
                ·
                  refine ⟨12825445018802705312330893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17100593358403607083107857 12825445018802705312330893)
                  ·
                    refine ⟨4809541882051014492124085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12825445018802705312330893 4809541882051014492124085)
                    ·
                      refine ⟨450894551442282608636633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4809541882051014492124085 450894551442282608636633)
                      ·
                        rfl

theorem cell23_878114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_878114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878114 prefixEnd_878114 := by exact prefixLift 878114
  have htrace : WordTrace (prefixWord ++ tailWord_878114) baseStart_878114 baseEnd_878114 := by
    simpa [prefixWord, tailWord_878114, baseEnd_878114] using wordTrace_append hprefix tailTrace_878114
  have hstable : (prefixWord ++ tailWord_878114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878114).length < 2 ^ (prefixWord ++ tailWord_878114).sum := by decide
  have hdescent : baseEnd_878114 < baseStart_878114 := by decide
  rcases family_descends (prefixWord ++ tailWord_878114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878144 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_878144 : Nat := 118140960795 + 878144 * 2 ^ 59
def prefixEnd_878144 : Nat := 4983230072969 + 3 ^ 40 * 878144 * 2
def baseEnd_878144 : Nat := 450909955861917491261495

theorem tailTrace_878144 : CollatzResearch.WordTrace tailWord_878144 prefixEnd_878144 450909955861917491261495 := by
  unfold tailWord_878144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014271465320868950092743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21352361953761158600123657 16014271465320868950092743)
  ·
    refine ⟨24021407197981303425139115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16014271465320868950092743 24021407197981303425139115)
    ·
      refine ⟨36032110796971955137708673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24021407197981303425139115 36032110796971955137708673)
      ·
        refine ⟨27024083097728966353281505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36032110796971955137708673 27024083097728966353281505)
        ·
          refine ⟨20268062323296724764961129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27024083097728966353281505 20268062323296724764961129)
          ·
            refine ⟨15201046742472543573720847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20268062323296724764961129 15201046742472543573720847)
            ·
              refine ⟨22801570113708815360581271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15201046742472543573720847 22801570113708815360581271)
              ·
                refine ⟨34202355170563223040871907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22801570113708815360581271 34202355170563223040871907)
                ·
                  refine ⟨51303532755844834561307861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34202355170563223040871907 51303532755844834561307861)
                  ·
                    refine ⟨1202426548965113310030653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51303532755844834561307861 1202426548965113310030653)
                    ·
                      refine ⟨450909955861917491261495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1202426548965113310030653 450909955861917491261495)
                      ·
                        rfl

theorem cell23_878144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_878144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878144 prefixEnd_878144 := by exact prefixLift 878144
  have htrace : WordTrace (prefixWord ++ tailWord_878144) baseStart_878144 baseEnd_878144 := by
    simpa [prefixWord, tailWord_878144, baseEnd_878144] using wordTrace_append hprefix tailTrace_878144
  have hstable : (prefixWord ++ tailWord_878144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878144).length < 2 ^ (prefixWord ++ tailWord_878144).sum := by decide
  have hdescent : baseEnd_878144 < baseStart_878144 := by decide
  rcases family_descends (prefixWord ++ tailWord_878144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878172 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_878172 : Nat := 118140960795 + 878172 * 2 ^ 59
def prefixEnd_878172 : Nat := 4983230072969 + 3 ^ 40 * 878172 * 2
def baseEnd_878172 : Nat := 150308111106747793903789

theorem tailTrace_878172 : CollatzResearch.WordTrace tailWord_878172 prefixEnd_878172 150308111106747793903789 := by
  unfold tailWord_878172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014782087270149341102385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21353042783026865788136513 16014782087270149341102385)
  ·
    refine ⟨12011086565452612005826789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16014782087270149341102385 12011086565452612005826789)
    ·
      refine ⟨2252078731022364751092523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12011086565452612005826789 2252078731022364751092523)
      ·
        refine ⟨3378118096533547126638785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252078731022364751092523 3378118096533547126638785)
        ·
          refine ⟨2533588572400160344979089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378118096533547126638785 2533588572400160344979089)
          ·
            refine ⟨1900191429300120258734317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533588572400160344979089 1900191429300120258734317)
            ·
              refine ⟨712571785987545097025369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900191429300120258734317 712571785987545097025369)
              ·
                refine ⟨534428839490658822769027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712571785987545097025369 534428839490658822769027)
                ·
                  refine ⟨801643259235988234153541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534428839490658822769027 801643259235988234153541)
                  ·
                    refine ⟨150308111106747793903789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 801643259235988234153541 150308111106747793903789)
                    ·
                      rfl

theorem cell23_878172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_878172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878172 prefixEnd_878172 := by exact prefixLift 878172
  have htrace : WordTrace (prefixWord ++ tailWord_878172) baseStart_878172 baseEnd_878172 := by
    simpa [prefixWord, tailWord_878172, baseEnd_878172] using wordTrace_append hprefix tailTrace_878172
  have hstable : (prefixWord ++ tailWord_878172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878172).length < 2 ^ (prefixWord ++ tailWord_878172).sum := by decide
  have hdescent : baseEnd_878172 < baseStart_878172 := by decide
  rcases family_descends (prefixWord ++ tailWord_878172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878198 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_878198 : Nat := 118140960795 + 878198 * 2 ^ 59
def prefixEnd_878198 : Nat := 4983230072969 + 3 ^ 40 * 878198 * 2
def baseEnd_878198 : Nat := 150312561272420093328749

theorem tailTrace_878198 : CollatzResearch.WordTrace tailWord_878198 prefixEnd_878198 150312561272420093328749 := by
  unfold tailWord_878198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001907029527881570165703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21353674981630736748434165 2001907029527881570165703)
  ·
    refine ⟨3002860544291822355248555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001907029527881570165703 3002860544291822355248555)
    ·
      refine ⟨4504290816437733532872833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002860544291822355248555 4504290816437733532872833)
      ·
        refine ⟨3378218112328300149654625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504290816437733532872833 3378218112328300149654625)
        ·
          refine ⟨2533663584246225112240969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378218112328300149654625 2533663584246225112240969)
          ·
            refine ⟨1900247688184668834180727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533663584246225112240969 1900247688184668834180727)
            ·
              refine ⟨2850371532277003251271091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900247688184668834180727 2850371532277003251271091)
              ·
                refine ⟨4275557298415504876906637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850371532277003251271091 4275557298415504876906637)
                ·
                  refine ⟨1603333986905814328839989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4275557298415504876906637 1603333986905814328839989)
                  ·
                    refine ⟨150312561272420093328749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1603333986905814328839989 150312561272420093328749)
                    ·
                      rfl

theorem cell23_878198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_878198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878198 prefixEnd_878198 := by exact prefixLift 878198
  have htrace : WordTrace (prefixWord ++ tailWord_878198) baseStart_878198 baseEnd_878198 := by
    simpa [prefixWord, tailWord_878198, baseEnd_878198] using wordTrace_append hprefix tailTrace_878198
  have hstable : (prefixWord ++ tailWord_878198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878198).length < 2 ^ (prefixWord ++ tailWord_878198).sum := by decide
  have hdescent : baseEnd_878198 < baseStart_878198 := by decide
  rcases family_descends (prefixWord ++ tailWord_878198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878201 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_878201 : Nat := 118140960795 + 878201 * 2 ^ 59
def prefixEnd_878201 : Nat := 4983230072969 + 3 ^ 40 * 878201 * 2
def baseEnd_878201 : Nat := 450939224259223768248733

theorem tailTrace_878201 : CollatzResearch.WordTrace tailWord_878201 prefixEnd_878201 450939224259223768248733 := by
  unfold tailWord_878201
  simp only [CollatzResearch.WordTrace]
  refine ⟨32030621891435236635010457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21353747927623491090006971 32030621891435236635010457)
  ·
    refine ⟨24022966418576427476257843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32030621891435236635010457 24022966418576427476257843)
    ·
      refine ⟨36034449627864641214386765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24022966418576427476257843 36034449627864641214386765)
      ·
        refine ⟨13512918610449240455395037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36034449627864641214386765 13512918610449240455395037)
        ·
          refine ⟨5067344478918465170773139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13512918610449240455395037 5067344478918465170773139)
          ·
            refine ⟨7601016718377697756159709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067344478918465170773139 7601016718377697756159709)
            ·
              refine ⟨2850381269391636658559891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7601016718377697756159709 2850381269391636658559891)
              ·
                refine ⟨4275571904087454987839837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850381269391636658559891 4275571904087454987839837)
                ·
                  refine ⟨1603339464032795620439939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4275571904087454987839837 1603339464032795620439939)
                  ·
                    refine ⟨2405009196049193430659909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1603339464032795620439939 2405009196049193430659909)
                    ·
                      refine ⟨450939224259223768248733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2405009196049193430659909 450939224259223768248733)
                      ·
                        rfl

theorem cell23_878201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_878201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878201 prefixEnd_878201 := by exact prefixLift 878201
  have htrace : WordTrace (prefixWord ++ tailWord_878201) baseStart_878201 baseEnd_878201 := by
    simpa [prefixWord, tailWord_878201, baseEnd_878201] using wordTrace_append hprefix tailTrace_878201
  have hstable : (prefixWord ++ tailWord_878201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878201).length < 2 ^ (prefixWord ++ tailWord_878201).sum := by decide
  have hdescent : baseEnd_878201 < baseStart_878201 := by decide
  rcases family_descends (prefixWord ++ tailWord_878201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878205 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_878205 : Nat := 118140960795 + 878205 * 2 ^ 59
def prefixEnd_878205 : Nat := 4983230072969 + 3 ^ 40 * 878205 * 2
def baseEnd_878205 : Nat := 450941278181841752598715

theorem tailTrace_878205 : CollatzResearch.WordTrace tailWord_878205 prefixEnd_878205 450941278181841752598715 := by
  unfold tailWord_878205
  simp only [CollatzResearch.WordTrace]
  refine ⟨32030767783420745318156069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21353845188947163545437379 32030767783420745318156069)
  ·
    refine ⟨6005768959391389747154263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32030767783420745318156069 6005768959391389747154263)
    ·
      refine ⟨9008653439087084620731395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6005768959391389747154263 9008653439087084620731395)
      ·
        refine ⟨13512980158630626931097093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9008653439087084620731395 13512980158630626931097093)
        ·
          refine ⟨2533683779743242549580705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13512980158630626931097093 2533683779743242549580705)
          ·
            refine ⟨1900262834807431912185529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533683779743242549580705 1900262834807431912185529)
            ·
              refine ⟨1425197126105573934139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900262834807431912185529 1425197126105573934139147)
              ·
                refine ⟨2137795689158360901208721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425197126105573934139147 2137795689158360901208721)
                ·
                  refine ⟨1603346766868770675906541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137795689158360901208721 1603346766868770675906541)
                  ·
                    refine ⟨601255037575789003464953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603346766868770675906541 601255037575789003464953)
                    ·
                      refine ⟨450941278181841752598715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601255037575789003464953 450941278181841752598715)
                      ·
                        rfl

theorem cell23_878205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_878205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878205 prefixEnd_878205 := by exact prefixLift 878205
  have htrace : WordTrace (prefixWord ++ tailWord_878205) baseStart_878205 baseEnd_878205 := by
    simpa [prefixWord, tailWord_878205, baseEnd_878205] using wordTrace_append hprefix tailTrace_878205
  have hstable : (prefixWord ++ tailWord_878205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878205).length < 2 ^ (prefixWord ++ tailWord_878205).sum := by decide
  have hdescent : baseEnd_878205 < baseStart_878205 := by decide
  rcases family_descends (prefixWord ++ tailWord_878205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878241 : List Nat := [1, 2, 3, 3, 2, 1, 3, 8]
def baseStart_878241 : Nat := 118140960795 + 878241 * 2 ^ 59
def prefixEnd_878241 : Nat := 4983230072969 + 3 ^ 40 * 878241 * 2
def baseEnd_878241 : Nat := 16702213462422355990687

theorem tailTrace_878241 : CollatzResearch.WordTrace tailWord_878241 prefixEnd_878241 16702213462422355990687 := by
  unfold tailWord_878241
  simp only [CollatzResearch.WordTrace]
  refine ⟨32032080811290323466466577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21354720540860215644311051 32032080811290323466466577)
  ·
    refine ⟨24024060608467742599849933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32032080811290323466466577 24024060608467742599849933)
    ·
      refine ⟨9009022728175403474943725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24024060608467742599849933 9009022728175403474943725)
      ·
        refine ⟨3378383523065776303103897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9009022728175403474943725 3378383523065776303103897)
        ·
          refine ⟨2533787642299332227327923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378383523065776303103897 2533787642299332227327923)
          ·
            refine ⟨3800681463448998340991885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533787642299332227327923 3800681463448998340991885)
            ·
              refine ⟨1425255548793374377871957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3800681463448998340991885 1425255548793374377871957)
              ·
                refine ⟨16702213462422355990687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1425255548793374377871957 16702213462422355990687)
                ·
                  rfl

theorem cell23_878241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 8].length) (baseStart_878241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878241 prefixEnd_878241 := by exact prefixLift 878241
  have htrace : WordTrace (prefixWord ++ tailWord_878241) baseStart_878241 baseEnd_878241 := by
    simpa [prefixWord, tailWord_878241, baseEnd_878241] using wordTrace_append hprefix tailTrace_878241
  have hstable : (prefixWord ++ tailWord_878241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878241).length < 2 ^ (prefixWord ++ tailWord_878241).sum := by decide
  have hdescent : baseEnd_878241 < baseStart_878241 := by decide
  rcases family_descends (prefixWord ++ tailWord_878241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878268 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_878268 : Nat := 118140960795 + 878268 * 2 ^ 59
def prefixEnd_878268 : Nat := 4983230072969 + 3 ^ 40 * 878268 * 2
def baseEnd_878268 : Nat := 450973627463075006110925

theorem tailTrace_878268 : CollatzResearch.WordTrace tailWord_878268 prefixEnd_878268 450973627463075006110925 := by
  unfold tailWord_878268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16016532791096253538849729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21355377054795004718466305 16016532791096253538849729)
  ·
    refine ⟨12012399593322190154137297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16016532791096253538849729 12012399593322190154137297)
    ·
      refine ⟨9009299694991642615602973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12012399593322190154137297 9009299694991642615602973)
      ·
        refine ⟨3378487385621865980851115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9009299694991642615602973 3378487385621865980851115)
        ·
          refine ⟨5067731078432798971276673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378487385621865980851115 5067731078432798971276673)
          ·
            refine ⟨3800798308824599228457505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067731078432798971276673 3800798308824599228457505)
            ·
              refine ⟨2850598731618449421343129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800798308824599228457505 2850598731618449421343129)
              ·
                refine ⟨2137949048713837066007347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850598731618449421343129 2137949048713837066007347)
                ·
                  refine ⟨3206923573070755599011021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137949048713837066007347 3206923573070755599011021)
                  ·
                    refine ⟨1202596339901533349629133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3206923573070755599011021 1202596339901533349629133)
                    ·
                      refine ⟨450973627463075006110925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1202596339901533349629133 450973627463075006110925)
                      ·
                        rfl

theorem cell23_878268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_878268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878268 prefixEnd_878268 := by exact prefixLift 878268
  have htrace : WordTrace (prefixWord ++ tailWord_878268) baseStart_878268 baseEnd_878268 := by
    simpa [prefixWord, tailWord_878268, baseEnd_878268] using wordTrace_append hprefix tailTrace_878268
  have hstable : (prefixWord ++ tailWord_878268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878268).length < 2 ^ (prefixWord ++ tailWord_878268).sum := by decide
  have hdescent : baseEnd_878268 < baseStart_878268 := by decide
  rcases family_descends (prefixWord ++ tailWord_878268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878312 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_878312 : Nat := 118140960795 + 878312 * 2 ^ 59
def prefixEnd_878312 : Nat := 4983230072969 + 3 ^ 40 * 878312 * 2
def baseEnd_878312 : Nat := 450996220611872833960723

theorem tailTrace_878312 : CollatzResearch.WordTrace tailWord_878312 prefixEnd_878312 450996220611872833960723 := by
  unfold tailWord_878312
  simp only [CollatzResearch.WordTrace]
  refine ⟨16017335197016551296150595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21356446929355401728200793 16017335197016551296150595)
  ·
    refine ⟨24026002795524826944225893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16017335197016551296150595 24026002795524826944225893)
    ·
      refine ⟨4504875524160905052042355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24026002795524826944225893 4504875524160905052042355)
      ·
        refine ⟨6757313286241357578063533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504875524160905052042355 6757313286241357578063533)
        ·
          refine ⟨2533992482340509091773825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6757313286241357578063533 2533992482340509091773825)
          ·
            refine ⟨1900494361755381818830369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533992482340509091773825 1900494361755381818830369)
            ·
              refine ⟨1425370771316536364122777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900494361755381818830369 1425370771316536364122777)
              ·
                refine ⟨1069028078487402273092083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425370771316536364122777 1069028078487402273092083)
                ·
                  refine ⟨1603542117731103409638125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069028078487402273092083 1603542117731103409638125)
                  ·
                    refine ⟨601328294149163778614297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603542117731103409638125 601328294149163778614297)
                    ·
                      refine ⟨450996220611872833960723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601328294149163778614297 450996220611872833960723)
                      ·
                        rfl

theorem cell23_878312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_878312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878312 prefixEnd_878312 := by exact prefixLift 878312
  have htrace : WordTrace (prefixWord ++ tailWord_878312) baseStart_878312 baseEnd_878312 := by
    simpa [prefixWord, tailWord_878312, baseEnd_878312] using wordTrace_append hprefix tailTrace_878312
  have hstable : (prefixWord ++ tailWord_878312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878312).length < 2 ^ (prefixWord ++ tailWord_878312).sum := by decide
  have hdescent : baseEnd_878312 < baseStart_878312 := by decide
  rcases family_descends (prefixWord ++ tailWord_878312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878348 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 5]
def baseStart_878348 : Nat := 118140960795 + 878348 * 2 ^ 59
def prefixEnd_878348 : Nat := 4983230072969 + 3 ^ 40 * 878348 * 2
def baseEnd_878348 : Nat := 50112745101714965901173

theorem tailTrace_878348 : CollatzResearch.WordTrace tailWord_878348 prefixEnd_878348 50112745101714965901173 := by
  unfold tailWord_878348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16017991710951340370305849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21357322281268453827074465 16017991710951340370305849)
  ·
    refine ⟨12013493783213505277729387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16017991710951340370305849 12013493783213505277729387)
    ·
      refine ⟨18020240674820257916594081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12013493783213505277729387 18020240674820257916594081)
      ·
        refine ⟨13515180506115193437445561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18020240674820257916594081 13515180506115193437445561)
        ·
          refine ⟨10136385379586395078084171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13515180506115193437445561 10136385379586395078084171)
          ·
            refine ⟨15204578069379592617126257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136385379586395078084171 15204578069379592617126257)
            ·
              refine ⟨11403433552034694462844693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15204578069379592617126257 11403433552034694462844693)
              ·
                refine ⟨534535947751626302945845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11403433552034694462844693 534535947751626302945845)
                ·
                  refine ⟨50112745101714965901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534535947751626302945845 50112745101714965901173)
                  ·
                    rfl

theorem cell23_878348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_878348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878348 prefixEnd_878348 := by exact prefixLift 878348
  have htrace : WordTrace (prefixWord ++ tailWord_878348) baseStart_878348 baseEnd_878348 := by
    simpa [prefixWord, tailWord_878348, baseEnd_878348] using wordTrace_append hprefix tailTrace_878348
  have hstable : (prefixWord ++ tailWord_878348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878348).length < 2 ^ (prefixWord ++ tailWord_878348).sum := by decide
  have hdescent : baseEnd_878348 < baseStart_878348 := by decide
  rcases family_descends (prefixWord ++ tailWord_878348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878359 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 2, 2, 2]
def baseStart_878359 : Nat := 118140960795 + 878359 * 2 ^ 59
def prefixEnd_878359 : Nat := 4983230072969 + 3 ^ 40 * 878359 * 2
def baseEnd_878359 : Nat := 451020354202634150073007

theorem tailTrace_878359 : CollatzResearch.WordTrace tailWord_878359 prefixEnd_878359 451020354202634150073007 := by
  unfold tailWord_878359
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036384624862829619262131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21357589749908553079508087 32036384624862829619262131)
  ·
    refine ⟨48054576937294244428893197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32036384624862829619262131 48054576937294244428893197)
    ·
      refine ⟨18020466351485341660834949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48054576937294244428893197 18020466351485341660834949)
      ·
        refine ⟨3378837440903501561406553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18020466351485341660834949 3378837440903501561406553)
        ·
          refine ⟨2534128080677626171054915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378837440903501561406553 2534128080677626171054915)
          ·
            refine ⟨3801192121016439256582373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534128080677626171054915 3801192121016439256582373)
            ·
              refine ⟨712723522690582360609195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3801192121016439256582373 712723522690582360609195)
              ·
                refine ⟨1069085284035873540913793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712723522690582360609195 1069085284035873540913793)
                ·
                  refine ⟨801813963026905155685345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069085284035873540913793 801813963026905155685345)
                  ·
                    refine ⟨601360472270178866764009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801813963026905155685345 601360472270178866764009)
                    ·
                      refine ⟨451020354202634150073007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601360472270178866764009 451020354202634150073007)
                      ·
                        rfl

theorem cell23_878359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_878359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878359 prefixEnd_878359 := by exact prefixLift 878359
  have htrace : WordTrace (prefixWord ++ tailWord_878359) baseStart_878359 baseEnd_878359 := by
    simpa [prefixWord, tailWord_878359, baseEnd_878359] using wordTrace_append hprefix tailTrace_878359
  have hstable : (prefixWord ++ tailWord_878359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878359).length < 2 ^ (prefixWord ++ tailWord_878359).sum := by decide
  have hdescent : baseEnd_878359 < baseStart_878359 := by decide
  rcases family_descends (prefixWord ++ tailWord_878359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878399 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 5]
def baseStart_878399 : Nat := 118140960795 + 878399 * 2 ^ 59
def prefixEnd_878399 : Nat := 4983230072969 + 3 ^ 40 * 878399 * 2
def baseEnd_878399 : Nat := 50115654825423777063647

theorem tailTrace_878399 : CollatzResearch.WordTrace tailWord_878399 prefixEnd_878399 50115654825423777063647 := by
  unfold tailWord_878399
  simp only [CollatzResearch.WordTrace]
  refine ⟨32037843544717916450718251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21358562363145277633812167 32037843544717916450718251)
  ·
    refine ⟨48056765317076874676077377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32037843544717916450718251 48056765317076874676077377)
    ·
      refine ⟨36042573987807656007058033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48056765317076874676077377 36042573987807656007058033)
      ·
        refine ⟨27031930490855742005293525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36042573987807656007058033 27031930490855742005293525)
        ·
          refine ⟨633560870879431453249067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27031930490855742005293525 633560870879431453249067)
          ·
            refine ⟨950341306319147179873601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633560870879431453249067 950341306319147179873601)
            ·
              refine ⟨712755979739360384905201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950341306319147179873601 712755979739360384905201)
              ·
                refine ⟨534566984804520288678901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712755979739360384905201 534566984804520288678901)
                ·
                  refine ⟨50115654825423777063647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534566984804520288678901 50115654825423777063647)
                  ·
                    rfl

theorem cell23_878399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 5].length) (baseStart_878399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878399 prefixEnd_878399 := by exact prefixLift 878399
  have htrace : WordTrace (prefixWord ++ tailWord_878399) baseStart_878399 baseEnd_878399 := by
    simpa [prefixWord, tailWord_878399, baseEnd_878399] using wordTrace_append hprefix tailTrace_878399
  have hstable : (prefixWord ++ tailWord_878399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878399).length < 2 ^ (prefixWord ++ tailWord_878399).sum := by decide
  have hdescent : baseEnd_878399 < baseStart_878399 := by decide
  rcases family_descends (prefixWord ++ tailWord_878399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878435 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3]
def baseStart_878435 : Nat := 118140960795 + 878435 * 2 ^ 59
def prefixEnd_878435 : Nat := 4983230072969 + 3 ^ 40 * 878435 * 2
def baseEnd_878435 : Nat := 451059378732375852722657

theorem tailTrace_878435 : CollatzResearch.WordTrace tailWord_878435 prefixEnd_878435 451059378732375852722657 := by
  unfold tailWord_878435
  simp only [CollatzResearch.WordTrace]
  refine ⟨32039156572587494599028759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21359437715058329732685839 32039156572587494599028759)
  ·
    refine ⟨48058734858881241898543139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32039156572587494599028759 48058734858881241898543139)
    ·
      refine ⟨72088102288321862847814709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48058734858881241898543139 72088102288321862847814709)
      ·
        refine ⟨6758259589530174641982629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72088102288321862847814709 6758259589530174641982629)
        ·
          refine ⟨1267173673036907745371743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6758259589530174641982629 1267173673036907745371743)
          ·
            refine ⟨1900760509555361618057615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267173673036907745371743 1900760509555361618057615)
            ·
              refine ⟨2851140764333042427086423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900760509555361618057615 2851140764333042427086423)
              ·
                refine ⟨4276711146499563640629635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851140764333042427086423 4276711146499563640629635)
                ·
                  refine ⟨6415066719749345460944453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276711146499563640629635 6415066719749345460944453)
                  ·
                    refine ⟨1202825009953002273927085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6415066719749345460944453 1202825009953002273927085)
                    ·
                      refine ⟨451059378732375852722657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1202825009953002273927085 451059378732375852722657)
                      ·
                        rfl

theorem cell23_878435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_878435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878435 prefixEnd_878435 := by exact prefixLift 878435
  have htrace : WordTrace (prefixWord ++ tailWord_878435) baseStart_878435 baseEnd_878435 := by
    simpa [prefixWord, tailWord_878435, baseEnd_878435] using wordTrace_append hprefix tailTrace_878435
  have hstable : (prefixWord ++ tailWord_878435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878435).length < 2 ^ (prefixWord ++ tailWord_878435).sum := by decide
  have hdescent : baseEnd_878435 < baseStart_878435 := by decide
  rcases family_descends (prefixWord ++ tailWord_878435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_878441 : Nat := 118140960795 + 878441 * 2 ^ 59
def prefixEnd_878441 : Nat := 4983230072969 + 3 ^ 40 * 878441 * 2
def baseEnd_878441 : Nat := 451062459616302829247629

theorem tailTrace_878441 : CollatzResearch.WordTrace tailWord_878441 prefixEnd_878441 451062459616302829247629 := by
  unfold tailWord_878441
  simp only [CollatzResearch.WordTrace]
  refine ⟨32039375410565757623747177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21359583607043838415831451 32039375410565757623747177)
  ·
    refine ⟨24029531557924318217810383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32039375410565757623747177 24029531557924318217810383)
    ·
      refine ⟨36044297336886477326715575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24029531557924318217810383 36044297336886477326715575)
      ·
        refine ⟨54066446005329715990073363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36044297336886477326715575 54066446005329715990073363)
        ·
          refine ⟨81099669007994573985110045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54066446005329715990073363 81099669007994573985110045)
          ·
            refine ⟨30412375877997965244416267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81099669007994573985110045 30412375877997965244416267)
            ·
              refine ⟨45618563816996947866624401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30412375877997965244416267 45618563816996947866624401)
              ·
                refine ⟨34213922862747710899968301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45618563816996947866624401 34213922862747710899968301)
                ·
                  refine ⟨12830221073530391587488113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34213922862747710899968301 12830221073530391587488113)
                  ·
                    refine ⟨9622665805147793690616085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12830221073530391587488113 9622665805147793690616085)
                    ·
                      refine ⟨451062459616302829247629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9622665805147793690616085 451062459616302829247629)
                      ·
                        rfl

theorem cell23_878441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_878441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878441 prefixEnd_878441 := by exact prefixLift 878441
  have htrace : WordTrace (prefixWord ++ tailWord_878441) baseStart_878441 baseEnd_878441 := by
    simpa [prefixWord, tailWord_878441, baseEnd_878441] using wordTrace_append hprefix tailTrace_878441
  have hstable : (prefixWord ++ tailWord_878441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878441).length < 2 ^ (prefixWord ++ tailWord_878441).sum := by decide
  have hdescent : baseEnd_878441 < baseStart_878441 := by decide
  rcases family_descends (prefixWord ++ tailWord_878441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878468 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_878468 : Nat := 118140960795 + 878468 * 2 ^ 59
def prefixEnd_878468 : Nat := 4983230072969 + 3 ^ 40 * 878468 * 2
def baseEnd_878468 : Nat := 150358774531324741203335

theorem tailTrace_878468 : CollatzResearch.WordTrace tailWord_878468 prefixEnd_878468 150358774531324741203335 := by
  unfold tailWord_878468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020180090733970617490029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21360240120978627489986705 16020180090733970617490029)
  ·
    refine ⟨6007567534025238981558761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16020180090733970617490029 6007567534025238981558761)
    ·
      refine ⟨4505675650518929236169071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6007567534025238981558761 4505675650518929236169071)
      ·
        refine ⟨6758513475778393854253607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505675650518929236169071 6758513475778393854253607)
        ·
          refine ⟨10137770213667590781380411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758513475778393854253607 10137770213667590781380411)
          ·
            refine ⟨15206655320501386172070617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10137770213667590781380411 15206655320501386172070617)
            ·
              refine ⟨11404991490376039629052963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15206655320501386172070617 11404991490376039629052963)
              ·
                refine ⟨17107487235564059443579445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11404991490376039629052963 17107487235564059443579445)
                ·
                  refine ⟨1603826928334130572835573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17107487235564059443579445 1603826928334130572835573)
                  ·
                    refine ⟨150358774531324741203335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1603826928334130572835573 150358774531324741203335)
                    ·
                      rfl

theorem cell23_878468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_878468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878468 prefixEnd_878468 := by exact prefixLift 878468
  have htrace : WordTrace (prefixWord ++ tailWord_878468) baseStart_878468 baseEnd_878468 := by
    simpa [prefixWord, tailWord_878468, baseEnd_878468] using wordTrace_append hprefix tailTrace_878468
  have hstable : (prefixWord ++ tailWord_878468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878468).length < 2 ^ (prefixWord ++ tailWord_878468).sum := by decide
  have hdescent : baseEnd_878468 < baseStart_878468 := by decide
  rcases family_descends (prefixWord ++ tailWord_878468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878472 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 6]
def baseStart_878472 : Nat := 118140960795 + 878472 * 2 ^ 59
def prefixEnd_878472 : Nat := 4983230072969 + 3 ^ 40 * 878472 * 2
def baseEnd_878472 : Nat := 50119819724065800884443

theorem tailTrace_878472 : CollatzResearch.WordTrace tailWord_878472 prefixEnd_878472 50119819724065800884443 := by
  unfold tailWord_878472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020253036726724959062835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21360337382302299945417113 16020253036726724959062835)
  ·
    refine ⟨24030379555090087438594253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020253036726724959062835 24030379555090087438594253)
    ·
      refine ⟨9011392333158782789472845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24030379555090087438594253 9011392333158782789472845)
      ·
        refine ⟨3379272124934543546052317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9011392333158782789472845 3379272124934543546052317)
        ·
          refine ⟨1267227046850453829769619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3379272124934543546052317 1267227046850453829769619)
          ·
            refine ⟨1900840570275680744654429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267227046850453829769619 1900840570275680744654429)
            ·
              refine ⟨712815213853380279245411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900840570275680744654429 712815213853380279245411)
              ·
                refine ⟨1069222820780070418868117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712815213853380279245411 1069222820780070418868117)
                ·
                  refine ⟨50119819724065800884443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1069222820780070418868117 50119819724065800884443)
                  ·
                    rfl

theorem cell23_878472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 6].length) (baseStart_878472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878472 prefixEnd_878472 := by exact prefixLift 878472
  have htrace : WordTrace (prefixWord ++ tailWord_878472) baseStart_878472 baseEnd_878472 := by
    simpa [prefixWord, tailWord_878472, baseEnd_878472] using wordTrace_append hprefix tailTrace_878472
  have hstable : (prefixWord ++ tailWord_878472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878472).length < 2 ^ (prefixWord ++ tailWord_878472).sum := by decide
  have hdescent : baseEnd_878472 < baseStart_878472 := by decide
  rcases family_descends (prefixWord ++ tailWord_878472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878485 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_878485 : Nat := 118140960795 + 878485 * 2 ^ 59
def prefixEnd_878485 : Nat := 4983230072969 + 3 ^ 40 * 878485 * 2
def baseEnd_878485 : Nat := 150361684255033552365809

theorem tailTrace_878485 : CollatzResearch.WordTrace tailWord_878485 prefixEnd_878485 150361684255033552365809 := by
  unfold tailWord_878485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32040980222406353138348909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21360653481604235425565939 32040980222406353138348909)
  ·
    refine ⟨12015367583402382426880841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32040980222406353138348909 12015367583402382426880841)
    ·
      refine ⟨9011525687551786820160631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12015367583402382426880841 9011525687551786820160631)
      ·
        refine ⟨13517288531327680230240947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011525687551786820160631 13517288531327680230240947)
        ·
          refine ⟨20275932796991520345361421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13517288531327680230240947 20275932796991520345361421)
          ·
            refine ⟨7603474798871820129510533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20275932796991520345361421 7603474798871820129510533)
            ·
              refine ⟨1425651524788466274283225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7603474798871820129510533 1425651524788466274283225)
              ·
                refine ⟨1069238643591349705712419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425651524788466274283225 1069238643591349705712419)
                ·
                  refine ⟨1603857965387024558568629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069238643591349705712419 1603857965387024558568629)
                  ·
                    refine ⟨150361684255033552365809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1603857965387024558568629 150361684255033552365809)
                    ·
                      rfl

theorem cell23_878485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_878485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878485 prefixEnd_878485 := by exact prefixLift 878485
  have htrace : WordTrace (prefixWord ++ tailWord_878485) baseStart_878485 baseEnd_878485 := by
    simpa [prefixWord, tailWord_878485, baseEnd_878485] using wordTrace_append hprefix tailTrace_878485
  have hstable : (prefixWord ++ tailWord_878485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878485).length < 2 ^ (prefixWord ++ tailWord_878485).sum := by decide
  have hdescent : baseEnd_878485 < baseStart_878485 := by decide
  rcases family_descends (prefixWord ++ tailWord_878485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878492 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_878492 : Nat := 118140960795 + 878492 * 2 ^ 59
def prefixEnd_878492 : Nat := 4983230072969 + 3 ^ 40 * 878492 * 2
def baseEnd_878492 : Nat := 451088647129682129709895

theorem tailTrace_878492 : CollatzResearch.WordTrace tailWord_878492 prefixEnd_878492 451088647129682129709895 := by
  unfold tailWord_878492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020617766690496666926865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21360823688920662222569153 16020617766690496666926865)
  ·
    refine ⟨12015463325017872500195149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16020617766690496666926865 12015463325017872500195149)
    ·
      refine ⟨4505798746881702187573181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12015463325017872500195149 4505798746881702187573181)
      ·
        refine ⟨1689674530080638320339943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4505798746881702187573181 1689674530080638320339943)
        ·
          refine ⟨2534511795120957480509915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689674530080638320339943 2534511795120957480509915)
          ·
            refine ⟨3801767692681436220764873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534511795120957480509915 3801767692681436220764873)
            ·
              refine ⟨2851325769511077165573655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801767692681436220764873 2851325769511077165573655)
              ·
                refine ⟨4276988654266615748360483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851325769511077165573655 4276988654266615748360483)
                ·
                  refine ⟨6415482981399923622540725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276988654266615748360483 6415482981399923622540725)
                  ·
                    refine ⟨601451529506242839613193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6415482981399923622540725 601451529506242839613193)
                    ·
                      refine ⟨451088647129682129709895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601451529506242839613193 451088647129682129709895)
                      ·
                        rfl

theorem cell23_878492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_878492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878492 prefixEnd_878492 := by exact prefixLift 878492
  have htrace : WordTrace (prefixWord ++ tailWord_878492) baseStart_878492 baseEnd_878492 := by
    simpa [prefixWord, tailWord_878492, baseEnd_878492] using wordTrace_append hprefix tailTrace_878492
  have hstable : (prefixWord ++ tailWord_878492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878492).length < 2 ^ (prefixWord ++ tailWord_878492).sum := by decide
  have hdescent : baseEnd_878492 < baseStart_878492 := by decide
  rcases family_descends (prefixWord ++ tailWord_878492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878510 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_878510 : Nat := 118140960795 + 878510 * 2 ^ 59
def prefixEnd_878510 : Nat := 4983230072969 + 3 ^ 40 * 878510 * 2
def baseEnd_878510 : Nat := 150365963260487686428271

theorem tailTrace_878510 : CollatzResearch.WordTrace tailWord_878510 prefixEnd_878510 150365963260487686428271 := by
  unfold tailWord_878510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005236505914472801001123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21361261364877188272005989 4005236505914472801001123)
  ·
    refine ⟨6007854758871709201501685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4005236505914472801001123 6007854758871709201501685)
    ·
      refine ⟨563236383644222737640783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6007854758871709201501685 563236383644222737640783)
      ·
        refine ⟨844854575466334106461175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563236383644222737640783 844854575466334106461175)
        ·
          refine ⟨1267281863199501159691763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844854575466334106461175 1267281863199501159691763)
          ·
            refine ⟨1900922794799251739537645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267281863199501159691763 1900922794799251739537645)
            ·
              refine ⟨712846048049719402326617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900922794799251739537645 712846048049719402326617)
              ·
                refine ⟨534634536037289551744963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712846048049719402326617 534634536037289551744963)
                ·
                  refine ⟨801951804055934327617445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534634536037289551744963 801951804055934327617445)
                  ·
                    refine ⟨150365963260487686428271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 801951804055934327617445 150365963260487686428271)
                    ·
                      rfl

theorem cell23_878510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_878510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878510 prefixEnd_878510 := by exact prefixLift 878510
  have htrace : WordTrace (prefixWord ++ tailWord_878510) baseStart_878510 baseEnd_878510 := by
    simpa [prefixWord, tailWord_878510, baseEnd_878510] using wordTrace_append hprefix tailTrace_878510
  have hstable : (prefixWord ++ tailWord_878510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878510).length < 2 ^ (prefixWord ++ tailWord_878510).sum := by decide
  have hdescent : baseEnd_878510 < baseStart_878510 := by decide
  rcases family_descends (prefixWord ++ tailWord_878510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878515 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 2, 4]
def baseStart_878515 : Nat := 118140960795 + 878515 * 2 ^ 59
def prefixEnd_878515 : Nat := 4983230072969 + 3 ^ 40 * 878515 * 2
def baseEnd_878515 : Nat := 150366819061578513240763

theorem tailTrace_878515 : CollatzResearch.WordTrace tailWord_878515 prefixEnd_878515 150366819061578513240763 := by
  unfold tailWord_878515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32042074412297668261940999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21361382941531778841293999 32042074412297668261940999)
  ·
    refine ⟨48063111618446502392911499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32042074412297668261940999 48063111618446502392911499)
    ·
      refine ⟨72094667427669753589367249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48063111618446502392911499 72094667427669753589367249)
      ·
        refine ⟨54071000570752315192025437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72094667427669753589367249 54071000570752315192025437)
        ·
          refine ⟨20276625214032118197009539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54071000570752315192025437 20276625214032118197009539)
          ·
            refine ⟨30414937821048177295514309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276625214032118197009539 30414937821048177295514309)
            ·
              refine ⟨5702800841446533242908933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30414937821048177295514309 5702800841446533242908933)
              ·
                refine ⟨1069275157771224983045425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5702800841446533242908933 1069275157771224983045425)
                ·
                  refine ⟨801956368328418737284069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069275157771224983045425 801956368328418737284069)
                  ·
                    refine ⟨150366819061578513240763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 801956368328418737284069 150366819061578513240763)
                    ·
                      rfl

theorem cell23_878515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 4].length) (baseStart_878515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878515 prefixEnd_878515 := by exact prefixLift 878515
  have htrace : WordTrace (prefixWord ++ tailWord_878515) baseStart_878515 baseEnd_878515 := by
    simpa [prefixWord, tailWord_878515, baseEnd_878515] using wordTrace_append hprefix tailTrace_878515
  have hstable : (prefixWord ++ tailWord_878515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878515).length < 2 ^ (prefixWord ++ tailWord_878515).sum := by decide
  have hdescent : baseEnd_878515 < baseStart_878515 := by decide
  rcases family_descends (prefixWord ++ tailWord_878515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878522 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_878522 : Nat := 118140960795 + 878522 * 2 ^ 59
def prefixEnd_878522 : Nat := 4983230072969 + 3 ^ 40 * 878522 * 2
def baseEnd_878522 : Nat := 451104051549317012334757

theorem tailTrace_878522 : CollatzResearch.WordTrace tailWord_878522 prefixEnd_878522 451104051549317012334757 := by
  unfold tailWord_878522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010582430818077114361455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21361553148848205638297213 8010582430818077114361455)
  ·
    refine ⟨12015873646227115671542183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8010582430818077114361455 12015873646227115671542183)
    ·
      refine ⟨18023810469340673507313275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12015873646227115671542183 18023810469340673507313275)
      ·
        refine ⟨27035715704011010260969913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18023810469340673507313275 27035715704011010260969913)
        ·
          refine ⟨20276786778008257695727435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27035715704011010260969913 20276786778008257695727435)
          ·
            refine ⟨30415180167012386543591153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20276786778008257695727435 30415180167012386543591153)
            ·
              refine ⟨22811385125259289907693365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30415180167012386543591153 22811385125259289907693365)
              ·
                refine ⟨2138567355493058428846253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22811385125259289907693365 2138567355493058428846253)
                ·
                  refine ⟨801962758309896910817345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2138567355493058428846253 801962758309896910817345)
                  ·
                    refine ⟨601472068732422683113009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 801962758309896910817345 601472068732422683113009)
                    ·
                      refine ⟨451104051549317012334757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601472068732422683113009 451104051549317012334757)
                      ·
                        rfl

theorem cell23_878522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_878522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878522 prefixEnd_878522 := by exact prefixLift 878522
  have htrace : WordTrace (prefixWord ++ tailWord_878522) baseStart_878522 baseEnd_878522 := by
    simpa [prefixWord, tailWord_878522, baseEnd_878522] using wordTrace_append hprefix tailTrace_878522
  have hstable : (prefixWord ++ tailWord_878522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878522).length < 2 ^ (prefixWord ++ tailWord_878522).sum := by decide
  have hdescent : baseEnd_878522 < baseStart_878522 := by decide
  rcases family_descends (prefixWord ++ tailWord_878522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878525 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_878525 : Nat := 118140960795 + 878525 * 2 ^ 59
def prefixEnd_878525 : Nat := 4983230072969 + 3 ^ 40 * 878525 * 2
def baseEnd_878525 : Nat := 451105591991280500597243

theorem tailTrace_878525 : CollatzResearch.WordTrace tailWord_878525 prefixEnd_878525 451105591991280500597243 := by
  unfold tailWord_878525
  simp only [CollatzResearch.WordTrace]
  refine ⟨32042439142261439969805029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21361626094840959979870019 32042439142261439969805029)
  ·
    refine ⟨6007957339174019994338443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32042439142261439969805029 6007957339174019994338443)
    ·
      refine ⟨9011936008761029991507665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007957339174019994338443 9011936008761029991507665)
      ·
        refine ⟨6758952006570772493630749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011936008761029991507665 6758952006570772493630749)
        ·
          refine ⟨2534607002464039685111531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6758952006570772493630749 2534607002464039685111531)
          ·
            refine ⟨3801910503696059527667297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534607002464039685111531 3801910503696059527667297)
            ·
              refine ⟨2851432877772044645750473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801910503696059527667297 2851432877772044645750473)
              ·
                refine ⟨2138574658329033484312855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851432877772044645750473 2138574658329033484312855)
                ·
                  refine ⟨3207861987493550226469283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138574658329033484312855 3207861987493550226469283)
                  ·
                    refine ⟨4811792981240325339703925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3207861987493550226469283 4811792981240325339703925)
                    ·
                      refine ⟨451105591991280500597243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4811792981240325339703925 451105591991280500597243)
                      ·
                        rfl

theorem cell23_878525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_878525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878525 prefixEnd_878525 := by exact prefixLift 878525
  have htrace : WordTrace (prefixWord ++ tailWord_878525) baseStart_878525 baseEnd_878525 := by
    simpa [prefixWord, tailWord_878525, baseEnd_878525] using wordTrace_append hprefix tailTrace_878525
  have hstable : (prefixWord ++ tailWord_878525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878525).length < 2 ^ (prefixWord ++ tailWord_878525).sum := by decide
  have hdescent : baseEnd_878525 < baseStart_878525 := by decide
  rcases family_descends (prefixWord ++ tailWord_878525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878528 : List Nat := [2, 1, 1, 2, 3, 2, 4, 8]
def baseStart_878528 : Nat := 118140960795 + 878528 * 2 ^ 59
def prefixEnd_878528 : Nat := 4983230072969 + 3 ^ 40 * 878528 * 2
def baseEnd_878528 : Nat := 16707671571601629217027

theorem tailTrace_878528 : CollatzResearch.WordTrace tailWord_878528 prefixEnd_878528 16707671571601629217027 := by
  unfold tailWord_878528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021274280625285741082119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21361699040833714321442825 16021274280625285741082119)
  ·
    refine ⟨24031911420937928611623179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16021274280625285741082119 24031911420937928611623179)
    ·
      refine ⟨36047867131406892917434769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24031911420937928611623179 36047867131406892917434769)
      ·
        refine ⟨27035900348555169688076077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36047867131406892917434769 27035900348555169688076077)
        ·
          refine ⟨10138462630708188633028529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27035900348555169688076077 10138462630708188633028529)
          ·
            refine ⟨7603846973031141474771397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10138462630708188633028529 7603846973031141474771397)
            ·
              refine ⟨1425721307443339026519637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7603846973031141474771397 1425721307443339026519637)
              ·
                refine ⟨16707671571601629217027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1425721307443339026519637 16707671571601629217027)
                ·
                  rfl

theorem cell23_878528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 8].length) (baseStart_878528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878528 prefixEnd_878528 := by exact prefixLift 878528
  have htrace : WordTrace (prefixWord ++ tailWord_878528) baseStart_878528 baseEnd_878528 := by
    simpa [prefixWord, tailWord_878528, baseEnd_878528] using wordTrace_append hprefix tailTrace_878528
  have hstable : (prefixWord ++ tailWord_878528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878528).length < 2 ^ (prefixWord ++ tailWord_878528).sum := by decide
  have hdescent : baseEnd_878528 < baseStart_878528 := by decide
  rcases family_descends (prefixWord ++ tailWord_878528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878559 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 1, 2, 3]
def baseStart_878559 : Nat := 118140960795 + 878559 * 2 ^ 59
def prefixEnd_878559 : Nat := 4983230072969 + 3 ^ 40 * 878559 * 2
def baseEnd_878559 : Nat := 451123050333533367572087

theorem tailTrace_878559 : CollatzResearch.WordTrace tailWord_878559 prefixEnd_878559 451123050333533367572087 := by
  unfold tailWord_878559
  simp only [CollatzResearch.WordTrace]
  refine ⟨32043679224138263776542731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21362452816092175851028487 32043679224138263776542731)
  ·
    refine ⟨48065518836207395664814097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32043679224138263776542731 48065518836207395664814097)
    ·
      refine ⟨36049139127155546748610573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48065518836207395664814097 36049139127155546748610573)
      ·
        refine ⟨13518427172683330030728965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36049139127155546748610573 13518427172683330030728965)
        ·
          refine ⟨2534705094878124380761681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13518427172683330030728965 2534705094878124380761681)
          ·
            refine ⟨1901028821158593285571261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534705094878124380761681 1901028821158593285571261)
            ·
              refine ⟨712885807934472482089223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901028821158593285571261 712885807934472482089223)
              ·
                refine ⟨1069328711901708723133835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712885807934472482089223 1069328711901708723133835)
                ·
                  refine ⟨1603993067852563084700753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069328711901708723133835 1603993067852563084700753)
                  ·
                    refine ⟨1202994800889422313525565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1603993067852563084700753 1202994800889422313525565)
                    ·
                      refine ⟨451123050333533367572087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1202994800889422313525565 451123050333533367572087)
                      ·
                        rfl

theorem cell23_878559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_878559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878559 prefixEnd_878559 := by exact prefixLift 878559
  have htrace : WordTrace (prefixWord ++ tailWord_878559) baseStart_878559 baseEnd_878559 := by
    simpa [prefixWord, tailWord_878559, baseEnd_878559] using wordTrace_append hprefix tailTrace_878559
  have hstable : (prefixWord ++ tailWord_878559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878559).length < 2 ^ (prefixWord ++ tailWord_878559).sum := by decide
  have hdescent : baseEnd_878559 < baseStart_878559 := by decide
  rcases family_descends (prefixWord ++ tailWord_878559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878562 : List Nat := [3, 3, 3, 1, 3, 10]
def baseStart_878562 : Nat := 118140960795 + 878562 * 2 ^ 59
def prefixEnd_878562 : Nat := 4983230072969 + 3 ^ 40 * 878562 * 2
def baseEnd_878562 : Nat := 1856479797430028213311

theorem tailTrace_878562 : CollatzResearch.WordTrace tailWord_878562 prefixEnd_878562 1856479797430028213311 := by
  unfold tailWord_878562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010947160781848822225485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21362525762084930192601293 8010947160781848822225485)
  ·
    refine ⟨3004105185293193308334557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8010947160781848822225485 3004105185293193308334557)
    ·
      refine ⟨1126539444484947490625459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3004105185293193308334557 1126539444484947490625459)
      ·
        refine ⟨1689809166727421235938189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126539444484947490625459 1689809166727421235938189)
        ·
          refine ⟨633678437522782963476821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1689809166727421235938189 633678437522782963476821)
          ·
            refine ⟨1856479797430028213311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 633678437522782963476821 1856479797430028213311)
            ·
              rfl

theorem cell23_878562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 10].length) (baseStart_878562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878562 prefixEnd_878562 := by exact prefixLift 878562
  have htrace : WordTrace (prefixWord ++ tailWord_878562) baseStart_878562 baseEnd_878562 := by
    simpa [prefixWord, tailWord_878562, baseEnd_878562] using wordTrace_append hprefix tailTrace_878562
  have hstable : (prefixWord ++ tailWord_878562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878562).length < 2 ^ (prefixWord ++ tailWord_878562).sum := by decide
  have hdescent : baseEnd_878562 < baseStart_878562 := by decide
  rcases family_descends (prefixWord ++ tailWord_878562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878629 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_878629 : Nat := 118140960795 + 878629 * 2 ^ 59
def prefixEnd_878629 : Nat := 4983230072969 + 3 ^ 40 * 878629 * 2
def baseEnd_878629 : Nat := 451158993979348093696765

theorem tailTrace_878629 : CollatzResearch.WordTrace tailWord_878629 prefixEnd_878629 451158993979348093696765 := by
  unfold tailWord_878629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32046232333884665731590941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21364154889256443821060627 32046232333884665731590941)
  ·
    refine ⟨12017337125206749649346603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32046232333884665731590941 12017337125206749649346603)
    ·
      refine ⟨18026005687810124474019905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12017337125206749649346603 18026005687810124474019905)
      ·
        refine ⟨13519504265857593355514929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18026005687810124474019905 13519504265857593355514929)
        ·
          refine ⟨10139628199393195016636197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13519504265857593355514929 10139628199393195016636197)
          ·
            refine ⟨1901180287386224065619287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10139628199393195016636197 1901180287386224065619287)
            ·
              refine ⟨2851770431079336098428931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901180287386224065619287 2851770431079336098428931)
              ·
                refine ⟨4277655646619004147643397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851770431079336098428931 4277655646619004147643397)
                ·
                  refine ⟨802060433741063277683137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4277655646619004147643397 802060433741063277683137)
                  ·
                    refine ⟨601545325305797458262353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802060433741063277683137 601545325305797458262353)
                    ·
                      refine ⟨451158993979348093696765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601545325305797458262353 451158993979348093696765)
                      ·
                        rfl

theorem cell23_878629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_878629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878629 prefixEnd_878629 := by exact prefixLift 878629
  have htrace : WordTrace (prefixWord ++ tailWord_878629) baseStart_878629 baseEnd_878629 := by
    simpa [prefixWord, tailWord_878629, baseEnd_878629] using wordTrace_append hprefix tailTrace_878629
  have hstable : (prefixWord ++ tailWord_878629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878629).length < 2 ^ (prefixWord ++ tailWord_878629).sum := by decide
  have hdescent : baseEnd_878629 < baseStart_878629 := by decide
  rcases family_descends (prefixWord ++ tailWord_878629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878665 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_878665 : Nat := 118140960795 + 878665 * 2 ^ 59
def prefixEnd_878665 : Nat := 4983230072969 + 3 ^ 40 * 878665 * 2
def baseEnd_878665 : Nat := 150392493094303317615533

theorem tailTrace_878665 : CollatzResearch.WordTrace tailWord_878665 prefixEnd_878665 150392493094303317615533 := by
  unfold tailWord_878665
  simp only [CollatzResearch.WordTrace]
  refine ⟨32047545361754243879901449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21365030241169495919934299 32047545361754243879901449)
  ·
    refine ⟨24035659021315682909926087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32047545361754243879901449 24035659021315682909926087)
    ·
      refine ⟨36053488531973524364889131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24035659021315682909926087 36053488531973524364889131)
      ·
        refine ⟨54080232797960286547333697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36053488531973524364889131 54080232797960286547333697)
        ·
          refine ⟨40560174598470214910500273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54080232797960286547333697 40560174598470214910500273)
          ·
            refine ⟨30420130948852661182875205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40560174598470214910500273 30420130948852661182875205)
            ·
              refine ⟨5703774552909873971789101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30420130948852661182875205 5703774552909873971789101)
              ·
                refine ⟨2138915457341202739420913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5703774552909873971789101 2138915457341202739420913)
                ·
                  refine ⟨1604186593005902054565685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2138915457341202739420913 1604186593005902054565685)
                  ·
                    refine ⟨150392493094303317615533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1604186593005902054565685 150392493094303317615533)
                    ·
                      rfl

theorem cell23_878665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_878665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878665 prefixEnd_878665 := by exact prefixLift 878665
  have htrace : WordTrace (prefixWord ++ tailWord_878665) baseStart_878665 baseEnd_878665 := by
    simpa [prefixWord, tailWord_878665, baseEnd_878665] using wordTrace_append hprefix tailTrace_878665
  have hstable : (prefixWord ++ tailWord_878665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878665).length < 2 ^ (prefixWord ++ tailWord_878665).sum := by decide
  have hdescent : baseEnd_878665 < baseStart_878665 := by decide
  rcases family_descends (prefixWord ++ tailWord_878665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878702 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_878702 : Nat := 118140960795 + 878702 * 2 ^ 59
def prefixEnd_878702 : Nat := 4983230072969 + 3 ^ 40 * 878702 * 2
def baseEnd_878702 : Nat := 451196478067126308083929

theorem tailTrace_878702 : CollatzResearch.WordTrace tailWord_878702 prefixEnd_878702 451196478067126308083929 := by
  unfold tailWord_878702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006111857827524899874795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21365929908413466132665573 4006111857827524899874795)
  ·
    refine ⟨6009167786741287349812193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4006111857827524899874795 6009167786741287349812193)
    ·
      refine ⟨4506875840055965512359145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6009167786741287349812193 4506875840055965512359145)
      ·
        refine ⟨3380156880041974134269359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4506875840055965512359145 3380156880041974134269359)
        ·
          refine ⟨5070235320062961201404039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380156880041974134269359 5070235320062961201404039)
          ·
            refine ⟨7605352980094441802106059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5070235320062961201404039 7605352980094441802106059)
            ·
              refine ⟨11408029470141662703159089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605352980094441802106059 11408029470141662703159089)
              ·
                refine ⟨8556022102606247027369317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11408029470141662703159089 8556022102606247027369317)
                ·
                  refine ⟨1604254144238671317631747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8556022102606247027369317 1604254144238671317631747)
                  ·
                    refine ⟨2406381216358006976447621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1604254144238671317631747 2406381216358006976447621)
                    ·
                      refine ⟨451196478067126308083929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2406381216358006976447621 451196478067126308083929)
                      ·
                        rfl

theorem cell23_878702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_878702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878702 prefixEnd_878702 := by exact prefixLift 878702
  have htrace : WordTrace (prefixWord ++ tailWord_878702) baseStart_878702 baseEnd_878702 := by
    simpa [prefixWord, tailWord_878702, baseEnd_878702] using wordTrace_append hprefix tailTrace_878702
  have hstable : (prefixWord ++ tailWord_878702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878702).length < 2 ^ (prefixWord ++ tailWord_878702).sum := by decide
  have hdescent : baseEnd_878702 < baseStart_878702 := by decide
  rcases family_descends (prefixWord ++ tailWord_878702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878729 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 1, 4]
def baseStart_878729 : Nat := 118140960795 + 878729 * 2 ^ 59
def prefixEnd_878729 : Nat := 4983230072969 + 3 ^ 40 * 878729 * 2
def baseEnd_878729 : Nat := 150403447348265900815435

theorem tailTrace_878729 : CollatzResearch.WordTrace tailWord_878729 prefixEnd_878729 150403447348265900815435 := by
  unfold tailWord_878729
  simp only [CollatzResearch.WordTrace]
  refine ⟨32049879633522382810231241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21366586422348255206820827 32049879633522382810231241)
  ·
    refine ⟨24037409725141787107673431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32049879633522382810231241 24037409725141787107673431)
    ·
      refine ⟨36056114587712680661510147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24037409725141787107673431 36056114587712680661510147)
      ·
        refine ⟨54084171881569020992265221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36056114587712680661510147 54084171881569020992265221)
        ·
          refine ⟨10140782227794191436049729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54084171881569020992265221 10140782227794191436049729)
          ·
            refine ⟨7605586670845643577037297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10140782227794191436049729 7605586670845643577037297)
            ·
              refine ⟨5704190003134232682777973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605586670845643577037297 5704190003134232682777973)
              ·
                refine ⟨534767812793834314010435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5704190003134232682777973 534767812793834314010435)
                ·
                  refine ⟨802151719190751471015653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534767812793834314010435 802151719190751471015653)
                  ·
                    refine ⟨150403447348265900815435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802151719190751471015653 150403447348265900815435)
                    ·
                      rfl

theorem cell23_878729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 4].length) (baseStart_878729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878729 prefixEnd_878729 := by exact prefixLift 878729
  have htrace : WordTrace (prefixWord ++ tailWord_878729) baseStart_878729 baseEnd_878729 := by
    simpa [prefixWord, tailWord_878729, baseEnd_878729] using wordTrace_append hprefix tailTrace_878729
  have hstable : (prefixWord ++ tailWord_878729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878729).length < 2 ^ (prefixWord ++ tailWord_878729).sum := by decide
  have hdescent : baseEnd_878729 < baseStart_878729 := by decide
  rcases family_descends (prefixWord ++ tailWord_878729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878773 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_878773 : Nat := 118140960795 + 878773 * 2 ^ 59
def prefixEnd_878773 : Nat := 4983230072969 + 3 ^ 40 * 878773 * 2
def baseEnd_878773 : Nat := 451232935193595530296103

theorem tailTrace_878773 : CollatzResearch.WordTrace tailWord_878773 prefixEnd_878773 451232935193595530296103 := by
  unfold tailWord_878773
  simp only [CollatzResearch.WordTrace]
  refine ⟨32051484445362978324832973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21367656296908652216555315 32051484445362978324832973)
  ·
    refine ⟨12019306667011116871812365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32051484445362978324832973 12019306667011116871812365)
    ·
      refine ⟨4507240000129168826929637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12019306667011116871812365 4507240000129168826929637)
      ·
        refine ⟨845107500024219155049307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4507240000129168826929637 845107500024219155049307)
        ·
          refine ⟨1267661250036328732573961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845107500024219155049307 1267661250036328732573961)
          ·
            refine ⟨950745937527246549430471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267661250036328732573961 950745937527246549430471)
            ·
              refine ⟨1426118906290869824145707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950745937527246549430471 1426118906290869824145707)
              ·
                refine ⟨2139178359436304736218561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426118906290869824145707 2139178359436304736218561)
                ·
                  refine ⟨1604383769577228552163921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139178359436304736218561 1604383769577228552163921)
                  ·
                    refine ⟨1203287827182921414122941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1604383769577228552163921 1203287827182921414122941)
                    ·
                      refine ⟨451232935193595530296103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203287827182921414122941 451232935193595530296103)
                      ·
                        rfl

theorem cell23_878773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_878773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878773 prefixEnd_878773 := by exact prefixLift 878773
  have htrace : WordTrace (prefixWord ++ tailWord_878773) baseStart_878773 baseEnd_878773 := by
    simpa [prefixWord, tailWord_878773, baseEnd_878773] using wordTrace_append hprefix tailTrace_878773
  have hstable : (prefixWord ++ tailWord_878773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878773).length < 2 ^ (prefixWord ++ tailWord_878773).sum := by decide
  have hdescent : baseEnd_878773 < baseStart_878773 := by decide
  rcases family_descends (prefixWord ++ tailWord_878773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878789 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_878789 : Nat := 118140960795 + 878789 * 2 ^ 59
def prefixEnd_878789 : Nat := 4983230072969 + 3 ^ 40 * 878789 * 2
def baseEnd_878789 : Nat := 150413716961355822565343

theorem tailTrace_878789 : CollatzResearch.WordTrace tailWord_878789 prefixEnd_878789 150413716961355822565343 := by
  unfold tailWord_878789
  simp only [CollatzResearch.WordTrace]
  refine ⟨32052068013305013057415421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21368045342203342038276947 32052068013305013057415421)
  ·
    refine ⟨12019525504989379896530783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32052068013305013057415421 12019525504989379896530783)
    ·
      refine ⟨18029288257484069844796175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12019525504989379896530783 18029288257484069844796175)
      ·
        refine ⟨27043932386226104767194263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18029288257484069844796175 27043932386226104767194263)
        ·
          refine ⟨40565898579339157150791395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27043932386226104767194263 40565898579339157150791395)
          ·
            refine ⟨60848847869008735726187093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40565898579339157150791395 60848847869008735726187093)
            ·
              refine ⟨713072435964946121791255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 60848847869008735726187093 713072435964946121791255)
              ·
                refine ⟨1069608653947419182686883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713072435964946121791255 1069608653947419182686883)
                ·
                  refine ⟨1604412980921128774030325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069608653947419182686883 1604412980921128774030325)
                  ·
                    refine ⟨150413716961355822565343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1604412980921128774030325 150413716961355822565343)
                    ·
                      rfl

theorem cell23_878789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_878789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878789 prefixEnd_878789 := by exact prefixLift 878789
  have htrace : WordTrace (prefixWord ++ tailWord_878789) baseStart_878789 baseEnd_878789 := by
    simpa [prefixWord, tailWord_878789, baseEnd_878789] using wordTrace_append hprefix tailTrace_878789
  have hstable : (prefixWord ++ tailWord_878789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878789).length < 2 ^ (prefixWord ++ tailWord_878789).sum := by decide
  have hdescent : baseEnd_878789 < baseStart_878789 := by decide
  rcases family_descends (prefixWord ++ tailWord_878789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878815 : List Nat := [1, 1, 2, 3, 2, 1, 1, 12]
def baseStart_878815 : Nat := 118140960795 + 878815 * 2 ^ 59
def prefixEnd_878815 : Nat := 4983230072969 + 3 ^ 40 * 878815 * 2
def baseEnd_878815 : Nat := 16713129680780902443367

theorem tailTrace_878815 : CollatzResearch.WordTrace tailWord_878815 prefixEnd_878815 16713129680780902443367 := by
  unfold tailWord_878815
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053016311210819497861899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21368677540807212998574599 32053016311210819497861899)
  ·
    refine ⟨48079524466816229246792849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32053016311210819497861899 48079524466816229246792849)
    ·
      refine ⟨36059643350112171935094637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48079524466816229246792849 36059643350112171935094637)
      ·
        refine ⟨13522366256292064475660489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36059643350112171935094637 13522366256292064475660489)
        ·
          refine ⟨10141774692219048356745367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13522366256292064475660489 10141774692219048356745367)
          ·
            refine ⟨15212662038328572535118051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141774692219048356745367 15212662038328572535118051)
            ·
              refine ⟨22818993057492858802677077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15212662038328572535118051 22818993057492858802677077)
              ·
                refine ⟨16713129680780902443367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 22818993057492858802677077 16713129680780902443367)
                ·
                  rfl

theorem cell23_878815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 12].length) (baseStart_878815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878815 prefixEnd_878815 := by exact prefixLift 878815
  have htrace : WordTrace (prefixWord ++ tailWord_878815) baseStart_878815 baseEnd_878815 := by
    simpa [prefixWord, tailWord_878815, baseEnd_878815] using wordTrace_append hprefix tailTrace_878815
  have hstable : (prefixWord ++ tailWord_878815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878815).length < 2 ^ (prefixWord ++ tailWord_878815).sum := by decide
  have hdescent : baseEnd_878815 < baseStart_878815 := by decide
  rcases family_descends (prefixWord ++ tailWord_878815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878825 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_878825 : Nat := 118140960795 + 878825 * 2 ^ 59
def prefixEnd_878825 : Nat := 4983230072969 + 3 ^ 40 * 878825 * 2
def baseEnd_878825 : Nat := 451259636187629326845863

theorem tailTrace_878825 : CollatzResearch.WordTrace tailWord_878825 prefixEnd_878825 451259636187629326845863 := by
  unfold tailWord_878825
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053381041174591205725929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21368920694116394137150619 32053381041174591205725929)
  ·
    refine ⟨24040035780880943404294447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32053381041174591205725929 24040035780880943404294447)
    ·
      refine ⟨36060053671321415106441671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24040035780880943404294447 36060053671321415106441671)
      ·
        refine ⟨54090080506982122659662507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36060053671321415106441671 54090080506982122659662507)
        ·
          refine ⟨81135120760473183989493761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54090080506982122659662507 81135120760473183989493761)
          ·
            refine ⟨60851340570354887992120321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81135120760473183989493761 60851340570354887992120321)
            ·
              refine ⟨45638505427766165994090241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60851340570354887992120321 45638505427766165994090241)
              ·
                refine ⟨34228879070824624495567681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45638505427766165994090241 34228879070824624495567681)
                ·
                  refine ⟨25671659303118468371675761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34228879070824624495567681 25671659303118468371675761)
                  ·
                    refine ⟨19253744477338851278756821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25671659303118468371675761 19253744477338851278756821)
                    ·
                      refine ⟨451259636187629326845863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19253744477338851278756821 451259636187629326845863)
                      ·
                        rfl

theorem cell23_878825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_878825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878825 prefixEnd_878825 := by exact prefixLift 878825
  have htrace : WordTrace (prefixWord ++ tailWord_878825) baseStart_878825 baseEnd_878825 := by
    simpa [prefixWord, tailWord_878825, baseEnd_878825] using wordTrace_append hprefix tailTrace_878825
  have hstable : (prefixWord ++ tailWord_878825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878825).length < 2 ^ (prefixWord ++ tailWord_878825).sum := by decide
  have hdescent : baseEnd_878825 < baseStart_878825 := by decide
  rcases family_descends (prefixWord ++ tailWord_878825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878826 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_878826 : Nat := 118140960795 + 878826 * 2 ^ 59
def prefixEnd_878826 : Nat := 4983230072969 + 3 ^ 40 * 878826 * 2
def baseEnd_878826 : Nat := 451260149668283822933359

theorem tailTrace_878826 : CollatzResearch.WordTrace tailWord_878826 prefixEnd_878826 451260149668283822933359 := by
  unfold tailWord_878826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013354378542742094128083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21368945009447312251008221 8013354378542742094128083)
  ·
    refine ⟨12020031567814113141192125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8013354378542742094128083 12020031567814113141192125)
    ·
      refine ⟨4507511837930292427947047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12020031567814113141192125 4507511837930292427947047)
      ·
        refine ⟨6761267756895438641920571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507511837930292427947047 6761267756895438641920571)
        ·
          refine ⟨10141901635343157962880857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761267756895438641920571 10141901635343157962880857)
          ·
            refine ⟨7606426226507368472160643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10141901635343157962880857 7606426226507368472160643)
            ·
              refine ⟨11409639339761052708240965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606426226507368472160643 11409639339761052708240965)
              ·
                refine ⟨2139307376205197382795181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11409639339761052708240965 2139307376205197382795181)
                ·
                  refine ⟨802240266076949018548193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2139307376205197382795181 802240266076949018548193)
                  ·
                    refine ⟨601680199557711763911145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802240266076949018548193 601680199557711763911145)
                    ·
                      refine ⟨451260149668283822933359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601680199557711763911145 451260149668283822933359)
                      ·
                        rfl

theorem cell23_878826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_878826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878826 prefixEnd_878826 := by exact prefixLift 878826
  have htrace : WordTrace (prefixWord ++ tailWord_878826) baseStart_878826 baseEnd_878826 := by
    simpa [prefixWord, tailWord_878826, baseEnd_878826] using wordTrace_append hprefix tailTrace_878826
  have hstable : (prefixWord ++ tailWord_878826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878826).length < 2 ^ (prefixWord ++ tailWord_878826).sum := by decide
  have hdescent : baseEnd_878826 < baseStart_878826 := by decide
  rcases family_descends (prefixWord ++ tailWord_878826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878846 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_878846 : Nat := 118140960795 + 878846 * 2 ^ 59
def prefixEnd_878846 : Nat := 4983230072969 + 3 ^ 40 * 878846 * 2
def baseEnd_878846 : Nat := 451270419281373744683267

theorem tailTrace_878846 : CollatzResearch.WordTrace tailWord_878846 prefixEnd_878846 451270419281373744683267 := by
  unfold tailWord_878846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006768371762313974030049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21369431316065674528160261 4006768371762313974030049)
  ·
    refine ⟨3005076278821735480522537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4006768371762313974030049 3005076278821735480522537)
    ·
      refine ⟨2253807209116301610391903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3005076278821735480522537 2253807209116301610391903)
      ·
        refine ⟨3380710813674452415587855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253807209116301610391903 3380710813674452415587855)
        ·
          refine ⟨5071066220511678623381783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380710813674452415587855 5071066220511678623381783)
          ·
            refine ⟨7606599330767517935072675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071066220511678623381783 7606599330767517935072675)
            ·
              refine ⟨11409898996151276902609013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606599330767517935072675 11409898996151276902609013)
              ·
                refine ⟨1069678030889182209619595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11409898996151276902609013 1069678030889182209619595)
                ·
                  refine ⟨1604517046333773314429393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069678030889182209619595 1604517046333773314429393)
                  ·
                    refine ⟨1203387784750329985822045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1604517046333773314429393 1203387784750329985822045)
                    ·
                      refine ⟨451270419281373744683267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203387784750329985822045 451270419281373744683267)
                      ·
                        rfl

theorem cell23_878846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_878846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878846 prefixEnd_878846 := by exact prefixLift 878846
  have htrace : WordTrace (prefixWord ++ tailWord_878846) baseStart_878846 baseEnd_878846 := by
    simpa [prefixWord, tailWord_878846, baseEnd_878846] using wordTrace_append hprefix tailTrace_878846
  have hstable : (prefixWord ++ tailWord_878846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878846).length < 2 ^ (prefixWord ++ tailWord_878846).sum := by decide
  have hdescent : baseEnd_878846 < baseStart_878846 := by decide
  rcases family_descends (prefixWord ++ tailWord_878846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878859 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 3]
def baseStart_878859 : Nat := 118140960795 + 878859 * 2 ^ 59
def prefixEnd_878859 : Nat := 4983230072969 + 3 ^ 40 * 878859 * 2
def baseEnd_878859 : Nat := 451277094529882193820707

theorem tailTrace_878859 : CollatzResearch.WordTrace tailWord_878859 prefixEnd_878859 451277094529882193820707 := by
  unfold tailWord_878859
  simp only [CollatzResearch.WordTrace]
  refine ⟨32054621123051415012463631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21369747415367610008309087 32054621123051415012463631)
  ·
    refine ⟨48081931684577122518695447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32054621123051415012463631 48081931684577122518695447)
    ·
      refine ⟨72122897526865683778043171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48081931684577122518695447 72122897526865683778043171)
      ·
        refine ⟨108184346290298525667064757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72122897526865683778043171 108184346290298525667064757)
        ·
          refine ⟨10142282464715486781287321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108184346290298525667064757 10142282464715486781287321)
          ·
            refine ⟨7606711848536615085965491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10142282464715486781287321 7606711848536615085965491)
            ·
              refine ⟨11410067772804922628948237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606711848536615085965491 11410067772804922628948237)
              ·
                refine ⟨4278775414801845985855589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11410067772804922628948237 4278775414801845985855589)
                ·
                  refine ⟨802270390275346122347923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4278775414801845985855589 802270390275346122347923)
                  ·
                    refine ⟨1203405585413019183521885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 802270390275346122347923 1203405585413019183521885)
                    ·
                      refine ⟨451277094529882193820707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203405585413019183521885 451277094529882193820707)
                      ·
                        rfl

theorem cell23_878859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 3].length) (baseStart_878859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878859 prefixEnd_878859 := by exact prefixLift 878859
  have htrace : WordTrace (prefixWord ++ tailWord_878859) baseStart_878859 baseEnd_878859 := by
    simpa [prefixWord, tailWord_878859, baseEnd_878859] using wordTrace_append hprefix tailTrace_878859
  have hstable : (prefixWord ++ tailWord_878859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878859).length < 2 ^ (prefixWord ++ tailWord_878859).sum := by decide
  have hdescent : baseEnd_878859 < baseStart_878859 := by decide
  rcases family_descends (prefixWord ++ tailWord_878859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878860 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 1, 2, 2]
def baseStart_878860 : Nat := 118140960795 + 878860 * 2 ^ 59
def prefixEnd_878860 : Nat := 4983230072969 + 3 ^ 40 * 878860 * 2
def baseEnd_878860 : Nat := 451277608010536689908203

theorem tailTrace_878860 : CollatzResearch.WordTrace tailWord_878860 prefixEnd_878860 451277608010536689908203 := by
  unfold tailWord_878860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027328798023896091625017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21369771730698528122166689 16027328798023896091625017)
  ·
    refine ⟨12020496598517922068718763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16027328798023896091625017 12020496598517922068718763)
    ·
      refine ⟨18030744897776883103078145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12020496598517922068718763 18030744897776883103078145)
      ·
        refine ⟨13523058673332662327308609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18030744897776883103078145 13523058673332662327308609)
        ·
          refine ⟨10142294004999496745481457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13523058673332662327308609 10142294004999496745481457)
          ·
            refine ⟨7606720503749622559111093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10142294004999496745481457 7606720503749622559111093)
            ·
              refine ⟨713130047226527114916665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7606720503749622559111093 713130047226527114916665)
              ·
                refine ⟨534847535419895336187499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713130047226527114916665 534847535419895336187499)
                ·
                  refine ⟨802271303129843004281249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534847535419895336187499 802271303129843004281249)
                  ·
                    refine ⟨601703477347382253210937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802271303129843004281249 601703477347382253210937)
                    ·
                      refine ⟨451277608010536689908203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601703477347382253210937 451277608010536689908203)
                      ·
                        rfl

theorem cell23_878860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_878860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878860 prefixEnd_878860 := by exact prefixLift 878860
  have htrace : WordTrace (prefixWord ++ tailWord_878860) baseStart_878860 baseEnd_878860 := by
    simpa [prefixWord, tailWord_878860, baseEnd_878860] using wordTrace_append hprefix tailTrace_878860
  have hstable : (prefixWord ++ tailWord_878860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878860).length < 2 ^ (prefixWord ++ tailWord_878860).sum := by decide
  have hdescent : baseEnd_878860 < baseStart_878860 := by decide
  rcases family_descends (prefixWord ++ tailWord_878860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878862 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_878862 : Nat := 118140960795 + 878862 * 2 ^ 59
def prefixEnd_878862 : Nat := 4983230072969 + 3 ^ 40 * 878862 * 2
def baseEnd_878862 : Nat := 150426211657281894027731

theorem tailTrace_878862 : CollatzResearch.WordTrace tailWord_878862 prefixEnd_878862 150426211657281894027731 := by
  unfold tailWord_878862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006841317755068315602855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21369820361360364349881893 4006841317755068315602855)
  ·
    refine ⟨6010261976632602473404283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4006841317755068315602855 6010261976632602473404283)
    ·
      refine ⟨9015392964948903710106425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6010261976632602473404283 9015392964948903710106425)
      ·
        refine ⟨6761544723711677782579819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9015392964948903710106425 6761544723711677782579819)
        ·
          refine ⟨10142317085567516673869729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761544723711677782579819 10142317085567516673869729)
          ·
            refine ⟨7606737814175637505402297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10142317085567516673869729 7606737814175637505402297)
            ·
              refine ⟨5705053360631728129051723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7606737814175637505402297 5705053360631728129051723)
              ·
                refine ⟨8557580040947592193577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705053360631728129051723 8557580040947592193577585)
                ·
                  refine ⟨6418185030710694145183189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557580040947592193577585 6418185030710694145183189)
                  ·
                    refine ⟨150426211657281894027731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6418185030710694145183189 150426211657281894027731)
                    ·
                      rfl

theorem cell23_878862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_878862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878862 prefixEnd_878862 := by exact prefixLift 878862
  have htrace : WordTrace (prefixWord ++ tailWord_878862) baseStart_878862 baseEnd_878862 := by
    simpa [prefixWord, tailWord_878862, baseEnd_878862] using wordTrace_append hprefix tailTrace_878862
  have hstable : (prefixWord ++ tailWord_878862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878862).length < 2 ^ (prefixWord ++ tailWord_878862).sum := by decide
  have hdescent : baseEnd_878862 < baseStart_878862 := by decide
  rcases family_descends (prefixWord ++ tailWord_878862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878893 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_878893 : Nat := 118140960795 + 878893 * 2 ^ 59
def prefixEnd_878893 : Nat := 4983230072969 + 3 ^ 40 * 878893 * 2
def baseEnd_878893 : Nat := 451294552872135060795551

theorem tailTrace_878893 : CollatzResearch.WordTrace tailWord_878893 prefixEnd_878893 451294552872135060795551 := by
  unfold tailWord_878893
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055861204928238819201333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21370574136618825879467555 32055861204928238819201333)
  ·
    refine ⟨3005236987962022389300125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32055861204928238819201333 3005236987962022389300125)
    ·
      refine ⟨1126963870485758395987547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3005236987962022389300125 1126963870485758395987547)
      ·
        refine ⟨1690445805728637593981321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126963870485758395987547 1690445805728637593981321)
        ·
          refine ⟨1267834354296478195485991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690445805728637593981321 1267834354296478195485991)
          ·
            refine ⟨1901751531444717293228987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267834354296478195485991 1901751531444717293228987)
            ·
              refine ⟨2852627297167075939843481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901751531444717293228987 2852627297167075939843481)
              ·
                refine ⟨2139470472875306954882611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852627297167075939843481 2139470472875306954882611)
                ·
                  refine ⟨3209205709312960432323917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139470472875306954882611 3209205709312960432323917)
                  ·
                    refine ⟨1203452140992360162121469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209205709312960432323917 1203452140992360162121469)
                    ·
                      refine ⟨451294552872135060795551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203452140992360162121469 451294552872135060795551)
                      ·
                        rfl

theorem cell23_878893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_878893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878893 prefixEnd_878893 := by exact prefixLift 878893
  have htrace : WordTrace (prefixWord ++ tailWord_878893) baseStart_878893 baseEnd_878893 := by
    simpa [prefixWord, tailWord_878893, baseEnd_878893] using wordTrace_append hprefix tailTrace_878893
  have hstable : (prefixWord ++ tailWord_878893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878893).length < 2 ^ (prefixWord ++ tailWord_878893).sum := by decide
  have hdescent : baseEnd_878893 < baseStart_878893 := by decide
  rcases family_descends (prefixWord ++ tailWord_878893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878929 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_878929 : Nat := 118140960795 + 878929 * 2 ^ 59
def prefixEnd_878929 : Nat := 4983230072969 + 3 ^ 40 * 878929 * 2
def baseEnd_878929 : Nat := 451313038175696919945385

theorem tailTrace_878929 : CollatzResearch.WordTrace tailWord_878929 prefixEnd_878929 451313038175696919945385 := by
  unfold tailWord_878929
  simp only [CollatzResearch.WordTrace]
  refine ⟨32057174232797816967511841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21371449488531877978341227 32057174232797816967511841)
  ·
    refine ⟨24042880674598362725633881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32057174232797816967511841 24042880674598362725633881)
    ·
      refine ⟨18032160505948772044225411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24042880674598362725633881 18032160505948772044225411)
      ·
        refine ⟨27048240758923158066338117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18032160505948772044225411 27048240758923158066338117)
        ·
          refine ⟨5071545142298092137438397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27048240758923158066338117 5071545142298092137438397)
          ·
            refine ⟨1901829428361784551539399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5071545142298092137438397 1901829428361784551539399)
            ·
              refine ⟨2852744142542676827309099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901829428361784551539399 2852744142542676827309099)
              ·
                refine ⟨4279116213814015240963649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852744142542676827309099 4279116213814015240963649)
                ·
                  refine ⟨3209337160360511430722737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4279116213814015240963649 3209337160360511430722737)
                  ·
                    refine ⟨2407002870270383573042053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3209337160360511430722737 2407002870270383573042053)
                    ·
                      refine ⟨451313038175696919945385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2407002870270383573042053 451313038175696919945385)
                      ·
                        rfl

theorem cell23_878929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_878929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878929 prefixEnd_878929 := by exact prefixLift 878929
  have htrace : WordTrace (prefixWord ++ tailWord_878929) baseStart_878929 baseEnd_878929 := by
    simpa [prefixWord, tailWord_878929, baseEnd_878929] using wordTrace_append hprefix tailTrace_878929
  have hstable : (prefixWord ++ tailWord_878929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878929).length < 2 ^ (prefixWord ++ tailWord_878929).sum := by decide
  have hdescent : baseEnd_878929 < baseStart_878929 := by decide
  rcases family_descends (prefixWord ++ tailWord_878929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878933 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_878933 : Nat := 118140960795 + 878933 * 2 ^ 59
def prefixEnd_878933 : Nat := 4983230072969 + 3 ^ 40 * 878933 * 2
def baseEnd_878933 : Nat := 451315092098314904295367

theorem tailTrace_878933 : CollatzResearch.WordTrace tailWord_878933 prefixEnd_878933 451315092098314904295367 := by
  unfold tailWord_878933
  simp only [CollatzResearch.WordTrace]
  refine ⟨32057320124783325650657453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21371546749855550433771635 32057320124783325650657453)
  ·
    refine ⟨12021495046793747118996545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32057320124783325650657453 12021495046793747118996545)
    ·
      refine ⟨9016121285095310339247409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12021495046793747118996545 9016121285095310339247409)
      ·
        refine ⟨6762090963821482754435557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9016121285095310339247409 6762090963821482754435557)
        ·
          refine ⟨1267892055716528016456667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6762090963821482754435557 1267892055716528016456667)
          ·
            refine ⟨1901838083574792024685001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267892055716528016456667 1901838083574792024685001)
            ·
              refine ⟨1426378562681094018513751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901838083574792024685001 1426378562681094018513751)
              ·
                refine ⟨2139567844021641027770627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426378562681094018513751 2139567844021641027770627)
                ·
                  refine ⟨3209351766032461541655941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139567844021641027770627 3209351766032461541655941)
                  ·
                    refine ⟨601753456131086539060489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3209351766032461541655941 601753456131086539060489)
                    ·
                      refine ⟨451315092098314904295367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601753456131086539060489 451315092098314904295367)
                      ·
                        rfl

theorem cell23_878933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_878933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878933 prefixEnd_878933 := by exact prefixLift 878933
  have htrace : WordTrace (prefixWord ++ tailWord_878933) baseStart_878933 baseEnd_878933 := by
    simpa [prefixWord, tailWord_878933, baseEnd_878933] using wordTrace_append hprefix tailTrace_878933
  have hstable : (prefixWord ++ tailWord_878933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878933).length < 2 ^ (prefixWord ++ tailWord_878933).sum := by decide
  have hdescent : baseEnd_878933 < baseStart_878933 := by decide
  rcases family_descends (prefixWord ++ tailWord_878933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878959 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 7, 2]
def baseStart_878959 : Nat := 118140960795 + 878959 * 2 ^ 59
def prefixEnd_878959 : Nat := 4983230072969 + 3 ^ 40 * 878959 * 2
def baseEnd_878959 : Nat := 451328442595331802570247

theorem tailTrace_878959 : CollatzResearch.WordTrace tailWord_878959 prefixEnd_878959 451328442595331802570247 := by
  unfold tailWord_878959
  simp only [CollatzResearch.WordTrace]
  refine ⟨32058268422689132091103931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21372178948459421394069287 32058268422689132091103931)
  ·
    refine ⟨48087402634033698136655897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32058268422689132091103931 48087402634033698136655897)
    ·
      refine ⟨36065551975525273602491923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48087402634033698136655897 36065551975525273602491923)
      ·
        refine ⟨54098327963287910403737885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36065551975525273602491923 54098327963287910403737885)
        ·
          refine ⟨20286872986232966401401707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54098327963287910403737885 20286872986232966401401707)
          ·
            refine ⟨30430309479349449602102561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286872986232966401401707 30430309479349449602102561)
            ·
              refine ⟨22822732109512087201576921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30430309479349449602102561 22822732109512087201576921)
              ·
                refine ⟨17117049082134065401182691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22822732109512087201576921 17117049082134065401182691)
                ·
                  refine ⟨25675573623201098101774037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17117049082134065401182691 25675573623201098101774037)
                  ·
                    refine ⟨601771256793775736760329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25675573623201098101774037 601771256793775736760329)
                    ·
                      refine ⟨451328442595331802570247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601771256793775736760329 451328442595331802570247)
                      ·
                        rfl

theorem cell23_878959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 7, 2].length) (baseStart_878959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878959 prefixEnd_878959 := by exact prefixLift 878959
  have htrace : WordTrace (prefixWord ++ tailWord_878959) baseStart_878959 baseEnd_878959 := by
    simpa [prefixWord, tailWord_878959, baseEnd_878959] using wordTrace_append hprefix tailTrace_878959
  have hstable : (prefixWord ++ tailWord_878959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878959).length < 2 ^ (prefixWord ++ tailWord_878959).sum := by decide
  have hdescent : baseEnd_878959 < baseStart_878959 := by decide
  rcases family_descends (prefixWord ++ tailWord_878959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878992 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_878992 : Nat := 118140960795 + 878992 * 2 ^ 59
def prefixEnd_878992 : Nat := 4983230072969 + 3 ^ 40 * 878992 * 2
def baseEnd_878992 : Nat := 451345387456930173457595

theorem tailTrace_878992 : CollatzResearch.WordTrace tailWord_878992 prefixEnd_878992 451345387456930173457595 := by
  unfold tailWord_878992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16029736015784789363527615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21372981354379719151370153 16029736015784789363527615)
  ·
    refine ⟨24044604023677184045291423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16029736015784789363527615 24044604023677184045291423)
    ·
      refine ⟨36066906035515776067937135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24044604023677184045291423 36066906035515776067937135)
      ·
        refine ⟨54100359053273664101905703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36066906035515776067937135 54100359053273664101905703)
        ·
          refine ⟨81150538579910496152858555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54100359053273664101905703 81150538579910496152858555)
          ·
            refine ⟨121725807869865744229287833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81150538579910496152858555 121725807869865744229287833)
            ·
              refine ⟨91294355902399308171965875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121725807869865744229287833 91294355902399308171965875)
              ·
                refine ⟨136941533853598962257948813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91294355902399308171965875 136941533853598962257948813)
                ·
                  refine ⟨51353075195099610846730805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136941533853598962257948813 51353075195099610846730805)
                  ·
                    refine ⟨4814350799540588516881013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51353075195099610846730805 4814350799540588516881013)
                    ·
                      refine ⟨451345387456930173457595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4814350799540588516881013 451345387456930173457595)
                      ·
                        rfl

theorem cell23_878992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_878992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_878992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_878992 prefixEnd_878992 := by exact prefixLift 878992
  have htrace : WordTrace (prefixWord ++ tailWord_878992) baseStart_878992 baseEnd_878992 := by
    simpa [prefixWord, tailWord_878992, baseEnd_878992] using wordTrace_append hprefix tailTrace_878992
  have hstable : (prefixWord ++ tailWord_878992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878992).length < 2 ^ (prefixWord ++ tailWord_878992).sum := by decide
  have hdescent : baseEnd_878992 < baseStart_878992 := by decide
  rcases family_descends (prefixWord ++ tailWord_878992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879026 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_879026 : Nat := 118140960795 + 879026 * 2 ^ 59
def prefixEnd_879026 : Nat := 4983230072969 + 3 ^ 40 * 879026 * 2
def baseEnd_879026 : Nat := 451362845799183040432439

theorem tailTrace_879026 : CollatzResearch.WordTrace tailWord_879026 prefixEnd_879026 451362845799183040432439 := by
  unfold tailWord_879026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015178028361600633448233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21373808075630935022528621 8015178028361600633448233)
  ·
    refine ⟨6011383521271200475086175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8015178028361600633448233 6011383521271200475086175)
    ·
      refine ⟨9017075281906800712629263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6011383521271200475086175 9017075281906800712629263)
      ·
        refine ⟨13525612922860201068943895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017075281906800712629263 13525612922860201068943895)
        ·
          refine ⟨20288419384290301603415843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13525612922860201068943895 20288419384290301603415843)
          ·
            refine ⟨30432629076435452405123765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20288419384290301603415843 30432629076435452405123765)
            ·
              refine ⟨2853058975915823662980353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30432629076435452405123765 2853058975915823662980353)
              ·
                refine ⟨2139794231936867747235265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853058975915823662980353 2139794231936867747235265)
                ·
                  refine ⟨1604845673952650810426449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2139794231936867747235265 1604845673952650810426449)
                  ·
                    refine ⟨1203634255464488107819837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1604845673952650810426449 1203634255464488107819837)
                    ·
                      refine ⟨451362845799183040432439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203634255464488107819837 451362845799183040432439)
                      ·
                        rfl

theorem cell23_879026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_879026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879026 prefixEnd_879026 := by exact prefixLift 879026
  have htrace : WordTrace (prefixWord ++ tailWord_879026) baseStart_879026 baseEnd_879026 := by
    simpa [prefixWord, tailWord_879026, baseEnd_879026] using wordTrace_append hprefix tailTrace_879026
  have hstable : (prefixWord ++ tailWord_879026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879026).length < 2 ^ (prefixWord ++ tailWord_879026).sum := by decide
  have hdescent : baseEnd_879026 < baseStart_879026 := by decide
  rcases family_descends (prefixWord ++ tailWord_879026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879033 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_879033 : Nat := 118140960795 + 879033 * 2 ^ 59
def prefixEnd_879033 : Nat := 4983230072969 + 3 ^ 40 * 879033 * 2
def baseEnd_879033 : Nat := 150455480054588171014969

theorem tailTrace_879033 : CollatzResearch.WordTrace tailWord_879033 prefixEnd_879033 150455480054588171014969 := by
  unfold tailWord_879033
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060967424421042729297753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21373978282947361819531835 32060967424421042729297753)
  ·
    refine ⟨24045725568315782046973315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32060967424421042729297753 24045725568315782046973315)
    ·
      refine ⟨36068588352473673070459973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24045725568315782046973315 36068588352473673070459973)
      ·
        refine ⟨6762860316088813700711245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36068588352473673070459973 6762860316088813700711245)
        ·
          refine ⟨2536072618533305137766717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6762860316088813700711245 2536072618533305137766717)
          ·
            refine ⟨951027231949989426662519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2536072618533305137766717 951027231949989426662519)
            ·
              refine ⟨1426540847924984139993779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951027231949989426662519 1426540847924984139993779)
              ·
                refine ⟨2139811271887476209990669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426540847924984139993779 2139811271887476209990669)
                ·
                  refine ⟨802429226957803578746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2139811271887476209990669 802429226957803578746501)
                  ·
                    refine ⟨150455480054588171014969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802429226957803578746501 150455480054588171014969)
                    ·
                      rfl

theorem cell23_879033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_879033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879033 prefixEnd_879033 := by exact prefixLift 879033
  have htrace : WordTrace (prefixWord ++ tailWord_879033) baseStart_879033 baseEnd_879033 := by
    simpa [prefixWord, tailWord_879033, baseEnd_879033] using wordTrace_append hprefix tailTrace_879033
  have hstable : (prefixWord ++ tailWord_879033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879033).length < 2 ^ (prefixWord ++ tailWord_879033).sum := by decide
  have hdescent : baseEnd_879033 < baseStart_879033 := by decide
  rcases family_descends (prefixWord ++ tailWord_879033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879089 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_879089 : Nat := 118140960795 + 879089 * 2 ^ 59
def prefixEnd_879089 : Nat := 4983230072969 + 3 ^ 40 * 879089 * 2
def baseEnd_879089 : Nat := 150465065026805431314883

theorem tailTrace_879089 : CollatzResearch.WordTrace tailWord_879089 prefixEnd_879089 150465065026805431314883 := by
  unfold tailWord_879089
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063009912218164293336321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21375339941478776195557547 32063009912218164293336321)
  ·
    refine ⟨24047257434163623220002241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32063009912218164293336321 24047257434163623220002241)
    ·
      refine ⟨18035443075622717415001681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24047257434163623220002241 18035443075622717415001681)
      ·
        refine ⟨13526582306717038061251261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18035443075622717415001681 13526582306717038061251261)
        ·
          refine ⟨5072468365018889272969223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13526582306717038061251261 5072468365018889272969223)
          ·
            refine ⟨7608702547528333909453835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072468365018889272969223 7608702547528333909453835)
            ·
              refine ⟨11413053821292500864180753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608702547528333909453835 11413053821292500864180753)
              ·
                refine ⟨8559790365969375648135565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11413053821292500864180753 8559790365969375648135565)
                ·
                  refine ⟨3209921387238515868050837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8559790365969375648135565 3209921387238515868050837)
                  ·
                    refine ⟨150465065026805431314883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3209921387238515868050837 150465065026805431314883)
                    ·
                      rfl

theorem cell23_879089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_879089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879089 prefixEnd_879089 := by exact prefixLift 879089
  have htrace : WordTrace (prefixWord ++ tailWord_879089) baseStart_879089 baseEnd_879089 := by
    simpa [prefixWord, tailWord_879089, baseEnd_879089] using wordTrace_append hprefix tailTrace_879089
  have hstable : (prefixWord ++ tailWord_879089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879089).length < 2 ^ (prefixWord ++ tailWord_879089).sum := by decide
  have hdescent : baseEnd_879089 < baseStart_879089 := by decide
  rcases family_descends (prefixWord ++ tailWord_879089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879099 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3]
def baseStart_879099 : Nat := 118140960795 + 879099 * 2 ^ 59
def prefixEnd_879099 : Nat := 4983230072969 + 3 ^ 40 * 879099 * 2
def baseEnd_879099 : Nat := 451400329886961254819603

theorem tailTrace_879099 : CollatzResearch.WordTrace tailWord_879099 prefixEnd_879099 451400329886961254819603 := by
  unfold tailWord_879099
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063374642181936001200351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21375583094787957334133567 32063374642181936001200351)
  ·
    refine ⟨48095061963272904001800527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32063374642181936001200351 48095061963272904001800527)
    ·
      refine ⟨72142592944909356002700791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48095061963272904001800527 72142592944909356002700791)
      ·
        refine ⟨108213889417364034004051187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72142592944909356002700791 108213889417364034004051187)
        ·
          refine ⟨162320834126046051006076781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108213889417364034004051187 162320834126046051006076781)
          ·
            refine ⟨60870312797267269127278793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162320834126046051006076781 60870312797267269127278793)
            ·
              refine ⟨45652734597950451845459095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60870312797267269127278793 45652734597950451845459095)
              ·
                refine ⟨68479101896925677768188643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45652734597950451845459095 68479101896925677768188643)
                ·
                  refine ⟨102718652845388516652282965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68479101896925677768188643 102718652845388516652282965)
                  ·
                    refine ⟨1203734213031896679518941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102718652845388516652282965 1203734213031896679518941)
                    ·
                      refine ⟨451400329886961254819603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203734213031896679518941 451400329886961254819603)
                      ·
                        rfl

theorem cell23_879099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 3].length) (baseStart_879099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879099 prefixEnd_879099 := by exact prefixLift 879099
  have htrace : WordTrace (prefixWord ++ tailWord_879099) baseStart_879099 baseEnd_879099 := by
    simpa [prefixWord, tailWord_879099, baseEnd_879099] using wordTrace_append hprefix tailTrace_879099
  have hstable : (prefixWord ++ tailWord_879099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879099).length < 2 ^ (prefixWord ++ tailWord_879099).sum := by decide
  have hdescent : baseEnd_879099 < baseStart_879099 := by decide
  rcases family_descends (prefixWord ++ tailWord_879099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879109 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_879109 : Nat := 118140960795 + 879109 * 2 ^ 59
def prefixEnd_879109 : Nat := 4983230072969 + 3 ^ 40 * 879109 * 2
def baseEnd_879109 : Nat := 451405464693506215694557

theorem tailTrace_879109 : CollatzResearch.WordTrace tailWord_879109 prefixEnd_879109 451405464693506215694557 := by
  unfold tailWord_879109
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063739372145707709064381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21375826248097138472709587 32063739372145707709064381)
  ·
    refine ⟨12023902264554640390899143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32063739372145707709064381 12023902264554640390899143)
    ·
      refine ⟨18035853396831960586348715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12023902264554640390899143 18035853396831960586348715)
      ·
        refine ⟨27053780095247940879523073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18035853396831960586348715 27053780095247940879523073)
        ·
          refine ⟨20290335071435955659642305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27053780095247940879523073 20290335071435955659642305)
          ·
            refine ⟨15217751303576966744731729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20290335071435955659642305 15217751303576966744731729)
            ·
              refine ⟨11413313477682725058548797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15217751303576966744731729 11413313477682725058548797)
              ·
                refine ⟨4279992554131021896955799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11413313477682725058548797 4279992554131021896955799)
                ·
                  refine ⟨6419988831196532845433699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279992554131021896955799 6419988831196532845433699)
                  ·
                    refine ⟨9629983246794799268150549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6419988831196532845433699 9629983246794799268150549)
                    ·
                      refine ⟨451405464693506215694557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9629983246794799268150549 451405464693506215694557)
                      ·
                        rfl

theorem cell23_879109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_879109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879109 prefixEnd_879109 := by exact prefixLift 879109
  have htrace : WordTrace (prefixWord ++ tailWord_879109) baseStart_879109 baseEnd_879109 := by
    simpa [prefixWord, tailWord_879109, baseEnd_879109] using wordTrace_append hprefix tailTrace_879109
  have hstable : (prefixWord ++ tailWord_879109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879109).length < 2 ^ (prefixWord ++ tailWord_879109).sum := by decide
  have hdescent : baseEnd_879109 < baseStart_879109 := by decide
  rcases family_descends (prefixWord ++ tailWord_879109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879117 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_879117 : Nat := 118140960795 + 879117 * 2 ^ 59
def prefixEnd_879117 : Nat := 4983230072969 + 3 ^ 40 * 879117 * 2
def baseEnd_879117 : Nat := 451409572538742184394521

theorem tailTrace_879117 : CollatzResearch.WordTrace tailWord_879117 prefixEnd_879117 451409572538742184394521 := by
  unfold tailWord_879117
  simp only [CollatzResearch.WordTrace]
  refine ⟨32064031156116725075355605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21376020770744483383570403 32064031156116725075355605)
  ·
    refine ⟨751500730221485743953647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32064031156116725075355605 751500730221485743953647)
    ·
      refine ⟨1127251095332228615930471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751500730221485743953647 1127251095332228615930471)
      ·
        refine ⟨1690876642998342923895707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127251095332228615930471 1690876642998342923895707)
        ·
          refine ⟨2536314964497514385843561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690876642998342923895707 2536314964497514385843561)
          ·
            refine ⟨1902236223373135789382671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536314964497514385843561 1902236223373135789382671)
            ·
              refine ⟨2853354335059703684074007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902236223373135789382671 2853354335059703684074007)
              ·
                refine ⟨4280031502589555526111011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853354335059703684074007 4280031502589555526111011)
                ·
                  refine ⟨6420047253884333289166517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280031502589555526111011 6420047253884333289166517)
                  ·
                    refine ⟨601879430051656245859361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6420047253884333289166517 601879430051656245859361)
                    ·
                      refine ⟨451409572538742184394521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601879430051656245859361 451409572538742184394521)
                      ·
                        rfl

theorem cell23_879117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_879117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879117 prefixEnd_879117 := by exact prefixLift 879117
  have htrace : WordTrace (prefixWord ++ tailWord_879117) baseStart_879117 baseEnd_879117 := by
    simpa [prefixWord, tailWord_879117, baseEnd_879117] using wordTrace_append hprefix tailTrace_879117
  have hstable : (prefixWord ++ tailWord_879117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879117).length < 2 ^ (prefixWord ++ tailWord_879117).sum := by decide
  have hdescent : baseEnd_879117 < baseStart_879117 := by decide
  rcases family_descends (prefixWord ++ tailWord_879117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879124 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_879124 : Nat := 118140960795 + 879124 * 2 ^ 59
def prefixEnd_879124 : Nat := 4983230072969 + 3 ^ 40 * 879124 * 2
def baseEnd_879124 : Nat := 451413166903323657006989

theorem tailTrace_879124 : CollatzResearch.WordTrace tailWord_879124 prefixEnd_879124 451413166903323657006989 := by
  unfold tailWord_879124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032143233545682635430213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21376190978060910180573617 16032143233545682635430213)
  ·
    refine ⟨3006026856289815494143165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16032143233545682635430213 3006026856289815494143165)
    ·
      refine ⟨1127260071108680810303687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3006026856289815494143165 1127260071108680810303687)
      ·
        refine ⟨1690890106663021215455531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127260071108680810303687 1690890106663021215455531)
        ·
          refine ⟨2536335159994531823183297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690890106663021215455531 2536335159994531823183297)
          ·
            refine ⟨1902251369995898867387473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536335159994531823183297 1902251369995898867387473)
            ·
              refine ⟨1426688527496924150540605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902251369995898867387473 1426688527496924150540605)
              ·
                refine ⟨535008197811346556452727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1426688527496924150540605 535008197811346556452727)
                ·
                  refine ⟨802512296717019834679091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535008197811346556452727 802512296717019834679091)
                  ·
                    refine ⟨1203768445075529752018637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 802512296717019834679091 1203768445075529752018637)
                    ·
                      refine ⟨451413166903323657006989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203768445075529752018637 451413166903323657006989)
                      ·
                        rfl

theorem cell23_879124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_879124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879124 prefixEnd_879124 := by exact prefixLift 879124
  have htrace : WordTrace (prefixWord ++ tailWord_879124) baseStart_879124 baseEnd_879124 := by
    simpa [prefixWord, tailWord_879124, baseEnd_879124] using wordTrace_append hprefix tailTrace_879124
  have hstable : (prefixWord ++ tailWord_879124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879124).length < 2 ^ (prefixWord ++ tailWord_879124).sum := by decide
  have hdescent : baseEnd_879124 < baseStart_879124 := by decide
  rcases family_descends (prefixWord ++ tailWord_879124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879127 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 1, 5]
def baseStart_879127 : Nat := 118140960795 + 879127 * 2 ^ 59
def prefixEnd_879127 : Nat := 4983230072969 + 3 ^ 40 * 879127 * 2
def baseEnd_879127 : Nat := 150471569115095715089825

theorem tailTrace_879127 : CollatzResearch.WordTrace tailWord_879127 prefixEnd_879127 150471569115095715089825 := by
  unfold tailWord_879127
  simp only [CollatzResearch.WordTrace]
  refine ⟨32064395886080496783219635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21376263924053664522146423 32064395886080496783219635)
  ·
    refine ⟨48096593829120745174829453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32064395886080496783219635 48096593829120745174829453)
    ·
      refine ⟨18036222685920279440561045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48096593829120745174829453 18036222685920279440561045)
      ·
        refine ⟨845447938402513098776299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18036222685920279440561045 845447938402513098776299)
        ·
          refine ⟨1268171907603769648164449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845447938402513098776299 1268171907603769648164449)
          ·
            refine ⟨951128930702827236123337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268171907603769648164449 951128930702827236123337)
            ·
              refine ⟨713346698027120427092503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951128930702827236123337 713346698027120427092503)
              ·
                refine ⟨1070020047040680640638755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713346698027120427092503 1070020047040680640638755)
                ·
                  refine ⟨1605030070561020960958133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070020047040680640638755 1605030070561020960958133)
                  ·
                    refine ⟨150471569115095715089825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1605030070561020960958133 150471569115095715089825)
                    ·
                      rfl

theorem cell23_879127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_879127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879127 prefixEnd_879127 := by exact prefixLift 879127
  have htrace : WordTrace (prefixWord ++ tailWord_879127) baseStart_879127 baseEnd_879127 := by
    simpa [prefixWord, tailWord_879127, baseEnd_879127] using wordTrace_append hprefix tailTrace_879127
  have hstable : (prefixWord ++ tailWord_879127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879127).length < 2 ^ (prefixWord ++ tailWord_879127).sum := by decide
  have hdescent : baseEnd_879127 < baseStart_879127 := by decide
  rcases family_descends (prefixWord ++ tailWord_879127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879136 : List Nat := [2, 1, 1, 6, 2, 1, 10]
def baseStart_879136 : Nat := 118140960795 + 879136 * 2 ^ 59
def prefixEnd_879136 : Nat := 4983230072969 + 3 ^ 40 * 879136 * 2
def baseEnd_879136 : Nat := 5573078131742933457493

theorem tailTrace_879136 : CollatzResearch.WordTrace tailWord_879136 prefixEnd_879136 5573078131742933457493 := by
  unfold tailWord_879136
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032362071523945660148631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21376482762031927546864841 16032362071523945660148631)
  ·
    refine ⟨24048543107285918490222947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16032362071523945660148631 24048543107285918490222947)
    ·
      refine ⟨36072814660928877735334421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24048543107285918490222947 36072814660928877735334421)
      ·
        refine ⟨1690913187231041143843801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36072814660928877735334421 1690913187231041143843801)
        ·
          refine ⟨1268184890423280857882851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690913187231041143843801 1268184890423280857882851)
          ·
            refine ⟨1902277335634921286824277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268184890423280857882851 1902277335634921286824277)
            ·
              refine ⟨5573078131742933457493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1902277335634921286824277 5573078131742933457493)
              ·
                rfl

theorem cell23_879136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 10].length) (baseStart_879136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879136 prefixEnd_879136 := by exact prefixLift 879136
  have htrace : WordTrace (prefixWord ++ tailWord_879136) baseStart_879136 baseEnd_879136 := by
    simpa [prefixWord, tailWord_879136, baseEnd_879136] using wordTrace_append hprefix tailTrace_879136
  have hstable : (prefixWord ++ tailWord_879136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879136).length < 2 ^ (prefixWord ++ tailWord_879136).sum := by decide
  have hdescent : baseEnd_879136 < baseStart_879136 := by decide
  rcases family_descends (prefixWord ++ tailWord_879136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879140 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_879140 : Nat := 118140960795 + 879140 * 2 ^ 59
def prefixEnd_879140 : Nat := 4983230072969 + 3 ^ 40 * 879140 * 2
def baseEnd_879140 : Nat := 150473794197931864802305

theorem tailTrace_879140 : CollatzResearch.WordTrace tailWord_879140 prefixEnd_879140 150473794197931864802305 := by
  unfold tailWord_879140
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032435017516700001721437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21376580023355600002295249 16032435017516700001721437)
  ·
    refine ⟨6012163131568762500645539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16032435017516700001721437 6012163131568762500645539)
    ·
      refine ⟨9018244697353143750968309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6012163131568762500645539 9018244697353143750968309)
      ·
        refine ⟨845460440376857226653279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9018244697353143750968309 845460440376857226653279)
        ·
          refine ⟨1268190660565285839979919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845460440376857226653279 1268190660565285839979919)
          ·
            refine ⟨1902285990847928759969879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268190660565285839979919 1902285990847928759969879)
            ·
              refine ⟨2853428986271893139954819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902285990847928759969879 2853428986271893139954819)
              ·
                refine ⟨4280143479407839709932229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853428986271893139954819 4280143479407839709932229)
                ·
                  refine ⟨802526902388969945612293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4280143479407839709932229 802526902388969945612293)
                  ·
                    refine ⟨150473794197931864802305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802526902388969945612293 150473794197931864802305)
                    ·
                      rfl

theorem cell23_879140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_879140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879140 prefixEnd_879140 := by exact prefixLift 879140
  have htrace : WordTrace (prefixWord ++ tailWord_879140) baseStart_879140 baseEnd_879140 := by
    simpa [prefixWord, tailWord_879140, baseEnd_879140] using wordTrace_append hprefix tailTrace_879140
  have hstable : (prefixWord ++ tailWord_879140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879140).length < 2 ^ (prefixWord ++ tailWord_879140).sum := by decide
  have hdescent : baseEnd_879140 < baseStart_879140 := by decide
  rcases family_descends (prefixWord ++ tailWord_879140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879179 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 8]
def baseStart_879179 : Nat := 118140960795 + 879179 * 2 ^ 59
def prefixEnd_879179 : Nat := 4983230072969 + 3 ^ 40 * 879179 * 2
def baseEnd_879179 : Nat := 150480469446440313939745

theorem tailTrace_879179 : CollatzResearch.WordTrace tailWord_879179 prefixEnd_879179 150480469446440313939745 := by
  unfold tailWord_879179
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066292481892109664112591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21377528321261406442741727 32066292481892109664112591)
  ·
    refine ⟨48099438722838164496168887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32066292481892109664112591 48099438722838164496168887)
    ·
      refine ⟨72149158084257246744253331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48099438722838164496168887 72149158084257246744253331)
      ·
        refine ⟨108223737126385870116379997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72149158084257246744253331 108223737126385870116379997)
        ·
          refine ⟨40583901422394701293642499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108223737126385870116379997 40583901422394701293642499)
          ·
            refine ⟨60875852133592051940463749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40583901422394701293642499 60875852133592051940463749)
            ·
              refine ⟨11414222275048509738836953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60875852133592051940463749 11414222275048509738836953)
              ·
                refine ⟨8560666706286382304127715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11414222275048509738836953 8560666706286382304127715)
                ·
                  refine ⟨12841000059429573456191573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560666706286382304127715 12841000059429573456191573)
                  ·
                    refine ⟨150480469446440313939745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12841000059429573456191573 150480469446440313939745)
                    ·
                      rfl

theorem cell23_879179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_879179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879179 prefixEnd_879179 := by exact prefixLift 879179
  have htrace : WordTrace (prefixWord ++ tailWord_879179) baseStart_879179 baseEnd_879179 := by
    simpa [prefixWord, tailWord_879179, baseEnd_879179] using wordTrace_append hprefix tailTrace_879179
  have hstable : (prefixWord ++ tailWord_879179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879179).length < 2 ^ (prefixWord ++ tailWord_879179).sum := by decide
  have hdescent : baseEnd_879179 < baseStart_879179 := by decide
  rcases family_descends (prefixWord ++ tailWord_879179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879181 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_879181 : Nat := 118140960795 + 879181 * 2 ^ 59
def prefixEnd_879181 : Nat := 4983230072969 + 3 ^ 40 * 879181 * 2
def baseEnd_879181 : Nat := 451442435300629933994227

theorem tailTrace_879181 : CollatzResearch.WordTrace tailWord_879181 prefixEnd_879181 451442435300629933994227 := by
  unfold tailWord_879181
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066365427884864005685397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21377576951923242670456931 32066365427884864005685397)
  ·
    refine ⟨1503110879432103000266503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32066365427884864005685397 1503110879432103000266503)
    ·
      refine ⟨2254666319148154500399755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503110879432103000266503 2254666319148154500399755)
      ·
        refine ⟨3381999478722231750599633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254666319148154500399755 3381999478722231750599633)
        ·
          refine ⟨2536499609041673812949725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3381999478722231750599633 2536499609041673812949725)
          ·
            refine ⟨951187353390627679856147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2536499609041673812949725 951187353390627679856147)
            ·
              refine ⟨1426781030085941519784221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951187353390627679856147 1426781030085941519784221)
              ·
                refine ⟨535042886282228069919083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1426781030085941519784221 535042886282228069919083)
                ·
                  refine ⟨802564329423342104878625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535042886282228069919083 802564329423342104878625)
                  ·
                    refine ⟨601923247067506578658969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802564329423342104878625 601923247067506578658969)
                    ·
                      refine ⟨451442435300629933994227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601923247067506578658969 451442435300629933994227)
                      ·
                        rfl

theorem cell23_879181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_879181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879181 prefixEnd_879181 := by exact prefixLift 879181
  have htrace : WordTrace (prefixWord ++ tailWord_879181) baseStart_879181 baseEnd_879181 := by
    simpa [prefixWord, tailWord_879181, baseEnd_879181] using wordTrace_append hprefix tailTrace_879181
  have hstable : (prefixWord ++ tailWord_879181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879181).length < 2 ^ (prefixWord ++ tailWord_879181).sum := by decide
  have hdescent : baseEnd_879181 < baseStart_879181 := by decide
  rcases family_descends (prefixWord ++ tailWord_879181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879198 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_879198 : Nat := 118140960795 + 879198 * 2 ^ 59
def prefixEnd_879198 : Nat := 4983230072969 + 3 ^ 40 * 879198 * 2
def baseEnd_879198 : Nat := 451451164471756367481649

theorem tailTrace_879198 : CollatzResearch.WordTrace tailWord_879198 prefixEnd_879198 451451164471756367481649 := by
  unfold tailWord_879198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008373183602909488631781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21377990312548850606036165 4008373183602909488631781)
  ·
    refine ⟨751569971925545529118459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4008373183602909488631781 751569971925545529118459)
    ·
      refine ⟨1127354957888318293677689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751569971925545529118459 1127354957888318293677689)
      ·
        refine ⟨845516218416238720258267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127354957888318293677689 845516218416238720258267)
        ·
          refine ⟨1268274327624358080387401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845516218416238720258267 1268274327624358080387401)
          ·
            refine ⟨951205745718268560290551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268274327624358080387401 951205745718268560290551)
            ·
              refine ⟨1426808618577402840435827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951205745718268560290551 1426808618577402840435827)
              ·
                refine ⟨2140212927866104260653741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426808618577402840435827 2140212927866104260653741)
                ·
                  refine ⟨802579847949789097745153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2140212927866104260653741 802579847949789097745153)
                  ·
                    refine ⟨601934885962341823308865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 802579847949789097745153 601934885962341823308865)
                    ·
                      refine ⟨451451164471756367481649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 601934885962341823308865 451451164471756367481649)
                      ·
                        rfl

theorem cell23_879198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_879198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879198 prefixEnd_879198 := by exact prefixLift 879198
  have htrace : WordTrace (prefixWord ++ tailWord_879198) baseStart_879198 baseEnd_879198 := by
    simpa [prefixWord, tailWord_879198, baseEnd_879198] using wordTrace_append hprefix tailTrace_879198
  have hstable : (prefixWord ++ tailWord_879198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879198).length < 2 ^ (prefixWord ++ tailWord_879198).sum := by decide
  have hdescent : baseEnd_879198 < baseStart_879198 := by decide
  rcases family_descends (prefixWord ++ tailWord_879198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879214 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_879214 : Nat := 118140960795 + 879214 * 2 ^ 59
def prefixEnd_879214 : Nat := 4983230072969 + 3 ^ 40 * 879214 * 2
def baseEnd_879214 : Nat := 451459380162228304881575

theorem tailTrace_879214 : CollatzResearch.WordTrace tailWord_879214 prefixEnd_879214 451459380162228304881575 := by
  unfold tailWord_879214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008446129595663830204587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21378379357843540427757797 4008446129595663830204587)
  ·
    refine ⟨6012669194393495745306881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4008446129595663830204587 6012669194393495745306881)
    ·
      refine ⟨4509501895795121808980161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6012669194393495745306881 4509501895795121808980161)
      ·
        refine ⟨3382126421846341356735121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4509501895795121808980161 3382126421846341356735121)
        ·
          refine ⟨2536594816384756017551341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3382126421846341356735121 2536594816384756017551341)
          ·
            refine ⟨951223056144283506581753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2536594816384756017551341 951223056144283506581753)
            ·
              refine ⟨713417292108212629936315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951223056144283506581753 713417292108212629936315)
              ·
                refine ⟨1070125938162318944904473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713417292108212629936315 1070125938162318944904473)
                ·
                  refine ⟨802594453621739208678355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1070125938162318944904473 802594453621739208678355)
                  ·
                    refine ⟨1203891680432608813017533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 802594453621739208678355 1203891680432608813017533)
                    ·
                      refine ⟨451459380162228304881575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1203891680432608813017533 451459380162228304881575)
                      ·
                        rfl

theorem cell23_879214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_879214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879214 prefixEnd_879214 := by exact prefixLift 879214
  have htrace : WordTrace (prefixWord ++ tailWord_879214) baseStart_879214 baseEnd_879214 := by
    simpa [prefixWord, tailWord_879214, baseEnd_879214] using wordTrace_append hprefix tailTrace_879214
  have hstable : (prefixWord ++ tailWord_879214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879214).length < 2 ^ (prefixWord ++ tailWord_879214).sum := by decide
  have hdescent : baseEnd_879214 < baseStart_879214 := by decide
  rcases family_descends (prefixWord ++ tailWord_879214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879260 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 5]
def baseStart_879260 : Nat := 118140960795 + 879260 * 2 ^ 59
def prefixEnd_879260 : Nat := 4983230072969 + 3 ^ 40 * 879260 * 2
def baseEnd_879260 : Nat := 50164777808037236100707

theorem tailTrace_879260 : CollatzResearch.WordTrace tailWord_879260 prefixEnd_879260 50164777808037236100707 := by
  unfold tailWord_879260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16034623397299330248905617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21379497863065773665207489 16034623397299330248905617)
  ·
    refine ⟨12025967547974497686679213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16034623397299330248905617 12025967547974497686679213)
    ·
      refine ⟨4509737830490436632504705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12025967547974497686679213 4509737830490436632504705)
      ·
        refine ⟨3382303372867827474378529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4509737830490436632504705 3382303372867827474378529)
        ·
          refine ⟨2536727529650870605783897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3382303372867827474378529 2536727529650870605783897)
          ·
            refine ⟨1902545647238152954337923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536727529650870605783897 1902545647238152954337923)
            ·
              refine ⟨2853818470857229431506885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902545647238152954337923 2853818470857229431506885)
              ·
                refine ⟨535090963285730518407541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2853818470857229431506885 535090963285730518407541)
                ·
                  refine ⟨50164777808037236100707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535090963285730518407541 50164777808037236100707)
                  ·
                    rfl

theorem cell23_879260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_879260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879260 prefixEnd_879260 := by exact prefixLift 879260
  have htrace : WordTrace (prefixWord ++ tailWord_879260) baseStart_879260 baseEnd_879260 := by
    simpa [prefixWord, tailWord_879260, baseEnd_879260] using wordTrace_append hprefix tailTrace_879260
  have hstable : (prefixWord ++ tailWord_879260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879260).length < 2 ^ (prefixWord ++ tailWord_879260).sum := by decide
  have hdescent : baseEnd_879260 < baseStart_879260 := by decide
  rcases family_descends (prefixWord ++ tailWord_879260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879293 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_879293 : Nat := 118140960795 + 879293 * 2 ^ 59
def prefixEnd_879293 : Nat := 4983230072969 + 3 ^ 40 * 879293 * 2
def baseEnd_879293 : Nat := 451499945133933495793711

theorem tailTrace_879293 : CollatzResearch.WordTrace tailWord_879293 prefixEnd_879293 451499945133933495793711 := by
  unfold tailWord_879293
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070450403479107133762533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21380300268986071422508355 32070450403479107133762533)
  ·
    refine ⟨6013209450652332587580475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32070450403479107133762533 6013209450652332587580475)
    ·
      refine ⟨9019814175978498881370713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013209450652332587580475 9019814175978498881370713)
      ·
        refine ⟨6764860631983874161028035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9019814175978498881370713 6764860631983874161028035)
        ·
          refine ⟨10147290947975811241542053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764860631983874161028035 10147290947975811241542053)
          ·
            refine ⟨1902617052745464607789135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10147290947975811241542053 1902617052745464607789135)
            ·
              refine ⟨2853925579118196911683703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902617052745464607789135 2853925579118196911683703)
              ·
                refine ⟨4280888368677295367525555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853925579118196911683703 4280888368677295367525555)
                ·
                  refine ⟨6421332553015943051288333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280888368677295367525555 6421332553015943051288333)
                  ·
                    refine ⟨2407999707380978644233125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6421332553015943051288333 2407999707380978644233125)
                    ·
                      refine ⟨451499945133933495793711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2407999707380978644233125 451499945133933495793711)
                      ·
                        rfl

theorem cell23_879293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_879293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879293 prefixEnd_879293 := by exact prefixLift 879293
  have htrace : WordTrace (prefixWord ++ tailWord_879293) baseStart_879293 baseEnd_879293 := by
    simpa [prefixWord, tailWord_879293, baseEnd_879293] using wordTrace_append hprefix tailTrace_879293
  have hstable : (prefixWord ++ tailWord_879293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879293).length < 2 ^ (prefixWord ++ tailWord_879293).sum := by decide
  have hdescent : baseEnd_879293 < baseStart_879293 := by decide
  rcases family_descends (prefixWord ++ tailWord_879293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879310 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_879310 : Nat := 118140960795 + 879310 * 2 ^ 59
def prefixEnd_879310 : Nat := 4983230072969 + 3 ^ 40 * 879310 * 2
def baseEnd_879310 : Nat := 451508674305059929281133

theorem tailTrace_879310 : CollatzResearch.WordTrace tailWord_879310 prefixEnd_879310 451508674305059929281133 := by
  unfold tailWord_879310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008883805552189879641423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21380713629611679358087589 4008883805552189879641423)
  ·
    refine ⟨6013325708328284819462135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4008883805552189879641423 6013325708328284819462135)
    ·
      refine ⟨9019988562492427229193203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013325708328284819462135 9019988562492427229193203)
      ·
        refine ⟨13529982843738640843789805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019988562492427229193203 13529982843738640843789805)
        ·
          refine ⟨5073743566401990316421177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13529982843738640843789805 5073743566401990316421177)
          ·
            refine ⟨3805307674801492737315883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073743566401990316421177 3805307674801492737315883)
            ·
              refine ⟨5707961512202239105973825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805307674801492737315883 5707961512202239105973825)
              ·
                refine ⟨4280971134151679329480369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707961512202239105973825 4280971134151679329480369)
                ·
                  refine ⟨3210728350613759497110277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280971134151679329480369 3210728350613759497110277)
                  ·
                    refine ⟨602011565740079905708177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3210728350613759497110277 602011565740079905708177)
                    ·
                      refine ⟨451508674305059929281133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602011565740079905708177 451508674305059929281133)
                      ·
                        rfl

theorem cell23_879310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_879310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879310 prefixEnd_879310 := by exact prefixLift 879310
  have htrace : WordTrace (prefixWord ++ tailWord_879310) baseStart_879310 baseEnd_879310 := by
    simpa [prefixWord, tailWord_879310, baseEnd_879310] using wordTrace_append hprefix tailTrace_879310
  have hstable : (prefixWord ++ tailWord_879310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879310).length < 2 ^ (prefixWord ++ tailWord_879310).sum := by decide
  have hdescent : baseEnd_879310 < baseStart_879310 := by decide
  rcases family_descends (prefixWord ++ tailWord_879310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879313 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_879313 : Nat := 118140960795 + 879313 * 2 ^ 59
def prefixEnd_879313 : Nat := 4983230072969 + 3 ^ 40 * 879313 * 2
def baseEnd_879313 : Nat := 451510214747023417543619

theorem tailTrace_879313 : CollatzResearch.WordTrace tailWord_879313 prefixEnd_879313 451510214747023417543619 := by
  unfold tailWord_879313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071179863406650549490593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21380786575604433699660395 32071179863406650549490593)
  ·
    refine ⟨24053384897554987912117945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32071179863406650549490593 24053384897554987912117945)
    ·
      refine ⟨18040038673166240934088459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24053384897554987912117945 18040038673166240934088459)
      ·
        refine ⟨27060058009749361401132689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18040038673166240934088459 27060058009749361401132689)
        ·
          refine ⟨20295043507312021050849517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27060058009749361401132689 20295043507312021050849517)
          ·
            refine ⟨7610641315242007894068569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20295043507312021050849517 7610641315242007894068569)
            ·
              refine ⟨5707980986431505920551427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610641315242007894068569 5707980986431505920551427)
              ·
                refine ⟨8561971479647258880827141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707980986431505920551427 8561971479647258880827141)
                ·
                  refine ⟨1605369652433861040155089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8561971479647258880827141 1605369652433861040155089)
                  ·
                    refine ⟨1204027239325395780116317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1605369652433861040155089 1204027239325395780116317)
                    ·
                      refine ⟨451510214747023417543619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204027239325395780116317 451510214747023417543619)
                      ·
                        rfl

theorem cell23_879313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_879313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879313 prefixEnd_879313 := by exact prefixLift 879313
  have htrace : WordTrace (prefixWord ++ tailWord_879313) baseStart_879313 baseEnd_879313 := by
    simpa [prefixWord, tailWord_879313, baseEnd_879313] using wordTrace_append hprefix tailTrace_879313
  have hstable : (prefixWord ++ tailWord_879313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879313).length < 2 ^ (prefixWord ++ tailWord_879313).sum := by decide
  have hdescent : baseEnd_879313 < baseStart_879313 := by decide
  rcases family_descends (prefixWord ++ tailWord_879313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879320 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_879320 : Nat := 118140960795 + 879320 * 2 ^ 59
def prefixEnd_879320 : Nat := 4983230072969 + 3 ^ 40 * 879320 * 2
def baseEnd_879320 : Nat := 150504603037201630052029

theorem tailTrace_879320 : CollatzResearch.WordTrace tailWord_879320 prefixEnd_879320 150504603037201630052029 := by
  unfold tailWord_879320
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035717587190645372497707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21380956782920860496663609 16035717587190645372497707)
  ·
    refine ⟨24053576380785968058746561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16035717587190645372497707 24053576380785968058746561)
    ·
      refine ⟨18040182285589476044059921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24053576380785968058746561 18040182285589476044059921)
      ·
        refine ⟨13530136714192107033044941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18040182285589476044059921 13530136714192107033044941)
        ·
          refine ⟨5073801267822040137391853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13530136714192107033044941 5073801267822040137391853)
          ·
            refine ⟨1902675475433265051521945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5073801267822040137391853 1902675475433265051521945)
            ·
              refine ⟨1427006606574948788641459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902675475433265051521945 1427006606574948788641459)
              ·
                refine ⟨2140509909862423182962189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427006606574948788641459 2140509909862423182962189)
                ·
                  refine ⟨802691216198408693610821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2140509909862423182962189 802691216198408693610821)
                  ·
                    refine ⟨150504603037201630052029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802691216198408693610821 150504603037201630052029)
                    ·
                      rfl

theorem cell23_879320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_879320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879320 prefixEnd_879320 := by exact prefixLift 879320
  have htrace : WordTrace (prefixWord ++ tailWord_879320) baseStart_879320 baseEnd_879320 := by
    simpa [prefixWord, tailWord_879320, baseEnd_879320] using wordTrace_append hprefix tailTrace_879320
  have hstable : (prefixWord ++ tailWord_879320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879320).length < 2 ^ (prefixWord ++ tailWord_879320).sum := by decide
  have hdescent : baseEnd_879320 < baseStart_879320 := by decide
  rcases family_descends (prefixWord ++ tailWord_879320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879377 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 1, 1, 3]
def baseStart_879377 : Nat := 118140960795 + 879377 * 2 ^ 59
def prefixEnd_879377 : Nat := 4983230072969 + 3 ^ 40 * 879377 * 2
def baseEnd_879377 : Nat := 451543077508911167143325

theorem tailTrace_879377 : CollatzResearch.WordTrace tailWord_879377 prefixEnd_879377 451543077508911167143325 := by
  unfold tailWord_879377
  simp only [CollatzResearch.WordTrace]
  refine ⟨32073514135174789479820385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21382342756783192986546923 32073514135174789479820385)
  ·
    refine ⟨24055135601381092109865289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32073514135174789479820385 24055135601381092109865289)
    ·
      refine ⟨18041351701035819082398967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24055135601381092109865289 18041351701035819082398967)
      ·
        refine ⟨27062027551553728623598451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18041351701035819082398967 27062027551553728623598451)
        ·
          refine ⟨40593041327330592935397677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27062027551553728623598451 40593041327330592935397677)
          ·
            refine ⟨15222390497748972350774129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40593041327330592935397677 15222390497748972350774129)
            ·
              refine ⟨11416792873311729263080597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15222390497748972350774129 11416792873311729263080597)
              ·
                refine ⟨535162165936487309206903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11416792873311729263080597 535162165936487309206903)
                ·
                  refine ⟨802743248904730963810355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535162165936487309206903 802743248904730963810355)
                  ·
                    refine ⟨1204114873357096445715533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 802743248904730963810355 1204114873357096445715533)
                    ·
                      refine ⟨451543077508911167143325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204114873357096445715533 451543077508911167143325)
                      ·
                        rfl

theorem cell23_879377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_879377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879377 prefixEnd_879377 := by exact prefixLift 879377
  have htrace : WordTrace (prefixWord ++ tailWord_879377) baseStart_879377 baseEnd_879377 := by
    simpa [prefixWord, tailWord_879377, baseEnd_879377] using wordTrace_append hprefix tailTrace_879377
  have hstable : (prefixWord ++ tailWord_879377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879377).length < 2 ^ (prefixWord ++ tailWord_879377).sum := by decide
  have hdescent : baseEnd_879377 < baseStart_879377 := by decide
  rcases family_descends (prefixWord ++ tailWord_879377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879393 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_879393 : Nat := 118140960795 + 879393 * 2 ^ 59
def prefixEnd_879393 : Nat := 4983230072969 + 3 ^ 40 * 879393 * 2
def baseEnd_879393 : Nat := 150517097733127701514417

theorem tailTrace_879393 : CollatzResearch.WordTrace tailWord_879393 prefixEnd_879393 150517097733127701514417 := by
  unfold tailWord_879393
  simp only [CollatzResearch.WordTrace]
  refine ⟨32074097703116824212402833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21382731802077882808268555 32074097703116824212402833)
  ·
    refine ⟨24055573277337618159302125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32074097703116824212402833 24055573277337618159302125)
    ·
      refine ⟨9020839979001606809738297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24055573277337618159302125 9020839979001606809738297)
      ·
        refine ⟨6765629984251205107303723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9020839979001606809738297 6765629984251205107303723)
        ·
          refine ⟨10148444976376807660955585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765629984251205107303723 10148444976376807660955585)
          ·
            refine ⟨7611333732282605745716689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148444976376807660955585 7611333732282605745716689)
            ·
              refine ⟨5708500299211954309287517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611333732282605745716689 5708500299211954309287517)
              ·
                refine ⟨2140687612204482865982819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708500299211954309287517 2140687612204482865982819)
                ·
                  refine ⟨3211031418306724298974229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140687612204482865982819 3211031418306724298974229)
                  ·
                    refine ⟨150517097733127701514417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3211031418306724298974229 150517097733127701514417)
                    ·
                      rfl

theorem cell23_879393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_879393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879393 prefixEnd_879393 := by exact prefixLift 879393
  have htrace : WordTrace (prefixWord ++ tailWord_879393) baseStart_879393 baseEnd_879393 := by
    simpa [prefixWord, tailWord_879393, baseEnd_879393] using wordTrace_append hprefix tailTrace_879393
  have hstable : (prefixWord ++ tailWord_879393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879393).length < 2 ^ (prefixWord ++ tailWord_879393).sum := by decide
  have hdescent : baseEnd_879393 < baseStart_879393 := by decide
  rcases family_descends (prefixWord ++ tailWord_879393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879400 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_879400 : Nat := 118140960795 + 879400 * 2 ^ 59
def prefixEnd_879400 : Nat := 4983230072969 + 3 ^ 40 * 879400 * 2
def baseEnd_879400 : Nat := 451554887563964577155719

theorem tailTrace_879400 : CollatzResearch.WordTrace tailWord_879400 prefixEnd_879400 451554887563964577155719 := by
  unfold tailWord_879400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16037176507045732203953827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21382902009394309605271769 16037176507045732203953827)
  ·
    refine ⟨24055764760568598305930741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16037176507045732203953827 24055764760568598305930741)
    ·
      refine ⟨2255227946303306091181007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24055764760568598305930741 2255227946303306091181007)
      ·
        refine ⟨3382841919454959136771511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2255227946303306091181007 3382841919454959136771511)
        ·
          refine ⟨5074262879182438705157267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382841919454959136771511 5074262879182438705157267)
          ·
            refine ⟨7611394318773658057735901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074262879182438705157267 7611394318773658057735901)
            ·
              refine ⟨2854272869540121771650963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7611394318773658057735901 2854272869540121771650963)
              ·
                refine ⟨4281409304310182657476445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854272869540121771650963 4281409304310182657476445)
                ·
                  refine ⟨1605528489116318496553667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4281409304310182657476445 1605528489116318496553667)
                  ·
                    refine ⟨2408292733674477744830501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1605528489116318496553667 2408292733674477744830501)
                    ·
                      refine ⟨451554887563964577155719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2408292733674477744830501 451554887563964577155719)
                      ·
                        rfl

theorem cell23_879400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_879400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879400 prefixEnd_879400 := by exact prefixLift 879400
  have htrace : WordTrace (prefixWord ++ tailWord_879400) baseStart_879400 baseEnd_879400 := by
    simpa [prefixWord, tailWord_879400, baseEnd_879400] using wordTrace_append hprefix tailTrace_879400
  have hstable : (prefixWord ++ tailWord_879400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879400).length < 2 ^ (prefixWord ++ tailWord_879400).sum := by decide
  have hdescent : baseEnd_879400 < baseStart_879400 := by decide
  rcases family_descends (prefixWord ++ tailWord_879400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879428 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_879428 : Nat := 118140960795 + 879428 * 2 ^ 59
def prefixEnd_879428 : Nat := 4983230072969 + 3 ^ 40 * 879428 * 2
def baseEnd_879428 : Nat := 451569265022290467605591

theorem tailTrace_879428 : CollatzResearch.WordTrace tailWord_879428 prefixEnd_879428 451569265022290467605591 := by
  unfold tailWord_879428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16037687128995012594963469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21383582838660016793284625 16037687128995012594963469)
  ·
    refine ⟨6014132673373129723111301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16037687128995012594963469 6014132673373129723111301)
    ·
      refine ⟨1127649876257461823083369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6014132673373129723111301 1127649876257461823083369)
      ·
        refine ⟨845737407193096367312527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127649876257461823083369 845737407193096367312527)
        ·
          refine ⟨1268606110789644550968791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845737407193096367312527 1268606110789644550968791)
          ·
            refine ⟨1902909166184466826453187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268606110789644550968791 1902909166184466826453187)
            ·
              refine ⟨2854363749276700239679781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902909166184466826453187 2854363749276700239679781)
              ·
                refine ⟨535193202989381294939959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2854363749276700239679781 535193202989381294939959)
                ·
                  refine ⟨802789804484071942409939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535193202989381294939959 802789804484071942409939)
                  ·
                    refine ⟨1204184706726107913614909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 802789804484071942409939 1204184706726107913614909)
                    ·
                      refine ⟨451569265022290467605591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204184706726107913614909 451569265022290467605591)
                      ·
                        rfl

theorem cell23_879428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_879428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879428 prefixEnd_879428 := by exact prefixLift 879428
  have htrace : WordTrace (prefixWord ++ tailWord_879428) baseStart_879428 baseEnd_879428 := by
    simpa [prefixWord, tailWord_879428, baseEnd_879428] using wordTrace_append hprefix tailTrace_879428
  have hstable : (prefixWord ++ tailWord_879428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879428).length < 2 ^ (prefixWord ++ tailWord_879428).sum := by decide
  have hdescent : baseEnd_879428 < baseStart_879428 := by decide
  rcases family_descends (prefixWord ++ tailWord_879428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879450 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_879450 : Nat := 118140960795 + 879450 * 2 ^ 59
def prefixEnd_879450 : Nat := 4983230072969 + 3 ^ 40 * 879450 * 2
def baseEnd_879450 : Nat := 451580561596689381530489

theorem tailTrace_879450 : CollatzResearch.WordTrace tailWord_879450 prefixEnd_879450 451580561596689381530489 := by
  unfold tailWord_879450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8019044165977580736806951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21384117775940215298151869 8019044165977580736806951)
  ·
    refine ⟨12028566248966371105210427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8019044165977580736806951 12028566248966371105210427)
    ·
      refine ⟨18042849373449556657815641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12028566248966371105210427 18042849373449556657815641)
      ·
        refine ⟨13532137030087167493361731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18042849373449556657815641 13532137030087167493361731)
        ·
          refine ⟨20298205545130751240042597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13532137030087167493361731 20298205545130751240042597)
          ·
            refine ⟨3805913539712015857507987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20298205545130751240042597 3805913539712015857507987)
            ·
              refine ⟨5708870309568023786261981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805913539712015857507987 5708870309568023786261981)
              ·
                refine ⟨2140826366088008919848243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708870309568023786261981 2140826366088008919848243)
                ·
                  refine ⟨3211239549132013379772365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140826366088008919848243 3211239549132013379772365)
                  ·
                    refine ⟨1204214830924505017414637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3211239549132013379772365 1204214830924505017414637)
                    ·
                      refine ⟨451580561596689381530489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204214830924505017414637 451580561596689381530489)
                      ·
                        rfl

theorem cell23_879450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_879450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879450 prefixEnd_879450 := by exact prefixLift 879450
  have htrace : WordTrace (prefixWord ++ tailWord_879450) baseStart_879450 baseEnd_879450 := by
    simpa [prefixWord, tailWord_879450, baseEnd_879450] using wordTrace_append hprefix tailTrace_879450
  have hstable : (prefixWord ++ tailWord_879450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879450).length < 2 ^ (prefixWord ++ tailWord_879450).sum := by decide
  have hdescent : baseEnd_879450 < baseStart_879450 := by decide
  rcases family_descends (prefixWord ++ tailWord_879450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879483 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 2, 6]
def baseStart_879483 : Nat := 118140960795 + 879483 * 2 ^ 59
def prefixEnd_879483 : Nat := 4983230072969 + 3 ^ 40 * 879483 * 2
def baseEnd_879483 : Nat := 150532502152762584139279

theorem tailTrace_879483 : CollatzResearch.WordTrace tailWord_879483 prefixEnd_879483 150532502152762584139279 := by
  unfold tailWord_879483
  simp only [CollatzResearch.WordTrace]
  refine ⟨32077380272790769583179103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21384920181860513055452735 32077380272790769583179103)
  ·
    refine ⟨48116070409186154374768655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32077380272790769583179103 48116070409186154374768655)
    ·
      refine ⟨72174105613779231562152983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48116070409186154374768655 72174105613779231562152983)
      ·
        refine ⟨108261158420668847343229475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72174105613779231562152983 108261158420668847343229475)
        ·
          refine ⟨162391737631003271014844213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108261158420668847343229475 162391737631003271014844213)
          ·
            refine ⟨15224225402906556657641645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162391737631003271014844213 15224225402906556657641645)
            ·
              refine ⟨5709084526089958746615617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15224225402906556657641645 5709084526089958746615617)
              ·
                refine ⟨4281813394567469059961713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709084526089958746615617 4281813394567469059961713)
                ·
                  refine ⟨3211360045925601794971285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4281813394567469059961713 3211360045925601794971285)
                  ·
                    refine ⟨150532502152762584139279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3211360045925601794971285 150532502152762584139279)
                    ·
                      rfl

theorem cell23_879483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_879483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879483 prefixEnd_879483 := by exact prefixLift 879483
  have htrace : WordTrace (prefixWord ++ tailWord_879483) baseStart_879483 baseEnd_879483 := by
    simpa [prefixWord, tailWord_879483, baseEnd_879483] using wordTrace_append hprefix tailTrace_879483
  have hstable : (prefixWord ++ tailWord_879483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879483).length < 2 ^ (prefixWord ++ tailWord_879483).sum := by decide
  have hdescent : baseEnd_879483 < baseStart_879483 := by decide
  rcases family_descends (prefixWord ++ tailWord_879483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879527 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_879527 : Nat := 118140960795 + 879527 * 2 ^ 59
def prefixEnd_879527 : Nat := 4983230072969 + 3 ^ 40 * 879527 * 2
def baseEnd_879527 : Nat := 451620099607085580267635

theorem tailTrace_879527 : CollatzResearch.WordTrace tailWord_879527 prefixEnd_879527 451620099607085580267635 := by
  unfold tailWord_879527
  simp only [CollatzResearch.WordTrace]
  refine ⟨32078985084631365097780835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21385990056420910065187223 32078985084631365097780835)
  ·
    refine ⟨48118477626947047646671253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32078985084631365097780835 48118477626947047646671253)
    ·
      refine ⟨2255553638763142858437715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48118477626947047646671253 2255553638763142858437715)
      ·
        refine ⟨3383330458144714287656573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2255553638763142858437715 3383330458144714287656573)
        ·
          refine ⟨1268748921804267857871215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3383330458144714287656573 1268748921804267857871215)
          ·
            refine ⟨1903123382706401786806823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268748921804267857871215 1903123382706401786806823)
            ·
              refine ⟨2854685074059602680210235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903123382706401786806823 2854685074059602680210235)
              ·
                refine ⟨4282027611089404020315353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854685074059602680210235 4282027611089404020315353)
                ·
                  refine ⟨3211520708317053015236515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282027611089404020315353 3211520708317053015236515)
                  ·
                    refine ⟨4817281062475579522854773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211520708317053015236515 4817281062475579522854773)
                    ·
                      refine ⟨451620099607085580267635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4817281062475579522854773 451620099607085580267635)
                      ·
                        rfl

theorem cell23_879527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_879527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879527 prefixEnd_879527 := by exact prefixLift 879527
  have htrace : WordTrace (prefixWord ++ tailWord_879527) baseStart_879527 baseEnd_879527 := by
    simpa [prefixWord, tailWord_879527, baseEnd_879527] using wordTrace_append hprefix tailTrace_879527
  have hstable : (prefixWord ++ tailWord_879527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879527).length < 2 ^ (prefixWord ++ tailWord_879527).sum := by decide
  have hdescent : baseEnd_879527 < baseStart_879527 := by decide
  rcases family_descends (prefixWord ++ tailWord_879527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879577 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 2, 5]
def baseStart_879577 : Nat := 118140960795 + 879577 * 2 ^ 59
def prefixEnd_879577 : Nat := 4983230072969 + 3 ^ 40 * 879577 * 2
def baseEnd_879577 : Nat := 150548591213270128214135

theorem tailTrace_879577 : CollatzResearch.WordTrace tailWord_879577 prefixEnd_879577 150548591213270128214135 := by
  unfold tailWord_879577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32080808734450223637100985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21387205822966815758067323 32080808734450223637100985)
  ·
    refine ⟨24060606550837667727825739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32080808734450223637100985 24060606550837667727825739)
    ·
      refine ⟨36090909826256501591738609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24060606550837667727825739 36090909826256501591738609)
      ·
        refine ⟨27068182369692376193803957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36090909826256501591738609 27068182369692376193803957)
        ·
          refine ⟨2537642097158660268169121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27068182369692376193803957 2537642097158660268169121)
          ·
            refine ⟨1903231572868995201126841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537642097158660268169121 1903231572868995201126841)
            ·
              refine ⟨1427423679651746400845131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903231572868995201126841 1427423679651746400845131)
              ·
                refine ⟨2141135519477619601267697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427423679651746400845131 2141135519477619601267697)
                ·
                  refine ⟨1605851639608214700950773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2141135519477619601267697 1605851639608214700950773)
                  ·
                    refine ⟨150548591213270128214135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1605851639608214700950773 150548591213270128214135)
                    ·
                      rfl

theorem cell23_879577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_879577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879577 prefixEnd_879577 := by exact prefixLift 879577
  have htrace : WordTrace (prefixWord ++ tailWord_879577) baseStart_879577 baseEnd_879577 := by
    simpa [prefixWord, tailWord_879577, baseEnd_879577] using wordTrace_append hprefix tailTrace_879577
  have hstable : (prefixWord ++ tailWord_879577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879577).length < 2 ^ (prefixWord ++ tailWord_879577).sum := by decide
  have hdescent : baseEnd_879577 < baseStart_879577 := by decide
  rcases family_descends (prefixWord ++ tailWord_879577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879598 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_879598 : Nat := 118140960795 + 879598 * 2 ^ 59
def prefixEnd_879598 : Nat := 4983230072969 + 3 ^ 40 * 879598 * 2
def baseEnd_879598 : Nat := 50184061859283866942201

theorem tailTrace_879598 : CollatzResearch.WordTrace tailWord_879598 prefixEnd_879598 50184061859283866942201 := by
  unfold tailWord_879598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010196833421768027951931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21387716444916096149076965 4010196833421768027951931)
  ·
    refine ⟨6015295250132652041927897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010196833421768027951931 6015295250132652041927897)
    ·
      refine ⟨4511471437599489031445923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6015295250132652041927897 4511471437599489031445923)
      ·
        refine ⟨6767207156399233547168885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4511471437599489031445923 6767207156399233547168885)
        ·
          refine ⟨634425670912428145047083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6767207156399233547168885 634425670912428145047083)
          ·
            refine ⟨951638506368642217570625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634425670912428145047083 951638506368642217570625)
            ·
              refine ⟨713728879776481663177969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951638506368642217570625 713728879776481663177969)
              ·
                refine ⟨535296659832361247383477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713728879776481663177969 535296659832361247383477)
                ·
                  refine ⟨50184061859283866942201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535296659832361247383477 50184061859283866942201)
                  ·
                    rfl

theorem cell23_879598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_879598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879598 prefixEnd_879598 := by exact prefixLift 879598
  have htrace : WordTrace (prefixWord ++ tailWord_879598) baseStart_879598 baseEnd_879598 := by
    simpa [prefixWord, tailWord_879598, baseEnd_879598] using wordTrace_append hprefix tailTrace_879598
  have hstable : (prefixWord ++ tailWord_879598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879598).length < 2 ^ (prefixWord ++ tailWord_879598).sum := by decide
  have hdescent : baseEnd_879598 < baseStart_879598 := by decide
  rcases family_descends (prefixWord ++ tailWord_879598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879600 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_879600 : Nat := 118140960795 + 879600 * 2 ^ 59
def prefixEnd_879600 : Nat := 4983230072969 + 3 ^ 40 * 879600 * 2
def baseEnd_879600 : Nat := 451657583694863794654799

theorem tailTrace_879600 : CollatzResearch.WordTrace tailWord_879600 prefixEnd_879600 451657583694863794654799 := by
  unfold tailWord_879600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040823806683449282594127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21387765075577932376792169 16040823806683449282594127)
  ·
    refine ⟨24061235710025173923891191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16040823806683449282594127 24061235710025173923891191)
    ·
      refine ⟨36091853565037760885836787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24061235710025173923891191 36091853565037760885836787)
      ·
        refine ⟨54137780347556641328755181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091853565037760885836787 54137780347556641328755181)
        ·
          refine ⟨20301667630333740498283193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54137780347556641328755181 20301667630333740498283193)
          ·
            refine ⟨15226250722750305373712395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20301667630333740498283193 15226250722750305373712395)
            ·
              refine ⟨22839376084125458060568593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226250722750305373712395 22839376084125458060568593)
              ·
                refine ⟨17129532063094093545426445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22839376084125458060568593 17129532063094093545426445)
                ·
                  refine ⟨6423574523660285079534917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17129532063094093545426445 6423574523660285079534917)
                  ·
                    refine ⟨1204420223186303452412797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423574523660285079534917 1204420223186303452412797)
                    ·
                      refine ⟨451657583694863794654799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204420223186303452412797 451657583694863794654799)
                      ·
                        rfl

theorem cell23_879600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_879600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879600 prefixEnd_879600 := by exact prefixLift 879600
  have htrace : WordTrace (prefixWord ++ tailWord_879600) baseStart_879600 baseEnd_879600 := by
    simpa [prefixWord, tailWord_879600, baseEnd_879600] using wordTrace_append hprefix tailTrace_879600
  have hstable : (prefixWord ++ tailWord_879600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879600).length < 2 ^ (prefixWord ++ tailWord_879600).sum := by decide
  have hdescent : baseEnd_879600 < baseStart_879600 := by decide
  rcases family_descends (prefixWord ++ tailWord_879600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879664 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3]
def baseStart_879664 : Nat := 118140960795 + 879664 * 2 ^ 59
def prefixEnd_879664 : Nat := 4983230072969 + 3 ^ 40 * 879664 * 2
def baseEnd_879664 : Nat := 451690446456751544254505

theorem tailTrace_879664 : CollatzResearch.WordTrace tailWord_879664 prefixEnd_879664 451690446456751544254505 := by
  unfold tailWord_879664
  simp only [CollatzResearch.WordTrace]
  refine ⟨16041990942567518747759023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21389321256756691663678697 16041990942567518747759023)
  ·
    refine ⟨24062986413851278121638535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16041990942567518747759023 24062986413851278121638535)
    ·
      refine ⟨36094479620776917182457803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24062986413851278121638535 36094479620776917182457803)
      ·
        refine ⟨54141719431165375773686705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36094479620776917182457803 54141719431165375773686705)
        ·
          refine ⟨40606289573374031830265029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54141719431165375773686705 40606289573374031830265029)
          ·
            refine ⟨7613679295007630968174693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40606289573374031830265029 7613679295007630968174693)
            ·
              refine ⟨1427564867813930806532755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7613679295007630968174693 1427564867813930806532755)
              ·
                refine ⟨2141347301720896209799133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427564867813930806532755 2141347301720896209799133)
                ·
                  refine ⟨803005238145336078674675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2141347301720896209799133 803005238145336078674675)
                  ·
                    refine ⟨1204507857218004118012013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803005238145336078674675 1204507857218004118012013)
                    ·
                      refine ⟨451690446456751544254505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204507857218004118012013 451690446456751544254505)
                      ·
                        rfl

theorem cell23_879664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_879664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879664 prefixEnd_879664 := by exact prefixLift 879664
  have htrace : WordTrace (prefixWord ++ tailWord_879664) baseStart_879664 baseEnd_879664 := by
    simpa [prefixWord, tailWord_879664, baseEnd_879664] using wordTrace_append hprefix tailTrace_879664
  have hstable : (prefixWord ++ tailWord_879664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879664).length < 2 ^ (prefixWord ++ tailWord_879664).sum := by decide
  have hdescent : baseEnd_879664 < baseStart_879664 := by decide
  rcases family_descends (prefixWord ++ tailWord_879664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879697 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 4, 4]
def baseStart_879697 : Nat := 118140960795 + 879697 * 2 ^ 59
def prefixEnd_879697 : Nat := 4983230072969 + 3 ^ 40 * 879697 * 2
def baseEnd_879697 : Nat := 150569130439449971713951

theorem tailTrace_879697 : CollatzResearch.WordTrace tailWord_879697 prefixEnd_879697 150569130439449971713951 := by
  unfold tailWord_879697
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085185494015484131469345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21390123662676989420979563 32085185494015484131469345)
  ·
    refine ⟨24063889120511613098602009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32085185494015484131469345 24063889120511613098602009)
    ·
      refine ⟨18047916840383709823951507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24063889120511613098602009 18047916840383709823951507)
      ·
        refine ⟨27071875260575564735927261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18047916840383709823951507 27071875260575564735927261)
        ·
          refine ⟨10151953222715836775972723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27071875260575564735927261 10151953222715836775972723)
          ·
            refine ⟨15227929834073755163959085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10151953222715836775972723 15227929834073755163959085)
            ·
              refine ⟨5710473687777658186484657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15227929834073755163959085 5710473687777658186484657)
              ·
                refine ⟨4282855265833243639863493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5710473687777658186484657 4282855265833243639863493)
                ·
                  refine ⟨803035362343733182474405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4282855265833243639863493 803035362343733182474405)
                  ·
                    refine ⟨150569130439449971713951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 803035362343733182474405 150569130439449971713951)
                    ·
                      rfl

theorem cell23_879697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_879697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879697 prefixEnd_879697 := by exact prefixLift 879697
  have htrace : WordTrace (prefixWord ++ tailWord_879697) baseStart_879697 baseEnd_879697 := by
    simpa [prefixWord, tailWord_879697, baseEnd_879697] using wordTrace_append hprefix tailTrace_879697
  have hstable : (prefixWord ++ tailWord_879697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879697).length < 2 ^ (prefixWord ++ tailWord_879697).sum := by decide
  have hdescent : baseEnd_879697 < baseStart_879697 := by decide
  rcases family_descends (prefixWord ++ tailWord_879697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879698 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_879698 : Nat := 118140960795 + 879698 * 2 ^ 59
def prefixEnd_879698 : Nat := 4983230072969 + 3 ^ 40 * 879698 * 2
def baseEnd_879698 : Nat := 451707904799004411229349

theorem tailTrace_879698 : CollatzResearch.WordTrace tailWord_879698 prefixEnd_879698 451707904799004411229349 := by
  unfold tailWord_879698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021305491752965325563937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21390147978007907534837165 8021305491752965325563937)
  ·
    refine ⟨6015979118814723994172953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8021305491752965325563937 6015979118814723994172953)
    ·
      refine ⟨4511984339111042995629715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6015979118814723994172953 4511984339111042995629715)
      ·
        refine ⟨6767976508666564493444573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4511984339111042995629715 6767976508666564493444573)
        ·
          refine ⟨2537991190749961685041715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6767976508666564493444573 2537991190749961685041715)
          ·
            refine ⟨3806986786124942527562573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2537991190749961685041715 3806986786124942527562573)
            ·
              refine ⟨1427620044796853447835965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3806986786124942527562573 1427620044796853447835965)
              ·
                refine ⟨535357516798820042938487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1427620044796853447835965 535357516798820042938487)
                ·
                  refine ⟨803036275198230064407731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535357516798820042938487 803036275198230064407731)
                  ·
                    refine ⟨1204554412797345096611597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803036275198230064407731 1204554412797345096611597)
                    ·
                      refine ⟨451707904799004411229349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204554412797345096611597 451707904799004411229349)
                      ·
                        rfl

theorem cell23_879698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_879698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879698 prefixEnd_879698 := by exact prefixLift 879698
  have htrace : WordTrace (prefixWord ++ tailWord_879698) baseStart_879698 baseEnd_879698 := by
    simpa [prefixWord, tailWord_879698, baseEnd_879698] using wordTrace_append hprefix tailTrace_879698
  have hstable : (prefixWord ++ tailWord_879698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879698).length < 2 ^ (prefixWord ++ tailWord_879698).sum := by decide
  have hdescent : baseEnd_879698 < baseStart_879698 := by decide
  rcases family_descends (prefixWord ++ tailWord_879698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879721 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 3, 2, 2]
def baseStart_879721 : Nat := 118140960795 + 879721 * 2 ^ 59
def prefixEnd_879721 : Nat := 4983230072969 + 3 ^ 40 * 879721 * 2
def baseEnd_879721 : Nat := 451719714854057821241743

theorem tailTrace_879721 : CollatzResearch.WordTrace tailWord_879721 prefixEnd_879721 451719714854057821241743 := by
  unfold tailWord_879721
  simp only [CollatzResearch.WordTrace]
  refine ⟨32086060845928536230343017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21390707230619024153562011 32086060845928536230343017)
  ·
    refine ⟨24064545634446402172757263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32086060845928536230343017 24064545634446402172757263)
    ·
      refine ⟨36096818451669603259135895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24064545634446402172757263 36096818451669603259135895)
      ·
        refine ⟨54145227677504404888703843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36096818451669603259135895 54145227677504404888703843)
        ·
          refine ⟨81217841516256607333055765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54145227677504404888703843 81217841516256607333055765)
          ·
            refine ⟨3807086321074528468736989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81217841516256607333055765 3807086321074528468736989)
            ·
              refine ⟨1427657370402948175776371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3807086321074528468736989 1427657370402948175776371)
              ·
                refine ⟨2141486055604422263664557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427657370402948175776371 2141486055604422263664557)
                ·
                  refine ⟨803057270851658348874209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2141486055604422263664557 803057270851658348874209)
                  ·
                    refine ⟨602292953138743761655657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803057270851658348874209 602292953138743761655657)
                    ·
                      refine ⟨451719714854057821241743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602292953138743761655657 451719714854057821241743)
                      ·
                        rfl

theorem cell23_879721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 2, 2].length) (baseStart_879721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879721 prefixEnd_879721 := by exact prefixLift 879721
  have htrace : WordTrace (prefixWord ++ tailWord_879721) baseStart_879721 baseEnd_879721 := by
    simpa [prefixWord, tailWord_879721, baseEnd_879721] using wordTrace_append hprefix tailTrace_879721
  have hstable : (prefixWord ++ tailWord_879721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879721).length < 2 ^ (prefixWord ++ tailWord_879721).sum := by decide
  have hdescent : baseEnd_879721 < baseStart_879721 := by decide
  rcases family_descends (prefixWord ++ tailWord_879721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879734 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_879734 : Nat := 118140960795 + 879734 * 2 ^ 59
def prefixEnd_879734 : Nat := 4983230072969 + 3 ^ 40 * 879734 * 2
def baseEnd_879734 : Nat := 451726390102566270379183

theorem tailTrace_879734 : CollatzResearch.WordTrace tailWord_879734 prefixEnd_879734 451726390102566270379183 := by
  unfold tailWord_879734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005408437180089965660391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21391023329920959633710837 2005408437180089965660391)
  ·
    refine ⟨3008112655770134948490587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005408437180089965660391 3008112655770134948490587)
    ·
      refine ⟨4512168983655202422735881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3008112655770134948490587 4512168983655202422735881)
      ·
        refine ⟨3384126737741401817051911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512168983655202422735881 3384126737741401817051911)
        ·
          refine ⟨5076190106612102725577867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384126737741401817051911 5076190106612102725577867)
          ·
            refine ⟨7614285159918154088366801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076190106612102725577867 7614285159918154088366801)
            ·
              refine ⟨5710713869938615566275101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614285159918154088366801 5710713869938615566275101)
              ·
                refine ⟨2141517701226980837353163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5710713869938615566275101 2141517701226980837353163)
                ·
                  refine ⟨3212276551840471256029745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141517701226980837353163 3212276551840471256029745)
                  ·
                    refine ⟨2409207413880353442022309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212276551840471256029745 2409207413880353442022309)
                    ·
                      refine ⟨451726390102566270379183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2409207413880353442022309 451726390102566270379183)
                      ·
                        rfl

theorem cell23_879734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_879734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879734 prefixEnd_879734 := by exact prefixLift 879734
  have htrace : WordTrace (prefixWord ++ tailWord_879734) baseStart_879734 baseEnd_879734 := by
    simpa [prefixWord, tailWord_879734, baseEnd_879734] using wordTrace_append hprefix tailTrace_879734
  have hstable : (prefixWord ++ tailWord_879734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879734).length < 2 ^ (prefixWord ++ tailWord_879734).sum := by decide
  have hdescent : baseEnd_879734 < baseStart_879734 := by decide
  rcases family_descends (prefixWord ++ tailWord_879734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879742 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_879742 : Nat := 118140960795 + 879742 * 2 ^ 59
def prefixEnd_879742 : Nat := 4983230072969 + 3 ^ 40 * 879742 * 2
def baseEnd_879742 : Nat := 451730497947802239079147

theorem tailTrace_879742 : CollatzResearch.WordTrace tailWord_879742 prefixEnd_879742 451730497947802239079147 := by
  unfold tailWord_879742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010853347356557102107185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21391217852568304544571653 4010853347356557102107185)
  ·
    refine ⟨3008140010517417826580389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4010853347356557102107185 3008140010517417826580389)
    ·
      refine ⟨564026251972015842483823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3008140010517417826580389 564026251972015842483823)
      ·
        refine ⟨846039377958023763725735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564026251972015842483823 846039377958023763725735)
        ·
          refine ⟨1269059066937035645588603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846039377958023763725735 1269059066937035645588603)
          ·
            refine ⟨1903588600405553468382905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269059066937035645588603 1903588600405553468382905)
            ·
              refine ⟨1427691450304165101287179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903588600405553468382905 1427691450304165101287179)
              ·
                refine ⟨2141537175456247651930769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427691450304165101287179 2141537175456247651930769)
                ·
                  refine ⟨1606152881592185738948077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2141537175456247651930769 1606152881592185738948077)
                  ·
                    refine ⟨602307330597069652105529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606152881592185738948077 602307330597069652105529)
                    ·
                      refine ⟨451730497947802239079147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602307330597069652105529 451730497947802239079147)
                      ·
                        rfl

theorem cell23_879742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_879742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879742 prefixEnd_879742 := by exact prefixLift 879742
  have htrace : WordTrace (prefixWord ++ tailWord_879742) baseStart_879742 baseEnd_879742 := by
    simpa [prefixWord, tailWord_879742, baseEnd_879742] using wordTrace_append hprefix tailTrace_879742
  have hstable : (prefixWord ++ tailWord_879742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879742).length < 2 ^ (prefixWord ++ tailWord_879742).sum := by decide
  have hdescent : baseEnd_879742 < baseStart_879742 := by decide
  rcases family_descends (prefixWord ++ tailWord_879742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879754 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_879754 : Nat := 118140960795 + 879754 * 2 ^ 59
def prefixEnd_879754 : Nat := 4983230072969 + 3 ^ 40 * 879754 * 2
def baseEnd_879754 : Nat := 451736659715656192129091

theorem tailTrace_879754 : CollatzResearch.WordTrace tailWord_879754 prefixEnd_879754 451736659715656192129091 := by
  unfold tailWord_879754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021816113702245716573579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21391509636539321910862877 8021816113702245716573579)
  ·
    refine ⟨12032724170553368574860369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8021816113702245716573579 12032724170553368574860369)
    ·
      refine ⟨9024543127915026431145277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12032724170553368574860369 9024543127915026431145277)
      ·
        refine ⟨3384203672968134911679479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9024543127915026431145277 3384203672968134911679479)
        ·
          refine ⟨5076305509452202367519219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384203672968134911679479 5076305509452202367519219)
          ·
            refine ⟨7614458264178303551278829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076305509452202367519219 7614458264178303551278829)
            ·
              refine ⟨2855421849066863831729561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7614458264178303551278829 2855421849066863831729561)
              ·
                refine ⟨2141566386800147873797171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855421849066863831729561 2141566386800147873797171)
                ·
                  refine ⟨3212349580200221810695757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141566386800147873797171 3212349580200221810695757)
                  ·
                    refine ⟨1204631092575083179010909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212349580200221810695757 1204631092575083179010909)
                    ·
                      refine ⟨451736659715656192129091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204631092575083179010909 451736659715656192129091)
                      ·
                        rfl

theorem cell23_879754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_879754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879754 prefixEnd_879754 := by exact prefixLift 879754
  have htrace : WordTrace (prefixWord ++ tailWord_879754) baseStart_879754 baseEnd_879754 := by
    simpa [prefixWord, tailWord_879754, baseEnd_879754] using wordTrace_append hprefix tailTrace_879754
  have hstable : (prefixWord ++ tailWord_879754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879754).length < 2 ^ (prefixWord ++ tailWord_879754).sum := by decide
  have hdescent : baseEnd_879754 < baseStart_879754 := by decide
  rcases family_descends (prefixWord ++ tailWord_879754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879758 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_879758 : Nat := 118140960795 + 879758 * 2 ^ 59
def prefixEnd_879758 : Nat := 4983230072969 + 3 ^ 40 * 879758 * 2
def baseEnd_879758 : Nat := 451738713638274176479073

theorem tailTrace_879758 : CollatzResearch.WordTrace tailWord_879758 prefixEnd_879758 451738713638274176479073 := by
  unfold tailWord_879758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010926293349311443679991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21391606897862994366293285 4010926293349311443679991)
  ·
    refine ⟨6016389440023967165519987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010926293349311443679991 6016389440023967165519987)
    ·
      refine ⟨9024584160035950748279981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016389440023967165519987 9024584160035950748279981)
      ·
        refine ⟨3384219060013481530604993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9024584160035950748279981 3384219060013481530604993)
        ·
          refine ⟨2538164295010111147953745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384219060013481530604993 2538164295010111147953745)
          ·
            refine ⟨1903623221257583360965309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538164295010111147953745 1903623221257583360965309)
            ·
              refine ⟨713858707971593760361991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1903623221257583360965309 713858707971593760361991)
              ·
                refine ⟨1070788061957390640542987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713858707971593760361991 1070788061957390640542987)
                ·
                  refine ⟨1606182092936085960814481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1070788061957390640542987 1606182092936085960814481)
                  ·
                    refine ⟨1204636569702064470610861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1606182092936085960814481 1204636569702064470610861)
                    ·
                      refine ⟨451738713638274176479073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204636569702064470610861 451738713638274176479073)
                      ·
                        rfl

theorem cell23_879758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_879758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879758 prefixEnd_879758 := by exact prefixLift 879758
  have htrace : WordTrace (prefixWord ++ tailWord_879758) baseStart_879758 baseEnd_879758 := by
    simpa [prefixWord, tailWord_879758, baseEnd_879758] using wordTrace_append hprefix tailTrace_879758
  have hstable : (prefixWord ++ tailWord_879758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879758).length < 2 ^ (prefixWord ++ tailWord_879758).sum := by decide
  have hdescent : baseEnd_879758 < baseStart_879758 := by decide
  rcases family_descends (prefixWord ++ tailWord_879758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879772 : List Nat := [2, 2, 3, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_879772 : Nat := 118140960795 + 879772 * 2 ^ 59
def prefixEnd_879772 : Nat := 4983230072969 + 3 ^ 40 * 879772 * 2
def baseEnd_879772 : Nat := 451745902367437121704009

theorem tailTrace_879772 : CollatzResearch.WordTrace tailWord_879772 prefixEnd_879772 451745902367437121704009 := by
  unfold tailWord_879772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043960484371885970224785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21391947312495847960299713 16043960484371885970224785)
  ·
    refine ⟨12032970363278914477668589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16043960484371885970224785 12032970363278914477668589)
    ·
      refine ⟨4512363886229592929125721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12032970363278914477668589 4512363886229592929125721)
      ·
        refine ⟨3384272914672194696844291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512363886229592929125721 3384272914672194696844291)
        ·
          refine ⟨5076409372008292045266437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384272914672194696844291 5076409372008292045266437)
          ·
            refine ⟨951826757251554758487457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5076409372008292045266437 951826757251554758487457)
            ·
              refine ⟨713870067938666068865593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951826757251554758487457 713870067938666068865593)
              ·
                refine ⟨535402550953999551649195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713870067938666068865593 535402550953999551649195)
                ·
                  refine ⟨803103826430999327473793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535402550953999551649195 803103826430999327473793)
                  ·
                    refine ⟨602327869823249495605345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803103826430999327473793 602327869823249495605345)
                    ·
                      refine ⟨451745902367437121704009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602327869823249495605345 451745902367437121704009)
                      ·
                        rfl

theorem cell23_879772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_879772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879772 prefixEnd_879772 := by exact prefixLift 879772
  have htrace : WordTrace (prefixWord ++ tailWord_879772) baseStart_879772 baseEnd_879772 := by
    simpa [prefixWord, tailWord_879772, baseEnd_879772] using wordTrace_append hprefix tailTrace_879772
  have hstable : (prefixWord ++ tailWord_879772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879772).length < 2 ^ (prefixWord ++ tailWord_879772).sum := by decide
  have hdescent : baseEnd_879772 < baseStart_879772 := by decide
  rcases family_descends (prefixWord ++ tailWord_879772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879774 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_879774 : Nat := 118140960795 + 879774 * 2 ^ 59
def prefixEnd_879774 : Nat := 4983230072969 + 3 ^ 40 * 879774 * 2
def baseEnd_879774 : Nat := 150582309776248704626333

theorem tailTrace_879774 : CollatzResearch.WordTrace tailWord_879774 prefixEnd_879774 150582309776248704626333 := by
  unfold tailWord_879774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010999239342065785252797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21391995943157684188014917 4010999239342065785252797)
  ·
    refine ⟨1504124714753274669469799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4010999239342065785252797 1504124714753274669469799)
    ·
      refine ⟨2256187072129912004204699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504124714753274669469799 2256187072129912004204699)
      ·
        refine ⟨3384280608194868006307049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256187072129912004204699 3384280608194868006307049)
        ·
          refine ⟨2538210456146151004730287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384280608194868006307049 2538210456146151004730287)
          ·
            refine ⟨3807315684219226507095431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538210456146151004730287 3807315684219226507095431)
            ·
              refine ⟨5710973526328839760643147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807315684219226507095431 5710973526328839760643147)
              ·
                refine ⟨8566460289493259640964721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710973526328839760643147 8566460289493259640964721)
                ·
                  refine ⟨6424845217119944730723541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566460289493259640964721 6424845217119944730723541)
                  ·
                    refine ⟨150582309776248704626333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6424845217119944730723541 150582309776248704626333)
                    ·
                      rfl

theorem cell23_879774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_879774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879774 prefixEnd_879774 := by exact prefixLift 879774
  have htrace : WordTrace (prefixWord ++ tailWord_879774) baseStart_879774 baseEnd_879774 := by
    simpa [prefixWord, tailWord_879774, baseEnd_879774] using wordTrace_append hprefix tailTrace_879774
  have hstable : (prefixWord ++ tailWord_879774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879774).length < 2 ^ (prefixWord ++ tailWord_879774).sum := by decide
  have hdescent : baseEnd_879774 < baseStart_879774 := by decide
  rcases family_descends (prefixWord ++ tailWord_879774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879777 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_879777 : Nat := 118140960795 + 879777 * 2 ^ 59
def prefixEnd_879777 : Nat := 4983230072969 + 3 ^ 40 * 879777 * 2
def baseEnd_879777 : Nat := 451748469770709602141485

theorem tailTrace_879777 : CollatzResearch.WordTrace tailWord_879777 prefixEnd_879777 451748469770709602141485 := by
  unfold tailWord_879777
  simp only [CollatzResearch.WordTrace]
  refine ⟨32088103333725657794381585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21392068889150438529587723 32088103333725657794381585)
  ·
    refine ⟨24066077500294243345786189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32088103333725657794381585 24066077500294243345786189)
    ·
      refine ⟨9024779062610341254669821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24066077500294243345786189 9024779062610341254669821)
      ·
        refine ⟨3384292148478877970501183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9024779062610341254669821 3384292148478877970501183)
        ·
          refine ⟨5076438222718316955751775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384292148478877970501183 5076438222718316955751775)
          ·
            refine ⟨7614657334077475433627663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076438222718316955751775 7614657334077475433627663)
            ·
              refine ⟨11421986001116213150441495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614657334077475433627663 11421986001116213150441495)
              ·
                refine ⟨17132979001674319725662243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421986001116213150441495 17132979001674319725662243)
                ·
                  refine ⟨25699468502511479588493365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17132979001674319725662243 25699468502511479588493365)
                  ·
                    refine ⟨2409325172110451211421253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25699468502511479588493365 2409325172110451211421253)
                    ·
                      refine ⟨451748469770709602141485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2409325172110451211421253 451748469770709602141485)
                      ·
                        rfl

theorem cell23_879777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_879777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879777 prefixEnd_879777 := by exact prefixLift 879777
  have htrace : WordTrace (prefixWord ++ tailWord_879777) baseStart_879777 baseEnd_879777 := by
    simpa [prefixWord, tailWord_879777, baseEnd_879777] using wordTrace_append hprefix tailTrace_879777
  have hstable : (prefixWord ++ tailWord_879777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879777).length < 2 ^ (prefixWord ++ tailWord_879777).sum := by decide
  have hdescent : baseEnd_879777 < baseStart_879777 := by decide
  rcases family_descends (prefixWord ++ tailWord_879777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879827 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3]
def baseStart_879827 : Nat := 118140960795 + 879827 * 2 ^ 59
def prefixEnd_879827 : Nat := 4983230072969 + 3 ^ 40 * 879827 * 2
def baseEnd_879827 : Nat := 451774143803434406516255

theorem tailTrace_879827 : CollatzResearch.WordTrace tailWord_879827 prefixEnd_879827 451774143803434406516255 := by
  unfold tailWord_879827
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089926983544516333701735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21393284655696344222467823 32089926983544516333701735)
  ·
    refine ⟨48134890475316774500552603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32089926983544516333701735 48134890475316774500552603)
    ·
      refine ⟨72202335712975161750828905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48134890475316774500552603 72202335712975161750828905)
      ·
        refine ⟨54151751784731371313121679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72202335712975161750828905 54151751784731371313121679)
        ·
          refine ⟨81227627677097056969682519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54151751784731371313121679 81227627677097056969682519)
          ·
            refine ⟨121841441515645585454523779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81227627677097056969682519 121841441515645585454523779)
            ·
              refine ⟨182762162273468378181785669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121841441515645585454523779 182762162273468378181785669)
              ·
                refine ⟨34267905426275320909084813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182762162273468378181785669 34267905426275320909084813)
                ·
                  refine ⟨12850464534853245340906805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34267905426275320909084813 12850464534853245340906805)
                  ·
                    refine ⟨1204731050142491750710013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12850464534853245340906805 1204731050142491750710013)
                    ·
                      refine ⟨451774143803434406516255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204731050142491750710013 451774143803434406516255)
                      ·
                        rfl

theorem cell23_879827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_879827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879827 prefixEnd_879827 := by exact prefixLift 879827
  have htrace : WordTrace (prefixWord ++ tailWord_879827) baseStart_879827 baseEnd_879827 := by
    simpa [prefixWord, tailWord_879827, baseEnd_879827] using wordTrace_append hprefix tailTrace_879827
  have hstable : (prefixWord ++ tailWord_879827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879827).length < 2 ^ (prefixWord ++ tailWord_879827).sum := by decide
  have hdescent : baseEnd_879827 < baseStart_879827 := by decide
  rcases family_descends (prefixWord ++ tailWord_879827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879844 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_879844 : Nat := 118140960795 + 879844 * 2 ^ 59
def prefixEnd_879844 : Nat := 4983230072969 + 3 ^ 40 * 879844 * 2
def baseEnd_879844 : Nat := 451782872974560840003677

theorem tailTrace_879844 : CollatzResearch.WordTrace tailWord_879844 prefixEnd_879844 451782872974560840003677 := by
  unfold tailWord_879844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16045273512241464118535293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21393698016321952158047057 16045273512241464118535293)
  ·
    refine ⟨6016977567090549044450735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16045273512241464118535293 6016977567090549044450735)
    ·
      refine ⟨9025466350635823566676103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016977567090549044450735 9025466350635823566676103)
      ·
        refine ⟨13538199525953735350014155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025466350635823566676103 13538199525953735350014155)
        ·
          refine ⟨20307299288930603025021233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13538199525953735350014155 20307299288930603025021233)
          ·
            refine ⟨15230474466697952268765925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20307299288930603025021233 15230474466697952268765925)
            ·
              refine ⟨2855713962505866050393611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15230474466697952268765925 2855713962505866050393611)
              ·
                refine ⟨4283570943758799075590417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855713962505866050393611 4283570943758799075590417)
                ·
                  refine ⟨3212678207819099306692813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283570943758799075590417 3212678207819099306692813)
                  ·
                    refine ⟨1204754327932162240009805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212678207819099306692813 1204754327932162240009805)
                    ·
                      refine ⟨451782872974560840003677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204754327932162240009805 451782872974560840003677)
                      ·
                        rfl

theorem cell23_879844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_879844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879844 prefixEnd_879844 := by exact prefixLift 879844
  have htrace : WordTrace (prefixWord ++ tailWord_879844) baseStart_879844 baseEnd_879844 := by
    simpa [prefixWord, tailWord_879844, baseEnd_879844] using wordTrace_append hprefix tailTrace_879844
  have hstable : (prefixWord ++ tailWord_879844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879844).length < 2 ^ (prefixWord ++ tailWord_879844).sum := by decide
  have hdescent : baseEnd_879844 < baseStart_879844 := by decide
  rcases family_descends (prefixWord ++ tailWord_879844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879845 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_879845 : Nat := 118140960795 + 879845 * 2 ^ 59
def prefixEnd_879845 : Nat := 4983230072969 + 3 ^ 40 * 879845 * 2
def baseEnd_879845 : Nat := 451783386455215336091173

theorem tailTrace_879845 : CollatzResearch.WordTrace tailWord_879845 prefixEnd_879845 451783386455215336091173 := by
  unfold tailWord_879845
  simp only [CollatzResearch.WordTrace]
  refine ⟨32090583497479305407856989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21393722331652870271904659 32090583497479305407856989)
  ·
    refine ⟨12033968811554739527946371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32090583497479305407856989 12033968811554739527946371)
    ·
      refine ⟨18050953217332109291919557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033968811554739527946371 18050953217332109291919557)
      ·
        refine ⟨3384553728249770492234917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18050953217332109291919557 3384553728249770492234917)
        ·
          refine ⟨634603824046831967294047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3384553728249770492234917 634603824046831967294047)
          ·
            refine ⟨951905736070247950941071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634603824046831967294047 951905736070247950941071)
            ·
              refine ⟨1427858604105371926411607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951905736070247950941071 1427858604105371926411607)
              ·
                refine ⟨2141787906158057889617411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427858604105371926411607 2141787906158057889617411)
                ·
                  refine ⟨3212681859237086834426117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141787906158057889617411 3212681859237086834426117)
                  ·
                    refine ⟨602377848606953781454897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212681859237086834426117 602377848606953781454897)
                    ·
                      refine ⟨451783386455215336091173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602377848606953781454897 451783386455215336091173)
                      ·
                        rfl

theorem cell23_879845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_879845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879845 prefixEnd_879845 := by exact prefixLift 879845
  have htrace : WordTrace (prefixWord ++ tailWord_879845) baseStart_879845 baseEnd_879845 := by
    simpa [prefixWord, tailWord_879845, baseEnd_879845] using wordTrace_append hprefix tailTrace_879845
  have hstable : (prefixWord ++ tailWord_879845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879845).length < 2 ^ (prefixWord ++ tailWord_879845).sum := by decide
  have hdescent : baseEnd_879845 < baseStart_879845 := by decide
  rcases family_descends (prefixWord ++ tailWord_879845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879857 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_879857 : Nat := 118140960795 + 879857 * 2 ^ 59
def prefixEnd_879857 : Nat := 4983230072969 + 3 ^ 40 * 879857 * 2
def baseEnd_879857 : Nat := 451789548223069289141117

theorem tailTrace_879857 : CollatzResearch.WordTrace tailWord_879857 prefixEnd_879857 451789548223069289141117 := by
  unfold tailWord_879857
  simp only [CollatzResearch.WordTrace]
  refine ⟨32091021173435831457293825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21394014115623887638195883 32091021173435831457293825)
  ·
    refine ⟨24068265880076873592970369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32091021173435831457293825 24068265880076873592970369)
    ·
      refine ⟨18051199410057655194727777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24068265880076873592970369 18051199410057655194727777)
      ·
        refine ⟨13538399557543241396045833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18051199410057655194727777 13538399557543241396045833)
        ·
          refine ⟨10153799668157431047034375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13538399557543241396045833 10153799668157431047034375)
          ·
            refine ⟨15230699502236146570551563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153799668157431047034375 15230699502236146570551563)
            ·
              refine ⟨22846049253354219855827345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15230699502236146570551563 22846049253354219855827345)
              ·
                refine ⟨17134536940015664891870509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22846049253354219855827345 17134536940015664891870509)
                ·
                  refine ⟨6425451352505874334451441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17134536940015664891870509 6425451352505874334451441)
                  ·
                    refine ⟨4819088514379405750838581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6425451352505874334451441 4819088514379405750838581)
                    ·
                      refine ⟨451789548223069289141117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4819088514379405750838581 451789548223069289141117)
                      ·
                        rfl

theorem cell23_879857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_879857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879857 prefixEnd_879857 := by exact prefixLift 879857
  have htrace : WordTrace (prefixWord ++ tailWord_879857) baseStart_879857 baseEnd_879857 := by
    simpa [prefixWord, tailWord_879857, baseEnd_879857] using wordTrace_append hprefix tailTrace_879857
  have hstable : (prefixWord ++ tailWord_879857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879857).length < 2 ^ (prefixWord ++ tailWord_879857).sum := by decide
  have hdescent : baseEnd_879857 < baseStart_879857 := by decide
  rcases family_descends (prefixWord ++ tailWord_879857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879868 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 5]
def baseStart_879868 : Nat := 118140960795 + 879868 * 2 ^ 59
def prefixEnd_879868 : Nat := 4983230072969 + 3 ^ 40 * 879868 * 2
def baseEnd_879868 : Nat := 50199466278918749567063

theorem tailTrace_879868 : CollatzResearch.WordTrace tailWord_879868 prefixEnd_879868 50199466278918749567063 := by
  unfold tailWord_879868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16045711188197990167972129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21394281584263986890629505 16045711188197990167972129)
  ·
    refine ⟨12034283391148492625979097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16045711188197990167972129 12034283391148492625979097)
    ·
      refine ⟨9025712543361369469484323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12034283391148492625979097 9025712543361369469484323)
      ·
        refine ⟨13538568815042054204226485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025712543361369469484323 13538568815042054204226485)
        ·
          refine ⟨1269240826410192581646233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13538568815042054204226485 1269240826410192581646233)
          ·
            refine ⟨951930619807644436234675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269240826410192581646233 951930619807644436234675)
            ·
              refine ⟨1427895929711466654352013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951930619807644436234675 1427895929711466654352013)
              ·
                refine ⟨535460973641799995382005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1427895929711466654352013 535460973641799995382005)
                ·
                  refine ⟨50199466278918749567063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535460973641799995382005 50199466278918749567063)
                  ·
                    rfl

theorem cell23_879868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_879868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879868 prefixEnd_879868 := by exact prefixLift 879868
  have htrace : WordTrace (prefixWord ++ tailWord_879868) baseStart_879868 baseEnd_879868 := by
    simpa [prefixWord, tailWord_879868, baseEnd_879868] using wordTrace_append hprefix tailTrace_879868
  have hstable : (prefixWord ++ tailWord_879868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879868).length < 2 ^ (prefixWord ++ tailWord_879868).sum := by decide
  have hdescent : baseEnd_879868 < baseStart_879868 := by decide
  rcases family_descends (prefixWord ++ tailWord_879868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879884 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_879884 : Nat := 118140960795 + 879884 * 2 ^ 59
def prefixEnd_879884 : Nat := 4983230072969 + 3 ^ 40 * 879884 * 2
def baseEnd_879884 : Nat := 451803412200740683503493

theorem tailTrace_879884 : CollatzResearch.WordTrace tailWord_879884 prefixEnd_879884 451803412200740683503493 := by
  unfold tailWord_879884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16046002972169007534263353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21394670629558676712351137 16046002972169007534263353)
  ·
    refine ⟨12034502229126755650697515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16046002972169007534263353 12034502229126755650697515)
    ·
      refine ⟨18051753343690133476046273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034502229126755650697515 18051753343690133476046273)
      ·
        refine ⟨13538815007767600107034705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18051753343690133476046273 13538815007767600107034705)
        ·
          refine ⟨10154111255825700080276029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13538815007767600107034705 10154111255825700080276029)
          ·
            refine ⟨3807791720934637530103511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10154111255825700080276029 3807791720934637530103511)
            ·
              refine ⟨5711687581401956295155267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807791720934637530103511 5711687581401956295155267)
              ·
                refine ⟨8567531372102934442732901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711687581401956295155267 8567531372102934442732901)
                ·
                  refine ⟨1606412132269300208012419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8567531372102934442732901 1606412132269300208012419)
                  ·
                    refine ⟨2409618198403950312018629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1606412132269300208012419 2409618198403950312018629)
                    ·
                      refine ⟨451803412200740683503493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2409618198403950312018629 451803412200740683503493)
                      ·
                        rfl

theorem cell23_879884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_879884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879884 prefixEnd_879884 := by exact prefixLift 879884
  have htrace : WordTrace (prefixWord ++ tailWord_879884) baseStart_879884 baseEnd_879884 := by
    simpa [prefixWord, tailWord_879884, baseEnd_879884] using wordTrace_append hprefix tailTrace_879884
  have hstable : (prefixWord ++ tailWord_879884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879884).length < 2 ^ (prefixWord ++ tailWord_879884).sum := by decide
  have hdescent : baseEnd_879884 < baseStart_879884 := by decide
  rcases family_descends (prefixWord ++ tailWord_879884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879921 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_879921 : Nat := 118140960795 + 879921 * 2 ^ 59
def prefixEnd_879921 : Nat := 4983230072969 + 3 ^ 40 * 879921 * 2
def baseEnd_879921 : Nat := 451822410984957038740823

theorem tailTrace_879921 : CollatzResearch.WordTrace tailWord_879921 prefixEnd_879921 451822410984957038740823 := by
  unfold tailWord_879921
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093355445203970387623617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21395570296802646925082411 32093355445203970387623617)
  ·
    refine ⟨24070016583902977790717713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32093355445203970387623617 24070016583902977790717713)
    ·
      refine ⟨18052512437927233343038285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24070016583902977790717713 18052512437927233343038285)
      ·
        refine ⟨6769692164222712503639357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18052512437927233343038285 6769692164222712503639357)
        ·
          refine ⟨2538634561583517188864759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6769692164222712503639357 2538634561583517188864759)
          ·
            refine ⟨3807951842375275783297139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538634561583517188864759 3807951842375275783297139)
            ·
              refine ⟨5711927763562913674945709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807951842375275783297139 5711927763562913674945709)
              ·
                refine ⟨2141972911336092628104641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5711927763562913674945709 2141972911336092628104641)
                ·
                  refine ⟨1606479683502069471078481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2141972911336092628104641 1606479683502069471078481)
                  ·
                    refine ⟨1204859762626552103308861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1606479683502069471078481 1204859762626552103308861)
                    ·
                      refine ⟨451822410984957038740823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204859762626552103308861 451822410984957038740823)
                      ·
                        rfl

theorem cell23_879921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_879921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879921 prefixEnd_879921 := by exact prefixLift 879921
  have htrace : WordTrace (prefixWord ++ tailWord_879921) baseStart_879921 baseEnd_879921 := by
    simpa [prefixWord, tailWord_879921, baseEnd_879921] using wordTrace_append hprefix tailTrace_879921
  have hstable : (prefixWord ++ tailWord_879921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879921).length < 2 ^ (prefixWord ++ tailWord_879921).sum := by decide
  have hdescent : baseEnd_879921 < baseStart_879921 := by decide
  rcases family_descends (prefixWord ++ tailWord_879921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879927 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_879927 : Nat := 118140960795 + 879927 * 2 ^ 59
def prefixEnd_879927 : Nat := 4983230072969 + 3 ^ 40 * 879927 * 2
def baseEnd_879927 : Nat := 451825491868884015265795

theorem tailTrace_879927 : CollatzResearch.WordTrace tailWord_879927 prefixEnd_879927 451825491868884015265795 := by
  unfold tailWord_879927
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093574283182233412342035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21395716188788155608228023 32093574283182233412342035)
  ·
    refine ⟨48140361424773350118513053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32093574283182233412342035 48140361424773350118513053)
    ·
      refine ⟨18052635534290006294442395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48140361424773350118513053 18052635534290006294442395)
      ·
        refine ⟨27078953301435009441663593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18052635534290006294442395 27078953301435009441663593)
        ·
          refine ⟨20309214976076257081247695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27078953301435009441663593 20309214976076257081247695)
          ·
            refine ⟨30463822464114385621871543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20309214976076257081247695 30463822464114385621871543)
            ·
              refine ⟨45695733696171578432807315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30463822464114385621871543 45695733696171578432807315)
              ·
                refine ⟨68543600544257367649210973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45695733696171578432807315 68543600544257367649210973)
                ·
                  refine ⟨25703850204096512868454115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68543600544257367649210973 25703850204096512868454115)
                  ·
                    refine ⟨38555775306144769302681173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25703850204096512868454115 38555775306144769302681173)
                    ·
                      refine ⟨451825491868884015265795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 38555775306144769302681173 451825491868884015265795)
                      ·
                        rfl

theorem cell23_879927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_879927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879927 prefixEnd_879927 := by exact prefixLift 879927
  have htrace : WordTrace (prefixWord ++ tailWord_879927) baseStart_879927 baseEnd_879927 := by
    simpa [prefixWord, tailWord_879927, baseEnd_879927] using wordTrace_append hprefix tailTrace_879927
  have hstable : (prefixWord ++ tailWord_879927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879927).length < 2 ^ (prefixWord ++ tailWord_879927).sum := by decide
  have hdescent : baseEnd_879927 < baseStart_879927 := by decide
  rcases family_descends (prefixWord ++ tailWord_879927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879961 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 4, 3, 2]
def baseStart_879961 : Nat := 118140960795 + 879961 * 2 ^ 59
def prefixEnd_879961 : Nat := 4983230072969 + 3 ^ 40 * 879961 * 2
def baseEnd_879961 : Nat := 451842950211136882240639

theorem tailTrace_879961 : CollatzResearch.WordTrace tailWord_879961 prefixEnd_879961 451842950211136882240639 := by
  unfold tailWord_879961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32094814365059057219079737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21396542910039371479386491 32094814365059057219079737)
  ·
    refine ⟨24071110773794292914309803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32094814365059057219079737 24071110773794292914309803)
    ·
      refine ⟨36106666160691439371464705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24071110773794292914309803 36106666160691439371464705)
      ·
        refine ⟨27079999620518579528598529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36106666160691439371464705 27079999620518579528598529)
        ·
          refine ⟨20309999715388934646448897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27079999620518579528598529 20309999715388934646448897)
          ·
            refine ⟨15232499786541700984836673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20309999715388934646448897 15232499786541700984836673)
            ·
              refine ⟨11424374839906275738627505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15232499786541700984836673 11424374839906275738627505)
              ·
                refine ⟨8568281129929706803970629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11424374839906275738627505 8568281129929706803970629)
                ·
                  refine ⟨1606552711861820025744493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8568281129929706803970629 1606552711861820025744493)
                  ·
                    refine ⟨602457266948182509654185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1606552711861820025744493 602457266948182509654185)
                    ·
                      refine ⟨451842950211136882240639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602457266948182509654185 451842950211136882240639)
                      ·
                        rfl

theorem cell23_879961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_879961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879961 prefixEnd_879961 := by exact prefixLift 879961
  have htrace : WordTrace (prefixWord ++ tailWord_879961) baseStart_879961 baseEnd_879961 := by
    simpa [prefixWord, tailWord_879961, baseEnd_879961] using wordTrace_append hprefix tailTrace_879961
  have hstable : (prefixWord ++ tailWord_879961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879961).length < 2 ^ (prefixWord ++ tailWord_879961).sum := by decide
  have hdescent : baseEnd_879961 < baseStart_879961 := by decide
  rcases family_descends (prefixWord ++ tailWord_879961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879968 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3]
def baseStart_879968 : Nat := 118140960795 + 879968 * 2 ^ 59
def prefixEnd_879968 : Nat := 4983230072969 + 3 ^ 40 * 879968 * 2
def baseEnd_879968 : Nat := 451846544575718354853107

theorem tailTrace_879968 : CollatzResearch.WordTrace tailWord_879968 prefixEnd_879968 451846544575718354853107 := by
  unfold tailWord_879968
  simp only [CollatzResearch.WordTrace]
  refine ⟨16047534838016848707292279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21396713117355798276389705 16047534838016848707292279)
  ·
    refine ⟨24071302257025273060938419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16047534838016848707292279 24071302257025273060938419)
    ·
      refine ⟨36106953385537909591407629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24071302257025273060938419 36106953385537909591407629)
      ·
        refine ⟨13540107519576716096777861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36106953385537909591407629 13540107519576716096777861)
        ·
          refine ⟨2538770159920634268145849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13540107519576716096777861 2538770159920634268145849)
          ·
            refine ⟨1904077619940475701109387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538770159920634268145849 1904077619940475701109387)
            ·
              refine ⟨2856116429910713551664081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904077619940475701109387 2856116429910713551664081)
              ·
                refine ⟨2142087322433035163748061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856116429910713551664081 2142087322433035163748061)
                ·
                  refine ⟨803282745912388186405523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142087322433035163748061 803282745912388186405523)
                  ·
                    refine ⟨1204924118868582279608285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803282745912388186405523 1204924118868582279608285)
                    ·
                      refine ⟨451846544575718354853107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204924118868582279608285 451846544575718354853107)
                      ·
                        rfl

theorem cell23_879968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_879968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879968 prefixEnd_879968 := by exact prefixLift 879968
  have htrace : WordTrace (prefixWord ++ tailWord_879968) baseStart_879968 baseEnd_879968 := by
    simpa [prefixWord, tailWord_879968, baseEnd_879968] using wordTrace_append hprefix tailTrace_879968
  have hstable : (prefixWord ++ tailWord_879968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879968).length < 2 ^ (prefixWord ++ tailWord_879968).sum := by decide
  have hdescent : baseEnd_879968 < baseStart_879968 := by decide
  rcases family_descends (prefixWord ++ tailWord_879968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879984 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_879984 : Nat := 118140960795 + 879984 * 2 ^ 59
def prefixEnd_879984 : Nat := 4983230072969 + 3 ^ 40 * 879984 * 2
def baseEnd_879984 : Nat := 150618253422063430751011

theorem tailTrace_879984 : CollatzResearch.WordTrace tailWord_879984 prefixEnd_879984 150618253422063430751011 := by
  unfold tailWord_879984
  simp only [CollatzResearch.WordTrace]
  refine ⟨16047826621987866073583503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21397102162650488098111337 16047826621987866073583503)
  ·
    refine ⟨24071739932981799110375255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16047826621987866073583503 24071739932981799110375255)
    ·
      refine ⟨36107609899472698665562883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24071739932981799110375255 36107609899472698665562883)
      ·
        refine ⟨54161414849209047998344325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36107609899472698665562883 54161414849209047998344325)
        ·
          refine ⟨10155265284226696499689561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54161414849209047998344325 10155265284226696499689561)
          ·
            refine ⟨7616448963170022374767171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10155265284226696499689561 7616448963170022374767171)
            ·
              refine ⟨11424673444755033562150757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616448963170022374767171 11424673444755033562150757)
              ·
                refine ⟨2142126270891568792903267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11424673444755033562150757 2142126270891568792903267)
                ·
                  refine ⟨3213189406337353189354901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142126270891568792903267 3213189406337353189354901)
                  ·
                    refine ⟨150618253422063430751011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3213189406337353189354901 150618253422063430751011)
                    ·
                      rfl

theorem cell23_879984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_879984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879984 prefixEnd_879984 := by exact prefixLift 879984
  have htrace : WordTrace (prefixWord ++ tailWord_879984) baseStart_879984 baseEnd_879984 := by
    simpa [prefixWord, tailWord_879984, baseEnd_879984] using wordTrace_append hprefix tailTrace_879984
  have hstable : (prefixWord ++ tailWord_879984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879984).length < 2 ^ (prefixWord ++ tailWord_879984).sum := by decide
  have hdescent : baseEnd_879984 < baseStart_879984 := by decide
  rcases family_descends (prefixWord ++ tailWord_879984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879991 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_879991 : Nat := 118140960795 + 879991 * 2 ^ 59
def prefixEnd_879991 : Nat := 4983230072969 + 3 ^ 40 * 879991 * 2
def baseEnd_879991 : Nat := 451858354630771764865501

theorem tailTrace_879991 : CollatzResearch.WordTrace tailWord_879991 prefixEnd_879991 451858354630771764865501 := by
  unfold tailWord_879991
  simp only [CollatzResearch.WordTrace]
  refine ⟨32095908554950372342671827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21397272369966914895114551 32095908554950372342671827)
  ·
    refine ⟨48143862832425558514007741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32095908554950372342671827 48143862832425558514007741)
    ·
      refine ⟨18053948562159584442752903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48143862832425558514007741 18053948562159584442752903)
      ·
        refine ⟨27080922843239376664129355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18053948562159584442752903 27080922843239376664129355)
        ·
          refine ⟨40621384264859064996194033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27080922843239376664129355 40621384264859064996194033)
          ·
            refine ⟨30466038198644298747145525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40621384264859064996194033 30466038198644298747145525)
            ·
              refine ⟨2856191081122903007544893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30466038198644298747145525 2856191081122903007544893)
              ·
                refine ⟨1071071655421088627829335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2856191081122903007544893 1071071655421088627829335)
                ·
                  refine ⟨1606607483131632941744003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071071655421088627829335 1606607483131632941744003)
                  ·
                    refine ⟨2409911224697449412616005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1606607483131632941744003 2409911224697449412616005)
                    ·
                      refine ⟨451858354630771764865501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2409911224697449412616005 451858354630771764865501)
                      ·
                        rfl

theorem cell23_879991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_879991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_879991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_879991 prefixEnd_879991 := by exact prefixLift 879991
  have htrace : WordTrace (prefixWord ++ tailWord_879991) baseStart_879991 baseEnd_879991 := by
    simpa [prefixWord, tailWord_879991, baseEnd_879991] using wordTrace_append hprefix tailTrace_879991
  have hstable : (prefixWord ++ tailWord_879991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879991).length < 2 ^ (prefixWord ++ tailWord_879991).sum := by decide
  have hdescent : baseEnd_879991 < baseStart_879991 := by decide
  rcases family_descends (prefixWord ++ tailWord_879991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880002 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_880002 : Nat := 118140960795 + 880002 * 2 ^ 59
def prefixEnd_880002 : Nat := 4983230072969 + 3 ^ 40 * 880002 * 2
def baseEnd_880002 : Nat := 451864002917971221827951

theorem tailTrace_880002 : CollatzResearch.WordTrace tailWord_880002 prefixEnd_880002 451864002917971221827951 := by
  unfold tailWord_880002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024077439477630305330565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21397539838607014147548173 8024077439477630305330565)
  ·
    refine ⟨1504514519902055682249481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8024077439477630305330565 1504514519902055682249481)
    ·
      refine ⟨1128385889926541761687111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1504514519902055682249481 1128385889926541761687111)
      ·
        refine ⟨1692578834889812642530667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128385889926541761687111 1692578834889812642530667)
        ·
          refine ⟨2538868252334718963796001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692578834889812642530667 2538868252334718963796001)
          ·
            refine ⟨1904151189251039222847001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538868252334718963796001 1904151189251039222847001)
            ·
              refine ⟨1428113391938279417135251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904151189251039222847001 1428113391938279417135251)
              ·
                refine ⟨2142170087907419125702877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428113391938279417135251 2142170087907419125702877)
                ·
                  refine ⟨803313782965282172138579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142170087907419125702877 803313782965282172138579)
                  ·
                    refine ⟨1204970674447923258207869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803313782965282172138579 1204970674447923258207869)
                    ·
                      refine ⟨451864002917971221827951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1204970674447923258207869 451864002917971221827951)
                      ·
                        rfl

theorem cell23_880002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_880002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880002 prefixEnd_880002 := by exact prefixLift 880002
  have htrace : WordTrace (prefixWord ++ tailWord_880002) baseStart_880002 baseEnd_880002 := by
    simpa [prefixWord, tailWord_880002, baseEnd_880002] using wordTrace_append hprefix tailTrace_880002
  have hstable : (prefixWord ++ tailWord_880002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880002).length < 2 ^ (prefixWord ++ tailWord_880002).sum := by decide
  have hdescent : baseEnd_880002 < baseStart_880002 := by decide
  rcases family_descends (prefixWord ++ tailWord_880002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880021 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_880021 : Nat := 118140960795 + 880021 * 2 ^ 59
def prefixEnd_880021 : Nat := 4983230072969 + 3 ^ 40 * 880021 * 2
def baseEnd_880021 : Nat := 451873759050406647490363

theorem tailTrace_880021 : CollatzResearch.WordTrace tailWord_880021 prefixEnd_880021 451873759050406647490363 := by
  unfold tailWord_880021
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097002744841687466263917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21398001829894458310842611 32097002744841687466263917)
  ·
    refine ⟨12036376029315632799848969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32097002744841687466263917 12036376029315632799848969)
    ·
      refine ⟨9027282021986724599886727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12036376029315632799848969 9027282021986724599886727)
      ·
        refine ⟨13540923032980086899830091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027282021986724599886727 13540923032980086899830091)
        ·
          refine ⟨20311384549470130349745137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540923032980086899830091 20311384549470130349745137)
          ·
            refine ⟨15233538412102597762308853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20311384549470130349745137 15233538412102597762308853)
            ·
              refine ⟨1428144226134618540216455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15233538412102597762308853 1428144226134618540216455)
              ·
                refine ⟨2142216339201927810324683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428144226134618540216455 2142216339201927810324683)
                ·
                  refine ⟨3213324508802891715487025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142216339201927810324683 3213324508802891715487025)
                  ·
                    refine ⟨2409993381602168786615269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213324508802891715487025 2409993381602168786615269)
                    ·
                      refine ⟨451873759050406647490363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2409993381602168786615269 451873759050406647490363)
                      ·
                        rfl

theorem cell23_880021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_880021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880021 prefixEnd_880021 := by exact prefixLift 880021
  have htrace : WordTrace (prefixWord ++ tailWord_880021) baseStart_880021 baseEnd_880021 := by
    simpa [prefixWord, tailWord_880021, baseEnd_880021] using wordTrace_append hprefix tailTrace_880021
  have hstable : (prefixWord ++ tailWord_880021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880021).length < 2 ^ (prefixWord ++ tailWord_880021).sum := by decide
  have hdescent : baseEnd_880021 < baseStart_880021 := by decide
  rcases family_descends (prefixWord ++ tailWord_880021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880031 : List Nat := [1, 1, 2, 5, 1, 2, 4, 7]
def baseStart_880031 : Nat := 118140960795 + 880031 * 2 ^ 59
def prefixEnd_880031 : Nat := 4983230072969 + 3 ^ 40 * 880031 * 2
def baseEnd_880031 : Nat := 16736255328035244754271

theorem tailTrace_880031 : CollatzResearch.WordTrace tailWord_880031 prefixEnd_880031 16736255328035244754271 := by
  unfold tailWord_880031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097367474805459174127947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21398244983203639449418631 32097367474805459174127947)
  ·
    refine ⟨48146051212208188761191921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32097367474805459174127947 48146051212208188761191921)
    ·
      refine ⟨36109538409156141570893941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48146051212208188761191921 36109538409156141570893941)
      ·
        refine ⟨3385269225858388272271307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36109538409156141570893941 3385269225858388272271307)
        ·
          refine ⟨5077903838787582408406961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385269225858388272271307 5077903838787582408406961)
          ·
            refine ⟨3808427879090686806305221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077903838787582408406961 3808427879090686806305221)
            ·
              refine ⟨714080227329503776182229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3808427879090686806305221 714080227329503776182229)
              ·
                refine ⟨16736255328035244754271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 714080227329503776182229 16736255328035244754271)
                ·
                  rfl

theorem cell23_880031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 7].length) (baseStart_880031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880031 prefixEnd_880031 := by exact prefixLift 880031
  have htrace : WordTrace (prefixWord ++ tailWord_880031) baseStart_880031 baseEnd_880031 := by
    simpa [prefixWord, tailWord_880031, baseEnd_880031] using wordTrace_append hprefix tailTrace_880031
  have hstable : (prefixWord ++ tailWord_880031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880031).length < 2 ^ (prefixWord ++ tailWord_880031).sum := by decide
  have hdescent : baseEnd_880031 < baseStart_880031 := by decide
  rcases family_descends (prefixWord ++ tailWord_880031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880045 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_880045 : Nat := 118140960795 + 880045 * 2 ^ 59
def prefixEnd_880045 : Nat := 4983230072969 + 3 ^ 40 * 880045 * 2
def baseEnd_880045 : Nat := 451886082586114553590253

theorem tailTrace_880045 : CollatzResearch.WordTrace tailWord_880045 prefixEnd_880045 451886082586114553590253 := by
  unfold tailWord_880045
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097878096754739565137589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21398585397836493043425059 32097878096754739565137589)
  ·
    refine ⟨3009176071570756834231649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32097878096754739565137589 3009176071570756834231649)
    ·
      refine ⟨2256882053678067625673737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3009176071570756834231649 2256882053678067625673737)
      ·
        refine ⟨1692661540258550719255303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256882053678067625673737 1692661540258550719255303)
        ·
          refine ⟨2538992310387826078882955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692661540258550719255303 2538992310387826078882955)
          ·
            refine ⟨3808488465581739118324433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538992310387826078882955 3808488465581739118324433)
            ·
              refine ⟨2856366349186304338743325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808488465581739118324433 2856366349186304338743325)
              ·
                refine ⟨1071137380944864127028747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2856366349186304338743325 1071137380944864127028747)
                ·
                  refine ⟨1606706071417296190543121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071137380944864127028747 1606706071417296190543121)
                  ·
                    refine ⟨1205029553562972142907341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1606706071417296190543121 1205029553562972142907341)
                    ·
                      refine ⟨451886082586114553590253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1205029553562972142907341 451886082586114553590253)
                      ·
                        rfl

theorem cell23_880045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_880045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880045 prefixEnd_880045 := by exact prefixLift 880045
  have htrace : WordTrace (prefixWord ++ tailWord_880045) baseStart_880045 baseEnd_880045 := by
    simpa [prefixWord, tailWord_880045, baseEnd_880045] using wordTrace_append hprefix tailTrace_880045
  have hstable : (prefixWord ++ tailWord_880045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880045).length < 2 ^ (prefixWord ++ tailWord_880045).sum := by decide
  have hdescent : baseEnd_880045 < baseStart_880045 := by decide
  rcases family_descends (prefixWord ++ tailWord_880045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880075 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 2, 1, 3]
def baseStart_880075 : Nat := 118140960795 + 880075 * 2 ^ 59
def prefixEnd_880075 : Nat := 4983230072969 + 3 ^ 40 * 880075 * 2
def baseEnd_880075 : Nat := 451901487005749436215115

theorem tailTrace_880075 : CollatzResearch.WordTrace tailWord_880075 prefixEnd_880075 451901487005749436215115 := by
  unfold tailWord_880075
  simp only [CollatzResearch.WordTrace]
  refine ⟨32098972286646054688729679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21399314857764036459153119 32098972286646054688729679)
  ·
    refine ⟨48148458429969082033094519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32098972286646054688729679 48148458429969082033094519)
    ·
      refine ⟨72222687644953623049641779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48148458429969082033094519 72222687644953623049641779)
      ·
        refine ⟨108334031467430434574462669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72222687644953623049641779 108334031467430434574462669)
        ·
          refine ⟨40625261800286412965423501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108334031467430434574462669 40625261800286412965423501)
          ·
            refine ⟨15234473175107404862033813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40625261800286412965423501 15234473175107404862033813)
            ·
              refine ⟨714115930083159602907835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15234473175107404862033813 714115930083159602907835)
              ·
                refine ⟨1071173895124739404361753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714115930083159602907835 1071173895124739404361753)
                ·
                  refine ⟨803380421343554553271315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071173895124739404361753 803380421343554553271315)
                  ·
                    refine ⟨1205070632015331829906973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803380421343554553271315 1205070632015331829906973)
                    ·
                      refine ⟨451901487005749436215115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1205070632015331829906973 451901487005749436215115)
                      ·
                        rfl

theorem cell23_880075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 1, 3].length) (baseStart_880075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880075 prefixEnd_880075 := by exact prefixLift 880075
  have htrace : WordTrace (prefixWord ++ tailWord_880075) baseStart_880075 baseEnd_880075 := by
    simpa [prefixWord, tailWord_880075, baseEnd_880075] using wordTrace_append hprefix tailTrace_880075
  have hstable : (prefixWord ++ tailWord_880075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880075).length < 2 ^ (prefixWord ++ tailWord_880075).sum := by decide
  have hdescent : baseEnd_880075 < baseStart_880075 := by decide
  rcases family_descends (prefixWord ++ tailWord_880075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880118 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_880118 : Nat := 118140960795 + 880118 * 2 ^ 59
def prefixEnd_880118 : Nat := 4983230072969 + 3 ^ 40 * 880118 * 2
def baseEnd_880118 : Nat := 451923566673892767977417

theorem tailTrace_880118 : CollatzResearch.WordTrace tailWord_880118 prefixEnd_880118 451923566673892767977417 := by
  unfold tailWord_880118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006283789093142064534063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21400360416993515355030005 2006283789093142064534063)
  ·
    refine ⟨3009425683639713096801095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006283789093142064534063 3009425683639713096801095)
    ·
      refine ⟨4514138525459569645201643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009425683639713096801095 4514138525459569645201643)
      ·
        refine ⟨6771207788189354467802465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514138525459569645201643 6771207788189354467802465)
        ·
          refine ⟨5078405841142015850851849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6771207788189354467802465 5078405841142015850851849)
          ·
            refine ⟨3808804380856511888138887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5078405841142015850851849 3808804380856511888138887)
            ·
              refine ⟨5713206571284767832208331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808804380856511888138887 5713206571284767832208331)
              ·
                refine ⟨8569809856927151748312497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713206571284767832208331 8569809856927151748312497)
                ·
                  refine ⟨6427357392695363811234373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569809856927151748312497 6427357392695363811234373)
                  ·
                    refine ⟨1205129511130380714606445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427357392695363811234373 1205129511130380714606445)
                    ·
                      refine ⟨451923566673892767977417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1205129511130380714606445 451923566673892767977417)
                      ·
                        rfl

theorem cell23_880118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_880118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880118 prefixEnd_880118 := by exact prefixLift 880118
  have htrace : WordTrace (prefixWord ++ tailWord_880118) baseStart_880118 baseEnd_880118 := by
    simpa [prefixWord, tailWord_880118, baseEnd_880118] using wordTrace_append hprefix tailTrace_880118
  have hstable : (prefixWord ++ tailWord_880118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880118).length < 2 ^ (prefixWord ++ tailWord_880118).sum := by decide
  have hdescent : baseEnd_880118 < baseStart_880118 := by decide
  rcases family_descends (prefixWord ++ tailWord_880118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880132 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_880132 : Nat := 118140960795 + 880132 * 2 ^ 59
def prefixEnd_880132 : Nat := 4983230072969 + 3 ^ 40 * 880132 * 2
def baseEnd_880132 : Nat := 451930755403055713202353

theorem tailTrace_880132 : CollatzResearch.WordTrace tailWord_880132 prefixEnd_880132 451930755403055713202353 := by
  unfold tailWord_880132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050525623719776711777325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21400700831626368949036433 16050525623719776711777325)
  ·
    refine ⟨6018947108894916266916497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16050525623719776711777325 6018947108894916266916497)
    ·
      refine ⟨4514210331671187200187373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6018947108894916266916497 4514210331671187200187373)
      ·
        refine ⟨1692828874376695200070265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4514210331671187200187373 1692828874376695200070265)
        ·
          refine ⟨1269621655782521400052699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692828874376695200070265 1269621655782521400052699)
          ·
            refine ⟨1904432483673782100079049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269621655782521400052699 1904432483673782100079049)
            ·
              refine ⟨1428324362755336575059287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904432483673782100079049 1428324362755336575059287)
              ·
                refine ⟨2142486544133004862588931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428324362755336575059287 2142486544133004862588931)
                ·
                  refine ⟨3213729816199507293883397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142486544133004862588931 3213729816199507293883397)
                  ·
                    refine ⟨602574340537407617603137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3213729816199507293883397 602574340537407617603137)
                    ·
                      refine ⟨451930755403055713202353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602574340537407617603137 451930755403055713202353)
                      ·
                        rfl

theorem cell23_880132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_880132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880132 prefixEnd_880132 := by exact prefixLift 880132
  have htrace : WordTrace (prefixWord ++ tailWord_880132) baseStart_880132 baseEnd_880132 := by
    simpa [prefixWord, tailWord_880132, baseEnd_880132] using wordTrace_append hprefix tailTrace_880132
  have hstable : (prefixWord ++ tailWord_880132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880132).length < 2 ^ (prefixWord ++ tailWord_880132).sum := by decide
  have hdescent : baseEnd_880132 < baseStart_880132 := by decide
  rcases family_descends (prefixWord ++ tailWord_880132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880208 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_880208 : Nat := 118140960795 + 880208 * 2 ^ 59
def prefixEnd_880208 : Nat := 4983230072969 + 3 ^ 40 * 880208 * 2
def baseEnd_880208 : Nat := 451969779932797415852003

theorem tailTrace_880208 : CollatzResearch.WordTrace tailWord_880208 prefixEnd_880208 451969779932797415852003 := by
  unfold tailWord_880208
  simp only [CollatzResearch.WordTrace]
  refine ⟨16051911597582109201660639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21402548796776145602214185 16051911597582109201660639)
  ·
    refine ⟨24077867396373163802490959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16051911597582109201660639 24077867396373163802490959)
    ·
      refine ⟨36116801094559745703736439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24077867396373163802490959 36116801094559745703736439)
      ·
        refine ⟨54175201641839618555604659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36116801094559745703736439 54175201641839618555604659)
        ·
          refine ⟨81262802462759427833406989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54175201641839618555604659 81262802462759427833406989)
          ·
            refine ⟨30473550923534785437527621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81262802462759427833406989 30473550923534785437527621)
            ·
              refine ⟨5713790798162772269536429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30473550923534785437527621 5713790798162772269536429)
              ·
                refine ⟨2142671549311039601076161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5713790798162772269536429 2142671549311039601076161)
                ·
                  refine ⟨1607003661983279700807121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142671549311039601076161 1607003661983279700807121)
                  ·
                    refine ⟨1205252746487459775605341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1607003661983279700807121 1205252746487459775605341)
                    ·
                      refine ⟨451969779932797415852003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1205252746487459775605341 451969779932797415852003)
                      ·
                        rfl

theorem cell23_880208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_880208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880208 prefixEnd_880208 := by exact prefixLift 880208
  have htrace : WordTrace (prefixWord ++ tailWord_880208) baseStart_880208 baseEnd_880208 := by
    simpa [prefixWord, tailWord_880208, baseEnd_880208] using wordTrace_append hprefix tailTrace_880208
  have hstable : (prefixWord ++ tailWord_880208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880208).length < 2 ^ (prefixWord ++ tailWord_880208).sum := by decide
  have hdescent : baseEnd_880208 < baseStart_880208 := by decide
  rcases family_descends (prefixWord ++ tailWord_880208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880231 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_880231 : Nat := 118140960795 + 880231 * 2 ^ 59
def prefixEnd_880231 : Nat := 4983230072969 + 3 ^ 40 * 880231 * 2
def baseEnd_880231 : Nat := 451981589987850825864397

theorem tailTrace_880231 : CollatzResearch.WordTrace tailWord_880231 prefixEnd_880231 451981589987850825864397 := by
  unfold tailWord_880231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104662074080893331408547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21403108049387262220939031 32104662074080893331408547)
  ·
    refine ⟨48156993111121339997112821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32104662074080893331408547 48156993111121339997112821)
    ·
      refine ⟨4514718104167625624729327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48156993111121339997112821 4514718104167625624729327)
      ·
        refine ⟨6772077156251438437093991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514718104167625624729327 6772077156251438437093991)
        ·
          refine ⟨10158115734377157655640987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772077156251438437093991 10158115734377157655640987)
          ·
            refine ⟨15237173601565736483461481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10158115734377157655640987 15237173601565736483461481)
            ·
              refine ⟨11427880201174302362596111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15237173601565736483461481 11427880201174302362596111)
              ·
                refine ⟨17141820301761453543894167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11427880201174302362596111 17141820301761453543894167)
                ·
                  refine ⟨25712730452642180315841251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17141820301761453543894167 25712730452642180315841251)
                  ·
                    refine ⟨38569095678963270473761877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25712730452642180315841251 38569095678963270473761877)
                    ·
                      refine ⟨451981589987850825864397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 38569095678963270473761877 451981589987850825864397)
                      ·
                        rfl

theorem cell23_880231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_880231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880231 prefixEnd_880231 := by exact prefixLift 880231
  have htrace : WordTrace (prefixWord ++ tailWord_880231) baseStart_880231 baseEnd_880231 := by
    simpa [prefixWord, tailWord_880231, baseEnd_880231] using wordTrace_append hprefix tailTrace_880231
  have hstable : (prefixWord ++ tailWord_880231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880231).length < 2 ^ (prefixWord ++ tailWord_880231).sum := by decide
  have hdescent : baseEnd_880231 < baseStart_880231 := by decide
  rcases family_descends (prefixWord ++ tailWord_880231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880232 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_880232 : Nat := 118140960795 + 880232 * 2 ^ 59
def prefixEnd_880232 : Nat := 4983230072969 + 3 ^ 40 * 880232 * 2
def baseEnd_880232 : Nat := 150660701156168440650631

theorem tailTrace_880232 : CollatzResearch.WordTrace tailWord_880232 prefixEnd_880232 150660701156168440650631 := by
  unfold tailWord_880232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052349273538635251097475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21403132364718180334796633 16052349273538635251097475)
  ·
    refine ⟨24078523910307952876646213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16052349273538635251097475 24078523910307952876646213)
    ·
      refine ⟨4514723233182741164371165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24078523910307952876646213 4514723233182741164371165)
      ·
        refine ⟨1693021212443527936639187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4514723233182741164371165 1693021212443527936639187)
        ·
          refine ⟨2539531818665291904958781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693021212443527936639187 2539531818665291904958781)
          ·
            refine ⟨952324431999484464359543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2539531818665291904958781 952324431999484464359543)
            ·
              refine ⟨1428486647999226696539315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952324431999484464359543 1428486647999226696539315)
              ·
                refine ⟨2142729971998840044808973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428486647999226696539315 2142729971998840044808973)
                ·
                  refine ⟨803523739499565016803365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142729971998840044808973 803523739499565016803365)
                  ·
                    refine ⟨150660701156168440650631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 803523739499565016803365 150660701156168440650631)
                    ·
                      rfl

theorem cell23_880232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_880232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880232 prefixEnd_880232 := by exact prefixLift 880232
  have htrace : WordTrace (prefixWord ++ tailWord_880232) baseStart_880232 baseEnd_880232 := by
    simpa [prefixWord, tailWord_880232, baseEnd_880232] using wordTrace_append hprefix tailTrace_880232
  have hstable : (prefixWord ++ tailWord_880232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880232).length < 2 ^ (prefixWord ++ tailWord_880232).sum := by decide
  have hdescent : baseEnd_880232 < baseStart_880232 := by decide
  rcases family_descends (prefixWord ++ tailWord_880232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880245 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 6]
def baseStart_880245 : Nat := 118140960795 + 880245 * 2 ^ 59
def prefixEnd_880245 : Nat := 4983230072969 + 3 ^ 40 * 880245 * 2
def baseEnd_880245 : Nat := 50220975413001530121037

theorem tailTrace_880245 : CollatzResearch.WordTrace tailWord_880245 prefixEnd_880245 50220975413001530121037 := by
  unfold tailWord_880245
  simp only [CollatzResearch.WordTrace]
  refine ⟨32105172696030173722418189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21403448464020115814945459 32105172696030173722418189)
  ·
    refine ⟨12039439761011315145906821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32105172696030173722418189 12039439761011315145906821)
    ·
      refine ⟨2257394955189621589857529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12039439761011315145906821 2257394955189621589857529)
      ·
        refine ⟨1693046216392216192393147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2257394955189621589857529 1693046216392216192393147)
        ·
          refine ⟨2539569324588324288589721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693046216392216192393147 2539569324588324288589721)
          ·
            refine ⟨1904676993441243216442291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2539569324588324288589721 1904676993441243216442291)
            ·
              refine ⟨2857015490161864824663437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904676993441243216442291 2857015490161864824663437)
              ·
                refine ⟨1071380808810699309248789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2857015490161864824663437 1071380808810699309248789)
                ·
                  refine ⟨50220975413001530121037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1071380808810699309248789 50220975413001530121037)
                  ·
                    rfl

theorem cell23_880245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_880245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880245 prefixEnd_880245 := by exact prefixLift 880245
  have htrace : WordTrace (prefixWord ++ tailWord_880245) baseStart_880245 baseEnd_880245 := by
    simpa [prefixWord, tailWord_880245, baseEnd_880245] using wordTrace_append hprefix tailTrace_880245
  have hstable : (prefixWord ++ tailWord_880245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880245).length < 2 ^ (prefixWord ++ tailWord_880245).sum := by decide
  have hdescent : baseEnd_880245 < baseStart_880245 := by decide
  rcases family_descends (prefixWord ++ tailWord_880245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880265 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 2, 3, 2]
def baseStart_880265 : Nat := 118140960795 + 880265 * 2 ^ 59
def prefixEnd_880265 : Nat := 4983230072969 + 3 ^ 40 * 880265 * 2
def baseEnd_880265 : Nat := 451999048330103692839241

theorem tailTrace_880265 : CollatzResearch.WordTrace tailWord_880265 prefixEnd_880265 451999048330103692839241 := by
  unfold tailWord_880265
  simp only [CollatzResearch.WordTrace]
  refine ⟨32105902155957717138146249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21403934770638478092097499 32105902155957717138146249)
  ·
    refine ⟨24079426616968287853609687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32105902155957717138146249 24079426616968287853609687)
    ·
      refine ⟨36119139925452431780414531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24079426616968287853609687 36119139925452431780414531)
      ·
        refine ⟨54178709888178647670621797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36119139925452431780414531 54178709888178647670621797)
        ·
          refine ⟨10158508104033496438241587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54178709888178647670621797 10158508104033496438241587)
          ·
            refine ⟨15237762156050244657362381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10158508104033496438241587 15237762156050244657362381)
            ·
              refine ⟨5714160808518841746510893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15237762156050244657362381 5714160808518841746510893)
              ·
                refine ⟨2142810303194565654941585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5714160808518841746510893 2142810303194565654941585)
                ·
                  refine ⟨1607107727395924241206189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2142810303194565654941585 1607107727395924241206189)
                  ·
                    refine ⟨602665397773471590452321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607107727395924241206189 602665397773471590452321)
                    ·
                      refine ⟨451999048330103692839241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602665397773471590452321 451999048330103692839241)
                      ·
                        rfl

theorem cell23_880265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 3, 2].length) (baseStart_880265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880265 prefixEnd_880265 := by exact prefixLift 880265
  have htrace : WordTrace (prefixWord ++ tailWord_880265) baseStart_880265 baseEnd_880265 := by
    simpa [prefixWord, tailWord_880265, baseEnd_880265] using wordTrace_append hprefix tailTrace_880265
  have hstable : (prefixWord ++ tailWord_880265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880265).length < 2 ^ (prefixWord ++ tailWord_880265).sum := by decide
  have hdescent : baseEnd_880265 < baseStart_880265 := by decide
  rcases family_descends (prefixWord ++ tailWord_880265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880289 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_880289 : Nat := 118140960795 + 880289 * 2 ^ 59
def prefixEnd_880289 : Nat := 4983230072969 + 3 ^ 40 * 880289 * 2
def baseEnd_880289 : Nat := 452011371865811598939131

theorem tailTrace_880289 : CollatzResearch.WordTrace tailWord_880289 prefixEnd_880289 452011371865811598939131 := by
  unfold tailWord_880289
  simp only [CollatzResearch.WordTrace]
  refine ⟨32106777507870769237019921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21404518338580512824679947 32106777507870769237019921)
  ·
    refine ⟨24080083130903076927764941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32106777507870769237019921 24080083130903076927764941)
    ·
      refine ⟨9030031174088653847911853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24080083130903076927764941 9030031174088653847911853)
      ·
        refine ⟨3386261690283245192966945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9030031174088653847911853 3386261690283245192966945)
        ·
          refine ⟨2539696267712433894725209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386261690283245192966945 2539696267712433894725209)
          ·
            refine ⟨1904772200784325421043907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2539696267712433894725209 1904772200784325421043907)
            ·
              refine ⟨2857158301176488131565861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904772200784325421043907 2857158301176488131565861)
              ·
                refine ⟨535717181470591524668599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2857158301176488131565861 535717181470591524668599)
                ·
                  refine ⟨803575772205887287002899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 535717181470591524668599 803575772205887287002899)
                  ·
                    refine ⟨1205363658308830930504349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803575772205887287002899 1205363658308830930504349)
                    ·
                      refine ⟨452011371865811598939131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1205363658308830930504349 452011371865811598939131)
                      ·
                        rfl

theorem cell23_880289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_880289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880289 prefixEnd_880289 := by exact prefixLift 880289
  have htrace : WordTrace (prefixWord ++ tailWord_880289) baseStart_880289 baseEnd_880289 := by
    simpa [prefixWord, tailWord_880289, baseEnd_880289] using wordTrace_append hprefix tailTrace_880289
  have hstable : (prefixWord ++ tailWord_880289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880289).length < 2 ^ (prefixWord ++ tailWord_880289).sum := by decide
  have hdescent : baseEnd_880289 < baseStart_880289 := by decide
  rcases family_descends (prefixWord ++ tailWord_880289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880326 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_880326 : Nat := 118140960795 + 880326 * 2 ^ 59
def prefixEnd_880326 : Nat := 4983230072969 + 3 ^ 40 * 880326 * 2
def baseEnd_880326 : Nat := 150676790216675984725487

theorem tailTrace_880326 : CollatzResearch.WordTrace tailWord_880326 prefixEnd_880326 150676790216675984725487 := by
  unfold tailWord_880326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003378969023022642378651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21405418005824483037411221 1003378969023022642378651)
  ·
    refine ⟨1505068453534533963567977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1003378969023022642378651 1505068453534533963567977)
    ·
      refine ⟨1128801340150900472675983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1505068453534533963567977 1128801340150900472675983)
      ·
        refine ⟨1693202010226350709013975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128801340150900472675983 1693202010226350709013975)
        ·
          refine ⟨2539803015339526063520963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693202010226350709013975 2539803015339526063520963)
          ·
            refine ⟨3809704523009289095281445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539803015339526063520963 3809704523009289095281445)
            ·
              refine ⟨714319598064241705365271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3809704523009289095281445 714319598064241705365271)
              ·
                refine ⟨1071479397096362558047907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714319598064241705365271 1071479397096362558047907)
                ·
                  refine ⟨1607219095644543837071861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1071479397096362558047907 1607219095644543837071861)
                  ·
                    refine ⟨150676790216675984725487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1607219095644543837071861 150676790216675984725487)
                    ·
                      rfl

theorem cell23_880326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_880326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880326 prefixEnd_880326 := by exact prefixLift 880326
  have htrace : WordTrace (prefixWord ++ tailWord_880326) baseStart_880326 baseEnd_880326 := by
    simpa [prefixWord, tailWord_880326, baseEnd_880326] using wordTrace_append hprefix tailTrace_880326
  have hstable : (prefixWord ++ tailWord_880326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880326).length < 2 ^ (prefixWord ++ tailWord_880326).sum := by decide
  have hdescent : baseEnd_880326 < baseStart_880326 := by decide
  rcases family_descends (prefixWord ++ tailWord_880326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880359 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_880359 : Nat := 118140960795 + 880359 * 2 ^ 59
def prefixEnd_880359 : Nat := 4983230072969 + 3 ^ 40 * 880359 * 2
def baseEnd_880359 : Nat := 452047315511626325063809

theorem tailTrace_880359 : CollatzResearch.WordTrace tailWord_880359 prefixEnd_880359 452047315511626325063809 := by
  unfold tailWord_880359
  simp only [CollatzResearch.WordTrace]
  refine ⟨32109330617617171192068131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21406220411744780794712087 32109330617617171192068131)
  ·
    refine ⟨48163995926425756788102197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32109330617617171192068131 48163995926425756788102197)
    ·
      refine ⟨4515374618102414698884581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48163995926425756788102197 4515374618102414698884581)
      ·
        refine ⟨846632740894202756040859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4515374618102414698884581 846632740894202756040859)
        ·
          refine ⟨1269949111341304134061289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846632740894202756040859 1269949111341304134061289)
          ·
            refine ⟨952461833505978100545967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269949111341304134061289 952461833505978100545967)
            ·
              refine ⟨1428692750258967150818951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952461833505978100545967 1428692750258967150818951)
              ·
                refine ⟨2143039125388450726228427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428692750258967150818951 2143039125388450726228427)
                ·
                  refine ⟨3214558688082676089342641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143039125388450726228427 3214558688082676089342641)
                  ·
                    refine ⟨2410919016062007067006981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214558688082676089342641 2410919016062007067006981)
                    ·
                      refine ⟨452047315511626325063809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2410919016062007067006981 452047315511626325063809)
                      ·
                        rfl

theorem cell23_880359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_880359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880359 prefixEnd_880359 := by exact prefixLift 880359
  have htrace : WordTrace (prefixWord ++ tailWord_880359) baseStart_880359 baseEnd_880359 := by
    simpa [prefixWord, tailWord_880359, baseEnd_880359] using wordTrace_append hprefix tailTrace_880359
  have hstable : (prefixWord ++ tailWord_880359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880359).length < 2 ^ (prefixWord ++ tailWord_880359).sum := by decide
  have hdescent : baseEnd_880359 < baseStart_880359 := by decide
  rcases family_descends (prefixWord ++ tailWord_880359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880362 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_880362 : Nat := 118140960795 + 880362 * 2 ^ 59
def prefixEnd_880362 : Nat := 4983230072969 + 3 ^ 40 * 880362 * 2
def baseEnd_880362 : Nat := 452048855953589813326295

theorem tailTrace_880362 : CollatzResearch.WordTrace tailWord_880362 prefixEnd_880362 452048855953589813326295 := by
  unfold tailWord_880362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027360009151575676106835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21406293357737535136284893 8027360009151575676106835)
  ·
    refine ⟨12041040013727363514160253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8027360009151575676106835 12041040013727363514160253)
    ·
      refine ⟨4515390005147761317810095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12041040013727363514160253 4515390005147761317810095)
      ·
        refine ⟨6773085007721641976715143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515390005147761317810095 6773085007721641976715143)
        ·
          refine ⟨10159627511582462965072715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773085007721641976715143 10159627511582462965072715)
          ·
            refine ⟨15239441267373694447609073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159627511582462965072715 15239441267373694447609073)
            ·
              refine ⟨11429580950530270835706805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15239441267373694447609073 11429580950530270835706805)
              ·
                refine ⟨1071523214112212890847513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11429580950530270835706805 1071523214112212890847513)
                ·
                  refine ⟨803642410584159668135635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071523214112212890847513 803642410584159668135635)
                  ·
                    refine ⟨1205463615876239502203453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 803642410584159668135635 1205463615876239502203453)
                    ·
                      refine ⟨452048855953589813326295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1205463615876239502203453 452048855953589813326295)
                      ·
                        rfl

theorem cell23_880362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_880362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880362 prefixEnd_880362 := by exact prefixLift 880362
  have htrace : WordTrace (prefixWord ++ tailWord_880362) baseStart_880362 baseEnd_880362 := by
    simpa [prefixWord, tailWord_880362, baseEnd_880362] using wordTrace_append hprefix tailTrace_880362
  have hstable : (prefixWord ++ tailWord_880362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880362).length < 2 ^ (prefixWord ++ tailWord_880362).sum := by decide
  have hdescent : baseEnd_880362 < baseStart_880362 := by decide
  rcases family_descends (prefixWord ++ tailWord_880362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880397 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_880397 : Nat := 118140960795 + 880397 * 2 ^ 59
def prefixEnd_880397 : Nat := 4983230072969 + 3 ^ 40 * 880397 * 2
def baseEnd_880397 : Nat := 452066827776497176388635

theorem tailTrace_880397 : CollatzResearch.WordTrace tailWord_880397 prefixEnd_880397 452066827776497176388635 := by
  unfold tailWord_880397
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110716591479503681951445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21407144394319669121300963 32110716591479503681951445)
  ·
    refine ⟨752594920112800867545737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32110716591479503681951445 752594920112800867545737)
    ·
      refine ⟨564446190084600650659303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752594920112800867545737 564446190084600650659303)
      ·
        refine ⟨846669285126900975988955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564446190084600650659303 846669285126900975988955)
        ·
          refine ⟨1270003927690351463983433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846669285126900975988955 1270003927690351463983433)
          ·
            refine ⟨952502945767763597987575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270003927690351463983433 952502945767763597987575)
            ·
              refine ⟨1428754418651645396981363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952502945767763597987575 1428754418651645396981363)
              ·
                refine ⟨2143131627977468095472045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428754418651645396981363 2143131627977468095472045)
                ·
                  refine ⟨803674360491550535802017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2143131627977468095472045 803674360491550535802017)
                  ·
                    refine ⟨602755770368662901851513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803674360491550535802017 602755770368662901851513)
                    ·
                      refine ⟨452066827776497176388635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602755770368662901851513 452066827776497176388635)
                      ·
                        rfl

theorem cell23_880397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_880397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880397 prefixEnd_880397 := by exact prefixLift 880397
  have htrace : WordTrace (prefixWord ++ tailWord_880397) baseStart_880397 baseEnd_880397 := by
    simpa [prefixWord, tailWord_880397, baseEnd_880397] using wordTrace_append hprefix tailTrace_880397
  have hstable : (prefixWord ++ tailWord_880397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880397).length < 2 ^ (prefixWord ++ tailWord_880397).sum := by decide
  have hdescent : baseEnd_880397 < baseStart_880397 := by decide
  rcases family_descends (prefixWord ++ tailWord_880397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880455 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 2, 5]
def baseStart_880455 : Nat := 118140960795 + 880455 * 2 ^ 59
def prefixEnd_880455 : Nat := 4983230072969 + 3 ^ 40 * 880455 * 2
def baseEnd_880455 : Nat := 150698869884819316487789

theorem tailTrace_880455 : CollatzResearch.WordTrace tailWord_880455 prefixEnd_880455 150698869884819316487789 := by
  unfold tailWord_880455
  simp only [CollatzResearch.WordTrace]
  refine ⟨32112832025269379587562819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21408554683512919725041879 32112832025269379587562819)
  ·
    refine ⟨48169248037904069381344229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32112832025269379587562819 48169248037904069381344229)
    ·
      refine ⟨9031734007107013009002043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48169248037904069381344229 9031734007107013009002043)
      ·
        refine ⟨13547601010660519513503065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031734007107013009002043 13547601010660519513503065)
        ·
          refine ⟨10160700757995389635127299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13547601010660519513503065 10160700757995389635127299)
          ·
            refine ⟨15241051136993084452690949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160700757995389635127299 15241051136993084452690949)
            ·
              refine ⟨2857697088186203334879553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15241051136993084452690949 2857697088186203334879553)
              ·
                refine ⟨2143272816139652501159665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857697088186203334879553 2143272816139652501159665)
                ·
                  refine ⟨1607454612104739375869749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2143272816139652501159665 1607454612104739375869749)
                  ·
                    refine ⟨150698869884819316487789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1607454612104739375869749 150698869884819316487789)
                    ·
                      rfl

theorem cell23_880455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_880455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880455 prefixEnd_880455 := by exact prefixLift 880455
  have htrace : WordTrace (prefixWord ++ tailWord_880455) baseStart_880455 baseEnd_880455 := by
    simpa [prefixWord, tailWord_880455, baseEnd_880455] using wordTrace_append hprefix tailTrace_880455
  have hstable : (prefixWord ++ tailWord_880455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880455).length < 2 ^ (prefixWord ++ tailWord_880455).sum := by decide
  have hdescent : baseEnd_880455 < baseStart_880455 := by decide
  rcases family_descends (prefixWord ++ tailWord_880455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880465 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_880465 : Nat := 118140960795 + 880465 * 2 ^ 59
def prefixEnd_880465 : Nat := 4983230072969 + 3 ^ 40 * 880465 * 2
def baseEnd_880465 : Nat := 452101744461002910338321

theorem tailTrace_880465 : CollatzResearch.WordTrace tailWord_880465 prefixEnd_880465 452101744461002910338321 := by
  unfold tailWord_880465
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113196755233151295426849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21408797836822100863617899 32113196755233151295426849)
  ·
    refine ⟨24084897566424863471570137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32113196755233151295426849 24084897566424863471570137)
    ·
      refine ⟨18063673174818647603677603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24084897566424863471570137 18063673174818647603677603)
      ·
        refine ⟨27095509762227971405516405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18063673174818647603677603 27095509762227971405516405)
        ·
          refine ⟨2540204040208872319267163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27095509762227971405516405 2540204040208872319267163)
          ·
            refine ⟨3810306060313308478900745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540204040208872319267163 3810306060313308478900745)
            ·
              refine ⟨2857729545234981359175559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3810306060313308478900745 2857729545234981359175559)
              ·
                refine ⟨4286594317852472038763339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857729545234981359175559 4286594317852472038763339)
                ·
                  refine ⟨6429891476778708058145009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286594317852472038763339 6429891476778708058145009)
                  ·
                    refine ⟨4822418607584031043608757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429891476778708058145009 4822418607584031043608757)
                    ·
                      refine ⟨452101744461002910338321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4822418607584031043608757 452101744461002910338321)
                      ·
                        rfl

theorem cell23_880465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_880465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880465 prefixEnd_880465 := by exact prefixLift 880465
  have htrace : WordTrace (prefixWord ++ tailWord_880465) baseStart_880465 baseEnd_880465 := by
    simpa [prefixWord, tailWord_880465, baseEnd_880465] using wordTrace_append hprefix tailTrace_880465
  have hstable : (prefixWord ++ tailWord_880465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880465).length < 2 ^ (prefixWord ++ tailWord_880465).sum := by decide
  have hdescent : baseEnd_880465 < baseStart_880465 := by decide
  rcases family_descends (prefixWord ++ tailWord_880465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880492 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_880492 : Nat := 118140960795 + 880492 * 2 ^ 59
def prefixEnd_880492 : Nat := 4983230072969 + 3 ^ 40 * 880492 * 2
def baseEnd_880492 : Nat := 452115608438674304700697

theorem tailTrace_880492 : CollatzResearch.WordTrace tailWord_880492 prefixEnd_880492 452115608438674304700697 := by
  unfold tailWord_880492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16057090763067667453329865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21409454350756889937773153 16057090763067667453329865)
  ·
    refine ⟨12042818072300750589997399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16057090763067667453329865 12042818072300750589997399)
    ·
      refine ⟨18064227108451125884996099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12042818072300750589997399 18064227108451125884996099)
      ·
        refine ⟨27096340662676688827494149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18064227108451125884996099 27096340662676688827494149)
        ·
          refine ⟨5080563874251879155155153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27096340662676688827494149 5080563874251879155155153)
          ·
            refine ⟨3810422905688909366366365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5080563874251879155155153 3810422905688909366366365)
            ·
              refine ⟨1428908589633341012387387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3810422905688909366366365 1428908589633341012387387)
              ·
                refine ⟨2143362884450011518581081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428908589633341012387387 2143362884450011518581081)
                ·
                  refine ⟨1607522163337508638935811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2143362884450011518581081 1607522163337508638935811)
                  ·
                    refine ⟨2411283245006262958403717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1607522163337508638935811 2411283245006262958403717)
                    ·
                      refine ⟨452115608438674304700697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2411283245006262958403717 452115608438674304700697)
                      ·
                        rfl

theorem cell23_880492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_880492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880492 prefixEnd_880492 := by exact prefixLift 880492
  have htrace : WordTrace (prefixWord ++ tailWord_880492) baseStart_880492 baseEnd_880492 := by
    simpa [prefixWord, tailWord_880492, baseEnd_880492] using wordTrace_append hprefix tailTrace_880492
  have hstable : (prefixWord ++ tailWord_880492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880492).length < 2 ^ (prefixWord ++ tailWord_880492).sum := by decide
  have hdescent : baseEnd_880492 < baseStart_880492 := by decide
  rcases family_descends (prefixWord ++ tailWord_880492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880515 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 8]
def baseStart_880515 : Nat := 118140960795 + 880515 * 2 ^ 59
def prefixEnd_880515 : Nat := 4983230072969 + 3 ^ 40 * 880515 * 2
def baseEnd_880515 : Nat := 50236379832636412745899

theorem tailTrace_880515 : CollatzResearch.WordTrace tailWord_880515 prefixEnd_880515 50236379832636412745899 := by
  unfold tailWord_880515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32115020405052009834746999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21410013603368006556497999 32115020405052009834746999)
  ·
    refine ⟨48172530607578014752120499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32115020405052009834746999 48172530607578014752120499)
    ·
      refine ⟨72258795911367022128180749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48172530607578014752120499 72258795911367022128180749)
      ·
        refine ⟨27097048466762633298067781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72258795911367022128180749 27097048466762633298067781)
        ·
          refine ⟨5080696587517993743387709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27097048466762633298067781 5080696587517993743387709)
          ·
            refine ⟨1905261220319247653770391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5080696587517993743387709 1905261220319247653770391)
            ·
              refine ⟨2857891830478871480655587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905261220319247653770391 2857891830478871480655587)
              ·
                refine ⟨4286837745718307220983381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857891830478871480655587 4286837745718307220983381)
                ·
                  refine ⟨50236379832636412745899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4286837745718307220983381 50236379832636412745899)
                  ·
                    rfl

theorem cell23_880515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 8].length) (baseStart_880515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880515 prefixEnd_880515 := by exact prefixLift 880515
  have htrace : WordTrace (prefixWord ++ tailWord_880515) baseStart_880515 baseEnd_880515 := by
    simpa [prefixWord, tailWord_880515, baseEnd_880515] using wordTrace_append hprefix tailTrace_880515
  have hstable : (prefixWord ++ tailWord_880515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880515).length < 2 ^ (prefixWord ++ tailWord_880515).sum := by decide
  have hdescent : baseEnd_880515 < baseStart_880515 := by decide
  rcases family_descends (prefixWord ++ tailWord_880515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880519 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 3, 4]
def baseStart_880519 : Nat := 118140960795 + 880519 * 2 ^ 59
def prefixEnd_880519 : Nat := 4983230072969 + 3 ^ 40 * 880519 * 2
def baseEnd_880519 : Nat := 150709824138781899687691

theorem tailTrace_880519 : CollatzResearch.WordTrace tailWord_880519 prefixEnd_880519 150709824138781899687691 := by
  unfold tailWord_880519
  simp only [CollatzResearch.WordTrace]
  refine ⟨32115166297037518517892611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21410110864691679011928407 32115166297037518517892611)
  ·
    refine ⟨48172749445556277776838917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32115166297037518517892611 48172749445556277776838917)
    ·
      refine ⟨9032390521041802083157297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48172749445556277776838917 9032390521041802083157297)
      ·
        refine ⟨6774292890781351562367973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9032390521041802083157297 6774292890781351562367973)
        ·
          refine ⟨1270179917021503417943995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6774292890781351562367973 1270179917021503417943995)
          ·
            refine ⟨1905269875532255126915993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270179917021503417943995 1905269875532255126915993)
            ·
              refine ⟨1428952406649191345186995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905269875532255126915993 1428952406649191345186995)
              ·
                refine ⟨2143428609973787017780493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428952406649191345186995 2143428609973787017780493)
                ·
                  refine ⟨803785728740170131667685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2143428609973787017780493 803785728740170131667685)
                  ·
                    refine ⟨150709824138781899687691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 803785728740170131667685 150709824138781899687691)
                    ·
                      rfl

theorem cell23_880519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_880519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880519 prefixEnd_880519 := by exact prefixLift 880519
  have htrace : WordTrace (prefixWord ++ tailWord_880519) baseStart_880519 baseEnd_880519 := by
    simpa [prefixWord, tailWord_880519, baseEnd_880519] using wordTrace_append hprefix tailTrace_880519
  have hstable : (prefixWord ++ tailWord_880519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880519).length < 2 ^ (prefixWord ++ tailWord_880519).sum := by decide
  have hdescent : baseEnd_880519 < baseStart_880519 := by decide
  rcases family_descends (prefixWord ++ tailWord_880519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880569 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 2, 3, 2]
def baseStart_880569 : Nat := 118140960795 + 880569 * 2 ^ 59
def prefixEnd_880569 : Nat := 4983230072969 + 3 ^ 40 * 880569 * 2
def baseEnd_880569 : Nat := 452155146449070503437843

theorem tailTrace_880569 : CollatzResearch.WordTrace tailWord_880569 prefixEnd_880569 452155146449070503437843 := by
  unfold tailWord_880569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32116989946856377057212761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21411326631237584704808507 32116989946856377057212761)
  ·
    refine ⟨24087742460142282792909571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32116989946856377057212761 24087742460142282792909571)
    ·
      refine ⟨36131613690213424189364357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24087742460142282792909571 36131613690213424189364357)
      ·
        refine ⟨6774677566915017035505817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36131613690213424189364357 6774677566915017035505817)
        ·
          refine ⟨5081008175186262776629363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6774677566915017035505817 5081008175186262776629363)
          ·
            refine ⟨7621512262779394164944045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081008175186262776629363 7621512262779394164944045)
            ·
              refine ⟨2858067098542272811854017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7621512262779394164944045 2858067098542272811854017)
              ·
                refine ⟨2143550323906704608890513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858067098542272811854017 2143550323906704608890513)
                ·
                  refine ⟨1607662742930028456667885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2143550323906704608890513 1607662742930028456667885)
                  ·
                    refine ⟨602873528598760671250457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1607662742930028456667885 602873528598760671250457)
                    ·
                      refine ⟨452155146449070503437843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602873528598760671250457 452155146449070503437843)
                      ·
                        rfl

theorem cell23_880569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_880569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880569 prefixEnd_880569 := by exact prefixLift 880569
  have htrace : WordTrace (prefixWord ++ tailWord_880569) baseStart_880569 baseEnd_880569 := by
    simpa [prefixWord, tailWord_880569, baseEnd_880569] using wordTrace_append hprefix tailTrace_880569
  have hstable : (prefixWord ++ tailWord_880569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880569).length < 2 ^ (prefixWord ++ tailWord_880569).sum := by decide
  have hdescent : baseEnd_880569 < baseStart_880569 := by decide
  rcases family_descends (prefixWord ++ tailWord_880569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880599 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 5, 2, 2]
def baseStart_880599 : Nat := 118140960795 + 880599 * 2 ^ 59
def prefixEnd_880599 : Nat := 4983230072969 + 3 ^ 40 * 880599 * 2
def baseEnd_880599 : Nat := 452170550868705386062705

theorem tailTrace_880599 : CollatzResearch.WordTrace tailWord_880599 prefixEnd_880599 452170550868705386062705 := by
  unfold tailWord_880599
  simp only [CollatzResearch.WordTrace]
  refine ⟨32118084136747692180804851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21412056091165128120536567 32118084136747692180804851)
  ·
    refine ⟨48177126205121538271207277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32118084136747692180804851 48177126205121538271207277)
    ·
      refine ⟨18066422326920576851702729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48177126205121538271207277 18066422326920576851702729)
      ·
        refine ⟨13549816745190432638777047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18066422326920576851702729 13549816745190432638777047)
        ·
          refine ⟨20324725117785648958165571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549816745190432638777047 20324725117785648958165571)
          ·
            refine ⟨30487087676678473437248357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324725117785648958165571 30487087676678473437248357)
            ·
              refine ⟨5716328939377213769484067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30487087676678473437248357 5716328939377213769484067)
              ·
                refine ⟨8574493409065820654226101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716328939377213769484067 8574493409065820654226101)
                ·
                  refine ⟨803858757099920686333697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8574493409065820654226101 803858757099920686333697)
                  ·
                    refine ⟨602894067824940514750273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 803858757099920686333697 602894067824940514750273)
                    ·
                      refine ⟨452170550868705386062705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 602894067824940514750273 452170550868705386062705)
                      ·
                        rfl

theorem cell23_880599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_880599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880599 prefixEnd_880599 := by exact prefixLift 880599
  have htrace : WordTrace (prefixWord ++ tailWord_880599) baseStart_880599 baseEnd_880599 := by
    simpa [prefixWord, tailWord_880599, baseEnd_880599] using wordTrace_append hprefix tailTrace_880599
  have hstable : (prefixWord ++ tailWord_880599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880599).length < 2 ^ (prefixWord ++ tailWord_880599).sum := by decide
  have hdescent : baseEnd_880599 < baseStart_880599 := by decide
  rcases family_descends (prefixWord ++ tailWord_880599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880612 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_880612 : Nat := 118140960795 + 880612 * 2 ^ 59
def prefixEnd_880612 : Nat := 4983230072969 + 3 ^ 40 * 880612 * 2
def baseEnd_880612 : Nat := 452177226117213835200145

theorem tailTrace_880612 : CollatzResearch.WordTrace tailWord_880612 prefixEnd_880612 452177226117213835200145 := by
  unfold tailWord_880612
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059279142850297700514045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21412372190467063600685393 16059279142850297700514045)
  ·
    refine ⟨6022229678568861637692767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16059279142850297700514045 6022229678568861637692767)
    ·
      refine ⟨9033344517853292456539151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6022229678568861637692767 9033344517853292456539151)
      ·
        refine ⟨13550016776779938684808727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033344517853292456539151 13550016776779938684808727)
        ·
          refine ⟨20325025165169908027213091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13550016776779938684808727 20325025165169908027213091)
          ·
            refine ⟨30487537747754862040819637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20325025165169908027213091 30487537747754862040819637)
            ·
              refine ⟨2858206663852018316326841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30487537747754862040819637 2858206663852018316326841)
              ·
                refine ⟨2143654997889013737245131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858206663852018316326841 2143654997889013737245131)
                ·
                  refine ⟨3215482496833520605867697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143654997889013737245131 3215482496833520605867697)
                  ·
                    refine ⟨2411611872625140454400773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3215482496833520605867697 2411611872625140454400773)
                    ·
                      refine ⟨452177226117213835200145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2411611872625140454400773 452177226117213835200145)
                      ·
                        rfl

theorem cell23_880612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_880612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_880612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_880612 prefixEnd_880612 := by exact prefixLift 880612
  have htrace : WordTrace (prefixWord ++ tailWord_880612) baseStart_880612 baseEnd_880612 := by
    simpa [prefixWord, tailWord_880612, baseEnd_880612] using wordTrace_append hprefix tailTrace_880612
  have hstable : (prefixWord ++ tailWord_880612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880612).length < 2 ^ (prefixWord ++ tailWord_880612).sum := by decide
  have hdescent : baseEnd_880612 < baseStart_880612 := by decide
  rcases family_descends (prefixWord ++ tailWord_880612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
