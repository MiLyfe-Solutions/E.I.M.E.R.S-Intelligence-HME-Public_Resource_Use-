import V185TrunkScan23Chunk0145

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_862920 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_862920 : Nat := 118140960795 + 862920 * 2 ^ 59
def prefixEnd_862920 : Nat := 4983230072969 + 3 ^ 40 * 862920 * 2
def baseEnd_862920 : Nat := 443092726377869055231509

theorem tailTrace_862920 : CollatzResearch.WordTrace tailWord_862920 prefixEnd_862920 443092726377869055231509 := by
  unfold tailWord_862920
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736639016897844923993107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20982185355863793231990809 15736639016897844923993107)
  ·
    refine ⟨23604958525346767385989661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15736639016897844923993107 23604958525346767385989661)
    ·
      refine ⟨8851859447005037769746123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23604958525346767385989661 8851859447005037769746123)
      ·
        refine ⟨13277789170507556654619185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851859447005037769746123 13277789170507556654619185)
        ·
          refine ⟨9958341877880667490964389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13277789170507556654619185 9958341877880667490964389)
          ·
            refine ⟨1867189102102625154555823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9958341877880667490964389 1867189102102625154555823)
            ·
              refine ⟨2800783653153937731833735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867189102102625154555823 2800783653153937731833735)
              ·
                refine ⟨4201175479730906597750603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800783653153937731833735 4201175479730906597750603)
                ·
                  refine ⟨6301763219596359896625905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201175479730906597750603 6301763219596359896625905)
                  ·
                    refine ⟨4726322414697269922469429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6301763219596359896625905 4726322414697269922469429)
                    ·
                      refine ⟨443092726377869055231509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4726322414697269922469429 443092726377869055231509)
                      ·
                        rfl

theorem cell23_862920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_862920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862920 prefixEnd_862920 := by exact prefixLift 862920
  have htrace : WordTrace (prefixWord ++ tailWord_862920) baseStart_862920 baseEnd_862920 := by
    simpa [prefixWord, tailWord_862920, baseEnd_862920] using wordTrace_append hprefix tailTrace_862920
  have hstable : (prefixWord ++ tailWord_862920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862920).length < 2 ^ (prefixWord ++ tailWord_862920).sum := by decide
  have hdescent : baseEnd_862920 < baseStart_862920 := by decide
  rcases family_descends (prefixWord ++ tailWord_862920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862947 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4]
def baseStart_862947 : Nat := 118140960795 + 862947 * 2 ^ 59
def prefixEnd_862947 : Nat := 4983230072969 + 3 ^ 40 * 862947 * 2
def baseEnd_862947 : Nat := 443106590355540449593885

theorem tailTrace_862947 : CollatzResearch.WordTrace tailWord_862947 prefixEnd_862947 443106590355540449593885 := by
  unfold tailWord_862947
  simp only [CollatzResearch.WordTrace]
  refine ⟨31474262804697873459219095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20982841869798582306146063 31474262804697873459219095)
  ·
    refine ⟨47211394207046810188828643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31474262804697873459219095 47211394207046810188828643)
    ·
      refine ⟨70817091310570215283242965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47211394207046810188828643 70817091310570215283242965)
      ·
        refine ⟨1659775577591489420701007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 70817091310570215283242965 1659775577591489420701007)
        ·
          refine ⟨2489663366387234131051511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659775577591489420701007 2489663366387234131051511)
          ·
            refine ⟨3734495049580851196577267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489663366387234131051511 3734495049580851196577267)
            ·
              refine ⟨5601742574371276794865901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734495049580851196577267 5601742574371276794865901)
              ·
                refine ⟨2100653465389228798074713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5601742574371276794865901 2100653465389228798074713)
                ·
                  refine ⟨1575490099041921598556035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100653465389228798074713 1575490099041921598556035)
                  ·
                    refine ⟨2363235148562882397834053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1575490099041921598556035 2363235148562882397834053)
                    ·
                      refine ⟨443106590355540449593885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2363235148562882397834053 443106590355540449593885)
                      ·
                        rfl

theorem cell23_862947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_862947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862947 prefixEnd_862947 := by exact prefixLift 862947
  have htrace : WordTrace (prefixWord ++ tailWord_862947) baseStart_862947 baseEnd_862947 := by
    simpa [prefixWord, tailWord_862947, baseEnd_862947] using wordTrace_append hprefix tailTrace_862947
  have hstable : (prefixWord ++ tailWord_862947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862947).length < 2 ^ (prefixWord ++ tailWord_862947).sum := by decide
  have hdescent : baseEnd_862947 < baseStart_862947 := by decide
  rcases family_descends (prefixWord ++ tailWord_862947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862953 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 10]
def baseStart_862953 : Nat := 118140960795 + 862953 * 2 ^ 59
def prefixEnd_862953 : Nat := 4983230072969 + 3 ^ 40 * 862953 * 2
def baseEnd_862953 : Nat := 49234407915496380679873

theorem tailTrace_862953 : CollatzResearch.WordTrace tailWord_862953 prefixEnd_862953 49234407915496380679873 := by
  unfold tailWord_862953
  simp only [CollatzResearch.WordTrace]
  refine ⟨31474481642676136483937513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20982987761784090989291675 31474481642676136483937513)
  ·
    refine ⟨23605861232007102362953135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31474481642676136483937513 23605861232007102362953135)
    ·
      refine ⟨35408791848010653544429703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23605861232007102362953135 35408791848010653544429703)
      ·
        refine ⟨53113187772015980316644555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35408791848010653544429703 53113187772015980316644555)
        ·
          refine ⟨79669781658023970474966833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53113187772015980316644555 79669781658023970474966833)
          ·
            refine ⟨59752336243517977856225125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79669781658023970474966833 59752336243517977856225125)
            ·
              refine ⟨11203563045659620848042211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59752336243517977856225125 11203563045659620848042211)
              ·
                refine ⟨16805344568489431272063317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11203563045659620848042211 16805344568489431272063317)
                ·
                  refine ⟨49234407915496380679873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16805344568489431272063317 49234407915496380679873)
                  ·
                    rfl

theorem cell23_862953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_862953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862953 prefixEnd_862953 := by exact prefixLift 862953
  have htrace : WordTrace (prefixWord ++ tailWord_862953) baseStart_862953 baseEnd_862953 := by
    simpa [prefixWord, tailWord_862953, baseEnd_862953] using wordTrace_append hprefix tailTrace_862953
  have hstable : (prefixWord ++ tailWord_862953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862953).length < 2 ^ (prefixWord ++ tailWord_862953).sum := by decide
  have hdescent : baseEnd_862953 < baseStart_862953 := by decide
  rcases family_descends (prefixWord ++ tailWord_862953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862965 : List Nat := [1, 3, 6, 1, 1, 2, 2, 2, 5]
def baseStart_862965 : Nat := 118140960795 + 862965 * 2 ^ 59
def prefixEnd_862965 : Nat := 4983230072969 + 3 ^ 40 * 862965 * 2
def baseEnd_862965 : Nat := 49235092556369042129867

theorem tailTrace_862965 : CollatzResearch.WordTrace tailWord_862965 prefixEnd_862965 49235092556369042129867 := by
  unfold tailWord_862965
  simp only [CollatzResearch.WordTrace]
  refine ⟨31474919318632662533374349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20983279545755108355582899 31474919318632662533374349)
  ·
    refine ⟨11803094744487248450015381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31474919318632662533374349 11803094744487248450015381)
    ·
      refine ⟨553270066147839771094471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11803094744487248450015381 553270066147839771094471)
      ·
        refine ⟨829905099221759656641707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553270066147839771094471 829905099221759656641707)
        ·
          refine ⟨1244857648832639484962561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829905099221759656641707 1244857648832639484962561)
          ·
            refine ⟨933643236624479613721921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244857648832639484962561 933643236624479613721921)
            ·
              refine ⟨700232427468359710291441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933643236624479613721921 700232427468359710291441)
              ·
                refine ⟨525174320601269782718581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700232427468359710291441 525174320601269782718581)
                ·
                  refine ⟨49235092556369042129867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525174320601269782718581 49235092556369042129867)
                  ·
                    rfl

theorem cell23_862965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_862965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862965 prefixEnd_862965 := by exact prefixLift 862965
  have htrace : WordTrace (prefixWord ++ tailWord_862965) baseStart_862965 baseEnd_862965 := by
    simpa [prefixWord, tailWord_862965, baseEnd_862965] using wordTrace_append hprefix tailTrace_862965
  have hstable : (prefixWord ++ tailWord_862965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862965).length < 2 ^ (prefixWord ++ tailWord_862965).sum := by decide
  have hdescent : baseEnd_862965 < baseStart_862965 := by decide
  rcases family_descends (prefixWord ++ tailWord_862965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862970 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_862970 : Nat := 118140960795 + 862970 * 2 ^ 59
def prefixEnd_862970 : Nat := 4983230072969 + 3 ^ 40 * 862970 * 2
def baseEnd_862970 : Nat := 49235377823399317734031

theorem tailTrace_862970 : CollatzResearch.WordTrace tailWord_862970 prefixEnd_862970 49235377823399317734031 := by
  unfold tailWord_862970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868775420903637096826591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20983401122409698924870909 7868775420903637096826591)
  ·
    refine ⟨11803163131355455645239887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7868775420903637096826591 11803163131355455645239887)
    ·
      refine ⟨17704744697033183467859831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11803163131355455645239887 17704744697033183467859831)
      ·
        refine ⟨26557117045549775201789747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17704744697033183467859831 26557117045549775201789747)
        ·
          refine ⟨39835675568324662802684621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26557117045549775201789747 39835675568324662802684621)
          ·
            refine ⟨14938378338121748551006733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39835675568324662802684621 14938378338121748551006733)
            ·
              refine ⟨5601891876795655706627525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14938378338121748551006733 5601891876795655706627525)
              ·
                refine ⟨1050354726899185444992661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5601891876795655706627525 1050354726899185444992661)
                ·
                  refine ⟨49235377823399317734031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1050354726899185444992661 49235377823399317734031)
                  ·
                    rfl

theorem cell23_862970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_862970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_862970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_862970 prefixEnd_862970 := by exact prefixLift 862970
  have htrace : WordTrace (prefixWord ++ tailWord_862970) baseStart_862970 baseEnd_862970 := by
    simpa [prefixWord, tailWord_862970, baseEnd_862970] using wordTrace_append hprefix tailTrace_862970
  have hstable : (prefixWord ++ tailWord_862970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862970).length < 2 ^ (prefixWord ++ tailWord_862970).sum := by decide
  have hdescent : baseEnd_862970 < baseStart_862970 := by decide
  rcases family_descends (prefixWord ++ tailWord_862970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863094 : List Nat := [5, 1, 1, 3, 1, 2, 2, 8]
def baseStart_863094 : Nat := 118140960795 + 863094 * 2 ^ 59
def prefixEnd_863094 : Nat := 4983230072969 + 3 ^ 40 * 863094 * 2
def baseEnd_863094 : Nat := 16414150815250050905767

theorem tailTrace_863094 : CollatzResearch.WordTrace tailWord_863094 prefixEnd_863094 16414150815250050905767 := by
  unfold tailWord_863094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967476520947832347801271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20986416223443545043213557 1967476520947832347801271)
  ·
    refine ⟨2951214781421748521701907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967476520947832347801271 2951214781421748521701907)
    ·
      refine ⟨4426822172132622782552861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951214781421748521701907 4426822172132622782552861)
      ·
        refine ⟨1660058314549733543457323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4426822172132622782552861 1660058314549733543457323)
        ·
          refine ⟨2490087471824600315185985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660058314549733543457323 2490087471824600315185985)
          ·
            refine ⟨1867565603868450236389489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490087471824600315185985 1867565603868450236389489)
            ·
              refine ⟨1400674202901337677292117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867565603868450236389489 1400674202901337677292117)
              ·
                refine ⟨16414150815250050905767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1400674202901337677292117 16414150815250050905767)
                ·
                  rfl

theorem cell23_863094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_863094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863094 prefixEnd_863094 := by exact prefixLift 863094
  have htrace : WordTrace (prefixWord ++ tailWord_863094) baseStart_863094 baseEnd_863094 := by
    simpa [prefixWord, tailWord_863094, baseEnd_863094] using wordTrace_append hprefix tailTrace_863094
  have hstable : (prefixWord ++ tailWord_863094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863094).length < 2 ^ (prefixWord ++ tailWord_863094).sum := by decide
  have hdescent : baseEnd_863094 < baseStart_863094 := by decide
  rcases family_descends (prefixWord ++ tailWord_863094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863138 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_863138 : Nat := 118140960795 + 863138 * 2 ^ 59
def prefixEnd_863138 : Nat := 4983230072969 + 3 ^ 40 * 863138 * 2
def baseEnd_863138 : Nat := 443204665160549202305507

theorem tailTrace_863138 : CollatzResearch.WordTrace tailWord_863138 prefixEnd_863138 443204665160549202305507 := by
  unfold tailWord_863138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870307286751478269855517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20987486098003942052948045 7870307286751478269855517)
  ·
    refine ⟨2951365232531804351195819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7870307286751478269855517 2951365232531804351195819)
    ·
      refine ⟨4427047848797706526793729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951365232531804351195819 4427047848797706526793729)
      ·
        refine ⟨3320285886598279895095297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4427047848797706526793729 3320285886598279895095297)
        ·
          refine ⟨2490214414948709921321473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320285886598279895095297 2490214414948709921321473)
          ·
            refine ⟨1867660811211532440991105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490214414948709921321473 1867660811211532440991105)
            ·
              refine ⟨1400745608408649330743329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867660811211532440991105 1400745608408649330743329)
              ·
                refine ⟨1050559206306486998057497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400745608408649330743329 1050559206306486998057497)
                ·
                  refine ⟨787919404729865248543123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050559206306486998057497 787919404729865248543123)
                  ·
                    refine ⟨1181879107094797872814685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 787919404729865248543123 1181879107094797872814685)
                    ·
                      refine ⟨443204665160549202305507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181879107094797872814685 443204665160549202305507)
                      ·
                        rfl

theorem cell23_863138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_863138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863138 prefixEnd_863138 := by exact prefixLift 863138
  have htrace : WordTrace (prefixWord ++ tailWord_863138) baseStart_863138 baseEnd_863138 := by
    simpa [prefixWord, tailWord_863138, baseEnd_863138] using wordTrace_append hprefix tailTrace_863138
  have hstable : (prefixWord ++ tailWord_863138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863138).length < 2 ^ (prefixWord ++ tailWord_863138).sum := by decide
  have hdescent : baseEnd_863138 < baseStart_863138 := by decide
  rcases family_descends (prefixWord ++ tailWord_863138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863161 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 1, 4, 2]
def baseStart_863161 : Nat := 118140960795 + 863161 * 2 ^ 59
def prefixEnd_863161 : Nat := 4983230072969 + 3 ^ 40 * 863161 * 2
def baseEnd_863161 : Nat := 443216475215602612317901

theorem tailTrace_863161 : CollatzResearch.WordTrace tailWord_863161 prefixEnd_863161 443216475215602612317901 := by
  unfold tailWord_863161
  simp only [CollatzResearch.WordTrace]
  refine ⟨31482068025922588007509337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20988045350615058671672891 31482068025922588007509337)
  ·
    refine ⟨23611551019441941005632003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31482068025922588007509337 23611551019441941005632003)
    ·
      refine ⟨35417326529162911508448005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23611551019441941005632003 35417326529162911508448005)
      ·
        refine ⟨6640748724218045907834001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35417326529162911508448005 6640748724218045907834001)
        ·
          refine ⟨4980561543163534430875501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640748724218045907834001 4980561543163534430875501)
          ·
            refine ⟨1867710578686325411578313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4980561543163534430875501 1867710578686325411578313)
            ·
              refine ⟨1400782934014744058683735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867710578686325411578313 1400782934014744058683735)
              ·
                refine ⟨2101174401022116088025603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400782934014744058683735 2101174401022116088025603)
                ·
                  refine ⟨3151761601533174132038405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101174401022116088025603 3151761601533174132038405)
                  ·
                    refine ⟨590955300287470149757201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151761601533174132038405 590955300287470149757201)
                    ·
                      refine ⟨443216475215602612317901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590955300287470149757201 443216475215602612317901)
                      ·
                        rfl

theorem cell23_863161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_863161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863161 prefixEnd_863161 := by exact prefixLift 863161
  have htrace : WordTrace (prefixWord ++ tailWord_863161) baseStart_863161 baseEnd_863161 := by
    simpa [prefixWord, tailWord_863161, baseEnd_863161] using wordTrace_append hprefix tailTrace_863161
  have hstable : (prefixWord ++ tailWord_863161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863161).length < 2 ^ (prefixWord ++ tailWord_863161).sum := by decide
  have hdescent : baseEnd_863161 < baseStart_863161 := by decide
  rcases family_descends (prefixWord ++ tailWord_863161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863177 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_863177 : Nat := 118140960795 + 863177 * 2 ^ 59
def prefixEnd_863177 : Nat := 4983230072969 + 3 ^ 40 * 863177 * 2
def baseEnd_863177 : Nat := 443224690906074549717827

theorem tailTrace_863177 : CollatzResearch.WordTrace tailWord_863177 prefixEnd_863177 443224690906074549717827 := by
  unfold tailWord_863177
  simp only [CollatzResearch.WordTrace]
  refine ⟨31482651593864622740091785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20988434395909748493394523 31482651593864622740091785)
  ·
    refine ⟨23611988695398467055068839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31482651593864622740091785 23611988695398467055068839)
    ·
      refine ⟨35417983043097700582603259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23611988695398467055068839 35417983043097700582603259)
      ·
        refine ⟨53126974564646550873904889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35417983043097700582603259 53126974564646550873904889)
        ·
          refine ⟨39845230923484913155428667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53126974564646550873904889 39845230923484913155428667)
          ·
            refine ⟨59767846385227369733143001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39845230923484913155428667 59767846385227369733143001)
            ·
              refine ⟨44825884788920527299857251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59767846385227369733143001 44825884788920527299857251)
              ·
                refine ⟨67238827183380790949785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44825884788920527299857251 67238827183380790949785877)
                ·
                  refine ⟨3151820024220974575771213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67238827183380790949785877 3151820024220974575771213)
                  ·
                    refine ⟨1181932509082865465914205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151820024220974575771213 1181932509082865465914205)
                    ·
                      refine ⟨443224690906074549717827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181932509082865465914205 443224690906074549717827)
                      ·
                        rfl

theorem cell23_863177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_863177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863177 prefixEnd_863177 := by exact prefixLift 863177
  have htrace : WordTrace (prefixWord ++ tailWord_863177) baseStart_863177 baseEnd_863177 := by
    simpa [prefixWord, tailWord_863177, baseEnd_863177] using wordTrace_append hprefix tailTrace_863177
  have hstable : (prefixWord ++ tailWord_863177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863177).length < 2 ^ (prefixWord ++ tailWord_863177).sum := by decide
  have hdescent : baseEnd_863177 < baseStart_863177 := by decide
  rcases family_descends (prefixWord ++ tailWord_863177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863194 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_863194 : Nat := 118140960795 + 863194 * 2 ^ 59
def prefixEnd_863194 : Nat := 4983230072969 + 3 ^ 40 * 863194 * 2
def baseEnd_863194 : Nat := 443233420077200983205249

theorem tailTrace_863194 : CollatzResearch.WordTrace tailWord_863194 prefixEnd_863194 443233420077200983205249 := by
  unfold tailWord_863194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870817908700758660865159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20988847756535356428973757 7870817908700758660865159)
  ·
    refine ⟨11806226863051137991297739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7870817908700758660865159 11806226863051137991297739)
    ·
      refine ⟨17709340294576706986946609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11806226863051137991297739 17709340294576706986946609)
      ·
        refine ⟨13282005220932530240209957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17709340294576706986946609 13282005220932530240209957)
        ·
          refine ⟨2490375978924849420039367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13282005220932530240209957 2490375978924849420039367)
          ·
            refine ⟨3735563968387274130059051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490375978924849420039367 3735563968387274130059051)
            ·
              refine ⟨5603345952580911195088577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735563968387274130059051 5603345952580911195088577)
              ·
                refine ⟨4202509464435683396316433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603345952580911195088577 4202509464435683396316433)
                ·
                  refine ⟨3151882098326762547237325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202509464435683396316433 3151882098326762547237325)
                  ·
                    refine ⟨1181955786872535955213997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151882098326762547237325 1181955786872535955213997)
                    ·
                      refine ⟨443233420077200983205249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1181955786872535955213997 443233420077200983205249)
                      ·
                        rfl

theorem cell23_863194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_863194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863194 prefixEnd_863194 := by exact prefixLift 863194
  have htrace : WordTrace (prefixWord ++ tailWord_863194) baseStart_863194 baseEnd_863194 := by
    simpa [prefixWord, tailWord_863194, baseEnd_863194] using wordTrace_append hprefix tailTrace_863194
  have hstable : (prefixWord ++ tailWord_863194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863194).length < 2 ^ (prefixWord ++ tailWord_863194).sum := by decide
  have hdescent : baseEnd_863194 < baseStart_863194 := by decide
  rcases family_descends (prefixWord ++ tailWord_863194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863204 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_863204 : Nat := 118140960795 + 863204 * 2 ^ 59
def prefixEnd_863204 : Nat := 4983230072969 + 3 ^ 40 * 863204 * 2
def baseEnd_863204 : Nat := 443238554883745944080203

theorem tailTrace_863204 : CollatzResearch.WordTrace tailWord_863204 prefixEnd_863204 443238554883745944080203 := by
  unfold tailWord_863204
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741818182383403175662333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20989090909844537567549777 15741818182383403175662333)
  ·
    refine ⟨5903181818393776190873375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15741818182383403175662333 5903181818393776190873375)
    ·
      refine ⟨8854772727590664286310063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903181818393776190873375 8854772727590664286310063)
      ·
        refine ⟨13282159091385996429465095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854772727590664286310063 13282159091385996429465095)
        ·
          refine ⟨19923238637078994644197643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13282159091385996429465095 19923238637078994644197643)
          ·
            refine ⟨29884857955618491966296465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19923238637078994644197643 29884857955618491966296465)
            ·
              refine ⟨22413643466713868974722349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29884857955618491966296465 22413643466713868974722349)
              ·
                refine ⟨8405116300017700865520881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22413643466713868974722349 8405116300017700865520881)
                ·
                  refine ⟨6303837225013275649140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405116300017700865520881 6303837225013275649140661)
                  ·
                    refine ⟨590984739844994592106937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6303837225013275649140661 590984739844994592106937)
                    ·
                      refine ⟨443238554883745944080203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 590984739844994592106937 443238554883745944080203)
                      ·
                        rfl

theorem cell23_863204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_863204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863204 prefixEnd_863204 := by exact prefixLift 863204
  have htrace : WordTrace (prefixWord ++ tailWord_863204) baseStart_863204 baseEnd_863204 := by
    simpa [prefixWord, tailWord_863204, baseEnd_863204] using wordTrace_append hprefix tailTrace_863204
  have hstable : (prefixWord ++ tailWord_863204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863204).length < 2 ^ (prefixWord ++ tailWord_863204).sum := by decide
  have hdescent : baseEnd_863204 < baseStart_863204 := by decide
  rcases family_descends (prefixWord ++ tailWord_863204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863257 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 8]
def baseStart_863257 : Nat := 118140960795 + 863257 * 2 ^ 59
def prefixEnd_863257 : Nat := 4983230072969 + 3 ^ 40 * 863257 * 2
def baseEnd_863257 : Nat := 49251752150937137413051

theorem tailTrace_863257 : CollatzResearch.WordTrace tailWord_863257 prefixEnd_863257 49251752150937137413051 := by
  unfold tailWord_863257
  simp only [CollatzResearch.WordTrace]
  refine ⟨31485569433574796403004025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20990379622383197602002683 31485569433574796403004025)
  ·
    refine ⟨23614177075181097302253019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31485569433574796403004025 23614177075181097302253019)
    ·
      refine ⟨35421265612771645953379529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23614177075181097302253019 35421265612771645953379529)
      ·
        refine ⟨26565949209578734465034647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35421265612771645953379529 26565949209578734465034647)
        ·
          refine ⟨39848923814368101697551971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26565949209578734465034647 39848923814368101697551971)
          ·
            refine ⟨59773385721552152546327957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39848923814368101697551971 59773385721552152546327957)
            ·
              refine ⟨2801877455697757150609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59773385721552152546327957 2801877455697757150609123)
              ·
                refine ⟨4202816183546635725913685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801877455697757150609123 4202816183546635725913685)
                ·
                  refine ⟨49251752150937137413051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4202816183546635725913685 49251752150937137413051)
                  ·
                    rfl

theorem cell23_863257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_863257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863257 prefixEnd_863257 := by exact prefixLift 863257
  have htrace : WordTrace (prefixWord ++ tailWord_863257) baseStart_863257 baseEnd_863257 := by
    simpa [prefixWord, tailWord_863257, baseEnd_863257] using wordTrace_append hprefix tailTrace_863257
  have hstable : (prefixWord ++ tailWord_863257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863257).length < 2 ^ (prefixWord ++ tailWord_863257).sum := by decide
  have hdescent : baseEnd_863257 < baseStart_863257 := by decide
  rcases family_descends (prefixWord ++ tailWord_863257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863341 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_863341 : Nat := 118140960795 + 863341 * 2 ^ 59
def prefixEnd_863341 : Nat := 4983230072969 + 3 ^ 40 * 863341 * 2
def baseEnd_863341 : Nat := 443308901733411908067073

theorem tailTrace_863341 : CollatzResearch.WordTrace tailWord_863341 prefixEnd_863341 443308901733411908067073 := by
  unfold tailWord_863341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31488633165270478749061877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20992422110180319166041251 31488633165270478749061877)
  ·
    refine ⟨2952059359244107382724551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31488633165270478749061877 2952059359244107382724551)
    ·
      refine ⟨4428089038866161074086827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2952059359244107382724551 4428089038866161074086827)
      ·
        refine ⟨6642133558299241611130241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4428089038866161074086827 6642133558299241611130241)
        ·
          refine ⟨4981600168724431208347681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6642133558299241611130241 4981600168724431208347681)
          ·
            refine ⟨3736200126543323406260761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4981600168724431208347681 3736200126543323406260761)
            ·
              refine ⟨2802150094907492554695571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3736200126543323406260761 2802150094907492554695571)
              ·
                refine ⟨4203225142361238832043357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802150094907492554695571 4203225142361238832043357)
                ·
                  refine ⟨1576209428385464562016259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4203225142361238832043357 1576209428385464562016259)
                  ·
                    refine ⟨2364314142578196843024389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576209428385464562016259 2364314142578196843024389)
                    ·
                      refine ⟨443308901733411908067073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2364314142578196843024389 443308901733411908067073)
                      ·
                        rfl

theorem cell23_863341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_863341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863341 prefixEnd_863341 := by exact prefixLift 863341
  have htrace : WordTrace (prefixWord ++ tailWord_863341) baseStart_863341 baseEnd_863341 := by
    simpa [prefixWord, tailWord_863341, baseEnd_863341] using wordTrace_append hprefix tailTrace_863341
  have hstable : (prefixWord ++ tailWord_863341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863341).length < 2 ^ (prefixWord ++ tailWord_863341).sum := by decide
  have hdescent : baseEnd_863341 < baseStart_863341 := by decide
  rcases family_descends (prefixWord ++ tailWord_863341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863364 : List Nat := [2, 3, 2, 1, 2, 3, 10]
def baseStart_863364 : Nat := 118140960795 + 863364 * 2 ^ 59
def prefixEnd_863364 : Nat := 4983230072969 + 3 ^ 40 * 863364 * 2
def baseEnd_863364 : Nat := 5473095207265003926907

theorem tailTrace_863364 : CollatzResearch.WordTrace tailWord_863364 prefixEnd_863364 5473095207265003926907 := by
  unfold tailWord_863364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744736022093576838574573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20992981362791435784766097 15744736022093576838574573)
  ·
    refine ⟨5904276008285091314465465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15744736022093576838574573 5904276008285091314465465)
    ·
      refine ⟨4428207006213818485849099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5904276008285091314465465 4428207006213818485849099)
      ·
        refine ⟨6642310509320727728773649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4428207006213818485849099 6642310509320727728773649)
        ·
          refine ⟨4981732881990545796580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6642310509320727728773649 4981732881990545796580237)
          ·
            refine ⟨1868149830746454673717589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4981732881990545796580237 1868149830746454673717589)
            ·
              refine ⟨5473095207265003926907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1868149830746454673717589 5473095207265003926907)
              ·
                rfl

theorem cell23_863364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 10].length) (baseStart_863364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863364 prefixEnd_863364 := by exact prefixLift 863364
  have htrace : WordTrace (prefixWord ++ tailWord_863364) baseStart_863364 baseEnd_863364 := by
    simpa [prefixWord, tailWord_863364, baseEnd_863364] using wordTrace_append hprefix tailTrace_863364
  have hstable : (prefixWord ++ tailWord_863364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863364).length < 2 ^ (prefixWord ++ tailWord_863364).sum := by decide
  have hdescent : baseEnd_863364 < baseStart_863364 := by decide
  rcases family_descends (prefixWord ++ tailWord_863364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863368 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_863368 : Nat := 118140960795 + 863368 * 2 ^ 59
def prefixEnd_863368 : Nat := 4983230072969 + 3 ^ 40 * 863368 * 2
def baseEnd_863368 : Nat := 147774255237027767476483

theorem tailTrace_863368 : CollatzResearch.WordTrace tailWord_863368 prefixEnd_863368 147774255237027767476483 := by
  unfold tailWord_863368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744808968086331180147379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20993078624115108240196505 15744808968086331180147379)
  ·
    refine ⟨23617213452129496770221069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15744808968086331180147379 23617213452129496770221069)
    ·
      refine ⟨8856455044548561288832901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23617213452129496770221069 8856455044548561288832901)
      ·
        refine ⟨1660585320852855241656169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8856455044548561288832901 1660585320852855241656169)
        ·
          refine ⟨1245438990639641431242127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660585320852855241656169 1245438990639641431242127)
          ·
            refine ⟨1868158485959462146863191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245438990639641431242127 1868158485959462146863191)
            ·
              refine ⟨2802237728939193220294787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868158485959462146863191 2802237728939193220294787)
              ·
                refine ⟨4203356593408789830442181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802237728939193220294787 4203356593408789830442181)
                ·
                  refine ⟨788129361264148093207909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4203356593408789830442181 788129361264148093207909)
                  ·
                    refine ⟨147774255237027767476483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 788129361264148093207909 147774255237027767476483)
                    ·
                      rfl

theorem cell23_863368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_863368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863368 prefixEnd_863368 := by exact prefixLift 863368
  have htrace : WordTrace (prefixWord ++ tailWord_863368) baseStart_863368 baseEnd_863368 := by
    simpa [prefixWord, tailWord_863368, baseEnd_863368] using wordTrace_append hprefix tailTrace_863368
  have hstable : (prefixWord ++ tailWord_863368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863368).length < 2 ^ (prefixWord ++ tailWord_863368).sum := by decide
  have hdescent : baseEnd_863368 < baseStart_863368 := by decide
  rcases family_descends (prefixWord ++ tailWord_863368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863388 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_863388 : Nat := 118140960795 + 863388 * 2 ^ 59
def prefixEnd_863388 : Nat := 4983230072969 + 3 ^ 40 * 863388 * 2
def baseEnd_863388 : Nat := 443333035324173224179357

theorem tailTrace_863388 : CollatzResearch.WordTrace tailWord_863388 prefixEnd_863388 443333035324173224179357 := by
  unfold tailWord_863388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15745173698050102888011409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20993564930733470517348545 15745173698050102888011409)
  ·
    refine ⟨11808880273537577166008557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15745173698050102888011409 11808880273537577166008557)
    ·
      refine ⟨4428330102576591437253209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11808880273537577166008557 4428330102576591437253209)
      ·
        refine ⟨3321247576932443577939907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4428330102576591437253209 3321247576932443577939907)
        ·
          refine ⟨4981871365398665366909861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321247576932443577939907 4981871365398665366909861)
          ·
            refine ⟨934100881012249756295599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4981871365398665366909861 934100881012249756295599)
            ·
              refine ⟨1401151321518374634443399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934100881012249756295599 1401151321518374634443399)
              ·
                refine ⟨2101726982277561951665099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401151321518374634443399 2101726982277561951665099)
                ·
                  refine ⟨3152590473416342927497649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101726982277561951665099 3152590473416342927497649)
                  ·
                    refine ⟨2364442855062257195623237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3152590473416342927497649 2364442855062257195623237)
                    ·
                      refine ⟨443333035324173224179357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2364442855062257195623237 443333035324173224179357)
                      ·
                        rfl

theorem cell23_863388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_863388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863388 prefixEnd_863388 := by exact prefixLift 863388
  have htrace : WordTrace (prefixWord ++ tailWord_863388) baseStart_863388 baseEnd_863388 := by
    simpa [prefixWord, tailWord_863388, baseEnd_863388] using wordTrace_append hprefix tailTrace_863388
  have hstable : (prefixWord ++ tailWord_863388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863388).length < 2 ^ (prefixWord ++ tailWord_863388).sum := by decide
  have hdescent : baseEnd_863388 < baseStart_863388 := by decide
  rcases family_descends (prefixWord ++ tailWord_863388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863409 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 1, 2, 2]
def baseStart_863409 : Nat := 118140960795 + 863409 * 2 ^ 59
def prefixEnd_863409 : Nat := 4983230072969 + 3 ^ 40 * 863409 * 2
def baseEnd_863409 : Nat := 443343818417917642016761

theorem tailTrace_863409 : CollatzResearch.WordTrace tailWord_863409 prefixEnd_863409 443343818417917642016761 := by
  unfold tailWord_863409
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491113329024126362537281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20994075552682750908358187 31491113329024126362537281)
  ·
    refine ⟨23618334996768094771902961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31491113329024126362537281 23618334996768094771902961)
    ·
      refine ⟨17713751247576071078927221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23618334996768094771902961 17713751247576071078927221)
      ·
        refine ⟨1660664179460256663649427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17713751247576071078927221 1660664179460256663649427)
        ·
          refine ⟨2490996269190384995474141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660664179460256663649427 2490996269190384995474141)
          ·
            refine ⟨934123600946394373302803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2490996269190384995474141 934123600946394373302803)
            ·
              refine ⟨1401185401419591559954205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934123600946394373302803 1401185401419591559954205)
              ·
                refine ⟨525444525532346834982827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1401185401419591559954205 525444525532346834982827)
                ·
                  refine ⟨788166788298520252474241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525444525532346834982827 788166788298520252474241)
                  ·
                    refine ⟨591125091223890189355681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788166788298520252474241 591125091223890189355681)
                    ·
                      refine ⟨443343818417917642016761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591125091223890189355681 443343818417917642016761)
                      ·
                        rfl

theorem cell23_863409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_863409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863409 prefixEnd_863409 := by exact prefixLift 863409
  have htrace : WordTrace (prefixWord ++ tailWord_863409) baseStart_863409 baseEnd_863409 := by
    simpa [prefixWord, tailWord_863409, baseEnd_863409] using wordTrace_append hprefix tailTrace_863409
  have hstable : (prefixWord ++ tailWord_863409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863409).length < 2 ^ (prefixWord ++ tailWord_863409).sum := by decide
  have hdescent : baseEnd_863409 < baseStart_863409 := by decide
  rcases family_descends (prefixWord ++ tailWord_863409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863425 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_863425 : Nat := 118140960795 + 863425 * 2 ^ 59
def prefixEnd_863425 : Nat := 4983230072969 + 3 ^ 40 * 863425 * 2
def baseEnd_863425 : Nat := 443352034108389579416687

theorem tailTrace_863425 : CollatzResearch.WordTrace tailWord_863425 prefixEnd_863425 443352034108389579416687 := by
  unfold tailWord_863425
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491696896966161095119729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20994464597977440730079819 31491696896966161095119729)
  ·
    refine ⟨23618772672724620821339797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31491696896966161095119729 23618772672724620821339797)
    ·
      refine ⟨1107129969033966601000303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23618772672724620821339797 1107129969033966601000303)
      ·
        refine ⟨1660694953550949901500455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107129969033966601000303 1660694953550949901500455)
        ·
          refine ⟨2491042430326424852250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660694953550949901500455 2491042430326424852250683)
          ·
            refine ⟨3736563645489637278376025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491042430326424852250683 3736563645489637278376025)
            ·
              refine ⟨2802422734117227958782019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3736563645489637278376025 2802422734117227958782019)
              ·
                refine ⟨4203634101175841938173029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802422734117227958782019 4203634101175841938173029)
                ·
                  refine ⟨788181393970470363407443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4203634101175841938173029 788181393970470363407443)
                  ·
                    refine ⟨1182272090955705545111165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788181393970470363407443 1182272090955705545111165)
                    ·
                      refine ⟨443352034108389579416687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1182272090955705545111165 443352034108389579416687)
                      ·
                        rfl

theorem cell23_863425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_863425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863425 prefixEnd_863425 := by exact prefixLift 863425
  have htrace : WordTrace (prefixWord ++ tailWord_863425) baseStart_863425 baseEnd_863425 := by
    simpa [prefixWord, tailWord_863425, baseEnd_863425] using wordTrace_append hprefix tailTrace_863425
  have hstable : (prefixWord ++ tailWord_863425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863425).length < 2 ^ (prefixWord ++ tailWord_863425).sum := by decide
  have hdescent : baseEnd_863425 < baseStart_863425 := by decide
  rcases family_descends (prefixWord ++ tailWord_863425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863426 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_863426 : Nat := 118140960795 + 863426 * 2 ^ 59
def prefixEnd_863426 : Nat := 4983230072969 + 3 ^ 40 * 863426 * 2
def baseEnd_863426 : Nat := 443352547589044075504183

theorem tailTrace_863426 : CollatzResearch.WordTrace tailWord_863426 prefixEnd_863426 443352547589044075504183 := by
  unfold tailWord_863426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7872933342490634566476533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20994488913308358843937421 7872933342490634566476533)
  ·
    refine ⟨738087500858496990607175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7872933342490634566476533 738087500858496990607175)
    ·
      refine ⟨1107131251287745485910763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738087500858496990607175 1107131251287745485910763)
      ·
        refine ⟨1660696876931618228866145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107131251287745485910763 1660696876931618228866145)
        ·
          refine ⟨1245522657698713671649609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660696876931618228866145 1245522657698713671649609)
          ·
            refine ⟨934141993274035253737207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245522657698713671649609 934141993274035253737207)
            ·
              refine ⟨1401212989911052880605811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934141993274035253737207 1401212989911052880605811)
              ·
                refine ⟨2101819484866579320908717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401212989911052880605811 2101819484866579320908717)
                ·
                  refine ⟨788182306824967245340769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2101819484866579320908717 788182306824967245340769)
                  ·
                    refine ⟨591136730118725434005577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788182306824967245340769 591136730118725434005577)
                    ·
                      refine ⟨443352547589044075504183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591136730118725434005577 443352547589044075504183)
                      ·
                        rfl

theorem cell23_863426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_863426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863426 prefixEnd_863426 := by exact prefixLift 863426
  have htrace : WordTrace (prefixWord ++ tailWord_863426) baseStart_863426 baseEnd_863426 := by
    simpa [prefixWord, tailWord_863426, baseEnd_863426] using wordTrace_append hprefix tailTrace_863426
  have hstable : (prefixWord ++ tailWord_863426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863426).length < 2 ^ (prefixWord ++ tailWord_863426).sum := by decide
  have hdescent : baseEnd_863426 < baseStart_863426 := by decide
  rcases family_descends (prefixWord ++ tailWord_863426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863476 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_863476 : Nat := 118140960795 + 863476 * 2 ^ 59
def prefixEnd_863476 : Nat := 4983230072969 + 3 ^ 40 * 863476 * 2
def baseEnd_863476 : Nat := 443378221621768879878953

theorem tailTrace_863476 : CollatzResearch.WordTrace tailWord_863476 prefixEnd_863476 443378221621768879878953 := by
  unfold tailWord_863476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15746778509890698402613141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20995704679854264536817521 15746778509890698402613141)
  ·
    refine ⟨738130242651126487622491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15746778509890698402613141 738130242651126487622491)
    ·
      refine ⟨1107195363976689731433737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738130242651126487622491 1107195363976689731433737)
      ·
        refine ⟨830396522982517298575303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107195363976689731433737 830396522982517298575303)
        ·
          refine ⟨1245594784473775947862955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830396522982517298575303 1245594784473775947862955)
          ·
            refine ⟨1868392176710663921794433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245594784473775947862955 1868392176710663921794433)
            ·
              refine ⟨1401294132532997941345825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868392176710663921794433 1401294132532997941345825)
              ·
                refine ⟨1050970599399748456009369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401294132532997941345825 1050970599399748456009369)
                ·
                  refine ⟨788227949549811342007027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1050970599399748456009369 788227949549811342007027)
                  ·
                    refine ⟨1182341924324717013010541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788227949549811342007027 1182341924324717013010541)
                    ·
                      refine ⟨443378221621768879878953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1182341924324717013010541 443378221621768879878953)
                      ·
                        rfl

theorem cell23_863476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_863476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863476 prefixEnd_863476 := by exact prefixLift 863476
  have htrace : WordTrace (prefixWord ++ tailWord_863476) baseStart_863476 baseEnd_863476 := by
    simpa [prefixWord, tailWord_863476, baseEnd_863476] using wordTrace_append hprefix tailTrace_863476
  have hstable : (prefixWord ++ tailWord_863476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863476).length < 2 ^ (prefixWord ++ tailWord_863476).sum := by decide
  have hdescent : baseEnd_863476 < baseStart_863476 := by decide
  rcases family_descends (prefixWord ++ tailWord_863476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863481 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_863481 : Nat := 118140960795 + 863481 * 2 ^ 59
def prefixEnd_863481 : Nat := 4983230072969 + 3 ^ 40 * 863481 * 2
def baseEnd_863481 : Nat := 443380789025041360316429

theorem tailTrace_863481 : CollatzResearch.WordTrace tailWord_863481 prefixEnd_863481 443380789025041360316429 := by
  unfold tailWord_863481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31493739384763282659158297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20995826256508855106105531 31493739384763282659158297)
  ·
    refine ⟨23620304538572461994368723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31493739384763282659158297 23620304538572461994368723)
    ·
      refine ⟨35430456807858692991553085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23620304538572461994368723 35430456807858692991553085)
      ·
        refine ⟨13286421302947009871832407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35430456807858692991553085 13286421302947009871832407)
        ·
          refine ⟨19929631954420514807748611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13286421302947009871832407 19929631954420514807748611)
          ·
            refine ⟨29894447931630772211622917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19929631954420514807748611 29894447931630772211622917)
            ·
              refine ⟨5605208987180769789679297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29894447931630772211622917 5605208987180769789679297)
              ·
                refine ⟨4203906740385577342259473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5605208987180769789679297 4203906740385577342259473)
                ·
                  refine ⟨3152930055289183006694605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4203906740385577342259473 3152930055289183006694605)
                  ·
                    refine ⟨1182348770733443627510477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152930055289183006694605 1182348770733443627510477)
                    ·
                      refine ⟨443380789025041360316429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1182348770733443627510477 443380789025041360316429)
                      ·
                        rfl

theorem cell23_863481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_863481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863481 prefixEnd_863481 := by exact prefixLift 863481
  have htrace : WordTrace (prefixWord ++ tailWord_863481) baseStart_863481 baseEnd_863481 := by
    simpa [prefixWord, tailWord_863481, baseEnd_863481] using wordTrace_append hprefix tailTrace_863481
  have hstable : (prefixWord ++ tailWord_863481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863481).length < 2 ^ (prefixWord ++ tailWord_863481).sum := by decide
  have hdescent : baseEnd_863481 < baseStart_863481 := by decide
  rcases family_descends (prefixWord ++ tailWord_863481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863548 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_863548 : Nat := 118140960795 + 863548 * 2 ^ 59
def prefixEnd_863548 : Nat := 4983230072969 + 3 ^ 40 * 863548 * 2
def baseEnd_863548 : Nat := 147805064076297532726207

theorem tailTrace_863548 : CollatzResearch.WordTrace tailWord_863548 prefixEnd_863548 147805064076297532726207 := by
  unfold tailWord_863548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748091537760276550923649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20997455383680368734564865 15748091537760276550923649)
  ·
    refine ⟨11811068653320207413192737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15748091537760276550923649 11811068653320207413192737)
    ·
      refine ⟨8858301489990155559894553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11811068653320207413192737 8858301489990155559894553)
      ·
        refine ⟨6643726117492616669920915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8858301489990155559894553 6643726117492616669920915)
        ·
          refine ⟨9965589176238925004881373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6643726117492616669920915 9965589176238925004881373)
          ·
            refine ⟨3737095941089596876830515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9965589176238925004881373 3737095941089596876830515)
            ·
              refine ⟨5605643911634395315245773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737095941089596876830515 5605643911634395315245773)
              ·
                refine ⟨2102116466862898243217165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5605643911634395315245773 2102116466862898243217165)
                ·
                  refine ⟨788293675073586841206437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2102116466862898243217165 788293675073586841206437)
                  ·
                    refine ⟨147805064076297532726207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 788293675073586841206437 147805064076297532726207)
                    ·
                      rfl

theorem cell23_863548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_863548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863548 prefixEnd_863548 := by exact prefixLift 863548
  have htrace : WordTrace (prefixWord ++ tailWord_863548) baseStart_863548 baseEnd_863548 := by
    simpa [prefixWord, tailWord_863548, baseEnd_863548] using wordTrace_append hprefix tailTrace_863548
  have hstable : (prefixWord ++ tailWord_863548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863548).length < 2 ^ (prefixWord ++ tailWord_863548).sum := by decide
  have hdescent : baseEnd_863548 < baseStart_863548 := by decide
  rcases family_descends (prefixWord ++ tailWord_863548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863561 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 6]
def baseStart_863561 : Nat := 118140960795 + 863561 * 2 ^ 59
def prefixEnd_863561 : Nat := 4983230072969 + 3 ^ 40 * 863561 * 2
def baseEnd_863561 : Nat := 49269096386377894146229

theorem tailTrace_863561 : CollatzResearch.WordTrace tailWord_863561 prefixEnd_863561 49269096386377894146229 := by
  unfold tailWord_863561
  simp only [CollatzResearch.WordTrace]
  refine ⟨31496657224473456322070537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20997771482982304214713691 31496657224473456322070537)
  ·
    refine ⟨23622492918355092241552903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31496657224473456322070537 23622492918355092241552903)
    ·
      refine ⟨35433739377532638362329355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23622492918355092241552903 35433739377532638362329355)
      ·
        refine ⟨53150609066298957543494033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35433739377532638362329355 53150609066298957543494033)
        ·
          refine ⟨39862956799724218157620525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53150609066298957543494033 39862956799724218157620525)
          ·
            refine ⟨14948608799896581809107697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39862956799724218157620525 14948608799896581809107697)
            ·
              refine ⟨11211456599922436356830773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14948608799896581809107697 11211456599922436356830773)
              ·
                refine ⟨1051074056242728408452885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11211456599922436356830773 1051074056242728408452885)
                ·
                  refine ⟨49269096386377894146229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1051074056242728408452885 49269096386377894146229)
                  ·
                    rfl

theorem cell23_863561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_863561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863561 prefixEnd_863561 := by exact prefixLift 863561
  have htrace : WordTrace (prefixWord ++ tailWord_863561) baseStart_863561 baseEnd_863561 := by
    simpa [prefixWord, tailWord_863561, baseEnd_863561] using wordTrace_append hprefix tailTrace_863561
  have hstable : (prefixWord ++ tailWord_863561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863561).length < 2 ^ (prefixWord ++ tailWord_863561).sum := by decide
  have hdescent : baseEnd_863561 < baseStart_863561 := by decide
  rcases family_descends (prefixWord ++ tailWord_863561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863571 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3]
def baseStart_863571 : Nat := 118140960795 + 863571 * 2 ^ 59
def prefixEnd_863571 : Nat := 4983230072969 + 3 ^ 40 * 863571 * 2
def baseEnd_863571 : Nat := 443427002283946008191015

theorem tailTrace_863571 : CollatzResearch.WordTrace tailWord_863571 prefixEnd_863571 443427002283946008191015 := by
  unfold tailWord_863571
  simp only [CollatzResearch.WordTrace]
  refine ⟨31497021954437228029934567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20998014636291485353289711 31497021954437228029934567)
  ·
    refine ⟨47245532931655842044901851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31497021954437228029934567 47245532931655842044901851)
    ·
      refine ⟨70868299397483763067352777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47245532931655842044901851 70868299397483763067352777)
      ·
        refine ⟨53151224548112822300514583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70868299397483763067352777 53151224548112822300514583)
        ·
          refine ⟨79726836822169233450771875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53151224548112822300514583 79726836822169233450771875)
          ·
            refine ⟨119590255233253850176157813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79726836822169233450771875 119590255233253850176157813)
            ·
              refine ⟨11211586428117548454014795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119590255233253850176157813 11211586428117548454014795)
              ·
                refine ⟨16817379642176322681022193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11211586428117548454014795 16817379642176322681022193)
                ·
                  refine ⟨12613034731632242010766645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16817379642176322681022193 12613034731632242010766645)
                  ·
                    refine ⟨1182472006090522688509373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12613034731632242010766645 1182472006090522688509373)
                    ·
                      refine ⟨443427002283946008191015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1182472006090522688509373 443427002283946008191015)
                      ·
                        rfl

theorem cell23_863571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_863571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863571 prefixEnd_863571 := by exact prefixLift 863571
  have htrace : WordTrace (prefixWord ++ tailWord_863571) baseStart_863571 baseEnd_863571 := by
    simpa [prefixWord, tailWord_863571, baseEnd_863571] using wordTrace_append hprefix tailTrace_863571
  have hstable : (prefixWord ++ tailWord_863571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863571).length < 2 ^ (prefixWord ++ tailWord_863571).sum := by decide
  have hdescent : baseEnd_863571 < baseStart_863571 := by decide
  rcases family_descends (prefixWord ++ tailWord_863571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863628 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_863628 : Nat := 118140960795 + 863628 * 2 ^ 59
def prefixEnd_863628 : Nat := 4983230072969 + 3 ^ 40 * 863628 * 2
def baseEnd_863628 : Nat := 443456270681252285178253

theorem tailTrace_863628 : CollatzResearch.WordTrace tailWord_863628 prefixEnd_863628 443456270681252285178253 := by
  unfold tailWord_863628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15749550457615363382379769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20999400610153817843173025 15749550457615363382379769)
  ·
    refine ⟨11812162843211522536784827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15749550457615363382379769 11812162843211522536784827)
    ·
      refine ⟨17718244264817283805177241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11812162843211522536784827 17718244264817283805177241)
      ·
        refine ⟨13288683198612962853882931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17718244264817283805177241 13288683198612962853882931)
        ·
          refine ⟨19933024797919444280824397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13288683198612962853882931 19933024797919444280824397)
          ·
            refine ⟨7474884299219791605309149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19933024797919444280824397 7474884299219791605309149)
            ·
              refine ⟨2803081612207421851990931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7474884299219791605309149 2803081612207421851990931)
              ·
                refine ⟨4204622418311132777986397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803081612207421851990931 4204622418311132777986397)
                ·
                  refine ⟨1576733406866674791744899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4204622418311132777986397 1576733406866674791744899)
                  ·
                    refine ⟨2365100110300012187617349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576733406866674791744899 2365100110300012187617349)
                    ·
                      refine ⟨443456270681252285178253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2365100110300012187617349 443456270681252285178253)
                      ·
                        rfl

theorem cell23_863628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_863628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863628 prefixEnd_863628 := by exact prefixLift 863628
  have htrace : WordTrace (prefixWord ++ tailWord_863628) baseStart_863628 baseEnd_863628 := by
    simpa [prefixWord, tailWord_863628, baseEnd_863628] using wordTrace_append hprefix tailTrace_863628
  have hstable : (prefixWord ++ tailWord_863628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863628).length < 2 ^ (prefixWord ++ tailWord_863628).sum := by decide
  have hdescent : baseEnd_863628 < baseStart_863628 := by decide
  rcases family_descends (prefixWord ++ tailWord_863628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863656 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_863656 : Nat := 118140960795 + 863656 * 2 ^ 59
def prefixEnd_863656 : Nat := 4983230072969 + 3 ^ 40 * 863656 * 2
def baseEnd_863656 : Nat := 443470648139578175628125

theorem tailTrace_863656 : CollatzResearch.WordTrace tailWord_863656 prefixEnd_863656 443470648139578175628125 := by
  unfold tailWord_863656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15750061079564643773389411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21000081439419525031185881 15750061079564643773389411)
  ·
    refine ⟨23625091619346965660084117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15750061079564643773389411 23625091619346965660084117)
    ·
      refine ⟨1107426169656889015316443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23625091619346965660084117 1107426169656889015316443)
      ·
        refine ⟨1661139254485333522974665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107426169656889015316443 1661139254485333522974665)
        ·
          refine ⟨1245854440864000142230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661139254485333522974665 1245854440864000142230999)
          ·
            refine ⟨1868781661296000213346499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245854440864000142230999 1868781661296000213346499)
            ·
              refine ⟨2803172491944000320019749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868781661296000213346499 2803172491944000320019749)
              ·
                refine ⟨525594842239500060003703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2803172491944000320019749 525594842239500060003703)
                ·
                  refine ⟨788392263359250090005555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525594842239500060003703 788392263359250090005555)
                  ·
                    refine ⟨1182588395038875135008333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788392263359250090005555 1182588395038875135008333)
                    ·
                      refine ⟨443470648139578175628125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1182588395038875135008333 443470648139578175628125)
                      ·
                        rfl

theorem cell23_863656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_863656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863656 prefixEnd_863656 := by exact prefixLift 863656
  have htrace : WordTrace (prefixWord ++ tailWord_863656) baseStart_863656 baseEnd_863656 := by
    simpa [prefixWord, tailWord_863656, baseEnd_863656] using wordTrace_append hprefix tailTrace_863656
  have hstable : (prefixWord ++ tailWord_863656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863656).length < 2 ^ (prefixWord ++ tailWord_863656).sum := by decide
  have hdescent : baseEnd_863656 < baseStart_863656 := by decide
  rcases family_descends (prefixWord ++ tailWord_863656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863728 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_863728 : Nat := 118140960795 + 863728 * 2 ^ 59
def prefixEnd_863728 : Nat := 4983230072969 + 3 ^ 40 * 863728 * 2
def baseEnd_863728 : Nat := 147835872915567297975931

theorem tailTrace_863728 : CollatzResearch.WordTrace tailWord_863728 prefixEnd_863728 147835872915567297975931 := by
  unfold tailWord_863728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15751374107434221921699919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21001832143245629228933225 15751374107434221921699919)
  ·
    refine ⟨23627061161151332882549879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15751374107434221921699919 23627061161151332882549879)
    ·
      refine ⟨35440591741726999323824819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23627061161151332882549879 35440591741726999323824819)
      ·
        refine ⟨53160887612590498985737229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35440591741726999323824819 53160887612590498985737229)
        ·
          refine ⟨19935332854721437119651461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53160887612590498985737229 19935332854721437119651461)
          ·
            refine ⟨3737874910260269459934649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19935332854721437119651461 3737874910260269459934649)
            ·
              refine ⟨2803406182695202094950987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3737874910260269459934649 2803406182695202094950987)
              ·
                refine ⟨4205109274042803142426481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803406182695202094950987 4205109274042803142426481)
                ·
                  refine ⟨3153831955532102356819861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205109274042803142426481 3153831955532102356819861)
                  ·
                    refine ⟨147835872915567297975931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3153831955532102356819861 147835872915567297975931)
                    ·
                      rfl

theorem cell23_863728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_863728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863728 prefixEnd_863728 := by exact prefixLift 863728
  have htrace : WordTrace (prefixWord ++ tailWord_863728) baseStart_863728 baseEnd_863728 := by
    simpa [prefixWord, tailWord_863728, baseEnd_863728] using wordTrace_append hprefix tailTrace_863728
  have hstable : (prefixWord ++ tailWord_863728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863728).length < 2 ^ (prefixWord ++ tailWord_863728).sum := by decide
  have hdescent : baseEnd_863728 < baseStart_863728 := by decide
  rcases family_descends (prefixWord ++ tailWord_863728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863729 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_863729 : Nat := 118140960795 + 863729 * 2 ^ 59
def prefixEnd_863729 : Nat := 4983230072969 + 3 ^ 40 * 863729 * 2
def baseEnd_863729 : Nat := 443508132227356390015289

theorem tailTrace_863729 : CollatzResearch.WordTrace tailWord_863729 prefixEnd_863729 443508132227356390015289 := by
  unfold tailWord_863729
  simp only [CollatzResearch.WordTrace]
  refine ⟨31502784687864821014186241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21001856458576547342790827 31502784687864821014186241)
  ·
    refine ⟨23627088515898615760639681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31502784687864821014186241 23627088515898615760639681)
    ·
      refine ⟨17720316386923961820479761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23627088515898615760639681 17720316386923961820479761)
      ·
        refine ⟨13290237290192971365359821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17720316386923961820479761 13290237290192971365359821)
        ·
          refine ⟨4983838983822364262009933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13290237290192971365359821 4983838983822364262009933)
          ·
            refine ⟨1868939618933386598253725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4983838983822364262009933 1868939618933386598253725)
            ·
              refine ⟨700852357100019974345147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1868939618933386598253725 700852357100019974345147)
              ·
                refine ⟨1051278535650029961517721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700852357100019974345147 1051278535650029961517721)
                ·
                  refine ⟨788458901737522471138291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051278535650029961517721 788458901737522471138291)
                  ·
                    refine ⟨1182688352606283706707437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788458901737522471138291 1182688352606283706707437)
                    ·
                      refine ⟨443508132227356390015289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1182688352606283706707437 443508132227356390015289)
                      ·
                        rfl

theorem cell23_863729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_863729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863729 prefixEnd_863729 := by exact prefixLift 863729
  have htrace : WordTrace (prefixWord ++ tailWord_863729) baseStart_863729 baseEnd_863729 := by
    simpa [prefixWord, tailWord_863729, baseEnd_863729] using wordTrace_append hprefix tailTrace_863729
  have hstable : (prefixWord ++ tailWord_863729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863729).length < 2 ^ (prefixWord ++ tailWord_863729).sum := by decide
  have hdescent : baseEnd_863729 < baseStart_863729 := by decide
  rcases family_descends (prefixWord ++ tailWord_863729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863735 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_863735 : Nat := 118140960795 + 863735 * 2 ^ 59
def prefixEnd_863735 : Nat := 4983230072969 + 3 ^ 40 * 863735 * 2
def baseEnd_863735 : Nat := 443511213111283366540261

theorem tailTrace_863735 : CollatzResearch.WordTrace tailWord_863735 prefixEnd_863735 443511213111283366540261 := by
  unfold tailWord_863735
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503003525843084038904659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002002350562056025936439 31503003525843084038904659)
  ·
    refine ⟨47254505288764626058356989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31503003525843084038904659 47254505288764626058356989)
    ·
      refine ⟨17720439483286734771883871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47254505288764626058356989 17720439483286734771883871)
      ·
        refine ⟨26580659224930102157825807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17720439483286734771883871 26580659224930102157825807)
        ·
          refine ⟨39870988837395153236738711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26580659224930102157825807 39870988837395153236738711)
          ·
            refine ⟨59806483256092729855108067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39870988837395153236738711 59806483256092729855108067)
            ·
              refine ⟨89709724884139094782662101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59806483256092729855108067 89709724884139094782662101)
              ·
                refine ⟨2102571676972010033968643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89709724884139094782662101 2102571676972010033968643)
                ·
                  refine ⟨3153857515458015050952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2102571676972010033968643 3153857515458015050952965)
                  ·
                    refine ⟨591348284148377822053681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3153857515458015050952965 591348284148377822053681)
                    ·
                      refine ⟨443511213111283366540261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591348284148377822053681 443511213111283366540261)
                      ·
                        rfl

theorem cell23_863735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_863735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863735 prefixEnd_863735 := by exact prefixLift 863735
  have htrace : WordTrace (prefixWord ++ tailWord_863735) baseStart_863735 baseEnd_863735 := by
    simpa [prefixWord, tailWord_863735, baseEnd_863735] using wordTrace_append hprefix tailTrace_863735
  have hstable : (prefixWord ++ tailWord_863735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863735).length < 2 ^ (prefixWord ++ tailWord_863735).sum := by decide
  have hdescent : baseEnd_863735 < baseStart_863735 := by decide
  rcases family_descends (prefixWord ++ tailWord_863735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863738 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_863738 : Nat := 118140960795 + 863738 * 2 ^ 59
def prefixEnd_863738 : Nat := 4983230072969 + 3 ^ 40 * 863738 * 2
def baseEnd_863738 : Nat := 443512753553246854802747

theorem tailTrace_863738 : CollatzResearch.WordTrace tailWord_863738 prefixEnd_863738 443512753553246854802747 := by
  unfold tailWord_863738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875778236208053887815967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21002075296554810367509245 7875778236208053887815967)
  ·
    refine ⟨11813667354312080831723951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7875778236208053887815967 11813667354312080831723951)
    ·
      refine ⟨17720501031468121247585927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11813667354312080831723951 17720501031468121247585927)
      ·
        refine ⟨26580751547202181871378891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17720501031468121247585927 26580751547202181871378891)
        ·
          refine ⟨39871127320803272807068337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26580751547202181871378891 39871127320803272807068337)
          ·
            refine ⟨29903345490602454605301253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39871127320803272807068337 29903345490602454605301253)
            ·
              refine ⟨5606877279487960238493985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29903345490602454605301253 5606877279487960238493985)
              ·
                refine ⟨4205157959615970178870489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606877279487960238493985 4205157959615970178870489)
                ·
                  refine ⟨3153868469711977634152867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205157959615970178870489 3153868469711977634152867)
                  ·
                    refine ⟨4730802704567966451229301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153868469711977634152867 4730802704567966451229301)
                    ·
                      refine ⟨443512753553246854802747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4730802704567966451229301 443512753553246854802747)
                      ·
                        rfl

theorem cell23_863738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_863738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863738 prefixEnd_863738 := by exact prefixLift 863738
  have htrace : WordTrace (prefixWord ++ tailWord_863738) baseStart_863738 baseEnd_863738 := by
    simpa [prefixWord, tailWord_863738, baseEnd_863738] using wordTrace_append hprefix tailTrace_863738
  have hstable : (prefixWord ++ tailWord_863738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863738).length < 2 ^ (prefixWord ++ tailWord_863738).sum := by decide
  have hdescent : baseEnd_863738 < baseStart_863738 := by decide
  rcases family_descends (prefixWord ++ tailWord_863738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863752 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_863752 : Nat := 118140960795 + 863752 * 2 ^ 59
def prefixEnd_863752 : Nat := 4983230072969 + 3 ^ 40 * 863752 * 2
def baseEnd_863752 : Nat := 443519942282409800027683

theorem tailTrace_863752 : CollatzResearch.WordTrace tailWord_863752 prefixEnd_863752 443519942282409800027683 := by
  unfold tailWord_863752
  simp only [CollatzResearch.WordTrace]
  refine ⟨15751811783390747971136755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21002415711187663961515673 15751811783390747971136755)
  ·
    refine ⟨23627717675086121956705133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15751811783390747971136755 23627717675086121956705133)
    ·
      refine ⟨8860394128157295733764425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23627717675086121956705133 8860394128157295733764425)
      ·
        refine ⟨6645295596117971800323319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8860394128157295733764425 6645295596117971800323319)
        ·
          refine ⟨9967943394176957700484979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645295596117971800323319 9967943394176957700484979)
          ·
            refine ⟨14951915091265436550727469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9967943394176957700484979 14951915091265436550727469)
            ·
              refine ⟨5606968159224538706522801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14951915091265436550727469 5606968159224538706522801)
              ·
                refine ⟨4205226119418404029892101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606968159224538706522801 4205226119418404029892101)
                ·
                  refine ⟨788479897390950755604769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4205226119418404029892101 788479897390950755604769)
                  ·
                    refine ⟨591359923043213066703577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788479897390950755604769 591359923043213066703577)
                    ·
                      refine ⟨443519942282409800027683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591359923043213066703577 443519942282409800027683)
                      ·
                        rfl

theorem cell23_863752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_863752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863752 prefixEnd_863752 := by exact prefixLift 863752
  have htrace : WordTrace (prefixWord ++ tailWord_863752) baseStart_863752 baseEnd_863752 := by
    simpa [prefixWord, tailWord_863752, baseEnd_863752] using wordTrace_append hprefix tailTrace_863752
  have hstable : (prefixWord ++ tailWord_863752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863752).length < 2 ^ (prefixWord ++ tailWord_863752).sum := by decide
  have hdescent : baseEnd_863752 < baseStart_863752 := by decide
  rcases family_descends (prefixWord ++ tailWord_863752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863755 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5]
def baseStart_863755 : Nat := 118140960795 + 863755 * 2 ^ 59
def prefixEnd_863755 : Nat := 4983230072969 + 3 ^ 40 * 863755 * 2
def baseEnd_863755 : Nat := 443521482724373288290169

theorem tailTrace_863755 : CollatzResearch.WordTrace tailWord_863755 prefixEnd_863755 443521482724373288290169 := by
  unfold tailWord_863755
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503732985770627454632719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002488657180418303088479 31503732985770627454632719)
  ·
    refine ⟨47255599478655941181949079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31503732985770627454632719 47255599478655941181949079)
    ·
      refine ⟨70883399217983911772923619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47255599478655941181949079 70883399217983911772923619)
      ·
        refine ⟨106325098826975867659385429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70883399217983911772923619 106325098826975867659385429)
        ·
          refine ⟨1245997251878623449133423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 106325098826975867659385429 1245997251878623449133423)
          ·
            refine ⟨1868995877817935173700135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245997251878623449133423 1868995877817935173700135)
            ·
              refine ⟨2803493816726902760550203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868995877817935173700135 2803493816726902760550203)
              ·
                refine ⟨4205240725090354140825305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2803493816726902760550203 4205240725090354140825305)
                ·
                  refine ⟨3153930543817765605618979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4205240725090354140825305 3153930543817765605618979)
                  ·
                    refine ⟨4730895815726648408428469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3153930543817765605618979 4730895815726648408428469)
                    ·
                      refine ⟨443521482724373288290169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4730895815726648408428469 443521482724373288290169)
                      ·
                        rfl

theorem cell23_863755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5].length) (baseStart_863755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863755 prefixEnd_863755 := by exact prefixLift 863755
  have htrace : WordTrace (prefixWord ++ tailWord_863755) baseStart_863755 baseEnd_863755 := by
    simpa [prefixWord, tailWord_863755, baseEnd_863755] using wordTrace_append hprefix tailTrace_863755
  have hstable : (prefixWord ++ tailWord_863755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863755).length < 2 ^ (prefixWord ++ tailWord_863755).sum := by decide
  have hdescent : baseEnd_863755 < baseStart_863755 := by decide
  rcases family_descends (prefixWord ++ tailWord_863755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863775 : List Nat := [1, 1, 2, 4, 1, 1, 2, 6, 5]
def baseStart_863775 : Nat := 118140960795 + 863775 * 2 ^ 59
def prefixEnd_863775 : Nat := 4983230072969 + 3 ^ 40 * 863775 * 2
def baseEnd_863775 : Nat := 49281305815273690004453

theorem tailTrace_863775 : CollatzResearch.WordTrace tailWord_863775 prefixEnd_863775 49281305815273690004453 := by
  unfold tailWord_863775
  simp only [CollatzResearch.WordTrace]
  refine ⟨31504462445698170870360779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002974963798780580240519 31504462445698170870360779)
  ·
    refine ⟨47256693668547256305541169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31504462445698170870360779 47256693668547256305541169)
    ·
      refine ⟨35442520251410442229155877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47256693668547256305541169 35442520251410442229155877)
      ·
        refine ⟨6645472547139457917966727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35442520251410442229155877 6645472547139457917966727)
        ·
          refine ⟨9968208820709186876950091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645472547139457917966727 9968208820709186876950091)
          ·
            refine ⟨14952313231063780315425137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968208820709186876950091 14952313231063780315425137)
            ·
              refine ⟨11214234923297835236568853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14952313231063780315425137 11214234923297835236568853)
              ·
                refine ⟨525667262029586026714165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11214234923297835236568853 525667262029586026714165)
                ·
                  refine ⟨49281305815273690004453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525667262029586026714165 49281305815273690004453)
                  ·
                    rfl

theorem cell23_863775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 5].length) (baseStart_863775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863775 prefixEnd_863775 := by exact prefixLift 863775
  have htrace : WordTrace (prefixWord ++ tailWord_863775) baseStart_863775 baseEnd_863775 := by
    simpa [prefixWord, tailWord_863775, baseEnd_863775] using wordTrace_append hprefix tailTrace_863775
  have hstable : (prefixWord ++ tailWord_863775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863775).length < 2 ^ (prefixWord ++ tailWord_863775).sum := by decide
  have hdescent : baseEnd_863775 < baseStart_863775 := by decide
  rcases family_descends (prefixWord ++ tailWord_863775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863825 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_863825 : Nat := 118140960795 + 863825 * 2 ^ 59
def prefixEnd_863825 : Nat := 4983230072969 + 3 ^ 40 * 863825 * 2
def baseEnd_863825 : Nat := 443557426370188014414847

theorem tailTrace_863825 : CollatzResearch.WordTrace tailWord_863825 prefixEnd_863825 443557426370188014414847 := by
  unfold tailWord_863825
  simp only [CollatzResearch.WordTrace]
  refine ⟨31506286095517029409680929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21004190730344686273120619 31506286095517029409680929)
  ·
    refine ⟨23629714571637772057260697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31506286095517029409680929 23629714571637772057260697)
    ·
      refine ⟨17722285928728329042945523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23629714571637772057260697 17722285928728329042945523)
      ·
        refine ⟨26583428893092493564418285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17722285928728329042945523 26583428893092493564418285)
        ·
          refine ⟨9968785834909685086656857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26583428893092493564418285 9968785834909685086656857)
          ·
            refine ⟨7476589376182263814992643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9968785834909685086656857 7476589376182263814992643)
            ·
              refine ⟨11214884064273395722488965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7476589376182263814992643 11214884064273395722488965)
              ·
                refine ⟨2102790762051261697966681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11214884064273395722488965 2102790762051261697966681)
                ·
                  refine ⟨1577093071538446273475011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2102790762051261697966681 1577093071538446273475011)
                  ·
                    refine ⟨2365639607307669410212517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1577093071538446273475011 2365639607307669410212517)
                    ·
                      refine ⟨443557426370188014414847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2365639607307669410212517 443557426370188014414847)
                      ·
                        rfl

theorem cell23_863825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_863825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863825 prefixEnd_863825 := by exact prefixLift 863825
  have htrace : WordTrace (prefixWord ++ tailWord_863825) baseStart_863825 baseEnd_863825 := by
    simpa [prefixWord, tailWord_863825, baseEnd_863825] using wordTrace_append hprefix tailTrace_863825
  have hstable : (prefixWord ++ tailWord_863825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863825).length < 2 ^ (prefixWord ++ tailWord_863825).sum := by decide
  have hdescent : baseEnd_863825 < baseStart_863825 := by decide
  rcases family_descends (prefixWord ++ tailWord_863825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863869 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_863869 : Nat := 118140960795 + 863869 * 2 ^ 59
def prefixEnd_863869 : Nat := 4983230072969 + 3 ^ 40 * 863869 * 2
def baseEnd_863869 : Nat := 147860006506328614088215

theorem tailTrace_863869 : CollatzResearch.WordTrace tailWord_863869 prefixEnd_863869 147860006506328614088215 := by
  unfold tailWord_863869
  simp only [CollatzResearch.WordTrace]
  refine ⟨31507890907357624924282661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21005260604905083282855107 31507890907357624924282661)
  ·
    refine ⟨5907729545129554673302999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31507890907357624924282661 5907729545129554673302999)
    ·
      refine ⟨8861594317694332009954499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5907729545129554673302999 8861594317694332009954499)
      ·
        refine ⟨13292391476541498014931749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861594317694332009954499 13292391476541498014931749)
        ·
          refine ⟨2492323401851530877799703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13292391476541498014931749 2492323401851530877799703)
          ·
            refine ⟨3738485102777296316699555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492323401851530877799703 3738485102777296316699555)
            ·
              refine ⟨5607727654165944475049333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3738485102777296316699555 5607727654165944475049333)
              ·
                refine ⟨525724467578057294535875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5607727654165944475049333 525724467578057294535875)
                ·
                  refine ⟨788586701367085941803813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525724467578057294535875 788586701367085941803813)
                  ·
                    refine ⟨147860006506328614088215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 788586701367085941803813 147860006506328614088215)
                    ·
                      rfl

theorem cell23_863869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_863869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863869 prefixEnd_863869 := by exact prefixLift 863869
  have htrace : WordTrace (prefixWord ++ tailWord_863869) baseStart_863869 baseEnd_863869 := by
    simpa [prefixWord, tailWord_863869, baseEnd_863869] using wordTrace_append hprefix tailTrace_863869
  have hstable : (prefixWord ++ tailWord_863869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863869).length < 2 ^ (prefixWord ++ tailWord_863869).sum := by decide
  have hdescent : baseEnd_863869 < baseStart_863869 := by decide
  rcases family_descends (prefixWord ++ tailWord_863869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863882 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_863882 : Nat := 118140960795 + 863882 * 2 ^ 59
def prefixEnd_863882 : Nat := 4983230072969 + 3 ^ 40 * 863882 * 2
def baseEnd_863882 : Nat := 49287410529721587933565

theorem tailTrace_863882 : CollatzResearch.WordTrace tailWord_863882 prefixEnd_863882 49287410529721587933565 := by
  unfold tailWord_863882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877091264077632036126475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21005576704207018763003933 7877091264077632036126475)
  ·
    refine ⟨11815636896116448054189713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7877091264077632036126475 11815636896116448054189713)
    ·
      refine ⟨8861727672087336040642285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815636896116448054189713 8861727672087336040642285)
      ·
        refine ⟨3323147877032751015240857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8861727672087336040642285 3323147877032751015240857)
        ·
          refine ⟨2492360907774563261430643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323147877032751015240857 2492360907774563261430643)
          ·
            refine ⟨3738541361661844892145965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492360907774563261430643 3738541361661844892145965)
            ·
              refine ⟨1401953010623191834554737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3738541361661844892145965 1401953010623191834554737)
              ·
                refine ⟨1051464757967393875916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401953010623191834554737 1051464757967393875916053)
                ·
                  refine ⟨49287410529721587933565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1051464757967393875916053 49287410529721587933565)
                  ·
                    rfl

theorem cell23_863882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_863882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863882 prefixEnd_863882 := by exact prefixLift 863882
  have htrace : WordTrace (prefixWord ++ tailWord_863882) baseStart_863882 baseEnd_863882 := by
    simpa [prefixWord, tailWord_863882, baseEnd_863882] using wordTrace_append hprefix tailTrace_863882
  have hstable : (prefixWord ++ tailWord_863882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863882).length < 2 ^ (prefixWord ++ tailWord_863882).sum := by decide
  have hdescent : baseEnd_863882 < baseStart_863882 := by decide
  rcases family_descends (prefixWord ++ tailWord_863882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863969 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_863969 : Nat := 118140960795 + 863969 * 2 ^ 59
def prefixEnd_863969 : Nat := 4983230072969 + 3 ^ 40 * 863969 * 2
def baseEnd_863969 : Nat := 443631367584435451014185

theorem tailTrace_863969 : CollatzResearch.WordTrace tailWord_863969 prefixEnd_863969 443631367584435451014185 := by
  unfold tailWord_863969
  simp only [CollatzResearch.WordTrace]
  refine ⟨31511538206995342002922961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21007692137996894668615307 31511538206995342002922961)
  ·
    refine ⟨23633653655246506502192221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31511538206995342002922961 23633653655246506502192221)
    ·
      refine ⟨8862620120717439938322083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23633653655246506502192221 8862620120717439938322083)
      ·
        refine ⟨13293930181076159907483125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862620120717439938322083 13293930181076159907483125)
        ·
          refine ⟨1246305954475889991326543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13293930181076159907483125 1246305954475889991326543)
          ·
            refine ⟨1869458931713834986989815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246305954475889991326543 1869458931713834986989815)
            ·
              refine ⟨2804188397570752480484723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869458931713834986989815 2804188397570752480484723)
              ·
                refine ⟨4206282596356128720727085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804188397570752480484723 4206282596356128720727085)
                ·
                  refine ⟨1577355973633548270272657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4206282596356128720727085 1577355973633548270272657)
                  ·
                    refine ⟨1183016980225161202704493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577355973633548270272657 1183016980225161202704493)
                    ·
                      refine ⟨443631367584435451014185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1183016980225161202704493 443631367584435451014185)
                      ·
                        rfl

theorem cell23_863969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_863969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863969 prefixEnd_863969 := by exact prefixLift 863969
  have htrace : WordTrace (prefixWord ++ tailWord_863969) baseStart_863969 baseEnd_863969 := by
    simpa [prefixWord, tailWord_863969, baseEnd_863969] using wordTrace_append hprefix tailTrace_863969
  have hstable : (prefixWord ++ tailWord_863969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863969).length < 2 ^ (prefixWord ++ tailWord_863969).sum := by decide
  have hdescent : baseEnd_863969 < baseStart_863969 := by decide
  rcases family_descends (prefixWord ++ tailWord_863969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863986 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_863986 : Nat := 118140960795 + 863986 * 2 ^ 59
def prefixEnd_863986 : Nat := 4983230072969 + 3 ^ 40 * 863986 * 2
def baseEnd_863986 : Nat := 443640096755561884501607

theorem tailTrace_863986 : CollatzResearch.WordTrace tailWord_863986 prefixEnd_863986 443640096755561884501607 := by
  unfold tailWord_863986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878039561983438476572953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21008105498622502604194541 7878039561983438476572953)
  ·
    refine ⟨5908529671487578857429715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7878039561983438476572953 5908529671487578857429715)
    ·
      refine ⟨8862794507231368286144573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908529671487578857429715 8862794507231368286144573)
      ·
        refine ⟨3323547940211763107304215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8862794507231368286144573 3323547940211763107304215)
        ·
          refine ⟨4985321910317644660956323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323547940211763107304215 4985321910317644660956323)
          ·
            refine ⟨7477982865476466991434485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985321910317644660956323 7477982865476466991434485)
            ·
              refine ⟨701060893638418780446983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7477982865476466991434485 701060893638418780446983)
              ·
                refine ⟨1051591340457628170670475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701060893638418780446983 1051591340457628170670475)
                ·
                  refine ⟨1577387010686442256005713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051591340457628170670475 1577387010686442256005713)
                  ·
                    refine ⟨1183040258014831692004285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1577387010686442256005713 1183040258014831692004285)
                    ·
                      refine ⟨443640096755561884501607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1183040258014831692004285 443640096755561884501607)
                      ·
                        rfl

theorem cell23_863986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_863986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863986 prefixEnd_863986 := by exact prefixLift 863986
  have htrace : WordTrace (prefixWord ++ tailWord_863986) baseStart_863986 baseEnd_863986 := by
    simpa [prefixWord, tailWord_863986, baseEnd_863986] using wordTrace_append hprefix tailTrace_863986
  have hstable : (prefixWord ++ tailWord_863986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863986).length < 2 ^ (prefixWord ++ tailWord_863986).sum := by decide
  have hdescent : baseEnd_863986 < baseStart_863986 := by decide
  rcases family_descends (prefixWord ++ tailWord_863986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863999 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 3]
def baseStart_863999 : Nat := 118140960795 + 863999 * 2 ^ 59
def prefixEnd_863999 : Nat := 4983230072969 + 3 ^ 40 * 863999 * 2
def baseEnd_863999 : Nat := 443646772004070333639047

theorem tailTrace_863999 : CollatzResearch.WordTrace tailWord_863999 prefixEnd_863999 443646772004070333639047 := by
  unfold tailWord_863999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31512632396886657126515051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21008421597924438084343367 31512632396886657126515051)
  ·
    refine ⟨47268948595329985689772577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31512632396886657126515051 47268948595329985689772577)
    ·
      refine ⟨35451711446497489267329433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47268948595329985689772577 35451711446497489267329433)
      ·
        refine ⟨26588783584873116950497075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35451711446497489267329433 26588783584873116950497075)
        ·
          refine ⟨39883175377309675425745613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26588783584873116950497075 39883175377309675425745613)
          ·
            refine ⟨14956190766491128284654605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39883175377309675425745613 14956190766491128284654605)
            ·
              refine ⟨5608571537434173106745477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14956190766491128284654605 5608571537434173106745477)
              ·
                refine ⟨1051607163268907457514777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5608571537434173106745477 1051607163268907457514777)
                ·
                  refine ⟨788705372451680593136083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051607163268907457514777 788705372451680593136083)
                  ·
                    refine ⟨1183058058677520889704125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 788705372451680593136083 1183058058677520889704125)
                    ·
                      refine ⟨443646772004070333639047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1183058058677520889704125 443646772004070333639047)
                      ·
                        rfl

theorem cell23_863999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_863999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_863999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_863999 prefixEnd_863999 := by exact prefixLift 863999
  have htrace : WordTrace (prefixWord ++ tailWord_863999) baseStart_863999 baseEnd_863999 := by
    simpa [prefixWord, tailWord_863999, baseEnd_863999] using wordTrace_append hprefix tailTrace_863999
  have hstable : (prefixWord ++ tailWord_863999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863999).length < 2 ^ (prefixWord ++ tailWord_863999).sum := by decide
  have hdescent : baseEnd_863999 < baseStart_863999 := by decide
  rcases family_descends (prefixWord ++ tailWord_863999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864002 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_864002 : Nat := 118140960795 + 864002 * 2 ^ 59
def prefixEnd_864002 : Nat := 4983230072969 + 3 ^ 40 * 864002 * 2
def baseEnd_864002 : Nat := 147882770815344607300511

theorem tailTrace_864002 : CollatzResearch.WordTrace tailWord_864002 prefixEnd_864002 147882770815344607300511 := by
  unfold tailWord_864002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878185453968947159718565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21008494543917192425916173 7878185453968947159718565)
  ·
    refine ⟨1477159772619177592447231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7878185453968947159718565 1477159772619177592447231)
    ·
      refine ⟨2215739658928766388670847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477159772619177592447231 2215739658928766388670847)
      ·
        refine ⟨3323609488393149583006271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215739658928766388670847 3323609488393149583006271)
        ·
          refine ⟨4985414232589724374509407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323609488393149583006271 4985414232589724374509407)
          ·
            refine ⟨7478121348884586561764111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985414232589724374509407 7478121348884586561764111)
            ·
              refine ⟨11217182023326879842646167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7478121348884586561764111 11217182023326879842646167)
              ·
                refine ⟨16825773034990319763969251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11217182023326879842646167 16825773034990319763969251)
                ·
                  refine ⟨25238659552485479645953877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16825773034990319763969251 25238659552485479645953877)
                  ·
                    refine ⟨147882770815344607300511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25238659552485479645953877 147882770815344607300511)
                    ·
                      rfl

theorem cell23_864002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_864002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864002 prefixEnd_864002 := by exact prefixLift 864002
  have htrace : WordTrace (prefixWord ++ tailWord_864002) baseStart_864002 baseEnd_864002 := by
    simpa [prefixWord, tailWord_864002, baseEnd_864002] using wordTrace_append hprefix tailTrace_864002
  have hstable : (prefixWord ++ tailWord_864002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864002).length < 2 ^ (prefixWord ++ tailWord_864002).sum := by decide
  have hdescent : baseEnd_864002 < baseStart_864002 := by decide
  rcases family_descends (prefixWord ++ tailWord_864002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864055 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_864055 : Nat := 118140960795 + 864055 * 2 ^ 59
def prefixEnd_864055 : Nat := 4983230072969 + 3 ^ 40 * 864055 * 2
def baseEnd_864055 : Nat := 443675526920722114538789

theorem tailTrace_864055 : CollatzResearch.WordTrace tailWord_864055 prefixEnd_864055 443675526920722114538789 := by
  unfold tailWord_864055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31514674884683778690553619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21009783256455852460369079 31514674884683778690553619)
  ·
    refine ⟨47272012327025668035830429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31514674884683778690553619 47272012327025668035830429)
    ·
      refine ⟨17727004622634625513436411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47272012327025668035830429 17727004622634625513436411)
      ·
        refine ⟨26590506933951938270154617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727004622634625513436411 26590506933951938270154617)
        ·
          refine ⟨19942880200463953702615963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26590506933951938270154617 19942880200463953702615963)
          ·
            refine ⟨29914320300695930553923945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19942880200463953702615963 29914320300695930553923945)
            ·
              refine ⟨22435740225521947915442959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29914320300695930553923945 22435740225521947915442959)
              ·
                refine ⟨33653610338282921873164439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22435740225521947915442959 33653610338282921873164439)
                ·
                  refine ⟨50480415507424382809746659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33653610338282921873164439 50480415507424382809746659)
                  ·
                    refine ⟨75720623261136574214619989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50480415507424382809746659 75720623261136574214619989)
                    ·
                      refine ⟨443675526920722114538789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 75720623261136574214619989 443675526920722114538789)
                      ·
                        rfl

theorem cell23_864055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_864055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864055 prefixEnd_864055 := by exact prefixLift 864055
  have htrace : WordTrace (prefixWord ++ tailWord_864055) baseStart_864055 baseEnd_864055 := by
    simpa [prefixWord, tailWord_864055, baseEnd_864055] using wordTrace_append hprefix tailTrace_864055
  have hstable : (prefixWord ++ tailWord_864055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864055).length < 2 ^ (prefixWord ++ tailWord_864055).sum := by decide
  have hdescent : baseEnd_864055 < baseStart_864055 := by decide
  rcases family_descends (prefixWord ++ tailWord_864055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864056 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_864056 : Nat := 118140960795 + 864056 * 2 ^ 59
def prefixEnd_864056 : Nat := 4983230072969 + 3 ^ 40 * 864056 * 2
def baseEnd_864056 : Nat := 443676040401376610626285

theorem tailTrace_864056 : CollatzResearch.WordTrace tailWord_864056 prefixEnd_864056 443676040401376610626285 := by
  unfold tailWord_864056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757355678840077930670011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21009807571786770574226681 15757355678840077930670011)
  ·
    refine ⟨23636033518260116896005017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15757355678840077930670011 23636033518260116896005017)
    ·
      refine ⟨17727025138695087672003763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23636033518260116896005017 17727025138695087672003763)
      ·
        refine ⟨26590537708042631508005645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727025138695087672003763 26590537708042631508005645)
        ·
          refine ⟨9971451640515986815502117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26590537708042631508005645 9971451640515986815502117)
          ·
            refine ⟨1869647182596747527906647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9971451640515986815502117 1869647182596747527906647)
            ·
              refine ⟨2804470773895121291859971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869647182596747527906647 2804470773895121291859971)
              ·
                refine ⟨4206706160842681937789957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804470773895121291859971 4206706160842681937789957)
                ·
                  refine ⟨788757405158002863335617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4206706160842681937789957 788757405158002863335617)
                  ·
                    refine ⟨591568053868502147501713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788757405158002863335617 591568053868502147501713)
                    ·
                      refine ⟨443676040401376610626285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591568053868502147501713 443676040401376610626285)
                      ·
                        rfl

theorem cell23_864056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_864056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864056 prefixEnd_864056 := by exact prefixLift 864056
  have htrace : WordTrace (prefixWord ++ tailWord_864056) baseStart_864056 baseEnd_864056 := by
    simpa [prefixWord, tailWord_864056, baseEnd_864056] using wordTrace_append hprefix tailTrace_864056
  have hstable : (prefixWord ++ tailWord_864056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864056).length < 2 ^ (prefixWord ++ tailWord_864056).sum := by decide
  have hdescent : baseEnd_864056 < baseStart_864056 := by decide
  rcases family_descends (prefixWord ++ tailWord_864056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864073 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 2, 2, 2]
def baseStart_864073 : Nat := 118140960795 + 864073 * 2 ^ 59
def prefixEnd_864073 : Nat := 4983230072969 + 3 ^ 40 * 864073 * 2
def baseEnd_864073 : Nat := 443684769572503044113707

theorem tailTrace_864073 : CollatzResearch.WordTrace tailWord_864073 prefixEnd_864073 443684769572503044113707 := by
  unfold tailWord_864073
  simp only [CollatzResearch.WordTrace]
  refine ⟨31515331398618567764708873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21010220932412378509805915 31515331398618567764708873)
  ·
    refine ⟨23636498548963925823531655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31515331398618567764708873 23636498548963925823531655)
    ·
      refine ⟨35454747823445888735297483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23636498548963925823531655 35454747823445888735297483)
      ·
        refine ⟨53182121735168833102946225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35454747823445888735297483 53182121735168833102946225)
        ·
          refine ⟨39886591301376624827209669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53182121735168833102946225 39886591301376624827209669)
          ·
            refine ⟨7478735869008117155101813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39886591301376624827209669 7478735869008117155101813)
            ·
              refine ⟨701131487719510983290795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7478735869008117155101813 701131487719510983290795)
              ·
                refine ⟨1051697231579266474936193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701131487719510983290795 1051697231579266474936193)
                ·
                  refine ⟨788772923684449856202145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1051697231579266474936193 788772923684449856202145)
                  ·
                    refine ⟨591579692763337392151609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788772923684449856202145 591579692763337392151609)
                    ·
                      refine ⟨443684769572503044113707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591579692763337392151609 443684769572503044113707)
                      ·
                        rfl

theorem cell23_864073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 2, 2].length) (baseStart_864073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864073 prefixEnd_864073 := by exact prefixLift 864073
  have htrace : WordTrace (prefixWord ++ tailWord_864073) baseStart_864073 baseEnd_864073 := by
    simpa [prefixWord, tailWord_864073, baseEnd_864073] using wordTrace_append hprefix tailTrace_864073
  have hstable : (prefixWord ++ tailWord_864073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864073).length < 2 ^ (prefixWord ++ tailWord_864073).sum := by decide
  have hdescent : baseEnd_864073 < baseStart_864073 := by decide
  rcases family_descends (prefixWord ++ tailWord_864073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864096 : List Nat := [2, 1, 1, 3, 3, 4, 1, 3, 5]
def baseStart_864096 : Nat := 118140960795 + 864096 * 2 ^ 59
def prefixEnd_864096 : Nat := 4983230072969 + 3 ^ 40 * 864096 * 2
def baseEnd_864096 : Nat := 49299619958617383791789

theorem tailTrace_864096 : CollatzResearch.WordTrace tailWord_864096 prefixEnd_864096 49299619958617383791789 := by
  unfold tailWord_864096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758085138767621346398071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21010780185023495128530761 15758085138767621346398071)
  ·
    refine ⟨23637127708151432019597107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15758085138767621346398071 23637127708151432019597107)
    ·
      refine ⟨35455691562227148029395661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23637127708151432019597107 35455691562227148029395661)
      ·
        refine ⟨13295884335835180511023373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35455691562227148029395661 13295884335835180511023373)
        ·
          refine ⟨4985956625938192691633765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13295884335835180511023373 4985956625938192691633765)
          ·
            refine ⟨934866867363411129681331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4985956625938192691633765 934866867363411129681331)
            ·
              refine ⟨1402300301045116694521997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934866867363411129681331 1402300301045116694521997)
              ·
                refine ⟨525862612891918760445749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402300301045116694521997 525862612891918760445749)
                ·
                  refine ⟨49299619958617383791789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525862612891918760445749 49299619958617383791789)
                  ·
                    rfl

theorem cell23_864096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 5].length) (baseStart_864096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864096 prefixEnd_864096 := by exact prefixLift 864096
  have htrace : WordTrace (prefixWord ++ tailWord_864096) baseStart_864096 baseEnd_864096 := by
    simpa [prefixWord, tailWord_864096, baseEnd_864096] using wordTrace_append hprefix tailTrace_864096
  have hstable : (prefixWord ++ tailWord_864096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864096).length < 2 ^ (prefixWord ++ tailWord_864096).sum := by decide
  have hdescent : baseEnd_864096 < baseStart_864096 := by decide
  rcases family_descends (prefixWord ++ tailWord_864096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864146 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_864146 : Nat := 118140960795 + 864146 * 2 ^ 59
def prefixEnd_864146 : Nat := 4983230072969 + 3 ^ 40 * 864146 * 2
def baseEnd_864146 : Nat := 443722253660281258500871

theorem tailTrace_864146 : CollatzResearch.WordTrace tailWord_864146 prefixEnd_864146 443722253660281258500871 := by
  unfold tailWord_864146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879498481838525308029073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21011995951569400821410861 7879498481838525308029073)
  ·
    refine ⟨5909623861378893981021805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7879498481838525308029073 5909623861378893981021805)
    ·
      refine ⟨2216108948017085242883177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5909623861378893981021805 2216108948017085242883177)
      ·
        refine ⟨1662081711012813932162383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2216108948017085242883177 1662081711012813932162383)
        ·
          refine ⟨2493122566519220898243575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662081711012813932162383 2493122566519220898243575)
          ·
            refine ⟨3739683849778831347365363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493122566519220898243575 3739683849778831347365363)
            ·
              refine ⟨5609525774668247021048045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739683849778831347365363 5609525774668247021048045)
              ·
                refine ⟨2103572165500592632893017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5609525774668247021048045 2103572165500592632893017)
                ·
                  refine ⟨1577679124125444474669763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2103572165500592632893017 1577679124125444474669763)
                  ·
                    refine ⟨2366518686188166712004645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1577679124125444474669763 2366518686188166712004645)
                    ·
                      refine ⟨443722253660281258500871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2366518686188166712004645 443722253660281258500871)
                      ·
                        rfl

theorem cell23_864146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_864146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864146 prefixEnd_864146 := by exact prefixLift 864146
  have htrace : WordTrace (prefixWord ++ tailWord_864146) baseStart_864146 baseEnd_864146 := by
    simpa [prefixWord, tailWord_864146, baseEnd_864146] using wordTrace_append hprefix tailTrace_864146
  have hstable : (prefixWord ++ tailWord_864146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864146).length < 2 ^ (prefixWord ++ tailWord_864146).sum := by decide
  have hdescent : baseEnd_864146 < baseStart_864146 := by decide
  rcases family_descends (prefixWord ++ tailWord_864146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864180 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_864180 : Nat := 118140960795 + 864180 * 2 ^ 59
def prefixEnd_864180 : Nat := 4983230072969 + 3 ^ 40 * 864180 * 2
def baseEnd_864180 : Nat := 443739712002534125475715

theorem tailTrace_864180 : CollatzResearch.WordTrace tailWord_864180 prefixEnd_864180 443739712002534125475715 := by
  unfold tailWord_864180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759617004615462519426997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21012822672820616692569329 15759617004615462519426997)
  ·
    refine ⟨1477464094182699611196281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15759617004615462519426997 1477464094182699611196281)
    ·
      refine ⟨1108098070637024708397211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1477464094182699611196281 1108098070637024708397211)
      ·
        refine ⟨1662147105955537062595817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108098070637024708397211 1662147105955537062595817)
        ·
          refine ⟨1246610329466652796946863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1662147105955537062595817 1246610329466652796946863)
          ·
            refine ⟨1869915494199979195420295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246610329466652796946863 1869915494199979195420295)
            ·
              refine ⟨2804873241299968793130443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869915494199979195420295 2804873241299968793130443)
              ·
                refine ⟨4207309861949953189695665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804873241299968793130443 4207309861949953189695665)
                ·
                  refine ⟨3155482396462464892271749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4207309861949953189695665 3155482396462464892271749)
                  ·
                    refine ⟨591652949336712167300953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3155482396462464892271749 591652949336712167300953)
                    ·
                      refine ⟨443739712002534125475715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591652949336712167300953 443739712002534125475715)
                      ·
                        rfl

theorem cell23_864180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_864180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864180 prefixEnd_864180 := by exact prefixLift 864180
  have htrace : WordTrace (prefixWord ++ tailWord_864180) baseStart_864180 baseEnd_864180 := by
    simpa [prefixWord, tailWord_864180, baseEnd_864180] using wordTrace_append hprefix tailTrace_864180
  have hstable : (prefixWord ++ tailWord_864180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864180).length < 2 ^ (prefixWord ++ tailWord_864180).sum := by decide
  have hdescent : baseEnd_864180 < baseStart_864180 := by decide
  rcases family_descends (prefixWord ++ tailWord_864180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864192 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_864192 : Nat := 118140960795 + 864192 * 2 ^ 59
def prefixEnd_864192 : Nat := 4983230072969 + 3 ^ 40 * 864192 * 2
def baseEnd_864192 : Nat := 443745873770388078525659

theorem tailTrace_864192 : CollatzResearch.WordTrace tailWord_864192 prefixEnd_864192 443745873770388078525659 := by
  unfold tailWord_864192
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759835842593725544145415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21013114456791634058860553 15759835842593725544145415)
  ·
    refine ⟨23639753763890588316218123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15759835842593725544145415 23639753763890588316218123)
    ·
      refine ⟨35459630645835882474327185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23639753763890588316218123 35459630645835882474327185)
      ·
        refine ⟨26594722984376911855745389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35459630645835882474327185 26594722984376911855745389)
        ·
          refine ⟨9973021119141341945904521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26594722984376911855745389 9973021119141341945904521)
          ·
            refine ⟨7479765839356006459428391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973021119141341945904521 7479765839356006459428391)
            ·
              refine ⟨11219648759034009689142587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479765839356006459428391 11219648759034009689142587)
              ·
                refine ⟨16829473138551014533713881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11219648759034009689142587 16829473138551014533713881)
                ·
                  refine ⟨12622104853913260900285411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16829473138551014533713881 12622104853913260900285411)
                  ·
                    refine ⟨18933157280869891350428117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12622104853913260900285411 18933157280869891350428117)
                    ·
                      refine ⟨443745873770388078525659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18933157280869891350428117 443745873770388078525659)
                      ·
                        rfl

theorem cell23_864192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_864192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864192 prefixEnd_864192 := by exact prefixLift 864192
  have htrace : WordTrace (prefixWord ++ tailWord_864192) baseStart_864192 baseEnd_864192 := by
    simpa [prefixWord, tailWord_864192, baseEnd_864192] using wordTrace_append hprefix tailTrace_864192
  have hstable : (prefixWord ++ tailWord_864192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864192).length < 2 ^ (prefixWord ++ tailWord_864192).sum := by decide
  have hdescent : baseEnd_864192 < baseStart_864192 := by decide
  rcases family_descends (prefixWord ++ tailWord_864192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864199 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 1, 5]
def baseStart_864199 : Nat := 118140960795 + 864199 * 2 ^ 59
def prefixEnd_864199 : Nat := 4983230072969 + 3 ^ 40 * 864199 * 2
def baseEnd_864199 : Nat := 147916489378323183712709

theorem tailTrace_864199 : CollatzResearch.WordTrace tailWord_864199 prefixEnd_864199 147916489378323183712709 := by
  unfold tailWord_864199
  simp only [CollatzResearch.WordTrace]
  refine ⟨31519926996162091283795651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21013284664108060855863767 31519926996162091283795651)
  ·
    refine ⟨47279890494243136925693477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31519926996162091283795651 47279890494243136925693477)
    ·
      refine ⟨8864979467670588173567527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47279890494243136925693477 8864979467670588173567527)
      ·
        refine ⟨13297469201505882260351291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8864979467670588173567527 13297469201505882260351291)
        ·
          refine ⟨19946203802258823390526937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297469201505882260351291 19946203802258823390526937)
          ·
            refine ⟨14959652851694117542895203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19946203802258823390526937 14959652851694117542895203)
            ·
              refine ⟨22439479277541176314342805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14959652851694117542895203 22439479277541176314342805)
              ·
                refine ⟨1051850591134742639734819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22439479277541176314342805 1051850591134742639734819)
                ·
                  refine ⟨1577775886702113959602229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1051850591134742639734819 1577775886702113959602229)
                  ·
                    refine ⟨147916489378323183712709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1577775886702113959602229 147916489378323183712709)
                    ·
                      rfl

theorem cell23_864199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_864199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864199 prefixEnd_864199 := by exact prefixLift 864199
  have htrace : WordTrace (prefixWord ++ tailWord_864199) baseStart_864199 baseEnd_864199 := by
    simpa [prefixWord, tailWord_864199, baseEnd_864199] using wordTrace_append hprefix tailTrace_864199
  have hstable : (prefixWord ++ tailWord_864199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864199).length < 2 ^ (prefixWord ++ tailWord_864199).sum := by decide
  have hdescent : baseEnd_864199 < baseStart_864199 := by decide
  rcases family_descends (prefixWord ++ tailWord_864199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864206 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_864206 : Nat := 118140960795 + 864206 * 2 ^ 59
def prefixEnd_864206 : Nat := 4983230072969 + 3 ^ 40 * 864206 * 2
def baseEnd_864206 : Nat := 443753062499551023750595

theorem tailTrace_864206 : CollatzResearch.WordTrace tailWord_864206 prefixEnd_864206 443753062499551023750595 := by
  unfold tailWord_864206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940022788392091434912559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21013454871424487652866981 3940022788392091434912559)
  ·
    refine ⟨5910034182588137152368839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3940022788392091434912559 5910034182588137152368839)
    ·
      refine ⟨8865051273882205728553259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910034182588137152368839 8865051273882205728553259)
      ·
        refine ⟨13297576910823308592829889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865051273882205728553259 13297576910823308592829889)
        ·
          refine ⟨9973182683117481444622417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13297576910823308592829889 9973182683117481444622417)
          ·
            refine ⟨7479887012338111083466813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973182683117481444622417 7479887012338111083466813)
            ·
              refine ⟨2804957629626791656300055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7479887012338111083466813 2804957629626791656300055)
              ·
                refine ⟨4207436444440187484450083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2804957629626791656300055 4207436444440187484450083)
                ·
                  refine ⟨6311154666660281226675125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207436444440187484450083 6311154666660281226675125)
                  ·
                    refine ⟨591670749999401365000793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6311154666660281226675125 591670749999401365000793)
                    ·
                      refine ⟨443753062499551023750595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591670749999401365000793 443753062499551023750595)
                      ·
                        rfl

theorem cell23_864206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_864206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864206 prefixEnd_864206 := by exact prefixLift 864206
  have htrace : WordTrace (prefixWord ++ tailWord_864206) baseStart_864206 baseEnd_864206 := by
    simpa [prefixWord, tailWord_864206, baseEnd_864206] using wordTrace_append hprefix tailTrace_864206
  have hstable : (prefixWord ++ tailWord_864206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864206).length < 2 ^ (prefixWord ++ tailWord_864206).sum := by decide
  have hdescent : baseEnd_864206 < baseStart_864206 := by decide
  rcases family_descends (prefixWord ++ tailWord_864206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864239 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_864239 : Nat := 118140960795 + 864239 * 2 ^ 59
def prefixEnd_864239 : Nat := 4983230072969 + 3 ^ 40 * 864239 * 2
def baseEnd_864239 : Nat := 443770007361149394637943

theorem tailTrace_864239 : CollatzResearch.WordTrace tailWord_864239 prefixEnd_864239 443770007361149394637943 := by
  unfold tailWord_864239
  simp only [CollatzResearch.WordTrace]
  refine ⟨31521385916017178115251771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21014257277344785410167847 31521385916017178115251771)
  ·
    refine ⟨47282078874025767172877657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31521385916017178115251771 47282078874025767172877657)
    ·
      refine ⟨35461559155519325379658243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47282078874025767172877657 35461559155519325379658243)
      ·
        refine ⟨53192338733278988069487365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35461559155519325379658243 53192338733278988069487365)
        ·
          refine ⟨9973563512489810263028881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53192338733278988069487365 9973563512489810263028881)
          ·
            refine ⟨7480172634367357697271661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973563512489810263028881 7480172634367357697271661)
            ·
              refine ⟨2805064737887759136476873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7480172634367357697271661 2805064737887759136476873)
              ·
                refine ⟨2103798553415819352357655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805064737887759136476873 2103798553415819352357655)
                ·
                  refine ⟨3155697830123729028536483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2103798553415819352357655 3155697830123729028536483)
                  ·
                    refine ⟨4733546745185593542804725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3155697830123729028536483 4733546745185593542804725)
                    ·
                      refine ⟨443770007361149394637943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4733546745185593542804725 443770007361149394637943)
                      ·
                        rfl

theorem cell23_864239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_864239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864239 prefixEnd_864239 := by exact prefixLift 864239
  have htrace : WordTrace (prefixWord ++ tailWord_864239) baseStart_864239 baseEnd_864239 := by
    simpa [prefixWord, tailWord_864239, baseEnd_864239] using wordTrace_append hprefix tailTrace_864239
  have hstable : (prefixWord ++ tailWord_864239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864239).length < 2 ^ (prefixWord ++ tailWord_864239).sum := by decide
  have hdescent : baseEnd_864239 < baseStart_864239 := by decide
  rcases family_descends (prefixWord ++ tailWord_864239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864249 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_864249 : Nat := 118140960795 + 864249 * 2 ^ 59
def prefixEnd_864249 : Nat := 4983230072969 + 3 ^ 40 * 864249 * 2
def baseEnd_864249 : Nat := 443775142167694355512897

theorem tailTrace_864249 : CollatzResearch.WordTrace tailWord_864249 prefixEnd_864249 443775142167694355512897 := by
  unfold tailWord_864249
  simp only [CollatzResearch.WordTrace]
  refine ⟨31521750645980949823115801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21014500430653966548743867 31521750645980949823115801)
  ·
    refine ⟨23641312984485712367336851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31521750645980949823115801 23641312984485712367336851)
    ·
      refine ⟨35461969476728568551005277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23641312984485712367336851 35461969476728568551005277)
      ·
        refine ⟨13298238553773213206626979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35461969476728568551005277 13298238553773213206626979)
        ·
          refine ⟨19947357830659819809940469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298238553773213206626979 19947357830659819809940469)
          ·
            refine ⟨1870064796624358107181919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19947357830659819809940469 1870064796624358107181919)
            ·
              refine ⟨2805097194936537160772879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870064796624358107181919 2805097194936537160772879)
              ·
                refine ⟨4207645792404805741159319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2805097194936537160772879 4207645792404805741159319)
                ·
                  refine ⟨6311468688607208611738979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4207645792404805741159319 6311468688607208611738979)
                  ·
                    refine ⟨9467203032910812917608469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6311468688607208611738979 9467203032910812917608469)
                    ·
                      refine ⟨443775142167694355512897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9467203032910812917608469 443775142167694355512897)
                      ·
                        rfl

theorem cell23_864249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_864249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864249 prefixEnd_864249 := by exact prefixLift 864249
  have htrace : WordTrace (prefixWord ++ tailWord_864249) baseStart_864249 baseEnd_864249 := by
    simpa [prefixWord, tailWord_864249, baseEnd_864249] using wordTrace_append hprefix tailTrace_864249
  have hstable : (prefixWord ++ tailWord_864249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864249).length < 2 ^ (prefixWord ++ tailWord_864249).sum := by decide
  have hdescent : baseEnd_864249 < baseStart_864249 := by decide
  rcases family_descends (prefixWord ++ tailWord_864249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864253 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_864253 : Nat := 118140960795 + 864253 * 2 ^ 59
def prefixEnd_864253 : Nat := 4983230072969 + 3 ^ 40 * 864253 * 2
def baseEnd_864253 : Nat := 443777196090312339862879

theorem tailTrace_864253 : CollatzResearch.WordTrace tailWord_864253 prefixEnd_864253 443777196090312339862879 := by
  unfold tailWord_864253
  simp only [CollatzResearch.WordTrace]
  refine ⟨31521896537966458506261413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21014597691977639004174275 31521896537966458506261413)
  ·
    refine ⟨5910355600868710969924015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31521896537966458506261413 5910355600868710969924015)
    ·
      refine ⟨8865533401303066454886023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910355600868710969924015 8865533401303066454886023)
      ·
        refine ⟨13298300101954599682329035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865533401303066454886023 13298300101954599682329035)
        ·
          refine ⟨19947450152931899523493553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13298300101954599682329035 19947450152931899523493553)
          ·
            refine ⟨14960587614698924642620165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19947450152931899523493553 14960587614698924642620165)
            ·
              refine ⟨2805110177756048370491281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14960587614698924642620165 2805110177756048370491281)
              ·
                refine ⟨2103832633317036277868461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805110177756048370491281 2103832633317036277868461)
                ·
                  refine ⟨788937237493888604200673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2103832633317036277868461 788937237493888604200673)
                  ·
                    refine ⟨591702928120416453150505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788937237493888604200673 591702928120416453150505)
                    ·
                      refine ⟨443777196090312339862879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591702928120416453150505 443777196090312339862879)
                      ·
                        rfl

theorem cell23_864253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_864253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864253 prefixEnd_864253 := by exact prefixLift 864253
  have htrace : WordTrace (prefixWord ++ tailWord_864253) baseStart_864253 baseEnd_864253 := by
    simpa [prefixWord, tailWord_864253, baseEnd_864253] using wordTrace_append hprefix tailTrace_864253
  have hstable : (prefixWord ++ tailWord_864253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864253).length < 2 ^ (prefixWord ++ tailWord_864253).sum := by decide
  have hdescent : baseEnd_864253 < baseStart_864253 := by decide
  rcases family_descends (prefixWord ++ tailWord_864253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864287 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 1, 2, 2]
def baseStart_864287 : Nat := 118140960795 + 864287 * 2 ^ 59
def prefixEnd_864287 : Nat := 4983230072969 + 3 ^ 40 * 864287 * 2
def baseEnd_864287 : Nat := 443794654432565206837723

theorem tailTrace_864287 : CollatzResearch.WordTrace tailWord_864287 prefixEnd_864287 443794654432565206837723 := by
  unfold tailWord_864287
  simp only [CollatzResearch.WordTrace]
  refine ⟨31523136619843282312999115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21015424413228854875332743 31523136619843282312999115)
  ·
    refine ⟨47284704929764923469498673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31523136619843282312999115 47284704929764923469498673)
    ·
      refine ⟨35463528697323692602124005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47284704929764923469498673 35463528697323692602124005)
      ·
        refine ⟨6649411630748192362898251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35463528697323692602124005 6649411630748192362898251)
        ·
          refine ⟨9974117446122288544347377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6649411630748192362898251 9974117446122288544347377)
          ·
            refine ⟨7480588084591716408260533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9974117446122288544347377 7480588084591716408260533)
            ·
              refine ⟨701305132930473413274425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7480588084591716408260533 701305132930473413274425)
              ·
                refine ⟨525978849697855059955819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701305132930473413274425 525978849697855059955819)
                ·
                  refine ⟨788968274546782589933729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525978849697855059955819 788968274546782589933729)
                  ·
                    refine ⟨591726205910086942450297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 788968274546782589933729 591726205910086942450297)
                    ·
                      refine ⟨443794654432565206837723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591726205910086942450297 443794654432565206837723)
                      ·
                        rfl

theorem cell23_864287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_864287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864287 prefixEnd_864287 := by exact prefixLift 864287
  have htrace : WordTrace (prefixWord ++ tailWord_864287) baseStart_864287 baseEnd_864287 := by
    simpa [prefixWord, tailWord_864287, baseEnd_864287] using wordTrace_append hprefix tailTrace_864287
  have hstable : (prefixWord ++ tailWord_864287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864287).length < 2 ^ (prefixWord ++ tailWord_864287).sum := by decide
  have hdescent : baseEnd_864287 < baseStart_864287 := by decide
  rcases family_descends (prefixWord ++ tailWord_864287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864329 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_864329 : Nat := 118140960795 + 864329 * 2 ^ 59
def prefixEnd_864329 : Nat := 4983230072969 + 3 ^ 40 * 864329 * 2
def baseEnd_864329 : Nat := 443816220620054042512529

theorem tailTrace_864329 : CollatzResearch.WordTrace tailWord_864329 prefixEnd_864329 443816220620054042512529 := by
  unfold tailWord_864329
  simp only [CollatzResearch.WordTrace]
  refine ⟨31524668485691123486028041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21016445657127415657352027 31524668485691123486028041)
  ·
    refine ⟨23643501364268342614521031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31524668485691123486028041 23643501364268342614521031)
    ·
      refine ⟨35465252046402513921781547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23643501364268342614521031 35465252046402513921781547)
      ·
        refine ⟨53197878069603770882672321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35465252046402513921781547 53197878069603770882672321)
        ·
          refine ⟨39898408552202828162004241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53197878069603770882672321 39898408552202828162004241)
          ·
            refine ⟨29923806414152121121503181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39898408552202828162004241 29923806414152121121503181)
            ·
              refine ⟨11221427405307045420563693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29923806414152121121503181 11221427405307045420563693)
              ·
                refine ⟨4208035276990142032711385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11221427405307045420563693 4208035276990142032711385)
                ·
                  refine ⟨3156026457742606524533539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4208035276990142032711385 3156026457742606524533539)
                  ·
                    refine ⟨4734039686613909786800309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3156026457742606524533539 4734039686613909786800309)
                    ·
                      refine ⟨443816220620054042512529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4734039686613909786800309 443816220620054042512529)
                      ·
                        rfl

theorem cell23_864329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_864329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864329 prefixEnd_864329 := by exact prefixLift 864329
  have htrace : WordTrace (prefixWord ++ tailWord_864329) baseStart_864329 baseEnd_864329 := by
    simpa [prefixWord, tailWord_864329, baseEnd_864329] using wordTrace_append hprefix tailTrace_864329
  have hstable : (prefixWord ++ tailWord_864329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864329).length < 2 ^ (prefixWord ++ tailWord_864329).sum := by decide
  have hdescent : baseEnd_864329 < baseStart_864329 := by decide
  rcases family_descends (prefixWord ++ tailWord_864329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864343 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_864343 : Nat := 118140960795 + 864343 * 2 ^ 59
def prefixEnd_864343 : Nat := 4983230072969 + 3 ^ 40 * 864343 * 2
def baseEnd_864343 : Nat := 443823409349216987737465

theorem tailTrace_864343 : CollatzResearch.WordTrace tailWord_864343 prefixEnd_864343 443823409349216987737465 := by
  unfold tailWord_864343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31525179107640403877037683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21016786071760269251358455 31525179107640403877037683)
  ·
    refine ⟨47287768661460605815556525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31525179107640403877037683 47287768661460605815556525)
    ·
      refine ⟨17732913248047727180833697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47287768661460605815556525 17732913248047727180833697)
      ·
        refine ⟨13299684936035795385625273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17732913248047727180833697 13299684936035795385625273)
        ·
          refine ⟨9974763702026846539218955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13299684936035795385625273 9974763702026846539218955)
          ·
            refine ⟨14962145553040269808828433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9974763702026846539218955 14962145553040269808828433)
            ·
              refine ⟨11221609164780202356621325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14962145553040269808828433 11221609164780202356621325)
              ·
                refine ⟨4208103436792575883732997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11221609164780202356621325 4208103436792575883732997)
                ·
                  refine ⟨789019394398607978199937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4208103436792575883732997 789019394398607978199937)
                  ·
                    refine ⟨591764545798955983649953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789019394398607978199937 591764545798955983649953)
                    ·
                      refine ⟨443823409349216987737465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591764545798955983649953 443823409349216987737465)
                      ·
                        rfl

theorem cell23_864343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_864343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864343 prefixEnd_864343 := by exact prefixLift 864343
  have htrace : WordTrace (prefixWord ++ tailWord_864343) baseStart_864343 baseEnd_864343 := by
    simpa [prefixWord, tailWord_864343, baseEnd_864343] using wordTrace_append hprefix tailTrace_864343
  have hstable : (prefixWord ++ tailWord_864343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864343).length < 2 ^ (prefixWord ++ tailWord_864343).sum := by decide
  have hdescent : baseEnd_864343 < baseStart_864343 := by decide
  rcases family_descends (prefixWord ++ tailWord_864343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864366 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_864366 : Nat := 118140960795 + 864366 * 2 ^ 59
def prefixEnd_864366 : Nat := 4983230072969 + 3 ^ 40 * 864366 * 2
def baseEnd_864366 : Nat := 49315024378252266416651

theorem tailTrace_864366 : CollatzResearch.WordTrace tailWord_864366 prefixEnd_864366 49315024378252266416651 := by
  unfold tailWord_864366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940752248319634850640619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21017345324371385870083301 3940752248319634850640619)
  ·
    refine ⟨5911128372479452275960929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3940752248319634850640619 5911128372479452275960929)
    ·
      refine ⟨4433346279359589206970697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5911128372479452275960929 4433346279359589206970697)
      ·
        refine ⟨3325009709519691905228023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4433346279359589206970697 3325009709519691905228023)
        ·
          refine ⟨4987514564279537857842035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325009709519691905228023 4987514564279537857842035)
          ·
            refine ⟨7481271846419306786763053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987514564279537857842035 7481271846419306786763053)
            ·
              refine ⟨2805476942407240045036145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7481271846419306786763053 2805476942407240045036145)
              ·
                refine ⟨2104107706805430033777109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2805476942407240045036145 2104107706805430033777109)
                ·
                  refine ⟨49315024378252266416651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2104107706805430033777109 49315024378252266416651)
                  ·
                    rfl

theorem cell23_864366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_864366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864366 prefixEnd_864366 := by exact prefixLift 864366
  have htrace : WordTrace (prefixWord ++ tailWord_864366) baseStart_864366 baseEnd_864366 := by
    simpa [prefixWord, tailWord_864366, baseEnd_864366] using wordTrace_append hprefix tailTrace_864366
  have hstable : (prefixWord ++ tailWord_864366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864366).length < 2 ^ (prefixWord ++ tailWord_864366).sum := by decide
  have hdescent : baseEnd_864366 < baseStart_864366 := by decide
  rcases family_descends (prefixWord ++ tailWord_864366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864416 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_864416 : Nat := 118140960795 + 864416 * 2 ^ 59
def prefixEnd_864416 : Nat := 4983230072969 + 3 ^ 40 * 864416 * 2
def baseEnd_864416 : Nat := 443860893436995202124629

theorem tailTrace_864416 : CollatzResearch.WordTrace tailWord_864416 prefixEnd_864416 443860893436995202124629 := by
  unfold tailWord_864416
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763920818187968672222551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21018561090917291562963401 15763920818187968672222551)
  ·
    refine ⟨23645881227281953008333827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15763920818187968672222551 23645881227281953008333827)
    ·
      refine ⟨35468821840922929512500741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23645881227281953008333827 35468821840922929512500741)
      ·
        refine ⟨6650404095173049283593889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35468821840922929512500741 6650404095173049283593889)
        ·
          refine ⟨4987803071379786962695417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6650404095173049283593889 4987803071379786962695417)
          ·
            refine ⟨3740852303534840222021563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987803071379786962695417 3740852303534840222021563)
            ·
              refine ⟨5611278455302260333032345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740852303534840222021563 5611278455302260333032345)
              ·
                refine ⟨4208458841476695249774259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5611278455302260333032345 4208458841476695249774259)
                ·
                  refine ⟨6312688262215042874661389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4208458841476695249774259 6312688262215042874661389)
                  ·
                    refine ⟨2367258098330641077998021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6312688262215042874661389 2367258098330641077998021)
                    ·
                      refine ⟨443860893436995202124629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2367258098330641077998021 443860893436995202124629)
                      ·
                        rfl

theorem cell23_864416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_864416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864416 prefixEnd_864416 := by exact prefixLift 864416
  have htrace : WordTrace (prefixWord ++ tailWord_864416) baseStart_864416 baseEnd_864416 := by
    simpa [prefixWord, tailWord_864416, baseEnd_864416] using wordTrace_append hprefix tailTrace_864416
  have hstable : (prefixWord ++ tailWord_864416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864416).length < 2 ^ (prefixWord ++ tailWord_864416).sum := by decide
  have hdescent : baseEnd_864416 < baseStart_864416 := by decide
  rcases family_descends (prefixWord ++ tailWord_864416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864456 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 6]
def baseStart_864456 : Nat := 118140960795 + 864456 * 2 ^ 59
def prefixEnd_864456 : Nat := 4983230072969 + 3 ^ 40 * 864456 * 2
def baseEnd_864456 : Nat := 49320159184797227291605

theorem tailTrace_864456 : CollatzResearch.WordTrace tailWord_864456 prefixEnd_864456 49320159184797227291605 := by
  unfold tailWord_864456
  simp only [CollatzResearch.WordTrace]
  refine ⟨15764650278115512087950611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21019533704154016117267481 15764650278115512087950611)
  ·
    refine ⟨23646975417173268131925917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15764650278115512087950611 23646975417173268131925917)
    ·
      refine ⟨8867615781439975549472219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23646975417173268131925917 8867615781439975549472219)
      ·
        refine ⟨13301423672159963324208329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8867615781439975549472219 13301423672159963324208329)
        ·
          refine ⟨9976067754119972493156247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13301423672159963324208329 9976067754119972493156247)
          ·
            refine ⟨14964101631179958739734371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976067754119972493156247 14964101631179958739734371)
            ·
              refine ⟨22446152446769938109601557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14964101631179958739734371 22446152446769938109601557)
              ·
                refine ⟨1052163395942340848887573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22446152446769938109601557 1052163395942340848887573)
                ·
                  refine ⟨49320159184797227291605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1052163395942340848887573 49320159184797227291605)
                  ·
                    rfl

theorem cell23_864456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_864456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864456 prefixEnd_864456 := by exact prefixLift 864456
  have htrace : WordTrace (prefixWord ++ tailWord_864456) baseStart_864456 baseEnd_864456 := by
    simpa [prefixWord, tailWord_864456, baseEnd_864456] using wordTrace_append hprefix tailTrace_864456
  have hstable : (prefixWord ++ tailWord_864456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864456).length < 2 ^ (prefixWord ++ tailWord_864456).sum := by decide
  have hdescent : baseEnd_864456 < baseStart_864456 := by decide
  rcases family_descends (prefixWord ++ tailWord_864456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864473 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 6]
def baseStart_864473 : Nat := 118140960795 + 864473 * 2 ^ 59
def prefixEnd_864473 : Nat := 4983230072969 + 3 ^ 40 * 864473 * 2
def baseEnd_864473 : Nat := 49321129092700164345763

theorem tailTrace_864473 : CollatzResearch.WordTrace tailWord_864473 prefixEnd_864473 49321129092700164345763 := by
  unfold tailWord_864473
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529920597169436079270073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21019947064779624052846715 31529920597169436079270073)
  ·
    refine ⟨23647440447877077059452555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31529920597169436079270073 23647440447877077059452555)
    ·
      refine ⟨35471160671815615589178833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23647440447877077059452555 35471160671815615589178833)
      ·
        refine ⟨26603370503861711691884125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35471160671815615589178833 26603370503861711691884125)
        ·
          refine ⟨9976263938948141884456547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26603370503861711691884125 9976263938948141884456547)
          ·
            refine ⟨14964395908422212826684821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9976263938948141884456547 14964395908422212826684821)
            ·
              refine ⟨701456058207291226250851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14964395908422212826684821 701456058207291226250851)
              ·
                refine ⟨1052184087310936839376277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701456058207291226250851 1052184087310936839376277)
                ·
                  refine ⟨49321129092700164345763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1052184087310936839376277 49321129092700164345763)
                  ·
                    rfl

theorem cell23_864473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 6].length) (baseStart_864473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864473 prefixEnd_864473 := by exact prefixLift 864473
  have htrace : WordTrace (prefixWord ++ tailWord_864473) baseStart_864473 baseEnd_864473 := by
    simpa [prefixWord, tailWord_864473, baseEnd_864473] using wordTrace_append hprefix tailTrace_864473
  have hstable : (prefixWord ++ tailWord_864473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864473).length < 2 ^ (prefixWord ++ tailWord_864473).sum := by decide
  have hdescent : baseEnd_864473 < baseStart_864473 := by decide
  rcases family_descends (prefixWord ++ tailWord_864473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864554 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_864554 : Nat := 118140960795 + 864554 * 2 ^ 59
def prefixEnd_864554 : Nat := 4983230072969 + 3 ^ 40 * 864554 * 2
def baseEnd_864554 : Nat := 147977251255771887399665

theorem tailTrace_864554 : CollatzResearch.WordTrace tailWord_864554 prefixEnd_864554 147977251255771887399665 := by
  unfold tailWord_864554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883218727468996728242179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21021916606583991275312477 7883218727468996728242179)
  ·
    refine ⟨11824828091203495092363269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7883218727468996728242179 11824828091203495092363269)
    ·
      refine ⟨2217155267100655329818113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11824828091203495092363269 2217155267100655329818113)
      ·
        refine ⟨1662866450325491497363585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2217155267100655329818113 1662866450325491497363585)
        ·
          refine ⟨1247149837744118623022689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1662866450325491497363585 1247149837744118623022689)
          ·
            refine ⟨935362378308088967267017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247149837744118623022689 935362378308088967267017)
            ·
              refine ⟨701521783731066725450263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935362378308088967267017 701521783731066725450263)
              ·
                refine ⟨1052282675596600088175395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701521783731066725450263 1052282675596600088175395)
                ·
                  refine ⟨1578424013394900132263093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052282675596600088175395 1578424013394900132263093)
                  ·
                    refine ⟨147977251255771887399665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1578424013394900132263093 147977251255771887399665)
                    ·
                      rfl

theorem cell23_864554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_864554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864554 prefixEnd_864554 := by exact prefixLift 864554
  have htrace : WordTrace (prefixWord ++ tailWord_864554) baseStart_864554 baseEnd_864554 := by
    simpa [prefixWord, tailWord_864554, baseEnd_864554] using wordTrace_append hprefix tailTrace_864554
  have hstable : (prefixWord ++ tailWord_864554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864554).length < 2 ^ (prefixWord ++ tailWord_864554).sum := by decide
  have hdescent : baseEnd_864554 < baseStart_864554 := by decide
  rcases family_descends (prefixWord ++ tailWord_864554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864574 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_864574 : Nat := 118140960795 + 864574 * 2 ^ 59
def prefixEnd_864574 : Nat := 4983230072969 + 3 ^ 40 * 864574 * 2
def baseEnd_864574 : Nat := 443942023380405583948903

theorem tailTrace_864574 : CollatzResearch.WordTrace tailWord_864574 prefixEnd_864574 443942023380405583948903 := by
  unfold tailWord_864574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941700546225441291087097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21022402913202353552464517 3941700546225441291087097)
  ·
    refine ⟨2956275409669080968315323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3941700546225441291087097 2956275409669080968315323)
    ·
      refine ⟨4434413114503621452472985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956275409669080968315323 4434413114503621452472985)
      ·
        refine ⟨3325809835877716089354739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434413114503621452472985 3325809835877716089354739)
        ·
          refine ⟨4988714753816574134032109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325809835877716089354739 4988714753816574134032109)
          ·
            refine ⟨1870768032681215300262041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988714753816574134032109 1870768032681215300262041)
            ·
              refine ⟨1403076024510911475196531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870768032681215300262041 1403076024510911475196531)
              ·
                refine ⟨2104614036766367212794797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403076024510911475196531 2104614036766367212794797)
                ·
                  refine ⟨789230263787387704798049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2104614036766367212794797 789230263787387704798049)
                  ·
                    refine ⟨591922697840540778598537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789230263787387704798049 591922697840540778598537)
                    ·
                      refine ⟨443942023380405583948903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591922697840540778598537 443942023380405583948903)
                      ·
                        rfl

theorem cell23_864574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_864574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864574 prefixEnd_864574 := by exact prefixLift 864574
  have htrace : WordTrace (prefixWord ++ tailWord_864574) baseStart_864574 baseEnd_864574 := by
    simpa [prefixWord, tailWord_864574, baseEnd_864574] using wordTrace_append hprefix tailTrace_864574
  have hstable : (prefixWord ++ tailWord_864574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864574).length < 2 ^ (prefixWord ++ tailWord_864574).sum := by decide
  have hdescent : baseEnd_864574 < baseStart_864574 := by decide
  rcases family_descends (prefixWord ++ tailWord_864574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864576 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_864576 : Nat := 118140960795 + 864576 * 2 ^ 59
def prefixEnd_864576 : Nat := 4983230072969 + 3 ^ 40 * 864576 * 2
def baseEnd_864576 : Nat := 147981016780571525374631

theorem tailTrace_864576 : CollatzResearch.WordTrace tailWord_864576 prefixEnd_864576 147981016780571525374631 := by
  unfold tailWord_864576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766838657898142335134791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21022451543864189780179721 15766838657898142335134791)
  ·
    refine ⟨23650257986847213502702187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15766838657898142335134791 23650257986847213502702187)
    ·
      refine ⟨35475386980270820254053281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23650257986847213502702187 35475386980270820254053281)
      ·
        refine ⟨26606540235203115190539961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35475386980270820254053281 26606540235203115190539961)
        ·
          refine ⟨19954905176402336392904971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26606540235203115190539961 19954905176402336392904971)
          ·
            refine ⟨29932357764603504589357457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19954905176402336392904971 29932357764603504589357457)
            ·
              refine ⟨22449268323452628442018093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29932357764603504589357457 22449268323452628442018093)
              ·
                refine ⟨8418475621294735665756785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22449268323452628442018093 8418475621294735665756785)
                ·
                  refine ⟨6313856715971051749317589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8418475621294735665756785 6313856715971051749317589)
                  ·
                    refine ⟨147981016780571525374631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6313856715971051749317589 147981016780571525374631)
                    ·
                      rfl

theorem cell23_864576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_864576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864576 prefixEnd_864576 := by exact prefixLift 864576
  have htrace : WordTrace (prefixWord ++ tailWord_864576) baseStart_864576 baseEnd_864576 := by
    simpa [prefixWord, tailWord_864576, baseEnd_864576] using wordTrace_append hprefix tailTrace_864576
  have hstable : (prefixWord ++ tailWord_864576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864576).length < 2 ^ (prefixWord ++ tailWord_864576).sum := by decide
  have hdescent : baseEnd_864576 < baseStart_864576 := by decide
  rcases family_descends (prefixWord ++ tailWord_864576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864597 : List Nat := [1, 3, 2, 2, 5, 1, 2, 7]
def baseStart_864597 : Nat := 118140960795 + 864597 * 2 ^ 59
def prefixEnd_864597 : Nat := 4983230072969 + 3 ^ 40 * 864597 * 2
def baseEnd_864597 : Nat := 16442734571683666443011

theorem tailTrace_864597 : CollatzResearch.WordTrace tailWord_864597 prefixEnd_864597 16442734571683666443011 := by
  unfold tailWord_864597
  simp only [CollatzResearch.WordTrace]
  refine ⟨31534443248720205256784045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21022962165813470171189363 31534443248720205256784045)
  ·
    refine ⟨11825416218270076971294017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31534443248720205256784045 11825416218270076971294017)
    ·
      refine ⟨8869062163702557728470513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11825416218270076971294017 8869062163702557728470513)
      ·
        refine ⟨6651796622776918296352885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8869062163702557728470513 6651796622776918296352885)
        ·
          refine ⟨623605933385336090283083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6651796622776918296352885 623605933385336090283083)
          ·
            refine ⟨935408900078004135424625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623605933385336090283083 935408900078004135424625)
            ·
              refine ⟨701556675058503101568469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935408900078004135424625 701556675058503101568469)
              ·
                refine ⟨16442734571683666443011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 701556675058503101568469 16442734571683666443011)
                ·
                  rfl

theorem cell23_864597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 7].length) (baseStart_864597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864597 prefixEnd_864597 := by exact prefixLift 864597
  have htrace : WordTrace (prefixWord ++ tailWord_864597) baseStart_864597 baseEnd_864597 := by
    simpa [prefixWord, tailWord_864597, baseEnd_864597] using wordTrace_append hprefix tailTrace_864597
  have hstable : (prefixWord ++ tailWord_864597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864597).length < 2 ^ (prefixWord ++ tailWord_864597).sum := by decide
  have hdescent : baseEnd_864597 < baseStart_864597 := by decide
  rcases family_descends (prefixWord ++ tailWord_864597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864608 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 1, 2, 2]
def baseStart_864608 : Nat := 118140960795 + 864608 * 2 ^ 59
def prefixEnd_864608 : Nat := 4983230072969 + 3 ^ 40 * 864608 * 2
def baseEnd_864608 : Nat := 443959481722658450923747

theorem tailTrace_864608 : CollatzResearch.WordTrace tailWord_864608 prefixEnd_864608 443959481722658450923747 := by
  unfold tailWord_864608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767422225840177067717239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21023229634453569423622985 15767422225840177067717239)
  ·
    refine ⟨23651133338760265601575859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15767422225840177067717239 23651133338760265601575859)
    ·
      refine ⟨35476700008140398402363789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651133338760265601575859 35476700008140398402363789)
      ·
        refine ⟨13303762503052649400886421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35476700008140398402363789 13303762503052649400886421)
        ·
          refine ⟨623613867330592940666551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13303762503052649400886421 623613867330592940666551)
          ·
            refine ⟨935420800995889410999827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623613867330592940666551 935420800995889410999827)
            ·
              refine ⟨1403131201493834116499741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935420800995889410999827 1403131201493834116499741)
              ·
                refine ⟨526174200560187793687403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403131201493834116499741 526174200560187793687403)
                ·
                  refine ⟨789261300840281690531105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526174200560187793687403 789261300840281690531105)
                  ·
                    refine ⟨591945975630211267898329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789261300840281690531105 591945975630211267898329)
                    ·
                      refine ⟨443959481722658450923747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 591945975630211267898329 443959481722658450923747)
                      ·
                        rfl

theorem cell23_864608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_864608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864608 prefixEnd_864608 := by exact prefixLift 864608
  have htrace : WordTrace (prefixWord ++ tailWord_864608) baseStart_864608 baseEnd_864608 := by
    simpa [prefixWord, tailWord_864608, baseEnd_864608] using wordTrace_append hprefix tailTrace_864608
  have hstable : (prefixWord ++ tailWord_864608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864608).length < 2 ^ (prefixWord ++ tailWord_864608).sum := by decide
  have hdescent : baseEnd_864608 < baseStart_864608 := by decide
  rcases family_descends (prefixWord ++ tailWord_864608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864633 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_864633 : Nat := 118140960795 + 864633 * 2 ^ 59
def prefixEnd_864633 : Nat := 4983230072969 + 3 ^ 40 * 864633 * 2
def baseEnd_864633 : Nat := 443972318739020853111131

theorem tailTrace_864633 : CollatzResearch.WordTrace tailWord_864633 prefixEnd_864633 443972318739020853111131 := by
  unfold tailWord_864633
  simp only [CollatzResearch.WordTrace]
  refine ⟨31535756276589783405094553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21023837517726522270063035 31535756276589783405094553)
  ·
    refine ⟨23651817207442337553820915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31535756276589783405094553 23651817207442337553820915)
    ·
      refine ⟨35477725811163506330731373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23651817207442337553820915 35477725811163506330731373)
      ·
        refine ⟨13304147179186314874024265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35477725811163506330731373 13304147179186314874024265)
        ·
          refine ⟨9978110384389736155518199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13304147179186314874024265 9978110384389736155518199)
          ·
            refine ⟨14967165576584604233277299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9978110384389736155518199 14967165576584604233277299)
            ·
              refine ⟨22450748364876906349915949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14967165576584604233277299 22450748364876906349915949)
              ·
                refine ⟨8419030636828839881218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22450748364876906349915949 8419030636828839881218481)
                ·
                  refine ⟨6314272977621629910913861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8419030636828839881218481 6314272977621629910913861)
                  ·
                    refine ⟨1183926183304055608296349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6314272977621629910913861 1183926183304055608296349)
                    ·
                      refine ⟨443972318739020853111131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1183926183304055608296349 443972318739020853111131)
                      ·
                        rfl

theorem cell23_864633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_864633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864633 prefixEnd_864633 := by exact prefixLift 864633
  have htrace : WordTrace (prefixWord ++ tailWord_864633) baseStart_864633 baseEnd_864633 := by
    simpa [prefixWord, tailWord_864633, baseEnd_864633] using wordTrace_append hprefix tailTrace_864633
  have hstable : (prefixWord ++ tailWord_864633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864633).length < 2 ^ (prefixWord ++ tailWord_864633).sum := by decide
  have hdescent : baseEnd_864633 < baseStart_864633 := by decide
  rcases family_descends (prefixWord ++ tailWord_864633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864641 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_864641 : Nat := 118140960795 + 864641 * 2 ^ 59
def prefixEnd_864641 : Nat := 4983230072969 + 3 ^ 40 * 864641 * 2
def baseEnd_864641 : Nat := 443976426584256821811095

theorem tailTrace_864641 : CollatzResearch.WordTrace tailWord_864641 prefixEnd_864641 443976426584256821811095 := by
  unfold tailWord_864641
  simp only [CollatzResearch.WordTrace]
  refine ⟨31536048060560800771385777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21024032040373867180923851 31536048060560800771385777)
  ·
    refine ⟨23652036045420600578539333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31536048060560800771385777 23652036045420600578539333)
    ·
      refine ⟨4434756758516362608476125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23652036045420600578539333 4434756758516362608476125)
      ·
        refine ⟨1663033784443635978178547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4434756758516362608476125 1663033784443635978178547)
        ·
          refine ⟨2494550676665453967267821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663033784443635978178547 2494550676665453967267821)
          ·
            refine ⟨935456503749545237725433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2494550676665453967267821 935456503749545237725433)
            ·
              refine ⟨701592377812158928294075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935456503749545237725433 701592377812158928294075)
              ·
                refine ⟨1052388566718238392441113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701592377812158928294075 1052388566718238392441113)
                ·
                  refine ⟨789291425038678794330835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052388566718238392441113 789291425038678794330835)
                  ·
                    refine ⟨1183937137558018191496253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 789291425038678794330835 1183937137558018191496253)
                    ·
                      refine ⟨443976426584256821811095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1183937137558018191496253 443976426584256821811095)
                      ·
                        rfl

theorem cell23_864641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_864641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864641 prefixEnd_864641 := by exact prefixLift 864641
  have htrace : WordTrace (prefixWord ++ tailWord_864641) baseStart_864641 baseEnd_864641 := by
    simpa [prefixWord, tailWord_864641, baseEnd_864641] using wordTrace_append hprefix tailTrace_864641
  have hstable : (prefixWord ++ tailWord_864641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864641).length < 2 ^ (prefixWord ++ tailWord_864641).sum := by decide
  have hdescent : baseEnd_864641 < baseStart_864641 := by decide
  rcases family_descends (prefixWord ++ tailWord_864641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864690 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_864690 : Nat := 118140960795 + 864690 * 2 ^ 59
def prefixEnd_864690 : Nat := 4983230072969 + 3 ^ 40 * 864690 * 2
def baseEnd_864690 : Nat := 444001587136327130098369

theorem tailTrace_864690 : CollatzResearch.WordTrace tailWord_864690 prefixEnd_864690 444001587136327130098369 := by
  unfold tailWord_864690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884458809345820534979881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21025223491588854759946349 7884458809345820534979881)
  ·
    refine ⟨5913344107009365401234911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7884458809345820534979881 5913344107009365401234911)
    ·
      refine ⟨8870016160514048101852367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913344107009365401234911 8870016160514048101852367)
      ·
        refine ⟨13305024240771072152778551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870016160514048101852367 13305024240771072152778551)
        ·
          refine ⟨19957536361156608229167827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13305024240771072152778551 19957536361156608229167827)
          ·
            refine ⟨29936304541734912343751741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19957536361156608229167827 29936304541734912343751741)
            ·
              refine ⟨11226114203150592128906903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29936304541734912343751741 11226114203150592128906903)
              ·
                refine ⟨16839171304725888193360355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11226114203150592128906903 16839171304725888193360355)
                ·
                  refine ⟨25258756957088832290040533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16839171304725888193360355 25258756957088832290040533)
                  ·
                    refine ⟨592002116181769506797825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25258756957088832290040533 592002116181769506797825)
                    ·
                      refine ⟨444001587136327130098369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592002116181769506797825 444001587136327130098369)
                      ·
                        rfl

theorem cell23_864690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_864690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864690 prefixEnd_864690 := by exact prefixLift 864690
  have htrace : WordTrace (prefixWord ++ tailWord_864690) baseStart_864690 baseEnd_864690 := by
    simpa [prefixWord, tailWord_864690, baseEnd_864690] using wordTrace_append hprefix tailTrace_864690
  have hstable : (prefixWord ++ tailWord_864690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864690).length < 2 ^ (prefixWord ++ tailWord_864690).sum := by decide
  have hdescent : baseEnd_864690 < baseStart_864690 := by decide
  rcases family_descends (prefixWord ++ tailWord_864690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864720 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2]
def baseStart_864720 : Nat := 118140960795 + 864720 * 2 ^ 59
def prefixEnd_864720 : Nat := 4983230072969 + 3 ^ 40 * 864720 * 2
def baseEnd_864720 : Nat := 444016991555962012723231

theorem tailTrace_864720 : CollatzResearch.WordTrace tailWord_864720 prefixEnd_864720 444016991555962012723231 := by
  unfold tailWord_864720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15769464713637298631755807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21025952951516398175674409 15769464713637298631755807)
  ·
    refine ⟨23654197070455947947633711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15769464713637298631755807 23654197070455947947633711)
    ·
      refine ⟨35481295605683921921450567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23654197070455947947633711 35481295605683921921450567)
      ·
        refine ⟨53221943408525882882175851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35481295605683921921450567 53221943408525882882175851)
        ·
          refine ⟨79832915112788824323263777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53221943408525882882175851 79832915112788824323263777)
          ·
            refine ⟨59874686334591618242447833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79832915112788824323263777 59874686334591618242447833)
            ·
              refine ⟨44906014750943713681835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59874686334591618242447833 44906014750943713681835875)
              ·
                refine ⟨67359022126415570522753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44906014750943713681835875 67359022126415570522753813)
                ·
                  refine ⟨3157454162175729868254085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67359022126415570522753813 3157454162175729868254085)
                  ·
                    refine ⟨592022655407949350297641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3157454162175729868254085 592022655407949350297641)
                    ·
                      refine ⟨444016991555962012723231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592022655407949350297641 444016991555962012723231)
                      ·
                        rfl

theorem cell23_864720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 4, 2].length) (baseStart_864720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864720 prefixEnd_864720 := by exact prefixLift 864720
  have htrace : WordTrace (prefixWord ++ tailWord_864720) baseStart_864720 baseEnd_864720 := by
    simpa [prefixWord, tailWord_864720, baseEnd_864720] using wordTrace_append hprefix tailTrace_864720
  have hstable : (prefixWord ++ tailWord_864720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864720).length < 2 ^ (prefixWord ++ tailWord_864720).sum := by decide
  have hdescent : baseEnd_864720 < baseStart_864720 := by decide
  rcases family_descends (prefixWord ++ tailWord_864720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864730 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_864730 : Nat := 118140960795 + 864730 * 2 ^ 59
def prefixEnd_864730 : Nat := 4983230072969 + 3 ^ 40 * 864730 * 2
def baseEnd_864730 : Nat := 148007375454168991199395

theorem tailTrace_864730 : CollatzResearch.WordTrace tailWord_864730 prefixEnd_864730 148007375454168991199395 := by
  unfold tailWord_864730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884823539309592242843911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21026196104825579314250429 7884823539309592242843911)
  ·
    refine ⟨11827235308964388364265867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884823539309592242843911 11827235308964388364265867)
    ·
      refine ⟨17740852963446582546398801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827235308964388364265867 17740852963446582546398801)
      ·
        refine ⟨13305639722584936909799101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17740852963446582546398801 13305639722584936909799101)
        ·
          refine ⟨4989614895969351341174663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13305639722584936909799101 4989614895969351341174663)
          ·
            refine ⟨7484422343954027011761995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989614895969351341174663 7484422343954027011761995)
            ·
              refine ⟨11226633515931040517642993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7484422343954027011761995 11226633515931040517642993)
              ·
                refine ⟨8419975136948280388232245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11226633515931040517642993 8419975136948280388232245)
                ·
                  refine ⟨789372669088901286396773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8419975136948280388232245 789372669088901286396773)
                  ·
                    refine ⟨148007375454168991199395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789372669088901286396773 148007375454168991199395)
                    ·
                      rfl

theorem cell23_864730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_864730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864730 prefixEnd_864730 := by exact prefixLift 864730
  have htrace : WordTrace (prefixWord ++ tailWord_864730) baseStart_864730 baseEnd_864730 := by
    simpa [prefixWord, tailWord_864730, baseEnd_864730] using wordTrace_append hprefix tailTrace_864730
  have hstable : (prefixWord ++ tailWord_864730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864730).length < 2 ^ (prefixWord ++ tailWord_864730).sum := by decide
  have hdescent : baseEnd_864730 < baseStart_864730 := by decide
  rcases family_descends (prefixWord ++ tailWord_864730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864747 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 1, 4]
def baseStart_864747 : Nat := 118140960795 + 864747 * 2 ^ 59
def prefixEnd_864747 : Nat := 4983230072969 + 3 ^ 40 * 864747 * 2
def baseEnd_864747 : Nat := 148010285177877802361869

theorem tailTrace_864747 : CollatzResearch.WordTrace tailWord_864747 prefixEnd_864747 148010285177877802361869 := by
  unfold tailWord_864747
  simp only [CollatzResearch.WordTrace]
  refine ⟨31539914198176780874744495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21026609465451187249829663 31539914198176780874744495)
  ·
    refine ⟨47309871297265171312116743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31539914198176780874744495 47309871297265171312116743)
    ·
      refine ⟨70964806945897756968175115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47309871297265171312116743 70964806945897756968175115)
      ·
        refine ⟨106447210418846635452262673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70964806945897756968175115 106447210418846635452262673)
        ·
          refine ⟨79835407814134976589197005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106447210418846635452262673 79835407814134976589197005)
          ·
            refine ⟨29938277930300616220948877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79835407814134976589197005 29938277930300616220948877)
            ·
              refine ⟨11226854223862731082855829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29938277930300616220948877 11226854223862731082855829)
              ·
                refine ⟨526258791743565519508867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11226854223862731082855829 526258791743565519508867)
                ·
                  refine ⟨789388187615348279263301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526258791743565519508867 789388187615348279263301)
                  ·
                    refine ⟨148010285177877802361869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789388187615348279263301 148010285177877802361869)
                    ·
                      rfl

theorem cell23_864747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 4].length) (baseStart_864747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864747 prefixEnd_864747 := by exact prefixLift 864747
  have htrace : WordTrace (prefixWord ++ tailWord_864747) baseStart_864747 baseEnd_864747 := by
    simpa [prefixWord, tailWord_864747, baseEnd_864747] using wordTrace_append hprefix tailTrace_864747
  have hstable : (prefixWord ++ tailWord_864747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864747).length < 2 ^ (prefixWord ++ tailWord_864747).sum := by decide
  have hdescent : baseEnd_864747 < baseStart_864747 := by decide
  rcases family_descends (prefixWord ++ tailWord_864747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864783 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_864783 : Nat := 118140960795 + 864783 * 2 ^ 59
def prefixEnd_864783 : Nat := 4983230072969 + 3 ^ 40 * 864783 * 2
def baseEnd_864783 : Nat := 444049340837195266235441

theorem tailTrace_864783 : CollatzResearch.WordTrace tailWord_864783 prefixEnd_864783 444049340837195266235441 := by
  unfold tailWord_864783
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541227226046359023055003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21027484817364239348703335 31541227226046359023055003)
  ·
    refine ⟨47311840839069538534582505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31541227226046359023055003 47311840839069538534582505)
    ·
      refine ⟨35483880629302153900936879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47311840839069538534582505 35483880629302153900936879)
      ·
        refine ⟨53225820943953230851405319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35483880629302153900936879 53225820943953230851405319)
        ·
          refine ⟨79838731415929846277107979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53225820943953230851405319 79838731415929846277107979)
          ·
            refine ⟨119758097123894769415661969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79838731415929846277107979 119758097123894769415661969)
            ·
              refine ⟨89818572842921077061746477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119758097123894769415661969 89818572842921077061746477)
              ·
                refine ⟨33681964816095403898154929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89818572842921077061746477 33681964816095403898154929)
                ·
                  refine ⟨25261473612071552923616197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33681964816095403898154929 25261473612071552923616197)
                  ·
                    refine ⟨4736526302263416173178037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25261473612071552923616197 4736526302263416173178037)
                    ·
                      refine ⟨444049340837195266235441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4736526302263416173178037 444049340837195266235441)
                      ·
                        rfl

theorem cell23_864783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_864783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864783 prefixEnd_864783 := by exact prefixLift 864783
  have htrace : WordTrace (prefixWord ++ tailWord_864783) baseStart_864783 baseEnd_864783 := by
    simpa [prefixWord, tailWord_864783, baseEnd_864783] using wordTrace_append hprefix tailTrace_864783
  have hstable : (prefixWord ++ tailWord_864783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864783).length < 2 ^ (prefixWord ++ tailWord_864783).sum := by decide
  have hdescent : baseEnd_864783 < baseStart_864783 := by decide
  rcases family_descends (prefixWord ++ tailWord_864783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864844 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_864844 : Nat := 118140960795 + 864844 * 2 ^ 59
def prefixEnd_864844 : Nat := 4983230072969 + 3 ^ 40 * 864844 * 2
def baseEnd_864844 : Nat := 444080663157119527572661

theorem tailTrace_864844 : CollatzResearch.WordTrace tailWord_864844 prefixEnd_864844 444080663157119527572661 := by
  unfold tailWord_864844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15771726039412683220512793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21028968052550244294017057 15771726039412683220512793)
  ·
    refine ⟨11828794529559512415384595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15771726039412683220512793 11828794529559512415384595)
    ·
      refine ⟨17743191794339268623076893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11828794529559512415384595 17743191794339268623076893)
      ·
        refine ⟨6653696922877225733653835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17743191794339268623076893 6653696922877225733653835)
        ·
          refine ⟨9980545384315838600480753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6653696922877225733653835 9980545384315838600480753)
          ·
            refine ⟨7485409038236878950360565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9980545384315838600480753 7485409038236878950360565)
            ·
              refine ⟨701757097334707401596303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7485409038236878950360565 701757097334707401596303)
              ·
                refine ⟨1052635646002061102394455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701757097334707401596303 1052635646002061102394455)
                ·
                  refine ⟨1578953469003091653591683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052635646002061102394455 1578953469003091653591683)
                  ·
                    refine ⟨2368430203504637480387525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1578953469003091653591683 2368430203504637480387525)
                    ·
                      refine ⟨444080663157119527572661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2368430203504637480387525 444080663157119527572661)
                      ·
                        rfl

theorem cell23_864844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_864844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864844 prefixEnd_864844 := by exact prefixLift 864844
  have htrace : WordTrace (prefixWord ++ tailWord_864844) baseStart_864844 baseEnd_864844 := by
    simpa [prefixWord, tailWord_864844, baseEnd_864844] using wordTrace_append hprefix tailTrace_864844
  have hstable : (prefixWord ++ tailWord_864844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864844).length < 2 ^ (prefixWord ++ tailWord_864844).sum := by decide
  have hdescent : baseEnd_864844 < baseStart_864844 := by decide
  rcases family_descends (prefixWord ++ tailWord_864844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864847 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_864847 : Nat := 118140960795 + 864847 * 2 ^ 59
def prefixEnd_864847 : Nat := 4983230072969 + 3 ^ 40 * 864847 * 2
def baseEnd_864847 : Nat := 444082203599083015835147

theorem tailTrace_864847 : CollatzResearch.WordTrace tailWord_864847 prefixEnd_864847 444082203599083015835147 := by
  unfold tailWord_864847
  simp only [CollatzResearch.WordTrace]
  refine ⟨31543561497814497953384795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21029040998542998635589863 31543561497814497953384795)
  ·
    refine ⟨47315342246721746930077193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31543561497814497953384795 47315342246721746930077193)
    ·
      refine ⟨35486506685041310197557895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47315342246721746930077193 35486506685041310197557895)
      ·
        refine ⟨53229760027561965296336843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35486506685041310197557895 53229760027561965296336843)
        ·
          refine ⟨79844640041342947944505265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53229760027561965296336843 79844640041342947944505265)
          ·
            refine ⟨59883480031007210958378949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79844640041342947944505265 59883480031007210958378949)
            ·
              refine ⟨11228152505813852054696053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59883480031007210958378949 11228152505813852054696053)
              ·
                refine ⟨1052639297420048630127755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11228152505813852054696053 1052639297420048630127755)
                ·
                  refine ⟨1578958946130072945191633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052639297420048630127755 1578958946130072945191633)
                  ·
                    refine ⟨1184219209597554708893725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1578958946130072945191633 1184219209597554708893725)
                    ·
                      refine ⟨444082203599083015835147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184219209597554708893725 444082203599083015835147)
                      ·
                        rfl

theorem cell23_864847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_864847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864847 prefixEnd_864847 := by exact prefixLift 864847
  have htrace : WordTrace (prefixWord ++ tailWord_864847) baseStart_864847 baseEnd_864847 := by
    simpa [prefixWord, tailWord_864847, baseEnd_864847] using wordTrace_append hprefix tailTrace_864847
  have hstable : (prefixWord ++ tailWord_864847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864847).length < 2 ^ (prefixWord ++ tailWord_864847).sum := by decide
  have hdescent : baseEnd_864847 < baseStart_864847 := by decide
  rcases family_descends (prefixWord ++ tailWord_864847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864917 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_864917 : Nat := 118140960795 + 864917 * 2 ^ 59
def prefixEnd_864917 : Nat := 4983230072969 + 3 ^ 40 * 864917 * 2
def baseEnd_864917 : Nat := 444118147244897741959825

theorem tailTrace_864917 : CollatzResearch.WordTrace tailWord_864917 prefixEnd_864917 444118147244897741959825 := by
  unfold tailWord_864917
  simp only [CollatzResearch.WordTrace]
  refine ⟨31546114607560899908433005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21030743071707266605622003 31546114607560899908433005)
  ·
    refine ⟨11829792977835337465662377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31546114607560899908433005 11829792977835337465662377)
    ·
      refine ⟨8872344733376503099246783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11829792977835337465662377 8872344733376503099246783)
      ·
        refine ⟨13308517100064754648870175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8872344733376503099246783 13308517100064754648870175)
        ·
          refine ⟨19962775650097131973305263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13308517100064754648870175 19962775650097131973305263)
          ·
            refine ⟨29944163475145697959957895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19962775650097131973305263 29944163475145697959957895)
            ·
              refine ⟨44916245212718546939936843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29944163475145697959957895 44916245212718546939936843)
              ·
                refine ⟨67374367819077820409905265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44916245212718546939936843 67374367819077820409905265)
                ·
                  refine ⟨50530775864308365307428949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67374367819077820409905265 50530775864308365307428949)
                  ·
                    refine ⟨592157529659863655946433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50530775864308365307428949 592157529659863655946433)
                    ·
                      refine ⟨444118147244897741959825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592157529659863655946433 444118147244897741959825)
                      ·
                        rfl

theorem cell23_864917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_864917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864917 prefixEnd_864917 := by exact prefixLift 864917
  have htrace : WordTrace (prefixWord ++ tailWord_864917) baseStart_864917 baseEnd_864917 := by
    simpa [prefixWord, tailWord_864917, baseEnd_864917] using wordTrace_append hprefix tailTrace_864917
  have hstable : (prefixWord ++ tailWord_864917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864917).length < 2 ^ (prefixWord ++ tailWord_864917).sum := by decide
  have hdescent : baseEnd_864917 < baseStart_864917 := by decide
  rcases family_descends (prefixWord ++ tailWord_864917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864928 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3]
def baseStart_864928 : Nat := 118140960795 + 864928 * 2 ^ 59
def prefixEnd_864928 : Nat := 4983230072969 + 3 ^ 40 * 864928 * 2
def baseEnd_864928 : Nat := 444123795532097198922275

theorem tailTrace_864928 : CollatzResearch.WordTrace tailWord_864928 prefixEnd_864928 444123795532097198922275 := by
  unfold tailWord_864928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773257905260524393541719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21031010540347365858055625 15773257905260524393541719)
  ·
    refine ⟨23659886857890786590312579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15773257905260524393541719 23659886857890786590312579)
    ·
      refine ⟨35489830286836179885468869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23659886857890786590312579 35489830286836179885468869)
      ·
        refine ⟨6654343178781783728525413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35489830286836179885468869 6654343178781783728525413)
        ·
          refine ⟨1247689346021584449098515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6654343178781783728525413 1247689346021584449098515)
          ·
            refine ⟨1871534019032376673647773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247689346021584449098515 1871534019032376673647773)
            ·
              refine ⟨701825257137141252617915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1871534019032376673647773 701825257137141252617915)
              ·
                refine ⟨1052737885705711878926873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701825257137141252617915 1052737885705711878926873)
                ·
                  refine ⟨789553414279283909195155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052737885705711878926873 789553414279283909195155)
                  ·
                    refine ⟨1184330121418925863792733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 789553414279283909195155 1184330121418925863792733)
                    ·
                      refine ⟨444123795532097198922275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184330121418925863792733 444123795532097198922275)
                      ·
                        rfl

theorem cell23_864928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_864928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864928 prefixEnd_864928 := by exact prefixLift 864928
  have htrace : WordTrace (prefixWord ++ tailWord_864928) baseStart_864928 baseEnd_864928 := by
    simpa [prefixWord, tailWord_864928, baseEnd_864928] using wordTrace_append hprefix tailTrace_864928
  have hstable : (prefixWord ++ tailWord_864928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864928).length < 2 ^ (prefixWord ++ tailWord_864928).sum := by decide
  have hdescent : baseEnd_864928 < baseStart_864928 := by decide
  rcases family_descends (prefixWord ++ tailWord_864928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864967 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_864967 : Nat := 118140960795 + 864967 * 2 ^ 59
def prefixEnd_864967 : Nat := 4983230072969 + 3 ^ 40 * 864967 * 2
def baseEnd_864967 : Nat := 444143821277622546334595

theorem tailTrace_864967 : CollatzResearch.WordTrace tailWord_864967 prefixEnd_864967 444143821277622546334595 := by
  unfold tailWord_864967
  simp only [CollatzResearch.WordTrace]
  refine ⟨31547938257379758447753155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21031958838253172298502103 31547938257379758447753155)
  ·
    refine ⟨47321907386069637671629733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31547938257379758447753155 47321907386069637671629733)
    ·
      refine ⟨8872857634888057063430575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47321907386069637671629733 8872857634888057063430575)
      ·
        refine ⟨13309286452332085595145863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8872857634888057063430575 13309286452332085595145863)
        ·
          refine ⟨19963929678498128392718795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309286452332085595145863 19963929678498128392718795)
          ·
            refine ⟨29945894517747192589078193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19963929678498128392718795 29945894517747192589078193)
            ·
              refine ⟨22459420888310394441808645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29945894517747192589078193 22459420888310394441808645)
              ·
                refine ⟨4211141416558198957839121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22459420888310394441808645 4211141416558198957839121)
                ·
                  refine ⟨3158356062418649218379341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4211141416558198957839121 3158356062418649218379341)
                  ·
                    refine ⟨1184383523406993456892253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3158356062418649218379341 1184383523406993456892253)
                    ·
                      refine ⟨444143821277622546334595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184383523406993456892253 444143821277622546334595)
                      ·
                        rfl

theorem cell23_864967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_864967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864967 prefixEnd_864967 := by exact prefixLift 864967
  have htrace : WordTrace (prefixWord ++ tailWord_864967) baseStart_864967 baseEnd_864967 := by
    simpa [prefixWord, tailWord_864967, baseEnd_864967] using wordTrace_append hprefix tailTrace_864967
  have hstable : (prefixWord ++ tailWord_864967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864967).length < 2 ^ (prefixWord ++ tailWord_864967).sum := by decide
  have hdescent : baseEnd_864967 < baseStart_864967 := by decide
  rcases family_descends (prefixWord ++ tailWord_864967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864974 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_864974 : Nat := 118140960795 + 864974 * 2 ^ 59
def prefixEnd_864974 : Nat := 4983230072969 + 3 ^ 40 * 864974 * 2
def baseEnd_864974 : Nat := 49349712849133779883007

theorem tailTrace_864974 : CollatzResearch.WordTrace tailWord_864974 prefixEnd_864974 49349712849133779883007 := by
  unfold tailWord_864974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943524196044299830407247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21032129045569599095505317 3943524196044299830407247)
  ·
    refine ⟨5915286294066449745610871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3943524196044299830407247 5915286294066449745610871)
    ·
      refine ⟨8872929441099674618416307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5915286294066449745610871 8872929441099674618416307)
      ·
        refine ⟨13309394161649511927624461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8872929441099674618416307 13309394161649511927624461)
        ·
          refine ⟨4991022810618566972859173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13309394161649511927624461 4991022810618566972859173)
          ·
            refine ⟨935816776990981307411095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4991022810618566972859173 935816776990981307411095)
            ·
              refine ⟨1403725165486471961116643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935816776990981307411095 1403725165486471961116643)
              ·
                refine ⟨2105587748229707941674965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403725165486471961116643 2105587748229707941674965)
                ·
                  refine ⟨49349712849133779883007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2105587748229707941674965 49349712849133779883007)
                  ·
                    rfl

theorem cell23_864974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_864974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_864974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_864974 prefixEnd_864974 := by exact prefixLift 864974
  have htrace : WordTrace (prefixWord ++ tailWord_864974) baseStart_864974 baseEnd_864974 := by
    simpa [prefixWord, tailWord_864974, baseEnd_864974] using wordTrace_append hprefix tailTrace_864974
  have hstable : (prefixWord ++ tailWord_864974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864974).length < 2 ^ (prefixWord ++ tailWord_864974).sum := by decide
  have hdescent : baseEnd_864974 < baseStart_864974 := by decide
  rcases family_descends (prefixWord ++ tailWord_864974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865027 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3]
def baseStart_865027 : Nat := 118140960795 + 865027 * 2 ^ 59
def prefixEnd_865027 : Nat := 4983230072969 + 3 ^ 40 * 865027 * 2
def baseEnd_865027 : Nat := 444174630116892311584319

theorem tailTrace_865027 : CollatzResearch.WordTrace tailWord_865027 prefixEnd_865027 444174630116892311584319 := by
  unfold tailWord_865027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31550126637162388694937335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21033417758108259129958223 31550126637162388694937335)
  ·
    refine ⟨47325189955743583042406003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31550126637162388694937335 47325189955743583042406003)
    ·
      refine ⟨70987784933615374563609005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47325189955743583042406003 70987784933615374563609005)
      ·
        refine ⟨26620419350105765461353377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70987784933615374563609005 26620419350105765461353377)
        ·
          refine ⟨19965314512579324096015033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26620419350105765461353377 19965314512579324096015033)
          ·
            refine ⟨14973985884434493072011275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19965314512579324096015033 14973985884434493072011275)
            ·
              refine ⟨22460978826651739608016913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14973985884434493072011275 22460978826651739608016913)
              ·
                refine ⟨16845734119988804706012685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22460978826651739608016913 16845734119988804706012685)
                ·
                  refine ⟨6317150294995801764754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16845734119988804706012685 6317150294995801764754757)
                  ·
                    refine ⟨1184465680311712830891517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6317150294995801764754757 1184465680311712830891517)
                    ·
                      refine ⟨444174630116892311584319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184465680311712830891517 444174630116892311584319)
                      ·
                        rfl

theorem cell23_865027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_865027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865027 prefixEnd_865027 := by exact prefixLift 865027
  have htrace : WordTrace (prefixWord ++ tailWord_865027) baseStart_865027 baseEnd_865027 := by
    simpa [prefixWord, tailWord_865027, baseEnd_865027] using wordTrace_append hprefix tailTrace_865027
  have hstable : (prefixWord ++ tailWord_865027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865027).length < 2 ^ (prefixWord ++ tailWord_865027).sum := by decide
  have hdescent : baseEnd_865027 < baseStart_865027 := by decide
  rcases family_descends (prefixWord ++ tailWord_865027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865034 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_865034 : Nat := 118140960795 + 865034 * 2 ^ 59
def prefixEnd_865034 : Nat := 4983230072969 + 3 ^ 40 * 865034 * 2
def baseEnd_865034 : Nat := 148059408160491261398929

theorem tailTrace_865034 : CollatzResearch.WordTrace tailWord_865034 prefixEnd_865034 148059408160491261398929 := by
  unfold tailWord_865034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887595487034257222610539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21033587965424685926961437 7887595487034257222610539)
  ·
    refine ⟨11831393230551385833915809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7887595487034257222610539 11831393230551385833915809)
    ·
      refine ⟨8873544922913539375436857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11831393230551385833915809 8873544922913539375436857)
      ·
        refine ⟨6655158692185154531577643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8873544922913539375436857 6655158692185154531577643)
        ·
          refine ⟨9982738038277731797366465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655158692185154531577643 9982738038277731797366465)
          ·
            refine ⟨7487053528708298848024849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9982738038277731797366465 7487053528708298848024849)
            ·
              refine ⟨5615290146531224136018637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7487053528708298848024849 5615290146531224136018637)
              ·
                refine ⟨2105733804949209051006989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5615290146531224136018637 2105733804949209051006989)
                ·
                  refine ⟨789650176855953394127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2105733804949209051006989 789650176855953394127621)
                  ·
                    refine ⟨148059408160491261398929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789650176855953394127621 148059408160491261398929)
                    ·
                      rfl

theorem cell23_865034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_865034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865034 prefixEnd_865034 := by exact prefixLift 865034
  have htrace : WordTrace (prefixWord ++ tailWord_865034) baseStart_865034 baseEnd_865034 := by
    simpa [prefixWord, tailWord_865034, baseEnd_865034] using wordTrace_append hprefix tailTrace_865034
  have hstable : (prefixWord ++ tailWord_865034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865034).length < 2 ^ (prefixWord ++ tailWord_865034).sum := by decide
  have hdescent : baseEnd_865034 < baseStart_865034 := by decide
  rcases family_descends (prefixWord ++ tailWord_865034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865091 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 3]
def baseStart_865091 : Nat := 118140960795 + 865091 * 2 ^ 59
def prefixEnd_865091 : Nat := 4983230072969 + 3 ^ 40 * 865091 * 2
def baseEnd_865091 : Nat := 444207492878780061184025

theorem tailTrace_865091 : CollatzResearch.WordTrace tailWord_865091 prefixEnd_865091 444207492878780061184025 := by
  unfold tailWord_865091
  simp only [CollatzResearch.WordTrace]
  refine ⟨31552460908930527625267127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21034973939287018416844751 31552460908930527625267127)
  ·
    refine ⟨47328691363395791437900691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31552460908930527625267127 47328691363395791437900691)
    ·
      refine ⟨70993037045093687156851037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47328691363395791437900691 70993037045093687156851037)
      ·
        refine ⟨26622388891910132683819139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70993037045093687156851037 26622388891910132683819139)
        ·
          refine ⟨39933583337865199025728709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26622388891910132683819139 39933583337865199025728709)
          ·
            refine ⟨7487546875849724817324133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39933583337865199025728709 7487546875849724817324133)
            ·
              refine ⟨1403915039221823403248275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7487546875849724817324133 1403915039221823403248275)
              ·
                refine ⟨2105872558832735104872413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403915039221823403248275 2105872558832735104872413)
                ·
                  refine ⟨789702209562275664327155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2105872558832735104872413 789702209562275664327155)
                  ·
                    refine ⟨1184553314343413496490733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 789702209562275664327155 1184553314343413496490733)
                    ·
                      refine ⟨444207492878780061184025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184553314343413496490733 444207492878780061184025)
                      ·
                        rfl

theorem cell23_865091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_865091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865091 prefixEnd_865091 := by exact prefixLift 865091
  have htrace : WordTrace (prefixWord ++ tailWord_865091) baseStart_865091 baseEnd_865091 := by
    simpa [prefixWord, tailWord_865091, baseEnd_865091] using wordTrace_append hprefix tailTrace_865091
  have hstable : (prefixWord ++ tailWord_865091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865091).length < 2 ^ (prefixWord ++ tailWord_865091).sum := by decide
  have hdescent : baseEnd_865091 < baseStart_865091 := by decide
  rcases family_descends (prefixWord ++ tailWord_865091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865111 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 1, 5]
def baseStart_865111 : Nat := 118140960795 + 865111 * 2 ^ 59
def prefixEnd_865111 : Nat := 4983230072969 + 3 ^ 40 * 865111 * 2
def baseEnd_865111 : Nat := 148072587497289994311311

theorem tailTrace_865111 : CollatzResearch.WordTrace tailWord_865111 prefixEnd_865111 148072587497289994311311 := by
  unfold tailWord_865111
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553190368858071040995187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21035460245905380693996791 31553190368858071040995187)
  ·
    refine ⟨47329785553287106561492781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31553190368858071040995187 47329785553287106561492781)
    ·
      refine ⟨17748669582482664960559793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47329785553287106561492781 17748669582482664960559793)
      ·
        refine ⟨13311502186861998720419845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17748669582482664960559793 13311502186861998720419845)
        ·
          refine ⟨2495906660036624760078721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13311502186861998720419845 2495906660036624760078721)
          ·
            refine ⟨1871929995027468570059041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495906660036624760078721 1871929995027468570059041)
            ·
              refine ⟨1403947496270601427544281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871929995027468570059041 1403947496270601427544281)
              ·
                refine ⟨1052960622202951070658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403947496270601427544281 1052960622202951070658211)
                ·
                  refine ⟨1579440933304426605987317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1052960622202951070658211 1579440933304426605987317)
                  ·
                    refine ⟨148072587497289994311311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1579440933304426605987317 148072587497289994311311)
                    ·
                      rfl

theorem cell23_865111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_865111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865111 prefixEnd_865111 := by exact prefixLift 865111
  have htrace : WordTrace (prefixWord ++ tailWord_865111) baseStart_865111 baseEnd_865111 := by
    simpa [prefixWord, tailWord_865111, baseEnd_865111] using wordTrace_append hprefix tailTrace_865111
  have hstable : (prefixWord ++ tailWord_865111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865111).length < 2 ^ (prefixWord ++ tailWord_865111).sum := by decide
  have hdescent : baseEnd_865111 < baseStart_865111 := by decide
  rcases family_descends (prefixWord ++ tailWord_865111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865131 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 5, 2, 2]
def baseStart_865131 : Nat := 118140960795 + 865131 * 2 ^ 59
def prefixEnd_865131 : Nat := 4983230072969 + 3 ^ 40 * 865131 * 2
def baseEnd_865131 : Nat := 444228032104959904683841

theorem tailTrace_865131 : CollatzResearch.WordTrace tailWord_865131 prefixEnd_865131 444228032104959904683841 := by
  unfold tailWord_865131
  simp only [CollatzResearch.WordTrace]
  refine ⟨31553919828785614456723247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21035946552523742971148831 31553919828785614456723247)
  ·
    refine ⟨47330879743178421685084871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31553919828785614456723247 47330879743178421685084871)
    ·
      refine ⟨70996319614767632527627307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47330879743178421685084871 70996319614767632527627307)
      ·
        refine ⟨106494479422151448791440961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70996319614767632527627307 106494479422151448791440961)
        ·
          refine ⟨79870859566613586593580721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106494479422151448791440961 79870859566613586593580721)
          ·
            refine ⟨59903144674960189945185541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79870859566613586593580721 59903144674960189945185541)
            ·
              refine ⟨11231839626555035614722289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59903144674960189945185541 11231839626555035614722289)
              ·
                refine ⟨8423879719916276711041717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231839626555035614722289 8423879719916276711041717)
                ·
                  refine ⟨789738723742150941660161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8423879719916276711041717 789738723742150941660161)
                  ·
                    refine ⟨592304042806613206245121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789738723742150941660161 592304042806613206245121)
                    ·
                      refine ⟨444228032104959904683841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592304042806613206245121 444228032104959904683841)
                      ·
                        rfl

theorem cell23_865131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2, 2].length) (baseStart_865131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865131 prefixEnd_865131 := by exact prefixLift 865131
  have htrace : WordTrace (prefixWord ++ tailWord_865131) baseStart_865131 baseEnd_865131 := by
    simpa [prefixWord, tailWord_865131, baseEnd_865131] using wordTrace_append hprefix tailTrace_865131
  have hstable : (prefixWord ++ tailWord_865131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865131).length < 2 ^ (prefixWord ++ tailWord_865131).sum := by decide
  have hdescent : baseEnd_865131 < baseStart_865131 := by decide
  rcases family_descends (prefixWord ++ tailWord_865131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865137 : List Nat := [1, 2, 2, 2, 1, 4, 11]
def baseStart_865137 : Nat := 118140960795 + 865137 * 2 ^ 59
def prefixEnd_865137 : Nat := 4983230072969 + 3 ^ 40 * 865137 * 2
def baseEnd_865137 : Nat := 5484334728257862730973

theorem tailTrace_865137 : CollatzResearch.WordTrace tailWord_865137 prefixEnd_865137 5484334728257862730973 := by
  unfold tailWord_865137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554138666763877481441665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21036092444509251654294443 31554138666763877481441665)
  ·
    refine ⟨23665604000072908111081249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31554138666763877481441665 23665604000072908111081249)
    ·
      refine ⟨17749203000054681083310937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23665604000072908111081249 17749203000054681083310937)
      ·
        refine ⟨13311902250041010812483203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17749203000054681083310937 13311902250041010812483203)
        ·
          refine ⟨19967853375061516218724805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13311902250041010812483203 19967853375061516218724805)
          ·
            refine ⟨3743972507824034291010901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19967853375061516218724805 3743972507824034291010901)
            ·
              refine ⟨5484334728257862730973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3743972507824034291010901 5484334728257862730973)
              ·
                rfl

theorem cell23_865137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 11].length) (baseStart_865137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865137 prefixEnd_865137 := by exact prefixLift 865137
  have htrace : WordTrace (prefixWord ++ tailWord_865137) baseStart_865137 baseEnd_865137 := by
    simpa [prefixWord, tailWord_865137, baseEnd_865137] using wordTrace_append hprefix tailTrace_865137
  have hstable : (prefixWord ++ tailWord_865137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865137).length < 2 ^ (prefixWord ++ tailWord_865137).sum := by decide
  have hdescent : baseEnd_865137 < baseStart_865137 := by decide
  rcases family_descends (prefixWord ++ tailWord_865137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865141 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_865141 : Nat := 118140960795 + 865141 * 2 ^ 59
def prefixEnd_865141 : Nat := 4983230072969 + 3 ^ 40 * 865141 * 2
def baseEnd_865141 : Nat := 148077722303834955186265

theorem tailTrace_865141 : CollatzResearch.WordTrace tailWord_865141 prefixEnd_865141 148077722303834955186265 := by
  unfold tailWord_865141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554284558749386164587277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21036189705832924109724851 31554284558749386164587277)
  ·
    refine ⟨11832856709531019811720229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31554284558749386164587277 11832856709531019811720229)
    ·
      refine ⟨2218660633037066214697543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11832856709531019811720229 2218660633037066214697543)
      ·
        refine ⟨3327990949555599322046315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218660633037066214697543 3327990949555599322046315)
        ·
          refine ⟨4991986424333398983069473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327990949555599322046315 4991986424333398983069473)
          ·
            refine ⟨3743989818250049237302105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991986424333398983069473 3743989818250049237302105)
            ·
              refine ⟨2807992363687536927976579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3743989818250049237302105 2807992363687536927976579)
              ·
                refine ⟨4211988545531305391964869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2807992363687536927976579 4211988545531305391964869)
                ·
                  refine ⟨789747852287119760993413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4211988545531305391964869 789747852287119760993413)
                  ·
                    refine ⟨148077722303834955186265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 789747852287119760993413 148077722303834955186265)
                    ·
                      rfl

theorem cell23_865141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_865141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865141 prefixEnd_865141 := by exact prefixLift 865141
  have htrace : WordTrace (prefixWord ++ tailWord_865141) baseStart_865141 baseEnd_865141 := by
    simpa [prefixWord, tailWord_865141, baseEnd_865141] using wordTrace_append hprefix tailTrace_865141
  have hstable : (prefixWord ++ tailWord_865141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865141).length < 2 ^ (prefixWord ++ tailWord_865141).sum := by decide
  have hdescent : baseEnd_865141 < baseStart_865141 := by decide
  rcases family_descends (prefixWord ++ tailWord_865141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865181 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_865181 : Nat := 118140960795 + 865181 * 2 ^ 59
def prefixEnd_865181 : Nat := 4983230072969 + 3 ^ 40 * 865181 * 2
def baseEnd_865181 : Nat := 444253706137684709058611

theorem tailTrace_865181 : CollatzResearch.WordTrace tailWord_865181 prefixEnd_865181 444253706137684709058611 := by
  unfold tailWord_865181
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555743478604472996043397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21037162319069648664028931 31555743478604472996043397)
  ·
    refine ⟨5916701902238338686758137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31555743478604472996043397 5916701902238338686758137)
    ·
      refine ⟨4437526426678754015068603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5916701902238338686758137 4437526426678754015068603)
      ·
        refine ⟨6656289640018131022602905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437526426678754015068603 6656289640018131022602905)
        ·
          refine ⟨4992217230013598266952179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6656289640018131022602905 4992217230013598266952179)
          ·
            refine ⟨7488325845020397400428269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992217230013598266952179 7488325845020397400428269)
            ·
              refine ⟨2808122191882649025160601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7488325845020397400428269 2808122191882649025160601)
              ·
                refine ⟨2106091643911986768870451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808122191882649025160601 2106091643911986768870451)
                ·
                  refine ⟨3159137465867980153305677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106091643911986768870451 3159137465867980153305677)
                  ·
                    refine ⟨1184676549700492557489629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3159137465867980153305677 1184676549700492557489629)
                    ·
                      refine ⟨444253706137684709058611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184676549700492557489629 444253706137684709058611)
                      ·
                        rfl

theorem cell23_865181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_865181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865181 prefixEnd_865181 := by exact prefixLift 865181
  have htrace : WordTrace (prefixWord ++ tailWord_865181) baseStart_865181 baseEnd_865181 := by
    simpa [prefixWord, tailWord_865181, baseEnd_865181] using wordTrace_append hprefix tailTrace_865181
  have hstable : (prefixWord ++ tailWord_865181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865181).length < 2 ^ (prefixWord ++ tailWord_865181).sum := by decide
  have hdescent : baseEnd_865181 < baseStart_865181 := by decide
  rcases family_descends (prefixWord ++ tailWord_865181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865185 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_865185 : Nat := 118140960795 + 865185 * 2 ^ 59
def prefixEnd_865185 : Nat := 4983230072969 + 3 ^ 40 * 865185 * 2
def baseEnd_865185 : Nat := 444255760060302693408593

theorem tailTrace_865185 : CollatzResearch.WordTrace tailWord_865185 prefixEnd_865185 444255760060302693408593 := by
  unfold tailWord_865185
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555889370589981679189009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21037259580393321119459339 31555889370589981679189009)
  ·
    refine ⟨23666917027942486259391757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31555889370589981679189009 23666917027942486259391757)
    ·
      refine ⟨8875093885478432347271909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23666917027942486259391757 8875093885478432347271909)
      ·
        refine ⟨1664080103527206065113483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8875093885478432347271909 1664080103527206065113483)
        ·
          refine ⟨2496120155290809097670225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664080103527206065113483 2496120155290809097670225)
          ·
            refine ⟨1872090116468106823252669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496120155290809097670225 1872090116468106823252669)
            ·
              refine ⟨702033793675540058719751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872090116468106823252669 702033793675540058719751)
              ·
                refine ⟨1053050690513310088079627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702033793675540058719751 1053050690513310088079627)
                ·
                  refine ⟨1579576035769965132119441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053050690513310088079627 1579576035769965132119441)
                  ·
                    refine ⟨1184682026827473849089581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1579576035769965132119441 1184682026827473849089581)
                    ·
                      refine ⟨444255760060302693408593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184682026827473849089581 444255760060302693408593)
                      ·
                        rfl

theorem cell23_865185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_865185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865185 prefixEnd_865185 := by exact prefixLift 865185
  have htrace : WordTrace (prefixWord ++ tailWord_865185) baseStart_865185 baseEnd_865185 := by
    simpa [prefixWord, tailWord_865185, baseEnd_865185] using wordTrace_append hprefix tailTrace_865185
  have hstable : (prefixWord ++ tailWord_865185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865185).length < 2 ^ (prefixWord ++ tailWord_865185).sum := by decide
  have hdescent : baseEnd_865185 < baseStart_865185 := by decide
  rcases family_descends (prefixWord ++ tailWord_865185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865242 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_865242 : Nat := 118140960795 + 865242 * 2 ^ 59
def prefixEnd_865242 : Nat := 4983230072969 + 3 ^ 40 * 865242 * 2
def baseEnd_865242 : Nat := 444285028457608970395831

theorem tailTrace_865242 : CollatzResearch.WordTrace tailWord_865242 prefixEnd_865242 444285028457608970395831 := by
  unfold tailWord_865242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889492082845870103503495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21038645554255653609342653 7889492082845870103503495)
  ·
    refine ⟨11834238124268805155255243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889492082845870103503495 11834238124268805155255243)
    ·
      refine ⟨17751357186403207732882865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834238124268805155255243 17751357186403207732882865)
      ·
        refine ⟨13313517889802405799662149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17751357186403207732882865 13313517889802405799662149)
        ·
          refine ⟨2496284604337951087436653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13313517889802405799662149 2496284604337951087436653)
          ·
            refine ⟨936106726626731657788745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2496284604337951087436653 936106726626731657788745)
            ·
              refine ⟨702080044970048743341559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936106726626731657788745 702080044970048743341559)
              ·
                refine ⟨1053120067455073115012339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702080044970048743341559 1053120067455073115012339)
                ·
                  refine ⟨1579680101182609672518509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1053120067455073115012339 1579680101182609672518509)
                  ·
                    refine ⟨592380037943478627194441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1579680101182609672518509 592380037943478627194441)
                    ·
                      refine ⟨444285028457608970395831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592380037943478627194441 444285028457608970395831)
                      ·
                        rfl

theorem cell23_865242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_865242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865242 prefixEnd_865242 := by exact prefixLift 865242
  have htrace : WordTrace (prefixWord ++ tailWord_865242) baseStart_865242 baseEnd_865242 := by
    simpa [prefixWord, tailWord_865242, baseEnd_865242] using wordTrace_append hprefix tailTrace_865242
  have hstable : (prefixWord ++ tailWord_865242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865242).length < 2 ^ (prefixWord ++ tailWord_865242).sum := by decide
  have hdescent : baseEnd_865242 < baseStart_865242 := by decide
  rcases family_descends (prefixWord ++ tailWord_865242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865255 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_865255 : Nat := 118140960795 + 865255 * 2 ^ 59
def prefixEnd_865255 : Nat := 4983230072969 + 3 ^ 40 * 865255 * 2
def baseEnd_865255 : Nat := 444291703706117419533271

theorem tailTrace_865255 : CollatzResearch.WordTrace tailWord_865255 prefixEnd_865255 444291703706117419533271 := by
  unfold tailWord_865255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558442480336383634237219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21038961653557589089491479 31558442480336383634237219)
  ·
    refine ⟨47337663720504575451355829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31558442480336383634237219 47337663720504575451355829)
    ·
      refine ⟨4437905973797303948564609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47337663720504575451355829 4437905973797303948564609)
      ·
        refine ⟨3328429480347977961423457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4437905973797303948564609 3328429480347977961423457)
        ·
          refine ⟨2496322110260983471067593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328429480347977961423457 2496322110260983471067593)
          ·
            refine ⟨1872241582695737603300695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496322110260983471067593 1872241582695737603300695)
            ·
              refine ⟨2808362374043606404951043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872241582695737603300695 2808362374043606404951043)
              ·
                refine ⟨4212543561065409607426565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808362374043606404951043 4212543561065409607426565)
                ·
                  refine ⟨789851917699764301392481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4212543561065409607426565 789851917699764301392481)
                  ·
                    refine ⟨592388938274823226044361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 789851917699764301392481 592388938274823226044361)
                    ·
                      refine ⟨444291703706117419533271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592388938274823226044361 444291703706117419533271)
                      ·
                        rfl

theorem cell23_865255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_865255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865255 prefixEnd_865255 := by exact prefixLift 865255
  have htrace : WordTrace (prefixWord ++ tailWord_865255) baseStart_865255 baseEnd_865255 := by
    simpa [prefixWord, tailWord_865255, baseEnd_865255] using wordTrace_append hprefix tailTrace_865255
  have hstable : (prefixWord ++ tailWord_865255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865255).length < 2 ^ (prefixWord ++ tailWord_865255).sum := by decide
  have hdescent : baseEnd_865255 < baseStart_865255 := by decide
  rcases family_descends (prefixWord ++ tailWord_865255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865308 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_865308 : Nat := 118140960795 + 865308 * 2 ^ 59
def prefixEnd_865308 : Nat := 4983230072969 + 3 ^ 40 * 865308 * 2
def baseEnd_865308 : Nat := 148106306060268570723509

theorem tailTrace_865308 : CollatzResearch.WordTrace tailWord_865308 prefixEnd_865308 148106306060268570723509 := by
  unfold tailWord_865308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780187774572186842958289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21040250366096249123944385 15780187774572186842958289)
  ·
    refine ⟨11835140830929140132218717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15780187774572186842958289 11835140830929140132218717)
    ·
      refine ⟨4438177811598427549582019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11835140830929140132218717 4438177811598427549582019)
      ·
        refine ⟨6657266717397641324373029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438177811598427549582019 6657266717397641324373029)
        ·
          refine ⟨1248237509512057748319943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6657266717397641324373029 1248237509512057748319943)
          ·
            refine ⟨1872356264268086622479915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248237509512057748319943 1872356264268086622479915)
            ·
              refine ⟨2808534396402129933719873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872356264268086622479915 2808534396402129933719873)
              ·
                refine ⟨2106400797301597450289905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2808534396402129933719873 2106400797301597450289905)
                ·
                  refine ⟨1579800597976198087717429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106400797301597450289905 1579800597976198087717429)
                  ·
                    refine ⟨148106306060268570723509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1579800597976198087717429 148106306060268570723509)
                    ·
                      rfl

theorem cell23_865308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_865308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865308 prefixEnd_865308 := by exact prefixLift 865308
  have htrace : WordTrace (prefixWord ++ tailWord_865308) baseStart_865308 baseEnd_865308 := by
    simpa [prefixWord, tailWord_865308, baseEnd_865308] using wordTrace_append hprefix tailTrace_865308
  have hstable : (prefixWord ++ tailWord_865308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865308).length < 2 ^ (prefixWord ++ tailWord_865308).sum := by decide
  have hdescent : baseEnd_865308 < baseStart_865308 := by decide
  rcases family_descends (prefixWord ++ tailWord_865308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865311 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_865311 : Nat := 118140960795 + 865311 * 2 ^ 59
def prefixEnd_865311 : Nat := 4983230072969 + 3 ^ 40 * 865311 * 2
def baseEnd_865311 : Nat := 444320458622769200433013

theorem tailTrace_865311 : CollatzResearch.WordTrace tailWord_865311 prefixEnd_865311 444320458622769200433013 := by
  unfold tailWord_865311
  simp only [CollatzResearch.WordTrace]
  refine ⟨31560484968133505198275787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21040323312089003465517191 31560484968133505198275787)
  ·
    refine ⟨47340727452200257797413681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31560484968133505198275787 47340727452200257797413681)
    ·
      refine ⟨35505545589150193348060261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47340727452200257797413681 35505545589150193348060261)
      ·
        refine ⟨6657289797965661252761299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35505545589150193348060261 6657289797965661252761299)
        ·
          refine ⟨9985934696948491879141949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657289797965661252761299 9985934696948491879141949)
          ·
            refine ⟨3744725511355684454678231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9985934696948491879141949 3744725511355684454678231)
            ·
              refine ⟨5617088267033526682017347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744725511355684454678231 5617088267033526682017347)
              ·
                refine ⟨8425632400550290023026021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5617088267033526682017347 8425632400550290023026021)
                ·
                  refine ⟨1579806075103179379317379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8425632400550290023026021 1579806075103179379317379)
                  ·
                    refine ⟨2369709112654769068976069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579806075103179379317379 2369709112654769068976069)
                    ·
                      refine ⟨444320458622769200433013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2369709112654769068976069 444320458622769200433013)
                      ·
                        rfl

theorem cell23_865311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_865311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865311 prefixEnd_865311 := by exact prefixLift 865311
  have htrace : WordTrace (prefixWord ++ tailWord_865311) baseStart_865311 baseEnd_865311 := by
    simpa [prefixWord, tailWord_865311, baseEnd_865311] using wordTrace_append hprefix tailTrace_865311
  have hstable : (prefixWord ++ tailWord_865311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865311).length < 2 ^ (prefixWord ++ tailWord_865311).sum := by decide
  have hdescent : baseEnd_865311 < baseStart_865311 := by decide
  rcases family_descends (prefixWord ++ tailWord_865311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865312 : List Nat := [2, 1, 1, 7, 1, 1, 3, 2, 5]
def baseStart_865312 : Nat := 118140960795 + 865312 * 2 ^ 59
def prefixEnd_865312 : Nat := 4983230072969 + 3 ^ 40 * 865312 * 2
def baseEnd_865312 : Nat := 49368996900380410724501

theorem tailTrace_865312 : CollatzResearch.WordTrace tailWord_865312 prefixEnd_865312 49368996900380410724501 := by
  unfold tailWord_865312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780260720564941184531095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21040347627419921579374793 15780260720564941184531095)
  ·
    refine ⟨23670391080847411776796643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15780260720564941184531095 23670391080847411776796643)
    ·
      refine ⟨35505586621271117665194965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23670391080847411776796643 35505586621271117665194965)
      ·
        refine ⟨832162186436041820278007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35505586621271117665194965 832162186436041820278007)
        ·
          refine ⟨1248243279654062730417011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832162186436041820278007 1248243279654062730417011)
          ·
            refine ⟨1872364919481094095625517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248243279654062730417011 1872364919481094095625517)
            ·
              refine ⟨702136844805410285859569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872364919481094095625517 702136844805410285859569)
              ·
                refine ⟨526602633604057714394677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702136844805410285859569 526602633604057714394677)
                ·
                  refine ⟨49368996900380410724501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 526602633604057714394677 49368996900380410724501)
                  ·
                    rfl

theorem cell23_865312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 2, 5].length) (baseStart_865312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865312 prefixEnd_865312 := by exact prefixLift 865312
  have htrace : WordTrace (prefixWord ++ tailWord_865312) baseStart_865312 baseEnd_865312 := by
    simpa [prefixWord, tailWord_865312, baseEnd_865312] using wordTrace_append hprefix tailTrace_865312
  have hstable : (prefixWord ++ tailWord_865312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865312).length < 2 ^ (prefixWord ++ tailWord_865312).sum := by decide
  have hdescent : baseEnd_865312 < baseStart_865312 := by decide
  rcases family_descends (prefixWord ++ tailWord_865312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865331 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3]
def baseStart_865331 : Nat := 118140960795 + 865331 * 2 ^ 59
def prefixEnd_865331 : Nat := 4983230072969 + 3 ^ 40 * 865331 * 2
def baseEnd_865331 : Nat := 444330728235859122182921

theorem tailTrace_865331 : CollatzResearch.WordTrace tailWord_865331 prefixEnd_865331 444330728235859122182921 := by
  unfold tailWord_865331
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561214428061048614003847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21040809618707365742669231 31561214428061048614003847)
  ·
    refine ⟨47341821642091572921005771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31561214428061048614003847 47341821642091572921005771)
    ·
      refine ⟨71012732463137359381508657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47341821642091572921005771 71012732463137359381508657)
      ·
        refine ⟨53259549347353019536131493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71012732463137359381508657 53259549347353019536131493)
        ·
          refine ⟨9986165502628691163024655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53259549347353019536131493 9986165502628691163024655)
          ·
            refine ⟨14979248253943036744536983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986165502628691163024655 14979248253943036744536983)
            ·
              refine ⟨22468872380914555116805475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979248253943036744536983 22468872380914555116805475)
              ·
                refine ⟨33703308571371832675208213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22468872380914555116805475 33703308571371832675208213)
                ·
                  refine ⟨1579842589283054656650385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33703308571371832675208213 1579842589283054656650385)
                  ·
                    refine ⟨1184881941962290992487789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1579842589283054656650385 1184881941962290992487789)
                    ·
                      refine ⟨444330728235859122182921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184881941962290992487789 444330728235859122182921)
                      ·
                        rfl

theorem cell23_865331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_865331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865331 prefixEnd_865331 := by exact prefixLift 865331
  have htrace : WordTrace (prefixWord ++ tailWord_865331) baseStart_865331 baseEnd_865331 := by
    simpa [prefixWord, tailWord_865331, baseEnd_865331] using wordTrace_append hprefix tailTrace_865331
  have hstable : (prefixWord ++ tailWord_865331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865331).length < 2 ^ (prefixWord ++ tailWord_865331).sum := by decide
  have hdescent : baseEnd_865331 < baseStart_865331 := by decide
  rcases family_descends (prefixWord ++ tailWord_865331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865345 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_865345 : Nat := 118140960795 + 865345 * 2 ^ 59
def prefixEnd_865345 : Nat := 4983230072969 + 3 ^ 40 * 865345 * 2
def baseEnd_865345 : Nat := 444337916965022067407857

theorem tailTrace_865345 : CollatzResearch.WordTrace tailWord_865345 prefixEnd_865345 444337916965022067407857 := by
  unfold tailWord_865345
  simp only [CollatzResearch.WordTrace]
  refine ⟨31561725050010329005013489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21041150033340219336675659 31561725050010329005013489)
  ·
    refine ⟨23671293787507746753760117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31561725050010329005013489 23671293787507746753760117)
    ·
      refine ⟨2219183792578851258165011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23671293787507746753760117 2219183792578851258165011)
      ·
        refine ⟨3328775688868276887247517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219183792578851258165011 3328775688868276887247517)
        ·
          refine ⟨1248290883325603832717819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3328775688868276887247517 1248290883325603832717819)
          ·
            refine ⟨1872436324988405749076729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248290883325603832717819 1872436324988405749076729)
            ·
              refine ⟨1404327243741304311807547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872436324988405749076729 1404327243741304311807547)
              ·
                refine ⟨2106490865611956467711321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404327243741304311807547 2106490865611956467711321)
                ·
                  refine ⟨1579868149208967350783491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2106490865611956467711321 1579868149208967350783491)
                  ·
                    refine ⟨2369802223813451026175237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1579868149208967350783491 2369802223813451026175237)
                    ·
                      refine ⟨444337916965022067407857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2369802223813451026175237 444337916965022067407857)
                      ·
                        rfl

theorem cell23_865345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_865345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865345 prefixEnd_865345 := by exact prefixLift 865345
  have htrace : WordTrace (prefixWord ++ tailWord_865345) baseStart_865345 baseEnd_865345 := by
    simpa [prefixWord, tailWord_865345, baseEnd_865345] using wordTrace_append hprefix tailTrace_865345
  have hstable : (prefixWord ++ tailWord_865345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865345).length < 2 ^ (prefixWord ++ tailWord_865345).sum := by decide
  have hdescent : baseEnd_865345 < baseStart_865345 := by decide
  rcases family_descends (prefixWord ++ tailWord_865345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865381 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_865381 : Nat := 118140960795 + 865381 * 2 ^ 59
def prefixEnd_865381 : Nat := 4983230072969 + 3 ^ 40 * 865381 * 2
def baseEnd_865381 : Nat := 148118800756194642185897

theorem tailTrace_865381 : CollatzResearch.WordTrace tailWord_865381 prefixEnd_865381 148118800756194642185897 := by
  unfold tailWord_865381
  simp only [CollatzResearch.WordTrace]
  refine ⟨31563038077879907153323997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21042025385253271435549331 31563038077879907153323997)
  ·
    refine ⟨11836139279204965182496499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31563038077879907153323997 11836139279204965182496499)
    ·
      refine ⟨17754208918807447773744749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11836139279204965182496499 17754208918807447773744749)
      ·
        refine ⟨6657828344552792915154281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17754208918807447773744749 6657828344552792915154281)
        ·
          refine ⟨4993371258414594686365711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657828344552792915154281 4993371258414594686365711)
          ·
            refine ⟨7490056887621892029548567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993371258414594686365711 7490056887621892029548567)
            ·
              refine ⟨11235085331432838044322851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490056887621892029548567 11235085331432838044322851)
              ·
                refine ⟨16852627997149257066484277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11235085331432838044322851 16852627997149257066484277)
                ·
                  refine ⟨1579933874732742849982901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16852627997149257066484277 1579933874732742849982901)
                  ·
                    refine ⟨148118800756194642185897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1579933874732742849982901 148118800756194642185897)
                    ·
                      rfl

theorem cell23_865381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_865381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865381 prefixEnd_865381 := by exact prefixLift 865381
  have htrace : WordTrace (prefixWord ++ tailWord_865381) baseStart_865381 baseEnd_865381 := by
    simpa [prefixWord, tailWord_865381, baseEnd_865381] using wordTrace_append hprefix tailTrace_865381
  have hstable : (prefixWord ++ tailWord_865381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865381).length < 2 ^ (prefixWord ++ tailWord_865381).sum := by decide
  have hdescent : baseEnd_865381 < baseStart_865381 := by decide
  rcases family_descends (prefixWord ++ tailWord_865381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865388 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_865388 : Nat := 118140960795 + 865388 * 2 ^ 59
def prefixEnd_865388 : Nat := 4983230072969 + 3 ^ 40 * 865388 * 2
def baseEnd_865388 : Nat := 444359996633165399170159

theorem tailTrace_865388 : CollatzResearch.WordTrace tailWord_865388 prefixEnd_865388 444359996633165399170159 := by
  unfold tailWord_865388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781646694427273674414409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21042195592569698232552545 15781646694427273674414409)
  ·
    refine ⟨11836235020820455255810807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15781646694427273674414409 11836235020820455255810807)
    ·
      refine ⟨17754352531230682883716211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11836235020820455255810807 17754352531230682883716211)
      ·
        refine ⟨26631528796846024325574317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17754352531230682883716211 26631528796846024325574317)
        ·
          refine ⟨9986823298817259122090369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26631528796846024325574317 9986823298817259122090369)
          ·
            refine ⟨7490117474112944341567777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9986823298817259122090369 7490117474112944341567777)
            ·
              refine ⟨5617588105584708256175833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7490117474112944341567777 5617588105584708256175833)
              ·
                refine ⟨4213191079188531192131875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5617588105584708256175833 4213191079188531192131875)
                ·
                  refine ⟨6319786618782796788197813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4213191079188531192131875 6319786618782796788197813)
                  ·
                    refine ⟨592479995510887198893545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6319786618782796788197813 592479995510887198893545)
                    ·
                      refine ⟨444359996633165399170159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592479995510887198893545 444359996633165399170159)
                      ·
                        rfl

theorem cell23_865388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_865388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865388 prefixEnd_865388 := by exact prefixLift 865388
  have htrace : WordTrace (prefixWord ++ tailWord_865388) baseStart_865388 baseEnd_865388 := by
    simpa [prefixWord, tailWord_865388, baseEnd_865388] using wordTrace_append hprefix tailTrace_865388
  have hstable : (prefixWord ++ tailWord_865388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865388).length < 2 ^ (prefixWord ++ tailWord_865388).sum := by decide
  have hdescent : baseEnd_865388 < baseStart_865388 := by decide
  rcases family_descends (prefixWord ++ tailWord_865388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865398 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_865398 : Nat := 118140960795 + 865398 * 2 ^ 59
def prefixEnd_865398 : Nat := 4983230072969 + 3 ^ 40 * 865398 * 2
def baseEnd_865398 : Nat := 148121710479903453348371

theorem tailTrace_865398 : CollatzResearch.WordTrace tailWord_865398 prefixEnd_865398 148121710479903453348371 := by
  unfold tailWord_865398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972728632426144941043303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21042438745878879371128565 1972728632426144941043303)
  ·
    refine ⟨2959092948639217411564955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972728632426144941043303 2959092948639217411564955)
    ·
      refine ⟨4438639422958826117347433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959092948639217411564955 4438639422958826117347433)
      ·
        refine ⟨3328979567219119588010575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438639422958826117347433 3328979567219119588010575)
        ·
          refine ⟨4993469350828679382015863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328979567219119588010575 4993469350828679382015863)
          ·
            refine ⟨7490204026243019073023795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993469350828679382015863 7490204026243019073023795)
            ·
              refine ⟨11235306039364528609535693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490204026243019073023795 11235306039364528609535693)
              ·
                refine ⟨4213239764761698228575885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11235306039364528609535693 4213239764761698228575885)
                ·
                  refine ⟨1579964911785636835715957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4213239764761698228575885 1579964911785636835715957)
                  ·
                    refine ⟨148121710479903453348371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1579964911785636835715957 148121710479903453348371)
                    ·
                      rfl

theorem cell23_865398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_865398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865398 prefixEnd_865398 := by exact prefixLift 865398
  have htrace : WordTrace (prefixWord ++ tailWord_865398) baseStart_865398 baseEnd_865398 := by
    simpa [prefixWord, tailWord_865398, baseEnd_865398] using wordTrace_append hprefix tailTrace_865398
  have hstable : (prefixWord ++ tailWord_865398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865398).length < 2 ^ (prefixWord ++ tailWord_865398).sum := by decide
  have hdescent : baseEnd_865398 < baseStart_865398 := by decide
  rcases family_descends (prefixWord ++ tailWord_865398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865411 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 1, 6]
def baseStart_865411 : Nat := 118140960795 + 865411 * 2 ^ 59
def prefixEnd_865411 : Nat := 4983230072969 + 3 ^ 40 * 865411 * 2
def baseEnd_865411 : Nat := 148123935562739603060851

theorem tailTrace_865411 : CollatzResearch.WordTrace tailWord_865411 prefixEnd_865411 148123935562739603060851 := by
  unfold tailWord_865411
  simp only [CollatzResearch.WordTrace]
  refine ⟨31564132267771222276916087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21042754845180814851277391 31564132267771222276916087)
  ·
    refine ⟨47346198401656833415374131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31564132267771222276916087 47346198401656833415374131)
    ·
      refine ⟨71019297602485250123061197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47346198401656833415374131 71019297602485250123061197)
      ·
        refine ⟨26632236600931968796147949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71019297602485250123061197 26632236600931968796147949)
        ·
          refine ⟨9987088725349488298555481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26632236600931968796147949 9987088725349488298555481)
          ·
            refine ⟨7490316544012116223916611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9987088725349488298555481 7490316544012116223916611)
            ·
              refine ⟨11235474816018174335874917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7490316544012116223916611 11235474816018174335874917)
              ·
                refine ⟨2106651528003407687976547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11235474816018174335874917 2106651528003407687976547)
                ·
                  refine ⟨3159977292005111531964821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2106651528003407687976547 3159977292005111531964821)
                  ·
                    refine ⟨148123935562739603060851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3159977292005111531964821 148123935562739603060851)
                    ·
                      rfl

theorem cell23_865411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 6].length) (baseStart_865411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865411 prefixEnd_865411 := by exact prefixLift 865411
  have htrace : WordTrace (prefixWord ++ tailWord_865411) baseStart_865411 baseEnd_865411 := by
    simpa [prefixWord, tailWord_865411, baseEnd_865411] using wordTrace_append hprefix tailTrace_865411
  have hstable : (prefixWord ++ tailWord_865411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865411).length < 2 ^ (prefixWord ++ tailWord_865411).sum := by decide
  have hdescent : baseEnd_865411 < baseStart_865411 := by decide
  rcases family_descends (prefixWord ++ tailWord_865411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865412 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_865412 : Nat := 118140960795 + 865412 * 2 ^ 59
def prefixEnd_865412 : Nat := 4983230072969 + 3 ^ 40 * 865412 * 2
def baseEnd_865412 : Nat := 444372320168873305270049

theorem tailTrace_865412 : CollatzResearch.WordTrace tailWord_865412 prefixEnd_865412 444372320168873305270049 := by
  unfold tailWord_865412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782084370383799723851245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21042779160511732965134993 15782084370383799723851245)
  ·
    refine ⟨5918281638893924896444217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15782084370383799723851245 5918281638893924896444217)
    ·
      refine ⟨4438711229170443672333163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5918281638893924896444217 4438711229170443672333163)
      ·
        refine ⟨6658066843755665508499745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438711229170443672333163 6658066843755665508499745)
        ·
          refine ⟨4993550132816749131374809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6658066843755665508499745 4993550132816749131374809)
          ·
            refine ⟨3745162599612561848531107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993550132816749131374809 3745162599612561848531107)
            ·
              refine ⟨5617743899418842772796661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745162599612561848531107 5617743899418842772796661)
              ·
                refine ⟨526663490570516509949687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5617743899418842772796661 526663490570516509949687)
                ·
                  refine ⟨789995235855774764924531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526663490570516509949687 789995235855774764924531)
                  ·
                    refine ⟨1184992853783662147386797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 789995235855774764924531 1184992853783662147386797)
                    ·
                      refine ⟨444372320168873305270049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1184992853783662147386797 444372320168873305270049)
                      ·
                        rfl

theorem cell23_865412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_865412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865412 prefixEnd_865412 := by exact prefixLift 865412
  have htrace : WordTrace (prefixWord ++ tailWord_865412) baseStart_865412 baseEnd_865412 := by
    simpa [prefixWord, tailWord_865412, baseEnd_865412] using wordTrace_append hprefix tailTrace_865412
  have hstable : (prefixWord ++ tailWord_865412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865412).length < 2 ^ (prefixWord ++ tailWord_865412).sum := by decide
  have hdescent : baseEnd_865412 < baseStart_865412 := by decide
  rcases family_descends (prefixWord ++ tailWord_865412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865441 : List Nat := [1, 2, 3, 3, 1, 1, 2, 10]
def baseStart_865441 : Nat := 118140960795 + 865441 * 2 ^ 59
def prefixEnd_865441 : Nat := 4983230072969 + 3 ^ 40 * 865441 * 2
def baseEnd_865441 : Nat := 16458785596587173770645

theorem tailTrace_865441 : CollatzResearch.WordTrace tailWord_865441 prefixEnd_865441 16458785596587173770645 := by
  unfold tailWord_865441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31565226457662537400508177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21043484305108358267005451 31565226457662537400508177)
  ·
    refine ⟨23673919843246903050381133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31565226457662537400508177 23673919843246903050381133)
    ·
      refine ⟨8877719941217588643892925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23673919843246903050381133 8877719941217588643892925)
      ·
        refine ⟨3329144977956595741459847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8877719941217588643892925 3329144977956595741459847)
        ·
          refine ⟨4993717466934893612189771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329144977956595741459847 4993717466934893612189771)
          ·
            refine ⟨7490576200402340418284657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993717466934893612189771 7490576200402340418284657)
            ·
              refine ⟨5617932150301755313713493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7490576200402340418284657 5617932150301755313713493)
              ·
                refine ⟨16458785596587173770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5617932150301755313713493 16458785596587173770645)
                ·
                  rfl

theorem cell23_865441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 10].length) (baseStart_865441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865441 prefixEnd_865441 := by exact prefixLift 865441
  have htrace : WordTrace (prefixWord ++ tailWord_865441) baseStart_865441 baseEnd_865441 := by
    simpa [prefixWord, tailWord_865441, baseEnd_865441] using wordTrace_append hprefix tailTrace_865441
  have hstable : (prefixWord ++ tailWord_865441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865441).length < 2 ^ (prefixWord ++ tailWord_865441).sum := by decide
  have hdescent : baseEnd_865441 < baseStart_865441 := by decide
  rcases family_descends (prefixWord ++ tailWord_865441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865458 : List Nat := [3, 2, 1, 1, 1, 4, 4, 7]
def baseStart_865458 : Nat := 118140960795 + 865458 * 2 ^ 59
def prefixEnd_865458 : Nat := 4983230072969 + 3 ^ 40 * 865458 * 2
def baseEnd_865458 : Nat := 16459108899221486122031

theorem tailTrace_865458 : CollatzResearch.WordTrace tailWord_865458 prefixEnd_865458 16459108899221486122031 := by
  unfold tailWord_865458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891461624650237325969257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21043897665733966202584685 7891461624650237325969257)
  ·
    refine ⟨5918596218487677994476943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7891461624650237325969257 5918596218487677994476943)
    ·
      refine ⟨8877894327731516991715415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918596218487677994476943 8877894327731516991715415)
      ·
        refine ⟨13316841491597275487573123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8877894327731516991715415 13316841491597275487573123)
        ·
          refine ⟨19975262237395913231359685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13316841491597275487573123 19975262237395913231359685)
          ·
            refine ⟨3745361669511733730879941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19975262237395913231359685 3745361669511733730879941)
            ·
              refine ⟨702255313033450074539989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3745361669511733730879941 702255313033450074539989)
              ·
                refine ⟨16459108899221486122031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 702255313033450074539989 16459108899221486122031)
                ·
                  rfl

theorem cell23_865458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_865458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865458 prefixEnd_865458 := by exact prefixLift 865458
  have htrace : WordTrace (prefixWord ++ tailWord_865458) baseStart_865458 baseEnd_865458 := by
    simpa [prefixWord, tailWord_865458, baseEnd_865458] using wordTrace_append hprefix tailTrace_865458
  have hstable : (prefixWord ++ tailWord_865458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865458).length < 2 ^ (prefixWord ++ tailWord_865458).sum := by decide
  have hdescent : baseEnd_865458 < baseStart_865458 := by decide
  rcases family_descends (prefixWord ++ tailWord_865458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865469 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_865469 : Nat := 118140960795 + 865469 * 2 ^ 59
def prefixEnd_865469 : Nat := 4983230072969 + 3 ^ 40 * 865469 * 2
def baseEnd_865469 : Nat := 444401588566179582257287

theorem tailTrace_865469 : CollatzResearch.WordTrace tailWord_865469 prefixEnd_865469 444401588566179582257287 := by
  unfold tailWord_865469
  simp only [CollatzResearch.WordTrace]
  refine ⟨31566247701561098182527461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21044165134374065455018307 31566247701561098182527461)
  ·
    refine ⟨5918671444042705909223899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31566247701561098182527461 5918671444042705909223899)
    ·
      refine ⟨8878007166064058863835849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918671444042705909223899 8878007166064058863835849)
      ·
        refine ⟨6658505374548044147876887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8878007166064058863835849 6658505374548044147876887)
        ·
          refine ⟨9987758061822066221815331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658505374548044147876887 9987758061822066221815331)
          ·
            refine ⟨14981637092733099332722997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9987758061822066221815331 14981637092733099332722997)
            ·
              refine ⟨1404528477443728062442781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14981637092733099332722997 1404528477443728062442781)
              ·
                refine ⟨526698179041398023416043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1404528477443728062442781 526698179041398023416043)
                ·
                  refine ⟨790047268562097035124065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526698179041398023416043 790047268562097035124065)
                  ·
                    refine ⟨592535451421572776343049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790047268562097035124065 592535451421572776343049)
                    ·
                      refine ⟨444401588566179582257287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592535451421572776343049 444401588566179582257287)
                      ·
                        rfl

theorem cell23_865469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_865469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865469 prefixEnd_865469 := by exact prefixLift 865469
  have htrace : WordTrace (prefixWord ++ tailWord_865469) baseStart_865469 baseEnd_865469 := by
    simpa [prefixWord, tailWord_865469, baseEnd_865469] using wordTrace_append hprefix tailTrace_865469
  have hstable : (prefixWord ++ tailWord_865469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865469).length < 2 ^ (prefixWord ++ tailWord_865469).sum := by decide
  have hdescent : baseEnd_865469 < baseStart_865469 := by decide
  rcases family_descends (prefixWord ++ tailWord_865469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865486 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_865486 : Nat := 118140960795 + 865486 * 2 ^ 59
def prefixEnd_865486 : Nat := 4983230072969 + 3 ^ 40 * 865486 * 2
def baseEnd_865486 : Nat := 444410317737306015744709

theorem tailTrace_865486 : CollatzResearch.WordTrace tailWord_865486 prefixEnd_865486 444410317737306015744709 := by
  unfold tailWord_865486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945858467812438760737039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21044578494999673390597541 3945858467812438760737039)
  ·
    refine ⟨5918787701718658141105559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3945858467812438760737039 5918787701718658141105559)
    ·
      refine ⟨8878181552577987211658339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918787701718658141105559 8878181552577987211658339)
      ·
        refine ⟨13317272328866980817487509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8878181552577987211658339 13317272328866980817487509)
        ·
          refine ⟨624247140415639725819727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13317272328866980817487509 624247140415639725819727)
          ·
            refine ⟨936370710623459588729591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624247140415639725819727 936370710623459588729591)
            ·
              refine ⟨1404556065935189383094387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936370710623459588729591 1404556065935189383094387)
              ·
                refine ⟨2106834098902784074641581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404556065935189383094387 2106834098902784074641581)
                ·
                  refine ⟨790062787088544027990593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2106834098902784074641581 790062787088544027990593)
                  ·
                    refine ⟨592547090316408020992945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790062787088544027990593 592547090316408020992945)
                    ·
                      refine ⟨444410317737306015744709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592547090316408020992945 444410317737306015744709)
                      ·
                        rfl

theorem cell23_865486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_865486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865486 prefixEnd_865486 := by exact prefixLift 865486
  have htrace : WordTrace (prefixWord ++ tailWord_865486) baseStart_865486 baseEnd_865486 := by
    simpa [prefixWord, tailWord_865486, baseEnd_865486] using wordTrace_append hprefix tailTrace_865486
  have hstable : (prefixWord ++ tailWord_865486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865486).length < 2 ^ (prefixWord ++ tailWord_865486).sum := by decide
  have hdescent : baseEnd_865486 < baseStart_865486 := by decide
  rcases family_descends (prefixWord ++ tailWord_865486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865491 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_865491 : Nat := 118140960795 + 865491 * 2 ^ 59
def prefixEnd_865491 : Nat := 4983230072969 + 3 ^ 40 * 865491 * 2
def baseEnd_865491 : Nat := 444412885140578496182185

theorem tailTrace_865491 : CollatzResearch.WordTrace tailWord_865491 prefixEnd_865491 444412885140578496182185 := by
  unfold tailWord_865491
  simp only [CollatzResearch.WordTrace]
  refine ⟨31567050107481395939828327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21044700071654263959885551 31567050107481395939828327)
  ·
    refine ⟨47350575161222093909742491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31567050107481395939828327 47350575161222093909742491)
    ·
      refine ⟨71025862741833140864613737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47350575161222093909742491 71025862741833140864613737)
      ·
        refine ⟨53269397056374855648460303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71025862741833140864613737 53269397056374855648460303)
        ·
          refine ⟨79904095584562283472690455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53269397056374855648460303 79904095584562283472690455)
          ·
            refine ⟨119856143376843425209035683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79904095584562283472690455 119856143376843425209035683)
            ·
              refine ⟨179784215065265137813553525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119856143376843425209035683 179784215065265137813553525)
              ·
                refine ⟨16854770162368606670020643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179784215065265137813553525 16854770162368606670020643)
                ·
                  refine ⟨25282155243552910005030965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16854770162368606670020643 25282155243552910005030965)
                  ·
                    refine ⟨2370202054083085312971653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25282155243552910005030965 2370202054083085312971653)
                    ·
                      refine ⟨444412885140578496182185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2370202054083085312971653 444412885140578496182185)
                      ·
                        rfl

theorem cell23_865491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_865491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865491 prefixEnd_865491 := by exact prefixLift 865491
  have htrace : WordTrace (prefixWord ++ tailWord_865491) baseStart_865491 baseEnd_865491 := by
    simpa [prefixWord, tailWord_865491, baseEnd_865491] using wordTrace_append hprefix tailTrace_865491
  have hstable : (prefixWord ++ tailWord_865491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865491).length < 2 ^ (prefixWord ++ tailWord_865491).sum := by decide
  have hdescent : baseEnd_865491 < baseStart_865491 := by decide
  rcases family_descends (prefixWord ++ tailWord_865491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865551 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_865551 : Nat := 118140960795 + 865551 * 2 ^ 59
def prefixEnd_865551 : Nat := 4983230072969 + 3 ^ 40 * 865551 * 2
def baseEnd_865551 : Nat := 444443693979848261431909

theorem tailTrace_865551 : CollatzResearch.WordTrace tailWord_865551 prefixEnd_865551 444443693979848261431909 := by
  unfold tailWord_865551
  simp only [CollatzResearch.WordTrace]
  refine ⟨31569238487264026187012507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21046158991509350791341671 31569238487264026187012507)
  ·
    refine ⟨47353857730896039280518761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31569238487264026187012507 47353857730896039280518761)
    ·
      refine ⟨35515393298172029460389071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47353857730896039280518761 35515393298172029460389071)
      ·
        refine ⟨53273089947258044190583607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35515393298172029460389071 53273089947258044190583607)
        ·
          refine ⟨79909634920887066285875411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53273089947258044190583607 79909634920887066285875411)
          ·
            refine ⟨119864452381330599428813117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79909634920887066285875411 119864452381330599428813117)
            ·
              refine ⟨44949169642998974785804919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119864452381330599428813117 44949169642998974785804919)
              ·
                refine ⟨67423754464498462178707379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44949169642998974785804919 67423754464498462178707379)
                ·
                  refine ⟨101135631696747693268061069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67423754464498462178707379 101135631696747693268061069)
                  ·
                    refine ⟨37925861886280384975522901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101135631696747693268061069 37925861886280384975522901)
                    ·
                      refine ⟨444443693979848261431909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37925861886280384975522901 444443693979848261431909)
                      ·
                        rfl

theorem cell23_865551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_865551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865551 prefixEnd_865551 := by exact prefixLift 865551
  have htrace : WordTrace (prefixWord ++ tailWord_865551) baseStart_865551 baseEnd_865551 := by
    simpa [prefixWord, tailWord_865551, baseEnd_865551] using wordTrace_append hprefix tailTrace_865551
  have hstable : (prefixWord ++ tailWord_865551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865551).length < 2 ^ (prefixWord ++ tailWord_865551).sum := by decide
  have hdescent : baseEnd_865551 < baseStart_865551 := by decide
  rcases family_descends (prefixWord ++ tailWord_865551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865565 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 7]
def baseStart_865565 : Nat := 118140960795 + 865565 * 2 ^ 59
def prefixEnd_865565 : Nat := 4983230072969 + 3 ^ 40 * 865565 * 2
def baseEnd_865565 : Nat := 49383431412112356295205

theorem tailTrace_865565 : CollatzResearch.WordTrace tailWord_865565 prefixEnd_865565 49383431412112356295205 := by
  unfold tailWord_865565
  simp only [CollatzResearch.WordTrace]
  refine ⟨31569749109213306578022149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21046499406142204385348099 31569749109213306578022149)
  ·
    refine ⟨5919327957977494983379153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31569749109213306578022149 5919327957977494983379153)
    ·
      refine ⟨4439495968483121237534365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5919327957977494983379153 4439495968483121237534365)
      ·
        refine ⟨1664810988181170464075387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4439495968483121237534365 1664810988181170464075387)
        ·
          refine ⟨2497216482271755696113081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664810988181170464075387 2497216482271755696113081)
          ·
            refine ⟨1872912361703816772084811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2497216482271755696113081 1872912361703816772084811)
            ·
              refine ⟨2809368542555725158127217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872912361703816772084811 2809368542555725158127217)
              ·
                refine ⟨2107026406916793868595413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809368542555725158127217 2107026406916793868595413)
                ·
                  refine ⟨49383431412112356295205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2107026406916793868595413 49383431412112356295205)
                  ·
                    rfl

theorem cell23_865565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_865565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865565 prefixEnd_865565 := by exact prefixLift 865565
  have htrace : WordTrace (prefixWord ++ tailWord_865565) baseStart_865565 baseEnd_865565 := by
    simpa [prefixWord, tailWord_865565, baseEnd_865565] using wordTrace_append hprefix tailTrace_865565
  have hstable : (prefixWord ++ tailWord_865565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865565).length < 2 ^ (prefixWord ++ tailWord_865565).sum := by decide
  have hdescent : baseEnd_865565 < baseStart_865565 := by decide
  rcases family_descends (prefixWord ++ tailWord_865565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865593 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 2, 2, 2]
def baseStart_865593 : Nat := 118140960795 + 865593 * 2 ^ 59
def prefixEnd_865593 : Nat := 4983230072969 + 3 ^ 40 * 865593 * 2
def baseEnd_865593 : Nat := 444465260167337097106717

theorem tailTrace_865593 : CollatzResearch.WordTrace tailWord_865593 prefixEnd_865593 444465260167337097106717 := by
  unfold tailWord_865593
  simp only [CollatzResearch.WordTrace]
  refine ⟨31570770353111867360041433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21047180235407911573360955 31570770353111867360041433)
  ·
    refine ⟨23678077764833900520031075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31570770353111867360041433 23678077764833900520031075)
    ·
      refine ⟨35517116647250850780046613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23678077764833900520031075 35517116647250850780046613)
      ·
        refine ⟨1664864842839883630314685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35517116647250850780046613 1664864842839883630314685)
        ·
          refine ⟨624324316064956361368007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1664864842839883630314685 624324316064956361368007)
          ·
            refine ⟨936486474097434542052011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624324316064956361368007 936486474097434542052011)
            ·
              refine ⟨1404729711146151813078017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936486474097434542052011 1404729711146151813078017)
              ·
                refine ⟨1053547283359613859808513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404729711146151813078017 1053547283359613859808513)
                ·
                  refine ⟨790160462519710394856385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053547283359613859808513 790160462519710394856385)
                  ·
                    refine ⟨592620346889782796142289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790160462519710394856385 592620346889782796142289)
                    ·
                      refine ⟨444465260167337097106717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592620346889782796142289 444465260167337097106717)
                      ·
                        rfl

theorem cell23_865593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_865593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865593 prefixEnd_865593 := by exact prefixLift 865593
  have htrace : WordTrace (prefixWord ++ tailWord_865593) baseStart_865593 baseEnd_865593 := by
    simpa [prefixWord, tailWord_865593, baseEnd_865593] using wordTrace_append hprefix tailTrace_865593
  have hstable : (prefixWord ++ tailWord_865593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865593).length < 2 ^ (prefixWord ++ tailWord_865593).sum := by decide
  have hdescent : baseEnd_865593 < baseStart_865593 := by decide
  rcases family_descends (prefixWord ++ tailWord_865593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865625 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_865625 : Nat := 118140960795 + 865625 * 2 ^ 59
def prefixEnd_865625 : Nat := 4983230072969 + 3 ^ 40 * 865625 * 2
def baseEnd_865625 : Nat := 148160563849426990635523

theorem tailTrace_865625 : CollatzResearch.WordTrace tailWord_865625 prefixEnd_865625 148160563849426990635523 := by
  unfold tailWord_865625
  simp only [CollatzResearch.WordTrace]
  refine ⟨31571937488995936825206329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21047958325997291216804219 31571937488995936825206329)
  ·
    refine ⟨23678953116746952618904747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31571937488995936825206329 23678953116746952618904747)
    ·
      refine ⟨35518429675120428928357121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23678953116746952618904747 35518429675120428928357121)
      ·
        refine ⟨26638822256340321696267841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35518429675120428928357121 26638822256340321696267841)
        ·
          refine ⟨19979116692255241272200881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26638822256340321696267841 19979116692255241272200881)
          ·
            refine ⟨14984337519191430954150661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19979116692255241272200881 14984337519191430954150661)
            ·
              refine ⟨2809563284848393303903249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14984337519191430954150661 2809563284848393303903249)
              ·
                refine ⟨2107172463636294977927437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809563284848393303903249 2107172463636294977927437)
                ·
                  refine ⟨790189673863610616722789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2107172463636294977927437 790189673863610616722789)
                  ·
                    refine ⟨148160563849426990635523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790189673863610616722789 148160563849426990635523)
                    ·
                      rfl

theorem cell23_865625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_865625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865625 prefixEnd_865625 := by exact prefixLift 865625
  have htrace : WordTrace (prefixWord ++ tailWord_865625) baseStart_865625 baseEnd_865625 := by
    simpa [prefixWord, tailWord_865625, baseEnd_865625] using wordTrace_append hprefix tailTrace_865625
  have hstable : (prefixWord ++ tailWord_865625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865625).length < 2 ^ (prefixWord ++ tailWord_865625).sum := by decide
  have hdescent : baseEnd_865625 < baseStart_865625 := by decide
  rcases family_descends (prefixWord ++ tailWord_865625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865635 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3]
def baseStart_865635 : Nat := 118140960795 + 865635 * 2 ^ 59
def prefixEnd_865635 : Nat := 4983230072969 + 3 ^ 40 * 865635 * 2
def baseEnd_865635 : Nat := 444486826354825932781523

theorem tailTrace_865635 : CollatzResearch.WordTrace tailWord_865635 prefixEnd_865635 444486826354825932781523 := by
  unfold tailWord_865635
  simp only [CollatzResearch.WordTrace]
  refine ⟨31572302218959708533070359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21048201479306472355380239 31572302218959708533070359)
  ·
    refine ⟨47358453328439562799605539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31572302218959708533070359 47358453328439562799605539)
    ·
      refine ⟨71037679992659344199408309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47358453328439562799605539 71037679992659344199408309)
      ·
        refine ⟨6659782499311813518694529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71037679992659344199408309 6659782499311813518694529)
        ·
          refine ⟨4994836874483860139020897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659782499311813518694529 4994836874483860139020897)
          ·
            refine ⟨3746127655862895104265673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4994836874483860139020897 3746127655862895104265673)
            ·
              refine ⟨2809595741897171328199255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746127655862895104265673 2809595741897171328199255)
              ·
                refine ⟨4214393612845756992298883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809595741897171328199255 4214393612845756992298883)
                ·
                  refine ⟨6321590419268635488448325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214393612845756992298883 6321590419268635488448325)
                  ·
                    refine ⟨1185298203612869154084061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6321590419268635488448325 1185298203612869154084061)
                    ·
                      refine ⟨444486826354825932781523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185298203612869154084061 444486826354825932781523)
                      ·
                        rfl

theorem cell23_865635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_865635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865635 prefixEnd_865635 := by exact prefixLift 865635
  have htrace : WordTrace (prefixWord ++ tailWord_865635) baseStart_865635 baseEnd_865635 := by
    simpa [prefixWord, tailWord_865635, baseEnd_865635] using wordTrace_append hprefix tailTrace_865635
  have hstable : (prefixWord ++ tailWord_865635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865635).length < 2 ^ (prefixWord ++ tailWord_865635).sum := by decide
  have hdescent : baseEnd_865635 < baseStart_865635 := by decide
  rcases family_descends (prefixWord ++ tailWord_865635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865659 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 1, 4]
def baseStart_865659 : Nat := 118140960795 + 865659 * 2 ^ 59
def prefixEnd_865659 : Nat := 4983230072969 + 3 ^ 40 * 865659 * 2
def baseEnd_865659 : Nat := 148166383296844612960471

theorem tailTrace_865659 : CollatzResearch.WordTrace tailWord_865659 prefixEnd_865659 148166383296844612960471 := by
  unfold tailWord_865659
  simp only [CollatzResearch.WordTrace]
  refine ⟨31573177570872760631944031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21048785047248507087962687 31573177570872760631944031)
  ·
    refine ⟨47359766356309140947916047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31573177570872760631944031 47359766356309140947916047)
    ·
      refine ⟨71039649534463711421874071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47359766356309140947916047 71039649534463711421874071)
      ·
        refine ⟨106559474301695567132811107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71039649534463711421874071 106559474301695567132811107)
        ·
          refine ⟨159839211452543350699216661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106559474301695567132811107 159839211452543350699216661)
          ·
            refine ⟨7492463036837969564025781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159839211452543350699216661 7492463036837969564025781)
            ·
              refine ⟨702418409703559646627417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7492463036837969564025781 702418409703559646627417)
              ·
                refine ⟨526813807277669734970563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702418409703559646627417 526813807277669734970563)
                ·
                  refine ⟨790220710916504602455845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526813807277669734970563 790220710916504602455845)
                  ·
                    refine ⟨148166383296844612960471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790220710916504602455845 148166383296844612960471)
                    ·
                      rfl

theorem cell23_865659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 4].length) (baseStart_865659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865659 prefixEnd_865659 := by exact prefixLift 865659
  have htrace : WordTrace (prefixWord ++ tailWord_865659) baseStart_865659 baseEnd_865659 := by
    simpa [prefixWord, tailWord_865659, baseEnd_865659] using wordTrace_append hprefix tailTrace_865659
  have hstable : (prefixWord ++ tailWord_865659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865659).length < 2 ^ (prefixWord ++ tailWord_865659).sum := by decide
  have hdescent : baseEnd_865659 < baseStart_865659 := by decide
  rcases family_descends (prefixWord ++ tailWord_865659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865672 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 6]
def baseStart_865672 : Nat := 118140960795 + 865672 * 2 ^ 59
def prefixEnd_865672 : Nat := 4983230072969 + 3 ^ 40 * 865672 * 2
def baseEnd_865672 : Nat := 49389536126560254224317

theorem tailTrace_865672 : CollatzResearch.WordTrace tailWord_865672 prefixEnd_865672 49389536126560254224317 := by
  unfold tailWord_865672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786825859912831926083635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21049101146550442568111513 15786825859912831926083635)
  ·
    refine ⟨23680238789869247889125453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15786825859912831926083635 23680238789869247889125453)
    ·
      refine ⟨8880089546200967958422045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23680238789869247889125453 8880089546200967958422045)
      ·
        refine ⟨3330033579825362984408267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8880089546200967958422045 3330033579825362984408267)
        ·
          refine ⟨4995050369738044476612401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330033579825362984408267 4995050369738044476612401)
          ·
            refine ⟨3746287777303533357459301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995050369738044476612401 3746287777303533357459301)
            ·
              refine ⟨702428958244412504523619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3746287777303533357459301 702428958244412504523619)
              ·
                refine ⟨1053643437366618756785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702428958244412504523619 1053643437366618756785429)
                ·
                  refine ⟨49389536126560254224317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1053643437366618756785429 49389536126560254224317)
                  ·
                    rfl

theorem cell23_865672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 6].length) (baseStart_865672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865672 prefixEnd_865672 := by exact prefixLift 865672
  have htrace : WordTrace (prefixWord ++ tailWord_865672) baseStart_865672 baseEnd_865672 := by
    simpa [prefixWord, tailWord_865672, baseEnd_865672] using wordTrace_append hprefix tailTrace_865672
  have hstable : (prefixWord ++ tailWord_865672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865672).length < 2 ^ (prefixWord ++ tailWord_865672).sum := by decide
  have hdescent : baseEnd_865672 < baseStart_865672 := by decide
  rcases family_descends (prefixWord ++ tailWord_865672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865699 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 1, 1, 3]
def baseStart_865699 : Nat := 118140960795 + 865699 * 2 ^ 59
def prefixEnd_865699 : Nat := 4983230072969 + 3 ^ 40 * 865699 * 2
def baseEnd_865699 : Nat := 444519689116713682381229

theorem tailTrace_865699 : CollatzResearch.WordTrace tailWord_865699 prefixEnd_865699 444519689116713682381229 := by
  unfold tailWord_865699
  simp only [CollatzResearch.WordTrace]
  refine ⟨31574636490727847463400151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21049757660485231642266767 31574636490727847463400151)
  ·
    refine ⟨47361954736091771195100227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31574636490727847463400151 47361954736091771195100227)
    ·
      refine ⟨71042932104137656792650341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47361954736091771195100227 71042932104137656792650341)
      ·
        refine ⟨13320549769525810648621939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71042932104137656792650341 13320549769525810648621939)
        ·
          refine ⟨19980824654288715972932909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13320549769525810648621939 19980824654288715972932909)
          ·
            refine ⟨7492809245358268489849841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19980824654288715972932909 7492809245358268489849841)
            ·
              refine ⟨5619606934018701367387381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7492809245358268489849841 5619606934018701367387381)
              ·
                refine ⟨526838150064253253192567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5619606934018701367387381 526838150064253253192567)
                ·
                  refine ⟨790257225096379879788851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526838150064253253192567 790257225096379879788851)
                  ·
                    refine ⟨1185385837644569819683277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 790257225096379879788851 1185385837644569819683277)
                    ·
                      refine ⟨444519689116713682381229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185385837644569819683277 444519689116713682381229)
                      ·
                        rfl

theorem cell23_865699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_865699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865699 prefixEnd_865699 := by exact prefixLift 865699
  have htrace : WordTrace (prefixWord ++ tailWord_865699) baseStart_865699 baseEnd_865699 := by
    simpa [prefixWord, tailWord_865699, baseEnd_865699] using wordTrace_append hprefix tailTrace_865699
  have hstable : (prefixWord ++ tailWord_865699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865699).length < 2 ^ (prefixWord ++ tailWord_865699).sum := by decide
  have hdescent : baseEnd_865699 < baseStart_865699 := by decide
  rcases family_descends (prefixWord ++ tailWord_865699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865715 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 4, 4]
def baseStart_865715 : Nat := 118140960795 + 865715 * 2 ^ 59
def prefixEnd_865715 : Nat := 4983230072969 + 3 ^ 40 * 865715 * 2
def baseEnd_865715 : Nat := 148175968269061873260385

theorem tailTrace_865715 : CollatzResearch.WordTrace tailWord_865715 prefixEnd_865715 148175968269061873260385 := by
  unfold tailWord_865715
  simp only [CollatzResearch.WordTrace]
  refine ⟨31575220058669882195982599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21050146705779921463988399 31575220058669882195982599)
  ·
    refine ⟨47362830088004823293973899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31575220058669882195982599 47362830088004823293973899)
    ·
      refine ⟨71044245132007234940960849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47362830088004823293973899 71044245132007234940960849)
      ·
        refine ⟨53283183849005426205720637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71044245132007234940960849 53283183849005426205720637)
        ·
          refine ⟨19981193943377034827145239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53283183849005426205720637 19981193943377034827145239)
          ·
            refine ⟨29971790915065552240717859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19981193943377034827145239 29971790915065552240717859)
            ·
              refine ⟨44957686372598328361076789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29971790915065552240717859 44957686372598328361076789)
              ·
                refine ⟨4214783097431093283850949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44957686372598328361076789 4214783097431093283850949)
                ·
                  refine ⟨790271830768329990722053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4214783097431093283850949 790271830768329990722053)
                  ·
                    refine ⟨148175968269061873260385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790271830768329990722053 148175968269061873260385)
                    ·
                      rfl

theorem cell23_865715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 4].length) (baseStart_865715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865715 prefixEnd_865715 := by exact prefixLift 865715
  have htrace : WordTrace (prefixWord ++ tailWord_865715) baseStart_865715 baseEnd_865715 := by
    simpa [prefixWord, tailWord_865715, baseEnd_865715] using wordTrace_append hprefix tailTrace_865715
  have hstable : (prefixWord ++ tailWord_865715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865715).length < 2 ^ (prefixWord ++ tailWord_865715).sum := by decide
  have hdescent : baseEnd_865715 < baseStart_865715 := by decide
  rcases family_descends (prefixWord ++ tailWord_865715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865725 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_865725 : Nat := 118140960795 + 865725 * 2 ^ 59
def prefixEnd_865725 : Nat := 4983230072969 + 3 ^ 40 * 865725 * 2
def baseEnd_865725 : Nat := 444533039613730580656109

theorem tailTrace_865725 : CollatzResearch.WordTrace tailWord_865725 prefixEnd_865725 444533039613730580656109 := by
  unfold tailWord_865725
  simp only [CollatzResearch.WordTrace]
  refine ⟨31575584788633653903846629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21050389859089102602564419 31575584788633653903846629)
  ·
    refine ⟨5920422147868810106971243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31575584788633653903846629 5920422147868810106971243)
    ·
      refine ⟨8880633221803215160456865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920422147868810106971243 8880633221803215160456865)
      ·
        refine ⟨6660474916352411370342649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8880633221803215160456865 6660474916352411370342649)
        ·
          refine ⟨4995356187264308527756987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6660474916352411370342649 4995356187264308527756987)
          ·
            refine ⟨7493034280896462791635481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995356187264308527756987 7493034280896462791635481)
            ·
              refine ⟨5619775710672347093726611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493034280896462791635481 5619775710672347093726611)
              ·
                refine ⟨8429663566008520640589917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5619775710672347093726611 8429663566008520640589917)
                ·
                  refine ⟨3161123837253195240221219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8429663566008520640589917 3161123837253195240221219)
                  ·
                    refine ⟨4741685755879792860331829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3161123837253195240221219 4741685755879792860331829)
                    ·
                      refine ⟨444533039613730580656109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4741685755879792860331829 444533039613730580656109)
                      ·
                        rfl

theorem cell23_865725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_865725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865725 prefixEnd_865725 := by exact prefixLift 865725
  have htrace : WordTrace (prefixWord ++ tailWord_865725) baseStart_865725 baseEnd_865725 := by
    simpa [prefixWord, tailWord_865725, baseEnd_865725] using wordTrace_append hprefix tailTrace_865725
  have hstable : (prefixWord ++ tailWord_865725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865725).length < 2 ^ (prefixWord ++ tailWord_865725).sum := by decide
  have hdescent : baseEnd_865725 < baseStart_865725 := by decide
  rcases family_descends (prefixWord ++ tailWord_865725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865732 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_865732 : Nat := 118140960795 + 865732 * 2 ^ 59
def prefixEnd_865732 : Nat := 4983230072969 + 3 ^ 40 * 865732 * 2
def baseEnd_865732 : Nat := 148178877992770684422859

theorem tailTrace_865732 : CollatzResearch.WordTrace tailWord_865732 prefixEnd_865732 148178877992770684422859 := by
  unfold tailWord_865732
  simp only [CollatzResearch.WordTrace]
  refine ⟨15787920049804147049675725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21050560066405529399567633 15787920049804147049675725)
  ·
    refine ⟨5920470018676555143628397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15787920049804147049675725 5920470018676555143628397)
    ·
      refine ⟨2220176257003708178860649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5920470018676555143628397 2220176257003708178860649)
      ·
        refine ⟨1665132192752781134145487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2220176257003708178860649 1665132192752781134145487)
        ·
          refine ⟨2497698289129171701218231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665132192752781134145487 2497698289129171701218231)
          ·
            refine ⟨3746547433693757551827347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497698289129171701218231 3746547433693757551827347)
            ·
              refine ⟨5619821150540636327741021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746547433693757551827347 5619821150540636327741021)
              ·
                refine ⟨2107432931452738622902883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5619821150540636327741021 2107432931452738622902883)
                ·
                  refine ⟨3161149397179107934354325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107432931452738622902883 3161149397179107934354325)
                  ·
                    refine ⟨148178877992770684422859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3161149397179107934354325 148178877992770684422859)
                    ·
                      rfl

theorem cell23_865732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_865732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865732 prefixEnd_865732 := by exact prefixLift 865732
  have htrace : WordTrace (prefixWord ++ tailWord_865732) baseStart_865732 baseEnd_865732 := by
    simpa [prefixWord, tailWord_865732, baseEnd_865732] using wordTrace_append hprefix tailTrace_865732
  have hstable : (prefixWord ++ tailWord_865732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865732).length < 2 ^ (prefixWord ++ tailWord_865732).sum := by decide
  have hdescent : baseEnd_865732 < baseStart_865732 := by decide
  rcases family_descends (prefixWord ++ tailWord_865732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865742 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_865742 : Nat := 118140960795 + 865742 * 2 ^ 59
def prefixEnd_865742 : Nat := 4983230072969 + 3 ^ 40 * 865742 * 2
def baseEnd_865742 : Nat := 444541768784857014143531

theorem tailTrace_865742 : CollatzResearch.WordTrace tailWord_865742 prefixEnd_865742 444541768784857014143531 := by
  unfold tailWord_865742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947025603696508225901935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21050803219714710538143653 3947025603696508225901935)
  ·
    refine ⟨5920538405544762338852903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947025603696508225901935 5920538405544762338852903)
    ·
      refine ⟨8880807608317143508279355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920538405544762338852903 8880807608317143508279355)
      ·
        refine ⟨13321211412475715262419033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8880807608317143508279355 13321211412475715262419033)
        ·
          refine ⟨9990908559356786446814275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13321211412475715262419033 9990908559356786446814275)
          ·
            refine ⟨14986362839035179670221413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9990908559356786446814275 14986362839035179670221413)
            ·
              refine ⟨2809943032319096188166515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14986362839035179670221413 2809943032319096188166515)
              ·
                refine ⟨4214914548478644282249773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809943032319096188166515 4214914548478644282249773)
                ·
                  refine ⟨1580592955679491605843665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4214914548478644282249773 1580592955679491605843665)
                  ·
                    refine ⟨1185444716759618704382749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1580592955679491605843665 1185444716759618704382749)
                    ·
                      refine ⟨444541768784857014143531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185444716759618704382749 444541768784857014143531)
                      ·
                        rfl

theorem cell23_865742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_865742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865742 prefixEnd_865742 := by exact prefixLift 865742
  have htrace : WordTrace (prefixWord ++ tailWord_865742) baseStart_865742 baseEnd_865742 := by
    simpa [prefixWord, tailWord_865742, baseEnd_865742] using wordTrace_append hprefix tailTrace_865742
  have hstable : (prefixWord ++ tailWord_865742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865742).length < 2 ^ (prefixWord ++ tailWord_865742).sum := by decide
  have hdescent : baseEnd_865742 < baseStart_865742 := by decide
  rcases family_descends (prefixWord ++ tailWord_865742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865773 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_865773 : Nat := 118140960795 + 865773 * 2 ^ 59
def prefixEnd_865773 : Nat := 4983230072969 + 3 ^ 40 * 865773 * 2
def baseEnd_865773 : Nat := 444557686685146392855889

theorem tailTrace_865773 : CollatzResearch.WordTrace tailWord_865773 prefixEnd_865773 444557686685146392855889 := by
  unfold tailWord_865773
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577335492459758101593973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21051556994973172067729315 31577335492459758101593973)
  ·
    refine ⟨2960375202418102322024435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31577335492459758101593973 2960375202418102322024435)
    ·
      refine ⟨4440562803627153483036653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960375202418102322024435 4440562803627153483036653)
      ·
        refine ⟨1665211051360182556138745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4440562803627153483036653 1665211051360182556138745)
        ·
          refine ⟨1248908288520136917104059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665211051360182556138745 1248908288520136917104059)
          ·
            refine ⟨1873362432780205375656089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248908288520136917104059 1873362432780205375656089)
            ·
              refine ⟨1405021824585154031742067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873362432780205375656089 1405021824585154031742067)
              ·
                refine ⟨2107532736877731047613101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405021824585154031742067 2107532736877731047613101)
                ·
                  refine ⟨790324776329149142854913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2107532736877731047613101 790324776329149142854913)
                  ·
                    refine ⟨592743582246861857141185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790324776329149142854913 592743582246861857141185)
                    ·
                      refine ⟨444557686685146392855889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592743582246861857141185 444557686685146392855889)
                      ·
                        rfl

theorem cell23_865773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_865773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865773 prefixEnd_865773 := by exact prefixLift 865773
  have htrace : WordTrace (prefixWord ++ tailWord_865773) baseStart_865773 baseEnd_865773 := by
    simpa [prefixWord, tailWord_865773, baseEnd_865773] using wordTrace_append hprefix tailTrace_865773
  have hstable : (prefixWord ++ tailWord_865773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865773).length < 2 ^ (prefixWord ++ tailWord_865773).sum := by decide
  have hdescent : baseEnd_865773 < baseStart_865773 := by decide
  rcases family_descends (prefixWord ++ tailWord_865773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865789 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_865789 : Nat := 118140960795 + 865789 * 2 ^ 59
def prefixEnd_865789 : Nat := 4983230072969 + 3 ^ 40 * 865789 * 2
def baseEnd_865789 : Nat := 444565902375618330255815

theorem tailTrace_865789 : CollatzResearch.WordTrace tailWord_865789 prefixEnd_865789 444565902375618330255815 := by
  unfold tailWord_865789
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577919060401792834176421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21051946040267861889450947 31577919060401792834176421)
  ·
    refine ⟨5920859823825336156408079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31577919060401792834176421 5920859823825336156408079)
    ·
      refine ⟨8881289735738004234612119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920859823825336156408079 8881289735738004234612119)
      ·
        refine ⟨13321934603607006351918179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8881289735738004234612119 13321934603607006351918179)
        ·
          refine ⟨19982901905410509527877269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13321934603607006351918179 19982901905410509527877269)
          ·
            refine ⟨936698526816117634119247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19982901905410509527877269 936698526816117634119247)
            ·
              refine ⟨1405047790224176451178871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936698526816117634119247 1405047790224176451178871)
              ·
                refine ⟨2107571685336264676768307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405047790224176451178871 2107571685336264676768307)
                ·
                  refine ⟨3161357528004397015152461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2107571685336264676768307 3161357528004397015152461)
                  ·
                    refine ⟨1185509073001648880682173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3161357528004397015152461 1185509073001648880682173)
                    ·
                      refine ⟨444565902375618330255815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185509073001648880682173 444565902375618330255815)
                      ·
                        rfl

theorem cell23_865789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_865789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865789 prefixEnd_865789 := by exact prefixLift 865789
  have htrace : WordTrace (prefixWord ++ tailWord_865789) baseStart_865789 baseEnd_865789 := by
    simpa [prefixWord, tailWord_865789, baseEnd_865789] using wordTrace_append hprefix tailTrace_865789
  have hstable : (prefixWord ++ tailWord_865789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865789).length < 2 ^ (prefixWord ++ tailWord_865789).sum := by decide
  have hdescent : baseEnd_865789 < baseStart_865789 := by decide
  rcases family_descends (prefixWord ++ tailWord_865789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865796 : List Nat := [2, 3, 2, 3, 3, 1, 2, 7]
def baseStart_865796 : Nat := 118140960795 + 865796 * 2 ^ 59
def prefixEnd_865796 : Nat := 4983230072969 + 3 ^ 40 * 865796 * 2
def baseEnd_865796 : Nat := 16465536916303696402529

theorem tailTrace_865796 : CollatzResearch.WordTrace tailWord_865796 prefixEnd_865796 16465536916303696402529 := by
  unfold tailWord_865796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789087185688216514840621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21052116247584288686454161 15789087185688216514840621)
  ·
    refine ⟨5920907694633081193065233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15789087185688216514840621 5920907694633081193065233)
    ·
      refine ⟨4440680770974810894798925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5920907694633081193065233 4440680770974810894798925)
      ·
        refine ⟨1665255289115554085549597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4440680770974810894798925 1665255289115554085549597)
        ·
          refine ⟨624470733418332782081099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1665255289115554085549597 624470733418332782081099)
          ·
            refine ⟨936706100127499173121649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624470733418332782081099 936706100127499173121649)
            ·
              refine ⟨702529575095624379841237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936706100127499173121649 702529575095624379841237)
              ·
                refine ⟨16465536916303696402529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 702529575095624379841237 16465536916303696402529)
                ·
                  rfl

theorem cell23_865796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 7].length) (baseStart_865796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865796 prefixEnd_865796 := by exact prefixLift 865796
  have htrace : WordTrace (prefixWord ++ tailWord_865796) baseStart_865796 baseEnd_865796 := by
    simpa [prefixWord, tailWord_865796, baseEnd_865796] using wordTrace_append hprefix tailTrace_865796
  have hstable : (prefixWord ++ tailWord_865796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865796).length < 2 ^ (prefixWord ++ tailWord_865796).sum := by decide
  have hdescent : baseEnd_865796 < baseStart_865796 := by decide
  rcases family_descends (prefixWord ++ tailWord_865796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865865 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_865865 : Nat := 118140960795 + 865865 * 2 ^ 59
def prefixEnd_865865 : Nat := 4983230072969 + 3 ^ 40 * 865865 * 2
def baseEnd_865865 : Nat := 148201642301786677635155

theorem tailTrace_865865 : CollatzResearch.WordTrace tailWord_865865 prefixEnd_865865 148201642301786677635155 := by
  unfold tailWord_865865
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580691008126457813943049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21053794005417638542628699 31580691008126457813943049)
  ·
    refine ⟨23685518256094843360457287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31580691008126457813943049 23685518256094843360457287)
    ·
      refine ⟨35528277384142265040685931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23685518256094843360457287 35528277384142265040685931)
      ·
        refine ⟨53292416076213397561028897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35528277384142265040685931 53292416076213397561028897)
        ·
          refine ⟨39969312057160048170771673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53292416076213397561028897 39969312057160048170771673)
          ·
            refine ⟨29976984042870036128078755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39969312057160048170771673 29976984042870036128078755)
            ·
              refine ⟨44965476064305054192118133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29976984042870036128078755 44965476064305054192118133)
              ·
                refine ⟨4215513381028598830511075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44965476064305054192118133 4215513381028598830511075)
                ·
                  refine ⟨6323270071542898245766613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215513381028598830511075 6323270071542898245766613)
                  ·
                    refine ⟨148201642301786677635155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6323270071542898245766613 148201642301786677635155)
                    ·
                      rfl

theorem cell23_865865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_865865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865865 prefixEnd_865865 := by exact prefixLift 865865
  have htrace : WordTrace (prefixWord ++ tailWord_865865) baseStart_865865 baseEnd_865865 := by
    simpa [prefixWord, tailWord_865865, baseEnd_865865] using wordTrace_append hprefix tailTrace_865865
  have hstable : (prefixWord ++ tailWord_865865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865865).length < 2 ^ (prefixWord ++ tailWord_865865).sum := by decide
  have hdescent : baseEnd_865865 < baseStart_865865 := by decide
  rcases family_descends (prefixWord ++ tailWord_865865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865892 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_865892 : Nat := 118140960795 + 865892 * 2 ^ 59
def prefixEnd_865892 : Nat := 4983230072969 + 3 ^ 40 * 865892 * 2
def baseEnd_865892 : Nat := 444618790883031427267841

theorem tailTrace_865892 : CollatzResearch.WordTrace tailWord_865892 prefixEnd_865892 444618790883031427267841 := by
  unfold tailWord_865892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15790837889514320712587965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21054450519352427616783953 15790837889514320712587965)
  ·
    refine ⟨5921564208567870267220487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15790837889514320712587965 5921564208567870267220487)
    ·
      refine ⟨8882346312851805400830731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5921564208567870267220487 8882346312851805400830731)
      ·
        refine ⟨13323519469277708101246097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882346312851805400830731 13323519469277708101246097)
        ·
          refine ⟨9992639601958281075934573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13323519469277708101246097 9992639601958281075934573)
          ·
            refine ⟨3747239850734355403475465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9992639601958281075934573 3747239850734355403475465)
            ·
              refine ⟨2810429888050766552606599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747239850734355403475465 2810429888050766552606599)
              ·
                refine ⟨4215644832076149828909899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2810429888050766552606599 4215644832076149828909899)
                ·
                  refine ⟨6323467248114224743364849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215644832076149828909899 6323467248114224743364849)
                  ·
                    refine ⟨4742600436085668557523637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323467248114224743364849 4742600436085668557523637)
                    ·
                      refine ⟨444618790883031427267841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4742600436085668557523637 444618790883031427267841)
                      ·
                        rfl

theorem cell23_865892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_865892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865892 prefixEnd_865892 := by exact prefixLift 865892
  have htrace : WordTrace (prefixWord ++ tailWord_865892) baseStart_865892 baseEnd_865892 := by
    simpa [prefixWord, tailWord_865892, baseEnd_865892] using wordTrace_append hprefix tailTrace_865892
  have hstable : (prefixWord ++ tailWord_865892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865892).length < 2 ^ (prefixWord ++ tailWord_865892).sum := by decide
  have hdescent : baseEnd_865892 < baseStart_865892 := by decide
  rcases family_descends (prefixWord ++ tailWord_865892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865979 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 6, 3, 2]
def baseStart_865979 : Nat := 118140960795 + 865979 * 2 ^ 59
def prefixEnd_865979 : Nat := 4983230072969 + 3 ^ 40 * 865979 * 2
def baseEnd_865979 : Nat := 444663463699972586879941

theorem tailTrace_865979 : CollatzResearch.WordTrace tailWord_865979 prefixEnd_865979 444663463699972586879941 := by
  unfold tailWord_865979
  simp only [CollatzResearch.WordTrace]
  refine ⟨31584848929713455283592991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21056565953142303522395327 31584848929713455283592991)
  ·
    refine ⟨47377273394570182925389487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31584848929713455283592991 47377273394570182925389487)
    ·
      refine ⟨71065910091855274388084231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47377273394570182925389487 71065910091855274388084231)
      ·
        refine ⟨106598865137782911582126347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71065910091855274388084231 106598865137782911582126347)
        ·
          refine ⟨159898297706674367373189521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106598865137782911582126347 159898297706674367373189521)
          ·
            refine ⟨119923723280005775529892141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159898297706674367373189521 119923723280005775529892141)
            ·
              refine ⟨44971396230002165823709553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119923723280005775529892141 44971396230002165823709553)
              ·
                refine ⟨33728547172501624367782165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44971396230002165823709553 33728547172501624367782165)
                ·
                  refine ⟨1581025648711013642239789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33728547172501624367782165 1581025648711013642239789)
                  ·
                    refine ⟨592884618266630115839921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581025648711013642239789 592884618266630115839921)
                    ·
                      refine ⟨444663463699972586879941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592884618266630115839921 444663463699972586879941)
                      ·
                        rfl

theorem cell23_865979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3, 2].length) (baseStart_865979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865979 prefixEnd_865979 := by exact prefixLift 865979
  have htrace : WordTrace (prefixWord ++ tailWord_865979) baseStart_865979 baseEnd_865979 := by
    simpa [prefixWord, tailWord_865979, baseEnd_865979] using wordTrace_append hprefix tailTrace_865979
  have hstable : (prefixWord ++ tailWord_865979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865979).length < 2 ^ (prefixWord ++ tailWord_865979).sum := by decide
  have hdescent : baseEnd_865979 < baseStart_865979 := by decide
  rcases family_descends (prefixWord ++ tailWord_865979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865990 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_865990 : Nat := 118140960795 + 865990 * 2 ^ 59
def prefixEnd_865990 : Nat := 4983230072969 + 3 ^ 40 * 865990 * 2
def baseEnd_865990 : Nat := 444669111987172043842391

theorem tailTrace_865990 : CollatzResearch.WordTrace tailWord_865990 prefixEnd_865990 444669111987172043842391 := by
  unfold tailWord_865990
  simp only [CollatzResearch.WordTrace]
  refine ⟨987039066646050130070107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21056833421782402774828949 987039066646050130070107)
  ·
    refine ⟨1480558599969075195105161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987039066646050130070107 1480558599969075195105161)
    ·
      refine ⟨1110418949976806396328871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480558599969075195105161 1110418949976806396328871)
      ·
        refine ⟨1665628424965209594493307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110418949976806396328871 1665628424965209594493307)
        ·
          refine ⟨2498442637447814391739961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665628424965209594493307 2498442637447814391739961)
          ·
            refine ⟨1873831978085860793804971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498442637447814391739961 1873831978085860793804971)
            ·
              refine ⟨2810747967128791190707457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873831978085860793804971 2810747967128791190707457)
              ·
                refine ⟨2108060975346593393030593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810747967128791190707457 2108060975346593393030593)
                ·
                  refine ⟨1581045731509945044772945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108060975346593393030593 1581045731509945044772945)
                  ·
                    refine ⟨1185784298632458783579709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1581045731509945044772945 1185784298632458783579709)
                    ·
                      refine ⟨444669111987172043842391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185784298632458783579709 444669111987172043842391)
                      ·
                        rfl

theorem cell23_865990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_865990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865990 prefixEnd_865990 := by exact prefixLift 865990
  have htrace : WordTrace (prefixWord ++ tailWord_865990) baseStart_865990 baseEnd_865990 := by
    simpa [prefixWord, tailWord_865990, baseEnd_865990] using wordTrace_append hprefix tailTrace_865990
  have hstable : (prefixWord ++ tailWord_865990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865990).length < 2 ^ (prefixWord ++ tailWord_865990).sum := by decide
  have hdescent : baseEnd_865990 < baseStart_865990 := by decide
  rcases family_descends (prefixWord ++ tailWord_865990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865997 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_865997 : Nat := 118140960795 + 865997 * 2 ^ 59
def prefixEnd_865997 : Nat := 4983230072969 + 3 ^ 40 * 865997 * 2
def baseEnd_865997 : Nat := 148224235450584505484953

theorem tailTrace_865997 : CollatzResearch.WordTrace tailWord_865997 prefixEnd_865997 148224235450584505484953 := by
  unfold tailWord_865997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31585505443648244357748245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21057003629098829571832163 31585505443648244357748245)
  ·
    refine ⟨1480570567671011454269449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31585505443648244357748245 1480570567671011454269449)
    ·
      refine ⟨1110427925753258590702087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480570567671011454269449 1110427925753258590702087)
      ·
        refine ⟨1665641888629887886053131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110427925753258590702087 1665641888629887886053131)
        ·
          refine ⟨2498462832944831829079697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665641888629887886053131 2498462832944831829079697)
          ·
            refine ⟨1873847124708623871809773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498462832944831829079697 1873847124708623871809773)
            ·
              refine ⟨702692671765733951928665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1873847124708623871809773 702692671765733951928665)
              ·
                refine ⟨527019503824300463946499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702692671765733951928665 527019503824300463946499)
                ·
                  refine ⟨790529255736450695919749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527019503824300463946499 790529255736450695919749)
                  ·
                    refine ⟨148224235450584505484953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 790529255736450695919749 148224235450584505484953)
                    ·
                      rfl

theorem cell23_865997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_865997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_865997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_865997 prefixEnd_865997 := by exact prefixLift 865997
  have htrace : WordTrace (prefixWord ++ tailWord_865997) baseStart_865997 baseEnd_865997 := by
    simpa [prefixWord, tailWord_865997, baseEnd_865997] using wordTrace_append hprefix tailTrace_865997
  have hstable : (prefixWord ++ tailWord_865997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865997).length < 2 ^ (prefixWord ++ tailWord_865997).sum := by decide
  have hdescent : baseEnd_865997 < baseStart_865997 := by decide
  rcases family_descends (prefixWord ++ tailWord_865997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866026 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_866026 : Nat := 118140960795 + 866026 * 2 ^ 59
def prefixEnd_866026 : Nat := 4983230072969 + 3 ^ 40 * 866026 * 2
def baseEnd_866026 : Nat := 444687597290733902992225

theorem tailTrace_866026 : CollatzResearch.WordTrace tailWord_866026 prefixEnd_866026 444687597290733902992225 := by
  unfold tailWord_866026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896640790135795577638483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21057708773695454873702621 7896640790135795577638483)
  ·
    refine ⟨11844961185203693366457725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7896640790135795577638483 11844961185203693366457725)
    ·
      refine ⟨4441860444451385012421647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11844961185203693366457725 4441860444451385012421647)
      ·
        refine ⟨6662790666677077518632471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441860444451385012421647 6662790666677077518632471)
        ·
          refine ⟨9994186000015616277948707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662790666677077518632471 9994186000015616277948707)
          ·
            refine ⟨14991279000023424416923061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994186000015616277948707 14991279000023424416923061)
            ·
              refine ⟨1405432406252196039086537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14991279000023424416923061 1405432406252196039086537)
              ·
                refine ⟨1054074304689147029314903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405432406252196039086537 1054074304689147029314903)
                ·
                  refine ⟨1581111457033720543972355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1054074304689147029314903 1581111457033720543972355)
                  ·
                    refine ⟨2371667185550580815958533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1581111457033720543972355 2371667185550580815958533)
                    ·
                      refine ⟨444687597290733902992225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2371667185550580815958533 444687597290733902992225)
                      ·
                        rfl

theorem cell23_866026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_866026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866026 prefixEnd_866026 := by exact prefixLift 866026
  have htrace : WordTrace (prefixWord ++ tailWord_866026) baseStart_866026 baseEnd_866026 := by
    simpa [prefixWord, tailWord_866026, baseEnd_866026] using wordTrace_append hprefix tailTrace_866026
  have hstable : (prefixWord ++ tailWord_866026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866026).length < 2 ^ (prefixWord ++ tailWord_866026).sum := by decide
  have hdescent : baseEnd_866026 < baseStart_866026 := by decide
  rcases family_descends (prefixWord ++ tailWord_866026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866066 : List Nat := [3, 2, 4, 1, 1, 1, 3, 8]
def baseStart_866066 : Nat := 118140960795 + 866066 * 2 ^ 59
def prefixEnd_866066 : Nat := 4983230072969 + 3 ^ 40 * 866066 * 2
def baseEnd_866066 : Nat := 16470671722848657277483

theorem tailTrace_866066 : CollatzResearch.WordTrace tailWord_866066 prefixEnd_866066 16470671722848657277483 := by
  unfold tailWord_866066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897005520099567285502513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21058681386932179428006701 7897005520099567285502513)
  ·
    refine ⟨5922754140074675464126885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7897005520099567285502513 5922754140074675464126885)
    ·
      refine ⟨1110516401264001649523791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5922754140074675464126885 1110516401264001649523791)
      ·
        refine ⟨1665774601896002474285687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110516401264001649523791 1665774601896002474285687)
        ·
          refine ⟨2498661902844003711428531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665774601896002474285687 2498661902844003711428531)
          ·
            refine ⟨3747992854266005567142797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498661902844003711428531 3747992854266005567142797)
            ·
              refine ⟨1405497320349752087678549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3747992854266005567142797 1405497320349752087678549)
              ·
                refine ⟨16470671722848657277483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1405497320349752087678549 16470671722848657277483)
                ·
                  rfl

theorem cell23_866066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_866066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866066 prefixEnd_866066 := by exact prefixLift 866066
  have htrace : WordTrace (prefixWord ++ tailWord_866066) baseStart_866066 baseEnd_866066 := by
    simpa [prefixWord, tailWord_866066, baseEnd_866066] using wordTrace_append hprefix tailTrace_866066
  have hstable : (prefixWord ++ tailWord_866066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866066).length < 2 ^ (prefixWord ++ tailWord_866066).sum := by decide
  have hdescent : baseEnd_866066 < baseStart_866066 := by decide
  rcases family_descends (prefixWord ++ tailWord_866066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866076 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_866076 : Nat := 118140960795 + 866076 * 2 ^ 59
def prefixEnd_866076 : Nat := 4983230072969 + 3 ^ 40 * 866076 * 2
def baseEnd_866076 : Nat := 444713271323458707366995

theorem tailTrace_866076 : CollatzResearch.WordTrace tailWord_866076 prefixEnd_866076 444713271323458707366995 := by
  unfold tailWord_866076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794193405181020424937041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21058924540241360566582721 15794193405181020424937041)
  ·
    refine ⟨11845645053885765318702781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15794193405181020424937041 11845645053885765318702781)
    ·
      refine ⟨4442116895207161994513543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11845645053885765318702781 4442116895207161994513543)
      ·
        refine ⟨6663175342810742991770315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442116895207161994513543 6663175342810742991770315)
        ·
          refine ⟨9994763014216114487655473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663175342810742991770315 9994763014216114487655473)
          ·
            refine ⟨7496072260662085865741605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994763014216114487655473 7496072260662085865741605)
            ·
              refine ⟨1405513548874141099826551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7496072260662085865741605 1405513548874141099826551)
              ·
                refine ⟨2108270323311211649739827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405513548874141099826551 2108270323311211649739827)
                ·
                  refine ⟨3162405484966817474609741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108270323311211649739827 3162405484966817474609741)
                  ·
                    refine ⟨1185902056862556552978653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3162405484966817474609741 1185902056862556552978653)
                    ·
                      refine ⟨444713271323458707366995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185902056862556552978653 444713271323458707366995)
                      ·
                        rfl

theorem cell23_866076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_866076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866076 prefixEnd_866076 := by exact prefixLift 866076
  have htrace : WordTrace (prefixWord ++ tailWord_866076) baseStart_866076 baseEnd_866076 := by
    simpa [prefixWord, tailWord_866076, baseEnd_866076] using wordTrace_append hprefix tailTrace_866076
  have hstable : (prefixWord ++ tailWord_866076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866076).length < 2 ^ (prefixWord ++ tailWord_866076).sum := by decide
  have hdescent : baseEnd_866076 < baseStart_866076 := by decide
  rcases family_descends (prefixWord ++ tailWord_866076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866094 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_866094 : Nat := 118140960795 + 866094 * 2 ^ 59
def prefixEnd_866094 : Nat := 4983230072969 + 3 ^ 40 * 866094 * 2
def baseEnd_866094 : Nat := 444722513975239636941913

theorem tailTrace_866094 : CollatzResearch.WordTrace tailWord_866094 prefixEnd_866094 444722513975239636941913 := by
  unfold tailWord_866094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948630415537103740503667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21059362216197886616019557 3948630415537103740503667)
  ·
    refine ⟨5922945623305655610755501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948630415537103740503667 5922945623305655610755501)
    ·
      refine ⟨2221104608739620854033313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5922945623305655610755501 2221104608739620854033313)
      ·
        refine ⟨1665828456554715640524985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221104608739620854033313 1665828456554715640524985)
        ·
          refine ⟨1249371342416036730393739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665828456554715640524985 1249371342416036730393739)
          ·
            refine ⟨1874057013624055095590609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249371342416036730393739 1874057013624055095590609)
            ·
              refine ⟨1405542760218041321692957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874057013624055095590609 1405542760218041321692957)
              ·
                refine ⟨527078535081765495634859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405542760218041321692957 527078535081765495634859)
                ·
                  refine ⟨790617802622648243452289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527078535081765495634859 790617802622648243452289)
                  ·
                    refine ⟨592963351966986182589217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790617802622648243452289 592963351966986182589217)
                    ·
                      refine ⟨444722513975239636941913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592963351966986182589217 444722513975239636941913)
                      ·
                        rfl

theorem cell23_866094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_866094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866094 prefixEnd_866094 := by exact prefixLift 866094
  have htrace : WordTrace (prefixWord ++ tailWord_866094) baseStart_866094 baseEnd_866094 := by
    simpa [prefixWord, tailWord_866094, baseEnd_866094] using wordTrace_append hprefix tailTrace_866094
  have hstable : (prefixWord ++ tailWord_866094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866094).length < 2 ^ (prefixWord ++ tailWord_866094).sum := by decide
  have hdescent : baseEnd_866094 < baseStart_866094 := by decide
  rcases family_descends (prefixWord ++ tailWord_866094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866110 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_866110 : Nat := 118140960795 + 866110 * 2 ^ 59
def prefixEnd_866110 : Nat := 4983230072969 + 3 ^ 40 * 866110 * 2
def baseEnd_866110 : Nat := 444730729665711574341839

theorem tailTrace_866110 : CollatzResearch.WordTrace tailWord_866110 prefixEnd_866110 444730729665711574341839 := by
  unfold tailWord_866110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948703361529858082076473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21059751261492576437741189 3948703361529858082076473)
  ·
    refine ⟨2961527521147393561557355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3948703361529858082076473 2961527521147393561557355)
    ·
      refine ⟨4442291281721090342336033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961527521147393561557355 4442291281721090342336033)
      ·
        refine ⟨3331718461290817756752025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442291281721090342336033 3331718461290817756752025)
        ·
          refine ⟨2498788845968113317564019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331718461290817756752025 2498788845968113317564019)
          ·
            refine ⟨3748183268952169976346029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498788845968113317564019 3748183268952169976346029)
            ·
              refine ⟨1405568725857063741129761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3748183268952169976346029 1405568725857063741129761)
              ·
                refine ⟨1054176544392797805847321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405568725857063741129761 1054176544392797805847321)
                ·
                  refine ⟨790632408294598354385491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054176544392797805847321 790632408294598354385491)
                  ·
                    refine ⟨1185948612441897531578237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 790632408294598354385491 1185948612441897531578237)
                    ·
                      refine ⟨444730729665711574341839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185948612441897531578237 444730729665711574341839)
                      ·
                        rfl

theorem cell23_866110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_866110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866110 prefixEnd_866110 := by exact prefixLift 866110
  have htrace : WordTrace (prefixWord ++ tailWord_866110) baseStart_866110 baseEnd_866110 := by
    simpa [prefixWord, tailWord_866110, baseEnd_866110] using wordTrace_append hprefix tailTrace_866110
  have hstable : (prefixWord ++ tailWord_866110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866110).length < 2 ^ (prefixWord ++ tailWord_866110).sum := by decide
  have hdescent : baseEnd_866110 < baseStart_866110 := by decide
  rcases family_descends (prefixWord ++ tailWord_866110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866119 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_866119 : Nat := 118140960795 + 866119 * 2 ^ 59
def prefixEnd_866119 : Nat := 4983230072969 + 3 ^ 40 * 866119 * 2
def baseEnd_866119 : Nat := 444735350991602039129297

theorem tailTrace_866119 : CollatzResearch.WordTrace tailWord_866119 prefixEnd_866119 444735350991602039129297 := by
  unfold tailWord_866119
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589955149206259193689411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21059970099470839462459607 31589955149206259193689411)
  ·
    refine ⟨47384932723809388790534117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31589955149206259193689411 47384932723809388790534117)
    ·
      refine ⟨8884674885714260398225147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47384932723809388790534117 8884674885714260398225147)
      ·
        refine ⟨13327012328571390597337721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8884674885714260398225147 13327012328571390597337721)
        ·
          refine ⟨9995259246428542948003291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13327012328571390597337721 9995259246428542948003291)
          ·
            refine ⟨14992888869642814422004937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9995259246428542948003291 14992888869642814422004937)
            ·
              refine ⟨11244666652232110816503703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14992888869642814422004937 11244666652232110816503703)
              ·
                refine ⟨16866999978348166224755555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11244666652232110816503703 16866999978348166224755555)
                ·
                  refine ⟨25300499967522249337133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16866999978348166224755555 25300499967522249337133333)
                  ·
                    refine ⟨1185960935977605437678125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25300499967522249337133333 1185960935977605437678125)
                    ·
                      refine ⟨444735350991602039129297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1185960935977605437678125 444735350991602039129297)
                      ·
                        rfl

theorem cell23_866119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_866119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866119 prefixEnd_866119 := by exact prefixLift 866119
  have htrace : WordTrace (prefixWord ++ tailWord_866119) baseStart_866119 baseEnd_866119 := by
    simpa [prefixWord, tailWord_866119, baseEnd_866119] using wordTrace_append hprefix tailTrace_866119
  have hstable : (prefixWord ++ tailWord_866119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866119).length < 2 ^ (prefixWord ++ tailWord_866119).sum := by decide
  have hdescent : baseEnd_866119 < baseStart_866119 := by decide
  rcases family_descends (prefixWord ++ tailWord_866119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866133 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_866133 : Nat := 118140960795 + 866133 * 2 ^ 59
def prefixEnd_866133 : Nat := 4983230072969 + 3 ^ 40 * 866133 * 2
def baseEnd_866133 : Nat := 444742539720764984354233

theorem tailTrace_866133 : CollatzResearch.WordTrace tailWord_866133 prefixEnd_866133 444742539720764984354233 := by
  unfold tailWord_866133
  simp only [CollatzResearch.WordTrace]
  refine ⟨31590465771155539584699053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21060310514103693056466035 31590465771155539584699053)
  ·
    refine ⟨11846424664183327344262145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31590465771155539584699053 11846424664183327344262145)
    ·
      refine ⟨8884818498137495508196609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11846424664183327344262145 8884818498137495508196609)
      ·
        refine ⟨6663613873603121631147457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8884818498137495508196609 6663613873603121631147457)
        ·
          refine ⟨4997710405202341223360593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6663613873603121631147457 4997710405202341223360593)
          ·
            refine ⟨3748282803901755917520445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4997710405202341223360593 3748282803901755917520445)
            ·
              refine ⟨1405606051463158469070167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3748282803901755917520445 1405606051463158469070167)
              ·
                refine ⟨2108409077194737703605251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405606051463158469070167 2108409077194737703605251)
                ·
                  refine ⟨3162613615792106555407877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108409077194737703605251 3162613615792106555407877)
                  ·
                    refine ⟨592990052961019979138977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3162613615792106555407877 592990052961019979138977)
                    ·
                      refine ⟨444742539720764984354233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 592990052961019979138977 444742539720764984354233)
                      ·
                        rfl

theorem cell23_866133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_866133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866133 prefixEnd_866133 := by exact prefixLift 866133
  have htrace : WordTrace (prefixWord ++ tailWord_866133) baseStart_866133 baseEnd_866133 := by
    simpa [prefixWord, tailWord_866133, baseEnd_866133] using wordTrace_append hprefix tailTrace_866133
  have hstable : (prefixWord ++ tailWord_866133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866133).length < 2 ^ (prefixWord ++ tailWord_866133).sum := by decide
  have hdescent : baseEnd_866133 < baseStart_866133 := by decide
  rcases family_descends (prefixWord ++ tailWord_866133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866176 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2]
def baseStart_866176 : Nat := 118140960795 + 866176 * 2 ^ 59
def prefixEnd_866176 : Nat := 4983230072969 + 3 ^ 40 * 866176 * 2
def baseEnd_866176 : Nat := 444764619388908316116535

theorem tailTrace_866176 : CollatzResearch.WordTrace tailWord_866176 prefixEnd_866176 444764619388908316116535 := by
  unfold tailWord_866176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796017054999878964257191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21061356073333171952342921 15796017054999878964257191)
  ·
    refine ⟨23694025582499818446385787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15796017054999878964257191 23694025582499818446385787)
    ·
      refine ⟨35541038373749727669578681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23694025582499818446385787 35541038373749727669578681)
      ·
        refine ⟨26655778780312295752184011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35541038373749727669578681 26655778780312295752184011)
        ·
          refine ⟨39983668170468443628276017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26655778780312295752184011 39983668170468443628276017)
          ·
            refine ⟨29987751127851332721207013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39983668170468443628276017 29987751127851332721207013)
            ·
              refine ⟨5622703336472124885226315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29987751127851332721207013 5622703336472124885226315)
              ·
                refine ⟨8434055004708187327839473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622703336472124885226315 8434055004708187327839473)
                ·
                  refine ⟨6325541253531140495879605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8434055004708187327839473 6325541253531140495879605)
                  ·
                    refine ⟨593019492518544421488713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6325541253531140495879605 593019492518544421488713)
                    ·
                      refine ⟨444764619388908316116535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593019492518544421488713 444764619388908316116535)
                      ·
                        rfl

theorem cell23_866176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_866176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866176 prefixEnd_866176 := by exact prefixLift 866176
  have htrace : WordTrace (prefixWord ++ tailWord_866176) baseStart_866176 baseEnd_866176 := by
    simpa [prefixWord, tailWord_866176, baseEnd_866176] using wordTrace_append hprefix tailTrace_866176
  have hstable : (prefixWord ++ tailWord_866176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866176).length < 2 ^ (prefixWord ++ tailWord_866176).sum := by decide
  have hdescent : baseEnd_866176 < baseStart_866176 := by decide
  rcases family_descends (prefixWord ++ tailWord_866176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866179 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_866179 : Nat := 118140960795 + 866179 * 2 ^ 59
def prefixEnd_866179 : Nat := 4983230072969 + 3 ^ 40 * 866179 * 2
def baseEnd_866179 : Nat := 444766159830871804379021

theorem tailTrace_866179 : CollatzResearch.WordTrace tailWord_866179 prefixEnd_866179 444766159830871804379021 := by
  unfold tailWord_866179
  simp only [CollatzResearch.WordTrace]
  refine ⟨31592143528988889440873591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21061429019325926293915727 31592143528988889440873591)
  ·
    refine ⟨47388215293483334161310387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31592143528988889440873591 47388215293483334161310387)
    ·
      refine ⟨71082322940225001241965581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47388215293483334161310387 71082322940225001241965581)
      ·
        refine ⟨26655871102584375465737093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71082322940225001241965581 26655871102584375465737093)
        ·
          refine ⟨4997975831734570399825705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26655871102584375465737093 4997975831734570399825705)
          ·
            refine ⟨3748481873800927799869279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4997975831734570399825705 3748481873800927799869279)
            ·
              refine ⟨5622722810701391699803919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748481873800927799869279 5622722810701391699803919)
              ·
                refine ⟨8434084216052087549705879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622722810701391699803919 8434084216052087549705879)
                ·
                  refine ⟨12651126324078131324558819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434084216052087549705879 12651126324078131324558819)
                  ·
                    refine ⟨18976689486117196986838229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12651126324078131324558819 18976689486117196986838229)
                    ·
                      refine ⟨444766159830871804379021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18976689486117196986838229 444766159830871804379021)
                      ·
                        rfl

theorem cell23_866179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_866179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866179 prefixEnd_866179 := by exact prefixLift 866179
  have htrace : WordTrace (prefixWord ++ tailWord_866179) baseStart_866179 baseEnd_866179 := by
    simpa [prefixWord, tailWord_866179, baseEnd_866179] using wordTrace_append hprefix tailTrace_866179
  have hstable : (prefixWord ++ tailWord_866179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866179).length < 2 ^ (prefixWord ++ tailWord_866179).sum := by decide
  have hdescent : baseEnd_866179 < baseStart_866179 := by decide
  rcases family_descends (prefixWord ++ tailWord_866179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866184 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_866184 : Nat := 118140960795 + 866184 * 2 ^ 59
def prefixEnd_866184 : Nat := 4983230072969 + 3 ^ 40 * 866184 * 2
def baseEnd_866184 : Nat := 444768727234144284816499

theorem tailTrace_866184 : CollatzResearch.WordTrace tailWord_866184 prefixEnd_866184 444768727234144284816499 := by
  unfold tailWord_866184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796162946985387647402803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21061550595980516863203737 15796162946985387647402803)
  ·
    refine ⟨23694244420478081471104205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15796162946985387647402803 23694244420478081471104205)
    ·
      refine ⟨8885341657679280551664077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23694244420478081471104205 8885341657679280551664077)
      ·
        refine ⟨3332003121629730206874029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8885341657679280551664077 3332003121629730206874029)
        ·
          refine ⟨1249501170611148827577761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3332003121629730206874029 1249501170611148827577761)
          ·
            refine ⟨937125877958361620683321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249501170611148827577761 937125877958361620683321)
            ·
              refine ⟨702844408468771215512491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937125877958361620683321 702844408468771215512491)
              ·
                refine ⟨1054266612703156823268737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702844408468771215512491 1054266612703156823268737)
                ·
                  refine ⟨790699959527367617451553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054266612703156823268737 790699959527367617451553)
                  ·
                    refine ⟨593024969645525713088665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 790699959527367617451553 593024969645525713088665)
                    ·
                      refine ⟨444768727234144284816499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593024969645525713088665 444768727234144284816499)
                      ·
                        rfl

theorem cell23_866184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_866184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866184 prefixEnd_866184 := by exact prefixLift 866184
  have htrace : WordTrace (prefixWord ++ tailWord_866184) baseStart_866184 baseEnd_866184 := by
    simpa [prefixWord, tailWord_866184, baseEnd_866184] using wordTrace_append hprefix tailTrace_866184
  have hstable : (prefixWord ++ tailWord_866184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866184).length < 2 ^ (prefixWord ++ tailWord_866184).sum := by decide
  have hdescent : baseEnd_866184 < baseStart_866184 := by decide
  rcases family_descends (prefixWord ++ tailWord_866184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866249 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_866249 : Nat := 118140960795 + 866249 * 2 ^ 59
def prefixEnd_866249 : Nat := 4983230072969 + 3 ^ 40 * 866249 * 2
def baseEnd_866249 : Nat := 444802103476686530503699

theorem tailTrace_866249 : CollatzResearch.WordTrace tailWord_866249 prefixEnd_866249 444802103476686530503699 := by
  unfold tailWord_866249
  simp only [CollatzResearch.WordTrace]
  refine ⟨31594696638735291395921801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21063131092490194263947867 31594696638735291395921801)
  ·
    refine ⟨23696022479051468546941351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31594696638735291395921801 23696022479051468546941351)
    ·
      refine ⟨35544033718577202820412027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23696022479051468546941351 35544033718577202820412027)
      ·
        refine ⟨53316050577865804230618041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35544033718577202820412027 53316050577865804230618041)
        ·
          refine ⟨39987037933399353172963531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53316050577865804230618041 39987037933399353172963531)
          ·
            refine ⟨59980556900099029759445297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39987037933399353172963531 59980556900099029759445297)
            ·
              refine ⟨44985417675074272319583973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59980556900099029759445297 44985417675074272319583973)
              ·
                refine ⟨8434765814076426059921995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44985417675074272319583973 8434765814076426059921995)
                ·
                  refine ⟨12652148721114639089882993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434765814076426059921995 12652148721114639089882993)
                  ·
                    refine ⟨9489111540835979317412245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12652148721114639089882993 9489111540835979317412245)
                    ·
                      refine ⟨444802103476686530503699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9489111540835979317412245 444802103476686530503699)
                      ·
                        rfl

theorem cell23_866249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_866249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866249 prefixEnd_866249 := by exact prefixLift 866249
  have htrace : WordTrace (prefixWord ++ tailWord_866249) baseStart_866249 baseEnd_866249 := by
    simpa [prefixWord, tailWord_866249, baseEnd_866249] using wordTrace_append hprefix tailTrace_866249
  have hstable : (prefixWord ++ tailWord_866249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866249).length < 2 ^ (prefixWord ++ tailWord_866249).sum := by decide
  have hdescent : baseEnd_866249 < baseStart_866249 := by decide
  rcases family_descends (prefixWord ++ tailWord_866249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866283 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 2, 3, 2]
def baseStart_866283 : Nat := 118140960795 + 866283 * 2 ^ 59
def prefixEnd_866283 : Nat := 4983230072969 + 3 ^ 40 * 866283 * 2
def baseEnd_866283 : Nat := 444819561818939397478543

theorem tailTrace_866283 : CollatzResearch.WordTrace tailWord_866283 prefixEnd_866283 444819561818939397478543 := by
  unfold tailWord_866283
  simp only [CollatzResearch.WordTrace]
  refine ⟨31595936720612115202659503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21063957813741410135106335 31595936720612115202659503)
  ·
    refine ⟨47393905080918172803989255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31595936720612115202659503 47393905080918172803989255)
    ·
      refine ⟨71090857621377259205983883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47393905080918172803989255 71090857621377259205983883)
      ·
        refine ⟨106636286432065888808975825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71090857621377259205983883 106636286432065888808975825)
        ·
          refine ⟨79977214824049416606731869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106636286432065888808975825 79977214824049416606731869)
          ·
            refine ⟨29991455559018531227524451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79977214824049416606731869 29991455559018531227524451)
            ·
              refine ⟨44987183338527796841286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29991455559018531227524451 44987183338527796841286677)
              ·
                refine ⟨2108774218993490476935313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44987183338527796841286677 2108774218993490476935313)
                ·
                  refine ⟨1581580664245117857701485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2108774218993490476935313 1581580664245117857701485)
                  ·
                    refine ⟨593092749091919196638057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1581580664245117857701485 593092749091919196638057)
                    ·
                      refine ⟨444819561818939397478543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593092749091919196638057 444819561818939397478543)
                      ·
                        rfl

theorem cell23_866283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3, 2].length) (baseStart_866283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866283 prefixEnd_866283 := by exact prefixLift 866283
  have htrace : WordTrace (prefixWord ++ tailWord_866283) baseStart_866283 baseEnd_866283 := by
    simpa [prefixWord, tailWord_866283, baseEnd_866283] using wordTrace_append hprefix tailTrace_866283
  have hstable : (prefixWord ++ tailWord_866283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866283).length < 2 ^ (prefixWord ++ tailWord_866283).sum := by decide
  have hdescent : baseEnd_866283 < baseStart_866283 := by decide
  rcases family_descends (prefixWord ++ tailWord_866283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866296 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_866296 : Nat := 118140960795 + 866296 * 2 ^ 59
def prefixEnd_866296 : Nat := 4983230072969 + 3 ^ 40 * 866296 * 2
def baseEnd_866296 : Nat := 444826237067447846615983

theorem tailTrace_866296 : CollatzResearch.WordTrace tailWord_866296 prefixEnd_866296 444826237067447846615983 := by
  unfold tailWord_866296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15798205434782509211441371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21064273913043345615255161 15798205434782509211441371)
  ·
    refine ⟨23697308152173763817162057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15798205434782509211441371 23697308152173763817162057)
    ·
      refine ⟨17772981114130322862871543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23697308152173763817162057 17772981114130322862871543)
      ·
        refine ⟨26659471671195484294307315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17772981114130322862871543 26659471671195484294307315)
        ·
          refine ⟨39989207506793226441460973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26659471671195484294307315 39989207506793226441460973)
          ·
            refine ⟨14995952815047459915547865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39989207506793226441460973 14995952815047459915547865)
            ·
              refine ⟨11246964611285594936660899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14995952815047459915547865 11246964611285594936660899)
              ·
                refine ⟨16870446916928392404991349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11246964611285594936660899 16870446916928392404991349)
                ·
                  refine ⟨1581604398462036787967939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16870446916928392404991349 1581604398462036787967939)
                  ·
                    refine ⟨2372406597693055181951909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1581604398462036787967939 2372406597693055181951909)
                    ·
                      refine ⟨444826237067447846615983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2372406597693055181951909 444826237067447846615983)
                      ·
                        rfl

theorem cell23_866296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_866296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866296 prefixEnd_866296 := by exact prefixLift 866296
  have htrace : WordTrace (prefixWord ++ tailWord_866296) baseStart_866296 baseEnd_866296 := by
    simpa [prefixWord, tailWord_866296, baseEnd_866296] using wordTrace_append hprefix tailTrace_866296
  have hstable : (prefixWord ++ tailWord_866296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866296).length < 2 ^ (prefixWord ++ tailWord_866296).sum := by decide
  have hdescent : baseEnd_866296 < baseStart_866296 := by decide
  rcases family_descends (prefixWord ++ tailWord_866296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866316 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_866316 : Nat := 118140960795 + 866316 * 2 ^ 59
def prefixEnd_866316 : Nat := 4983230072969 + 3 ^ 40 * 866316 * 2
def baseEnd_866316 : Nat := 444836506680537768365891

theorem tailTrace_866316 : CollatzResearch.WordTrace tailWord_866316 prefixEnd_866316 444836506680537768365891 := by
  unfold tailWord_866316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15798570164746280919305401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21064760219661707892407201 15798570164746280919305401)
  ·
    refine ⟨11848927623559710689479051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15798570164746280919305401 11848927623559710689479051)
    ·
      refine ⟨17773391435339566034218577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11848927623559710689479051 17773391435339566034218577)
      ·
        refine ⟨13330043576504674525663933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17773391435339566034218577 13330043576504674525663933)
        ·
          refine ⟨4998766341189252947123975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13330043576504674525663933 4998766341189252947123975)
          ·
            refine ⟨7498149511783879420685963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998766341189252947123975 7498149511783879420685963)
            ·
              refine ⟨11247224267675819131028945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498149511783879420685963 11247224267675819131028945)
              ·
                refine ⟨8435418200756864348271709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11247224267675819131028945 8435418200756864348271709)
                ·
                  refine ⟨3163281825283824130601891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8435418200756864348271709 3163281825283824130601891)
                  ·
                    refine ⟨4744922737925736195902837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163281825283824130601891 4744922737925736195902837)
                    ·
                      refine ⟨444836506680537768365891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4744922737925736195902837 444836506680537768365891)
                      ·
                        rfl

theorem cell23_866316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_866316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866316 prefixEnd_866316 := by exact prefixLift 866316
  have htrace : WordTrace (prefixWord ++ tailWord_866316) baseStart_866316 baseEnd_866316 := by
    simpa [prefixWord, tailWord_866316, baseEnd_866316] using wordTrace_append hprefix tailTrace_866316
  have hstable : (prefixWord ++ tailWord_866316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866316).length < 2 ^ (prefixWord ++ tailWord_866316).sum := by decide
  have hdescent : baseEnd_866316 < baseStart_866316 := by decide
  rcases family_descends (prefixWord ++ tailWord_866316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866333 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_866333 : Nat := 118140960795 + 866333 * 2 ^ 59
def prefixEnd_866333 : Nat := 4983230072969 + 3 ^ 40 * 866333 * 2
def baseEnd_866333 : Nat := 444845235851664201853313

theorem tailTrace_866333 : CollatzResearch.WordTrace tailWord_866333 prefixEnd_866333 444845235851664201853313 := by
  unfold tailWord_866333
  simp only [CollatzResearch.WordTrace]
  refine ⟨31597760370430973741979653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21065173580287315827986435 31597760370430973741979653)
  ·
    refine ⟨5924580069455807576621185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31597760370430973741979653 5924580069455807576621185)
    ·
      refine ⟨4443435052091855682465889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5924580069455807576621185 4443435052091855682465889)
      ·
        refine ⟨3332576289068891761849417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4443435052091855682465889 3332576289068891761849417)
        ·
          refine ⟨2499432216801668821387063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3332576289068891761849417 2499432216801668821387063)
          ·
            refine ⟨3749148325202503232080595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499432216801668821387063 3749148325202503232080595)
            ·
              refine ⟨5623722487803754848120893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749148325202503232080595 5623722487803754848120893)
              ·
                refine ⟨2108895932926408068045335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5623722487803754848120893 2108895932926408068045335)
                ·
                  refine ⟨3163343899389612102068003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2108895932926408068045335 3163343899389612102068003)
                  ·
                    refine ⟨4745015849084418153102005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3163343899389612102068003 4745015849084418153102005)
                    ·
                      refine ⟨444845235851664201853313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4745015849084418153102005 444845235851664201853313)
                      ·
                        rfl

theorem cell23_866333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_866333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866333 prefixEnd_866333 := by exact prefixLift 866333
  have htrace : WordTrace (prefixWord ++ tailWord_866333) baseStart_866333 baseEnd_866333 := by
    simpa [prefixWord, tailWord_866333, baseEnd_866333] using wordTrace_append hprefix tailTrace_866333
  have hstable : (prefixWord ++ tailWord_866333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866333).length < 2 ^ (prefixWord ++ tailWord_866333).sum := by decide
  have hdescent : baseEnd_866333 < baseStart_866333 := by decide
  rcases family_descends (prefixWord ++ tailWord_866333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866376 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_866376 : Nat := 118140960795 + 866376 * 2 ^ 59
def prefixEnd_866376 : Nat := 4983230072969 + 3 ^ 40 * 866376 * 2
def baseEnd_866376 : Nat := 444867315519807533615615

theorem tailTrace_866376 : CollatzResearch.WordTrace tailWord_866376 prefixEnd_866376 444867315519807533615615 := by
  unfold tailWord_866376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799664354637596042897491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21066219139516794723863321 15799664354637596042897491)
  ·
    refine ⟨23699496531956394064346237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15799664354637596042897491 23699496531956394064346237)
    ·
      refine ⟨8887311199483647774129839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23699496531956394064346237 8887311199483647774129839)
      ·
        refine ⟨13330966799225471661194759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8887311199483647774129839 13330966799225471661194759)
        ·
          refine ⟨19996450198838207491792139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330966799225471661194759 19996450198838207491792139)
          ·
            refine ⟨29994675298257311237688209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19996450198838207491792139 29994675298257311237688209)
            ·
              refine ⟨22496006473692983428266157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29994675298257311237688209 22496006473692983428266157)
              ·
                refine ⟨8436002427634868785599809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22496006473692983428266157 8436002427634868785599809)
                ·
                  refine ⟨6327001820726151589199857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436002427634868785599809 6327001820726151589199857)
                  ·
                    refine ⟨4745251365544613691899893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327001820726151589199857 4745251365544613691899893)
                    ·
                      refine ⟨444867315519807533615615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4745251365544613691899893 444867315519807533615615)
                      ·
                        rfl

theorem cell23_866376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_866376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866376 prefixEnd_866376 := by exact prefixLift 866376
  have htrace : WordTrace (prefixWord ++ tailWord_866376) baseStart_866376 baseEnd_866376 := by
    simpa [prefixWord, tailWord_866376, baseEnd_866376] using wordTrace_append hprefix tailTrace_866376
  have hstable : (prefixWord ++ tailWord_866376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866376).length < 2 ^ (prefixWord ++ tailWord_866376).sum := by decide
  have hdescent : baseEnd_866376 < baseStart_866376 := by decide
  rcases family_descends (prefixWord ++ tailWord_866376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866413 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_866413 : Nat := 118140960795 + 866413 * 2 ^ 59
def prefixEnd_866413 : Nat := 4983230072969 + 3 ^ 40 * 866413 * 2
def baseEnd_866413 : Nat := 148295438101341296284315

theorem tailTrace_866413 : CollatzResearch.WordTrace tailWord_866413 prefixEnd_866413 148295438101341296284315 := by
  unfold tailWord_866413
  simp only [CollatzResearch.WordTrace]
  refine ⟨31600678210141147404891893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21067118806760764936594595 31600678210141147404891893)
  ·
    refine ⟨2962563582200732569208615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31600678210141147404891893 2962563582200732569208615)
    ·
      refine ⟨4443845373301098853812923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962563582200732569208615 4443845373301098853812923)
      ·
        refine ⟨6665768059951648280719385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443845373301098853812923 6665768059951648280719385)
        ·
          refine ⟨4999326044963736210539539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6665768059951648280719385 4999326044963736210539539)
          ·
            refine ⟨7498989067445604315809309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999326044963736210539539 7498989067445604315809309)
            ·
              refine ⟨2812120900292101618428491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7498989067445604315809309 2812120900292101618428491)
              ·
                refine ⟨4218181350438152427642737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812120900292101618428491 4218181350438152427642737)
                ·
                  refine ⟨3163636012828614320732053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4218181350438152427642737 3163636012828614320732053)
                  ·
                    refine ⟨148295438101341296284315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3163636012828614320732053 148295438101341296284315)
                    ·
                      rfl

theorem cell23_866413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_866413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866413 prefixEnd_866413 := by exact prefixLift 866413
  have htrace : WordTrace (prefixWord ++ tailWord_866413) baseStart_866413 baseEnd_866413 := by
    simpa [prefixWord, tailWord_866413, baseEnd_866413] using wordTrace_append hprefix tailTrace_866413
  have hstable : (prefixWord ++ tailWord_866413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866413).length < 2 ^ (prefixWord ++ tailWord_866413).sum := by decide
  have hdescent : baseEnd_866413 < baseStart_866413 := by decide
  rcases family_descends (prefixWord ++ tailWord_866413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866453 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_866453 : Nat := 118140960795 + 866453 * 2 ^ 59
def prefixEnd_866453 : Nat := 4983230072969 + 3 ^ 40 * 866453 * 2
def baseEnd_866453 : Nat := 444906853530203732352761

theorem tailTrace_866453 : CollatzResearch.WordTrace tailWord_866453 prefixEnd_866453 444906853530203732352761 := by
  unfold tailWord_866453
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602137129996234236348013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21068091419997489490898675 31602137129996234236348013)
  ·
    refine ⟨11850801423748587838630505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31602137129996234236348013 11850801423748587838630505)
    ·
      refine ⟨8888101067811440878972879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11850801423748587838630505 8888101067811440878972879)
      ·
        refine ⟨13332151601717161318459319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8888101067811440878972879 13332151601717161318459319)
        ·
          refine ⟨19998227402575741977688979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13332151601717161318459319 19998227402575741977688979)
          ·
            refine ⟨29997341103863612966533469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19998227402575741977688979 29997341103863612966533469)
            ·
              refine ⟨11249002913948854862450051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29997341103863612966533469 11249002913948854862450051)
              ·
                refine ⟨16873504370923282293675077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11249002913948854862450051 16873504370923282293675077)
                ·
                  refine ⟨3163782069548115430064077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16873504370923282293675077 3163782069548115430064077)
                  ·
                    refine ⟨1186418276080543286274029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3163782069548115430064077 1186418276080543286274029)
                    ·
                      refine ⟨444906853530203732352761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1186418276080543286274029 444906853530203732352761)
                      ·
                        rfl

theorem cell23_866453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_866453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866453 prefixEnd_866453 := by exact prefixLift 866453
  have htrace : WordTrace (prefixWord ++ tailWord_866453) baseStart_866453 baseEnd_866453 := by
    simpa [prefixWord, tailWord_866453, baseEnd_866453] using wordTrace_append hprefix tailTrace_866453
  have hstable : (prefixWord ++ tailWord_866453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866453).length < 2 ^ (prefixWord ++ tailWord_866453).sum := by decide
  have hdescent : baseEnd_866453 < baseStart_866453 := by decide
  rcases family_descends (prefixWord ++ tailWord_866453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866460 : List Nat := [2, 2, 3, 2, 1, 1, 1, 6, 5]
def baseStart_866460 : Nat := 118140960795 + 866460 * 2 ^ 59
def prefixEnd_866460 : Nat := 4983230072969 + 3 ^ 40 * 866460 * 2
def baseEnd_866460 : Nat := 49434494210531689440581

theorem tailTrace_866460 : CollatzResearch.WordTrace tailWord_866460 prefixEnd_866460 49434494210531689440581 := by
  unfold tailWord_866460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15801196220485437215926417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21068261627313916287901889 15801196220485437215926417)
  ·
    refine ⟨11850897165364077911944813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15801196220485437215926417 11850897165364077911944813)
    ·
      refine ⟨4444086437011529216979305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11850897165364077911944813 4444086437011529216979305)
      ·
        refine ⟨3333064827758646912734479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444086437011529216979305 3333064827758646912734479)
        ·
          refine ⟨4999597241637970369101719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333064827758646912734479 4999597241637970369101719)
          ·
            refine ⟨7499395862456955553652579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999597241637970369101719 7499395862456955553652579)
            ·
              refine ⟨11249093793685433330478869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7499395862456955553652579 11249093793685433330478869)
              ·
                refine ⟨527301271579004687366197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11249093793685433330478869 527301271579004687366197)
                ·
                  refine ⟨49434494210531689440581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527301271579004687366197 49434494210531689440581)
                  ·
                    rfl

theorem cell23_866460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_866460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866460 prefixEnd_866460 := by exact prefixLift 866460
  have htrace : WordTrace (prefixWord ++ tailWord_866460) baseStart_866460 baseEnd_866460 := by
    simpa [prefixWord, tailWord_866460, baseEnd_866460] using wordTrace_append hprefix tailTrace_866460
  have hstable : (prefixWord ++ tailWord_866460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866460).length < 2 ^ (prefixWord ++ tailWord_866460).sum := by decide
  have hdescent : baseEnd_866460 < baseStart_866460 := by decide
  rcases family_descends (prefixWord ++ tailWord_866460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866471 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_866471 : Nat := 118140960795 + 866471 * 2 ^ 59
def prefixEnd_866471 : Nat := 4983230072969 + 3 ^ 40 * 866471 * 2
def baseEnd_866471 : Nat := 444916096181984661927679

theorem tailTrace_866471 : CollatzResearch.WordTrace tailWord_866471 prefixEnd_866471 444916096181984661927679 := by
  unfold tailWord_866471
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602793643931023310503267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21068529095954015540335511 31602793643931023310503267)
  ·
    refine ⟨47404190465896534965754901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31602793643931023310503267 47404190465896534965754901)
    ·
      refine ⟨2222071428088900076519761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47404190465896534965754901 2222071428088900076519761)
      ·
        refine ⟨1666553571066675057389821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2222071428088900076519761 1666553571066675057389821)
        ·
          refine ⟨624957589150003146521183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1666553571066675057389821 624957589150003146521183)
          ·
            refine ⟨937436383725004719781775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624957589150003146521183 937436383725004719781775)
            ·
              refine ⟨1406154575587507079672663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937436383725004719781775 1406154575587507079672663)
              ·
                refine ⟨2109231863381260619508995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406154575587507079672663 2109231863381260619508995)
                ·
                  refine ⟨3163847795071890929263493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109231863381260619508995 3163847795071890929263493)
                  ·
                    refine ⟨593221461575979549236905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3163847795071890929263493 593221461575979549236905)
                    ·
                      refine ⟨444916096181984661927679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593221461575979549236905 444916096181984661927679)
                      ·
                        rfl

theorem cell23_866471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_866471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866471 prefixEnd_866471 := by exact prefixLift 866471
  have htrace : WordTrace (prefixWord ++ tailWord_866471) baseStart_866471 baseEnd_866471 := by
    simpa [prefixWord, tailWord_866471, baseEnd_866471] using wordTrace_append hprefix tailTrace_866471
  have hstable : (prefixWord ++ tailWord_866471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866471).length < 2 ^ (prefixWord ++ tailWord_866471).sum := by decide
  have hdescent : baseEnd_866471 < baseStart_866471 := by decide
  rcases family_descends (prefixWord ++ tailWord_866471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866494 : List Nat := [4, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_866494 : Nat := 118140960795 + 866494 * 2 ^ 59
def prefixEnd_866494 : Nat := 4983230072969 + 3 ^ 40 * 866494 * 2
def baseEnd_866494 : Nat := 49436434026337563548897

theorem tailTrace_866494 : CollatzResearch.WordTrace tailWord_866494 prefixEnd_866494 49436434026337563548897 := by
  unfold tailWord_866494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950454065355962279823817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21069088348565132159060357 3950454065355962279823817)
  ·
    refine ⟨2962840549016971709867863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3950454065355962279823817 2962840549016971709867863)
    ·
      refine ⟨4444260823525457564801795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962840549016971709867863 4444260823525457564801795)
      ·
        refine ⟨6666391235288186347202693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444260823525457564801795 6666391235288186347202693)
        ·
          refine ⟨1249948356616534940100505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6666391235288186347202693 1249948356616534940100505)
          ·
            refine ⟨937461267462401205075379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249948356616534940100505 937461267462401205075379)
            ·
              refine ⟨1406191901193601807613069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937461267462401205075379 1406191901193601807613069)
              ·
                refine ⟨527321962947600677854901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406191901193601807613069 527321962947600677854901)
                ·
                  refine ⟨49436434026337563548897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527321962947600677854901 49436434026337563548897)
                  ·
                    rfl

theorem cell23_866494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_866494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866494 prefixEnd_866494 := by exact prefixLift 866494
  have htrace : WordTrace (prefixWord ++ tailWord_866494) baseStart_866494 baseEnd_866494 := by
    simpa [prefixWord, tailWord_866494, baseEnd_866494] using wordTrace_append hprefix tailTrace_866494
  have hstable : (prefixWord ++ tailWord_866494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866494).length < 2 ^ (prefixWord ++ tailWord_866494).sum := by decide
  have hdescent : baseEnd_866494 < baseStart_866494 := by decide
  rcases family_descends (prefixWord ++ tailWord_866494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866510 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_866510 : Nat := 118140960795 + 866510 * 2 ^ 59
def prefixEnd_866510 : Nat := 4983230072969 + 3 ^ 40 * 866510 * 2
def baseEnd_866510 : Nat := 444936121927510009339999

theorem tailTrace_866510 : CollatzResearch.WordTrace tailWord_866510 prefixEnd_866510 444936121927510009339999 := by
  unfold tailWord_866510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950527011348716621396623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21069477393859821980781989 3950527011348716621396623)
  ·
    refine ⟨5925790517023074932094935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3950527011348716621396623 5925790517023074932094935)
    ·
      refine ⟨8888685775534612398142403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5925790517023074932094935 8888685775534612398142403)
      ·
        refine ⟨13333028663301918597213605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8888685775534612398142403 13333028663301918597213605)
        ·
          refine ⟨2499942874369109736977551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13333028663301918597213605 2499942874369109736977551)
          ·
            refine ⟨3749914311553664605466327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499942874369109736977551 3749914311553664605466327)
            ·
              refine ⟨5624871467330496908199491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749914311553664605466327 5624871467330496908199491)
              ·
                refine ⟨8437307200995745362299237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624871467330496908199491 8437307200995745362299237)
                ·
                  refine ⟨1581995100186702255431107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8437307200995745362299237 1581995100186702255431107)
                  ·
                    refine ⟨2372992650280053383146661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1581995100186702255431107 2372992650280053383146661)
                    ·
                      refine ⟨444936121927510009339999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2372992650280053383146661 444936121927510009339999)
                      ·
                        rfl

theorem cell23_866510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_866510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866510 prefixEnd_866510 := by exact prefixLift 866510
  have htrace : WordTrace (prefixWord ++ tailWord_866510) baseStart_866510 baseEnd_866510 := by
    simpa [prefixWord, tailWord_866510, baseEnd_866510] using wordTrace_append hprefix tailTrace_866510
  have hstable : (prefixWord ++ tailWord_866510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866510).length < 2 ^ (prefixWord ++ tailWord_866510).sum := by decide
  have hdescent : baseEnd_866510 < baseStart_866510 := by decide
  rcases family_descends (prefixWord ++ tailWord_866510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866594 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_866594 : Nat := 118140960795 + 866594 * 2 ^ 59
def prefixEnd_866594 : Nat := 4983230072969 + 3 ^ 40 * 866594 * 2
def baseEnd_866594 : Nat := 444979254302487680689613

theorem tailTrace_866594 : CollatzResearch.WordTrace tailWord_866594 prefixEnd_866594 444979254302487680689613 := by
  unfold tailWord_866594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901819955621353829307709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21071519881656943544820557 7901819955621353829307709)
  ·
    refine ⟨2963182483358007685990391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7901819955621353829307709 2963182483358007685990391)
    ·
      refine ⟨4444773725037011528985587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963182483358007685990391 4444773725037011528985587)
      ·
        refine ⟨6667160587555517293478381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444773725037011528985587 6667160587555517293478381)
        ·
          refine ⟨2500185220333318985054393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6667160587555517293478381 2500185220333318985054393)
          ·
            refine ⟨1875138915249989238790795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500185220333318985054393 1875138915249989238790795)
            ·
              refine ⟨2812708372874983858186193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875138915249989238790795 2812708372874983858186193)
              ·
                refine ⟨2109531279656237893639645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812708372874983858186193 2109531279656237893639645)
                ·
                  refine ⟨791074229871089210114867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2109531279656237893639645 791074229871089210114867)
                  ·
                    refine ⟨1186611344806633815172301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791074229871089210114867 1186611344806633815172301)
                    ·
                      refine ⟨444979254302487680689613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1186611344806633815172301 444979254302487680689613)
                      ·
                        rfl

theorem cell23_866594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_866594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866594 prefixEnd_866594 := by exact prefixLift 866594
  have htrace : WordTrace (prefixWord ++ tailWord_866594) baseStart_866594 baseEnd_866594 := by
    simpa [prefixWord, tailWord_866594, baseEnd_866594] using wordTrace_append hprefix tailTrace_866594
  have hstable : (prefixWord ++ tailWord_866594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866594).length < 2 ^ (prefixWord ++ tailWord_866594).sum := by decide
  have hdescent : baseEnd_866594 < baseStart_866594 := by decide
  rcases family_descends (prefixWord ++ tailWord_866594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866620 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_866620 : Nat := 118140960795 + 866620 * 2 ^ 59
def prefixEnd_866620 : Nat := 4983230072969 + 3 ^ 40 * 866620 * 2
def baseEnd_866620 : Nat := 444992604799504578964493

theorem tailTrace_866620 : CollatzResearch.WordTrace tailWord_866620 prefixEnd_866620 444992604799504578964493 := by
  unfold tailWord_866620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15804114060195610878838657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21072152080260814505118209 15804114060195610878838657)
  ·
    refine ⟨11853085545146708159128993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15804114060195610878838657 11853085545146708159128993)
    ·
      refine ⟨8889814158860031119346745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11853085545146708159128993 8889814158860031119346745)
      ·
        refine ⟨6667360619145023339510059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8889814158860031119346745 6667360619145023339510059)
        ·
          refine ⟨10001040928717535009265089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667360619145023339510059 10001040928717535009265089)
          ·
            refine ⟨7500780696538151256948817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10001040928717535009265089 7500780696538151256948817)
            ·
              refine ⟨5625585522403613442711613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500780696538151256948817 5625585522403613442711613)
              ·
                refine ⟨2109594570901355041016855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5625585522403613442711613 2109594570901355041016855)
                ·
                  refine ⟨3164391856352032561525283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2109594570901355041016855 3164391856352032561525283)
                  ·
                    refine ⟨4746587784528048842287925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164391856352032561525283 4746587784528048842287925)
                    ·
                      refine ⟨444992604799504578964493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4746587784528048842287925 444992604799504578964493)
                      ·
                        rfl

theorem cell23_866620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_866620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866620 prefixEnd_866620 := by exact prefixLift 866620
  have htrace : WordTrace (prefixWord ++ tailWord_866620) baseStart_866620 baseEnd_866620 := by
    simpa [prefixWord, tailWord_866620, baseEnd_866620] using wordTrace_append hprefix tailTrace_866620
  have hstable : (prefixWord ++ tailWord_866620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866620).length < 2 ^ (prefixWord ++ tailWord_866620).sum := by decide
  have hdescent : baseEnd_866620 < baseStart_866620 := by decide
  rcases family_descends (prefixWord ++ tailWord_866620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866623 : List Nat := [1, 1, 2, 2, 4, 1, 12]
def baseStart_866623 : Nat := 118140960795 + 866623 * 2 ^ 59
def prefixEnd_866623 : Nat := 4983230072969 + 3 ^ 40 * 866623 * 2
def baseEnd_866623 : Nat := 5493754879524297126259

theorem tailTrace_866623 : CollatzResearch.WordTrace tailWord_866623 prefixEnd_866623 5493754879524297126259 := by
  unfold tailWord_866623
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608337539380353270036523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21072225026253568846691015 31608337539380353270036523)
  ·
    refine ⟨47412506309070529905054785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31608337539380353270036523 47412506309070529905054785)
    ·
      refine ⟨35559379731802897428791089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47412506309070529905054785 35559379731802897428791089)
      ·
        refine ⟨26669534798852173071593317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35559379731802897428791089 26669534798852173071593317)
        ·
          refine ⟨5000537774784782450923747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26669534798852173071593317 5000537774784782450923747)
          ·
            refine ⟨7500806662177173676385621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5000537774784782450923747 7500806662177173676385621)
            ·
              refine ⟨5493754879524297126259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 7500806662177173676385621 5493754879524297126259)
              ·
                rfl

theorem cell23_866623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 12].length) (baseStart_866623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866623 prefixEnd_866623 := by exact prefixLift 866623
  have htrace : WordTrace (prefixWord ++ tailWord_866623) baseStart_866623 baseEnd_866623 := by
    simpa [prefixWord, tailWord_866623, baseEnd_866623] using wordTrace_append hprefix tailTrace_866623
  have hstable : (prefixWord ++ tailWord_866623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866623).length < 2 ^ (prefixWord ++ tailWord_866623).sum := by decide
  have hdescent : baseEnd_866623 < baseStart_866623 := by decide
  rcases family_descends (prefixWord ++ tailWord_866623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866627 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 2, 4]
def baseStart_866627 : Nat := 118140960795 + 866627 * 2 ^ 59
def prefixEnd_866627 : Nat := 4983230072969 + 3 ^ 40 * 866627 * 2
def baseEnd_866627 : Nat := 148332066388028683858987

theorem tailTrace_866627 : CollatzResearch.WordTrace tailWord_866627 prefixEnd_866627 148332066388028683858987 := by
  unfold tailWord_866627
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608483431365861953182135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21072322287577241302121423 31608483431365861953182135)
  ·
    refine ⟨47412725147048792929773203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31608483431365861953182135 47412725147048792929773203)
    ·
      refine ⟨71119087720573189394659805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47412725147048792929773203 71119087720573189394659805)
      ·
        refine ⟨26669657895214946022997427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71119087720573189394659805 26669657895214946022997427)
        ·
          refine ⟨40004486842822419034496141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26669657895214946022997427 40004486842822419034496141)
          ·
            refine ⟨15001682566058407137936053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40004486842822419034496141 15001682566058407137936053)
            ·
              refine ⟨1406407740567975669181505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15001682566058407137936053 1406407740567975669181505)
              ·
                refine ⟨1054805805425981751886129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406407740567975669181505 1054805805425981751886129)
                ·
                  refine ⟨791104354069486313914597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1054805805425981751886129 791104354069486313914597)
                  ·
                    refine ⟨148332066388028683858987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 791104354069486313914597 148332066388028683858987)
                    ·
                      rfl

theorem cell23_866627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 4].length) (baseStart_866627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866627 prefixEnd_866627 := by exact prefixLift 866627
  have htrace : WordTrace (prefixWord ++ tailWord_866627) baseStart_866627 baseEnd_866627 := by
    simpa [prefixWord, tailWord_866627, baseEnd_866627] using wordTrace_append hprefix tailTrace_866627
  have hstable : (prefixWord ++ tailWord_866627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866627).length < 2 ^ (prefixWord ++ tailWord_866627).sum := by decide
  have hdescent : baseEnd_866627 < baseStart_866627 := by decide
  rcases family_descends (prefixWord ++ tailWord_866627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866633 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_866633 : Nat := 118140960795 + 866633 * 2 ^ 59
def prefixEnd_866633 : Nat := 4983230072969 + 3 ^ 40 * 866633 * 2
def baseEnd_866633 : Nat := 444999280048013028101933

theorem tailTrace_866633 : CollatzResearch.WordTrace tailWord_866633 prefixEnd_866633 444999280048013028101933 := by
  unfold tailWord_866633
  simp only [CollatzResearch.WordTrace]
  refine ⟨31608702269344124977900553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21072468179562749985267035 31608702269344124977900553)
  ·
    refine ⟨23706526702008093733425415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31608702269344124977900553 23706526702008093733425415)
    ·
      refine ⟨35559790053012140600138123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23706526702008093733425415 35559790053012140600138123)
      ·
        refine ⟨53339685079518210900207185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35559790053012140600138123 53339685079518210900207185)
        ·
          refine ⟨40004763809638658175155389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53339685079518210900207185 40004763809638658175155389)
          ·
            refine ⟨15001786428614496815683271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40004763809638658175155389 15001786428614496815683271)
            ·
              refine ⟨22502679642921745223524907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15001786428614496815683271 22502679642921745223524907)
              ·
                refine ⟨33754019464382617835287361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22502679642921745223524907 33754019464382617835287361)
                ·
                  refine ⟨25315514598286963376465521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33754019464382617835287361 25315514598286963376465521)
                  ·
                    refine ⟨18986635948715222532349141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25315514598286963376465521 18986635948715222532349141)
                    ·
                      refine ⟨444999280048013028101933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18986635948715222532349141 444999280048013028101933)
                      ·
                        rfl

theorem cell23_866633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_866633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866633 prefixEnd_866633 := by exact prefixLift 866633
  have htrace : WordTrace (prefixWord ++ tailWord_866633) baseStart_866633 baseEnd_866633 := by
    simpa [prefixWord, tailWord_866633, baseEnd_866633] using wordTrace_append hprefix tailTrace_866633
  have hstable : (prefixWord ++ tailWord_866633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866633).length < 2 ^ (prefixWord ++ tailWord_866633).sum := by decide
  have hdescent : baseEnd_866633 < baseStart_866633 := by decide
  rcases family_descends (prefixWord ++ tailWord_866633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866643 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_866643 : Nat := 118140960795 + 866643 * 2 ^ 59
def prefixEnd_866643 : Nat := 4983230072969 + 3 ^ 40 * 866643 * 2
def baseEnd_866643 : Nat := 445004414854557988976887

theorem tailTrace_866643 : CollatzResearch.WordTrace tailWord_866643 prefixEnd_866643 445004414854557988976887 := by
  unfold tailWord_866643
  simp only [CollatzResearch.WordTrace]
  refine ⟨31609066999307896685764583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21072711332871931123843055 31609066999307896685764583)
  ·
    refine ⟨47413600498961845028646875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31609066999307896685764583 47413600498961845028646875)
    ·
      refine ⟨71120400748442767542970313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47413600498961845028646875 71120400748442767542970313)
      ·
        refine ⟨53340300561332075657227735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71120400748442767542970313 53340300561332075657227735)
        ·
          refine ⟨80010450841998113485841603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53340300561332075657227735 80010450841998113485841603)
          ·
            refine ⟨120015676262997170228762405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80010450841998113485841603 120015676262997170228762405)
            ·
              refine ⟨22502939299311969417892951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120015676262997170228762405 22502939299311969417892951)
              ·
                refine ⟨33754408948967954126839427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22502939299311969417892951 33754408948967954126839427)
                ·
                  refine ⟨50631613423451931190259141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33754408948967954126839427 50631613423451931190259141)
                  ·
                    refine ⟨9493427516897237098173589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50631613423451931190259141 9493427516897237098173589)
                    ·
                      refine ⟨445004414854557988976887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9493427516897237098173589 445004414854557988976887)
                      ·
                        rfl

theorem cell23_866643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_866643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866643 prefixEnd_866643 := by exact prefixLift 866643
  have htrace : WordTrace (prefixWord ++ tailWord_866643) baseStart_866643 baseEnd_866643 := by
    simpa [prefixWord, tailWord_866643, baseEnd_866643] using wordTrace_append hprefix tailTrace_866643
  have hstable : (prefixWord ++ tailWord_866643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866643).length < 2 ^ (prefixWord ++ tailWord_866643).sum := by decide
  have hdescent : baseEnd_866643 < baseStart_866643 := by decide
  rcases family_descends (prefixWord ++ tailWord_866643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866724 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_866724 : Nat := 118140960795 + 866724 * 2 ^ 59
def prefixEnd_866724 : Nat := 4983230072969 + 3 ^ 40 * 866724 * 2
def baseEnd_866724 : Nat := 445046006787572172064015

theorem tailTrace_866724 : CollatzResearch.WordTrace tailWord_866724 prefixEnd_866724 445046006787572172064015 := by
  unfold tailWord_866724
  simp only [CollatzResearch.WordTrace]
  refine ⟨15806010656007223759731613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21074680874676298346308817 15806010656007223759731613)
  ·
    refine ⟨5927253996002708909899355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15806010656007223759731613 5927253996002708909899355)
    ·
      refine ⟨8890880994004063364849033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927253996002708909899355 8890880994004063364849033)
      ·
        refine ⟨6668160745503047523636775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8890880994004063364849033 6668160745503047523636775)
        ·
          refine ⟨10002241118254571285455163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668160745503047523636775 10002241118254571285455163)
          ·
            refine ⟨15003361677381856928182745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10002241118254571285455163 15003361677381856928182745)
            ·
              refine ⟨11252521258036392696137059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15003361677381856928182745 11252521258036392696137059)
              ·
                refine ⟨16878781887054589044205589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252521258036392696137059 16878781887054589044205589)
                ·
                  refine ⟨791192900955683861447137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16878781887054589044205589 791192900955683861447137)
                  ·
                    refine ⟨593394675716762896085353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791192900955683861447137 593394675716762896085353)
                    ·
                      refine ⟨445046006787572172064015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593394675716762896085353 445046006787572172064015)
                      ·
                        rfl

theorem cell23_866724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_866724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866724 prefixEnd_866724 := by exact prefixLift 866724
  have htrace : WordTrace (prefixWord ++ tailWord_866724) baseStart_866724 baseEnd_866724 := by
    simpa [prefixWord, tailWord_866724, baseEnd_866724] using wordTrace_append hprefix tailTrace_866724
  have hstable : (prefixWord ++ tailWord_866724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866724).length < 2 ^ (prefixWord ++ tailWord_866724).sum := by decide
  have hdescent : baseEnd_866724 < baseStart_866724 := by decide
  rcases family_descends (prefixWord ++ tailWord_866724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866727 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_866727 : Nat := 118140960795 + 866727 * 2 ^ 59
def prefixEnd_866727 : Nat := 4983230072969 + 3 ^ 40 * 866727 * 2
def baseEnd_866727 : Nat := 445047547229535660326501

theorem tailTrace_866727 : CollatzResearch.WordTrace tailWord_866727 prefixEnd_866727 445047547229535660326501 := by
  unfold tailWord_866727
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612130731003579031822435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074753820669052687881623 31612130731003579031822435)
  ·
    refine ⟨47418196096505368547733653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31612130731003579031822435 47418196096505368547733653)
    ·
      refine ⟨2222727942023689150675015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47418196096505368547733653 2222727942023689150675015)
      ·
        refine ⟨3334091913035533726012523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222727942023689150675015 3334091913035533726012523)
        ·
          refine ⟨5001137869553300589018785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334091913035533726012523 5001137869553300589018785)
          ·
            refine ⟨3750853402164975441764089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5001137869553300589018785 3750853402164975441764089)
            ·
              refine ⟨2813140051623731581323067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3750853402164975441764089 2813140051623731581323067)
              ·
                refine ⟨4219710077435597371984601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813140051623731581323067 4219710077435597371984601)
                ·
                  refine ⟨3164782558076698028988451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4219710077435597371984601 3164782558076698028988451)
                  ·
                    refine ⟨4747173837115047043482677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3164782558076698028988451 4747173837115047043482677)
                    ·
                      refine ⟨445047547229535660326501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4747173837115047043482677 445047547229535660326501)
                      ·
                        rfl

theorem cell23_866727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_866727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866727 prefixEnd_866727 := by exact prefixLift 866727
  have htrace : WordTrace (prefixWord ++ tailWord_866727) baseStart_866727 baseEnd_866727 := by
    simpa [prefixWord, tailWord_866727, baseEnd_866727] using wordTrace_append hprefix tailTrace_866727
  have hstable : (prefixWord ++ tailWord_866727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866727).length < 2 ^ (prefixWord ++ tailWord_866727).sum := by decide
  have hdescent : baseEnd_866727 < baseStart_866727 := by decide
  rcases family_descends (prefixWord ++ tailWord_866727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866767 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 5, 2]
def baseStart_866767 : Nat := 118140960795 + 866767 * 2 ^ 59
def prefixEnd_866767 : Nat := 4983230072969 + 3 ^ 40 * 866767 * 2
def baseEnd_866767 : Nat := 445068086455715503826317

theorem tailTrace_866767 : CollatzResearch.WordTrace tailWord_866767 prefixEnd_866767 445068086455715503826317 := by
  unfold tailWord_866767
  simp only [CollatzResearch.WordTrace]
  refine ⟨31613589650858665863278555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21075726433905777242185703 31613589650858665863278555)
  ·
    refine ⟨47420384476287998794917833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31613589650858665863278555 47420384476287998794917833)
    ·
      refine ⟨35565288357215999096188375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47420384476287998794917833 35565288357215999096188375)
      ·
        refine ⟨53347932535823998644282563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35565288357215999096188375 53347932535823998644282563)
        ·
          refine ⟨80021898803735997966423845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53347932535823998644282563 80021898803735997966423845)
          ·
            refine ⟨15004106025700499618704471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80021898803735997966423845 15004106025700499618704471)
            ·
              refine ⟨22506159038550749428056707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15004106025700499618704471 22506159038550749428056707)
              ·
                refine ⟨33759238557826124142085061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22506159038550749428056707 33759238557826124142085061)
                ·
                  refine ⟨6329857229592398276640949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33759238557826124142085061 6329857229592398276640949)
                  ·
                    refine ⟨593424115274287338435089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6329857229592398276640949 593424115274287338435089)
                    ·
                      refine ⟨445068086455715503826317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593424115274287338435089 445068086455715503826317)
                      ·
                        rfl

theorem cell23_866767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5, 2].length) (baseStart_866767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866767 prefixEnd_866767 := by exact prefixLift 866767
  have htrace : WordTrace (prefixWord ++ tailWord_866767) baseStart_866767 baseEnd_866767 := by
    simpa [prefixWord, tailWord_866767, baseEnd_866767] using wordTrace_append hprefix tailTrace_866767
  have hstable : (prefixWord ++ tailWord_866767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866767).length < 2 ^ (prefixWord ++ tailWord_866767).sum := by decide
  have hdescent : baseEnd_866767 < baseStart_866767 := by decide
  rcases family_descends (prefixWord ++ tailWord_866767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866774 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_866774 : Nat := 118140960795 + 866774 * 2 ^ 59
def prefixEnd_866774 : Nat := 4983230072969 + 3 ^ 40 * 866774 * 2
def baseEnd_866774 : Nat := 445071680820296976438785

theorem tailTrace_866774 : CollatzResearch.WordTrace tailWord_866774 prefixEnd_866774 445071680820296976438785 := by
  unfold tailWord_866774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975865310114581628673961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21075896641222204039188917 1975865310114581628673961)
  ·
    refine ⟨1481898982585936221505471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1975865310114581628673961 1481898982585936221505471)
    ·
      refine ⟨2222848473878904332258207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1481898982585936221505471 2222848473878904332258207)
      ·
        refine ⟨3334272710818356498387311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222848473878904332258207 3334272710818356498387311)
        ·
          refine ⟨5001409066227534747580967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334272710818356498387311 5001409066227534747580967)
          ·
            refine ⟨7502113599341302121371451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001409066227534747580967 7502113599341302121371451)
            ·
              refine ⟨11253170399011953182057177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7502113599341302121371451 11253170399011953182057177)
              ·
                refine ⟨8439877799258964886542883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11253170399011953182057177 8439877799258964886542883)
                ·
                  refine ⟨12659816698888447329814325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8439877799258964886542883 12659816698888447329814325)
                  ·
                    refine ⟨1186857815520791937170093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12659816698888447329814325 1186857815520791937170093)
                    ·
                      refine ⟨445071680820296976438785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1186857815520791937170093 445071680820296976438785)
                      ·
                        rfl

theorem cell23_866774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_866774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866774 prefixEnd_866774 := by exact prefixLift 866774
  have htrace : WordTrace (prefixWord ++ tailWord_866774) baseStart_866774 baseEnd_866774 := by
    simpa [prefixWord, tailWord_866774, baseEnd_866774] using wordTrace_append hprefix tailTrace_866774
  have hstable : (prefixWord ++ tailWord_866774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866774).length < 2 ^ (prefixWord ++ tailWord_866774).sum := by decide
  have hdescent : baseEnd_866774 < baseStart_866774 := by decide
  rcases family_descends (prefixWord ++ tailWord_866774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866867 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 3, 5]
def baseStart_866867 : Nat := 118140960795 + 866867 * 2 ^ 59
def prefixEnd_866867 : Nat := 4983230072969 + 3 ^ 40 * 866867 * 2
def baseEnd_866867 : Nat := 148373144840388370858619

theorem tailTrace_866867 : CollatzResearch.WordTrace tailWord_866867 prefixEnd_866867 148373144840388370858619 := by
  unfold tailWord_866867
  simp only [CollatzResearch.WordTrace]
  refine ⟨31617236950496382941918855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21078157966997588627945903 31617236950496382941918855)
  ·
    refine ⟨47425855425744574412878283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31617236950496382941918855 47425855425744574412878283)
    ·
      refine ⟨71138783138616861619317425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47425855425744574412878283 71138783138616861619317425)
      ·
        refine ⟨53354087353962646214488069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71138783138616861619317425 53354087353962646214488069)
        ·
          refine ⟨10003891378867996165216513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53354087353962646214488069 10003891378867996165216513)
          ·
            refine ⟨7502918534150997123912385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10003891378867996165216513 7502918534150997123912385)
            ·
              refine ⟨5627188900613247842934289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7502918534150997123912385 5627188900613247842934289)
              ·
                refine ⟨4220391675459935882200717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627188900613247842934289 4220391675459935882200717)
                ·
                  refine ⟨1582646878297475955825269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4220391675459935882200717 1582646878297475955825269)
                  ·
                    refine ⟨148373144840388370858619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1582646878297475955825269 148373144840388370858619)
                    ·
                      rfl

theorem cell23_866867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 5].length) (baseStart_866867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866867 prefixEnd_866867 := by exact prefixLift 866867
  have htrace : WordTrace (prefixWord ++ tailWord_866867) baseStart_866867 baseEnd_866867 := by
    simpa [prefixWord, tailWord_866867, baseEnd_866867] using wordTrace_append hprefix tailTrace_866867
  have hstable : (prefixWord ++ tailWord_866867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866867).length < 2 ^ (prefixWord ++ tailWord_866867).sum := by decide
  have hdescent : baseEnd_866867 < baseStart_866867 := by decide
  rcases family_descends (prefixWord ++ tailWord_866867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866897 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_866897 : Nat := 118140960795 + 866897 * 2 ^ 59
def prefixEnd_866897 : Nat := 4983230072969 + 3 ^ 40 * 866897 * 2
def baseEnd_866897 : Nat := 148378279646933331733573

theorem tailTrace_866897 : CollatzResearch.WordTrace tailWord_866897 prefixEnd_866897 148378279646933331733573 := by
  unfold tailWord_866897
  simp only [CollatzResearch.WordTrace]
  refine ⟨31618331140387698065510945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21078887426925132043673963 31618331140387698065510945)
  ·
    refine ⟨23713748355290773549133209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31618331140387698065510945 23713748355290773549133209)
    ·
      refine ⟨17785311266468080161849907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23713748355290773549133209 17785311266468080161849907)
      ·
        refine ⟨26677966899702120242774861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17785311266468080161849907 26677966899702120242774861)
        ·
          refine ⟨10004237587388295091040573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26677966899702120242774861 10004237587388295091040573)
          ·
            refine ⟨3751589095270610659140215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10004237587388295091040573 3751589095270610659140215)
            ·
              refine ⟨5627383642905915988710323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3751589095270610659140215 5627383642905915988710323)
              ·
                refine ⟨8441075464358873983065485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5627383642905915988710323 8441075464358873983065485)
                ·
                  refine ⟨3165403299134577743649557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8441075464358873983065485 3165403299134577743649557)
                  ·
                    refine ⟨148378279646933331733573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3165403299134577743649557 148378279646933331733573)
                    ·
                      rfl

theorem cell23_866897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_866897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866897 prefixEnd_866897 := by exact prefixLift 866897
  have htrace : WordTrace (prefixWord ++ tailWord_866897) baseStart_866897 baseEnd_866897 := by
    simpa [prefixWord, tailWord_866897, baseEnd_866897] using wordTrace_append hprefix tailTrace_866897
  have hstable : (prefixWord ++ tailWord_866897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866897).length < 2 ^ (prefixWord ++ tailWord_866897).sum := by decide
  have hdescent : baseEnd_866897 < baseStart_866897 := by decide
  rcases family_descends (prefixWord ++ tailWord_866897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866898 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_866898 : Nat := 118140960795 + 866898 * 2 ^ 59
def prefixEnd_866898 : Nat := 4983230072969 + 3 ^ 40 * 866898 * 2
def baseEnd_866898 : Nat := 445135352421454491288215

theorem tailTrace_866898 : CollatzResearch.WordTrace tailWord_866898 prefixEnd_866898 445135352421454491288215 := by
  unfold tailWord_866898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904591903346018809074337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21078911742256050157531565 7904591903346018809074337)
  ·
    refine ⟨5928443927509514106805753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7904591903346018809074337 5928443927509514106805753)
    ·
      refine ⟨4446332945632135580104315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5928443927509514106805753 4446332945632135580104315)
      ·
        refine ⟨6669499418448203370156473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446332945632135580104315 6669499418448203370156473)
        ·
          refine ⟨5002124563836152527617355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6669499418448203370156473 5002124563836152527617355)
          ·
            refine ⟨7503186845754228791426033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002124563836152527617355 7503186845754228791426033)
            ·
              refine ⟨5627390134315671593569525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7503186845754228791426033 5627390134315671593569525)
              ·
                refine ⟨527567825092094211897143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5627390134315671593569525 527567825092094211897143)
                ·
                  refine ⟨791351737638141317845715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527567825092094211897143 791351737638141317845715)
                  ·
                    refine ⟨1187027606457211976768573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791351737638141317845715 1187027606457211976768573)
                    ·
                      refine ⟨445135352421454491288215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187027606457211976768573 445135352421454491288215)
                      ·
                        rfl

theorem cell23_866898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_866898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866898 prefixEnd_866898 := by exact prefixLift 866898
  have htrace : WordTrace (prefixWord ++ tailWord_866898) baseStart_866898 baseEnd_866898 := by
    simpa [prefixWord, tailWord_866898, baseEnd_866898] using wordTrace_append hprefix tailTrace_866898
  have hstable : (prefixWord ++ tailWord_866898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866898).length < 2 ^ (prefixWord ++ tailWord_866898).sum := by decide
  have hdescent : baseEnd_866898 < baseStart_866898 := by decide
  rcases family_descends (prefixWord ++ tailWord_866898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866904 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_866904 : Nat := 118140960795 + 866904 * 2 ^ 59
def prefixEnd_866904 : Nat := 4983230072969 + 3 ^ 40 * 866904 * 2
def baseEnd_866904 : Nat := 445138433305381467813187

theorem tailTrace_866904 : CollatzResearch.WordTrace tailWord_866904 prefixEnd_866904 445138433305381467813187 := by
  unfold tailWord_866904
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809293225681169130507883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21079057634241558840677177 15809293225681169130507883)
  ·
    refine ⟨23713939838521753695761825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15809293225681169130507883 23713939838521753695761825)
    ·
      refine ⟨17785454878891315271821369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23713939838521753695761825 17785454878891315271821369)
      ·
        refine ⟨13339091159168486453866027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17785454878891315271821369 13339091159168486453866027)
        ·
          refine ⟨20008636738752729680799041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13339091159168486453866027 20008636738752729680799041)
          ·
            refine ⟨15006477554064547260599281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20008636738752729680799041 15006477554064547260599281)
            ·
              refine ⟨11254858165548410445449461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15006477554064547260599281 11254858165548410445449461)
              ·
                refine ⟨1055142953020163479260887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11254858165548410445449461 1055142953020163479260887)
                ·
                  refine ⟨1582714429530245218891331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1055142953020163479260887 1582714429530245218891331)
                  ·
                    refine ⟨2374071644295367828336997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1582714429530245218891331 2374071644295367828336997)
                    ·
                      refine ⟨445138433305381467813187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2374071644295367828336997 445138433305381467813187)
                      ·
                        rfl

theorem cell23_866904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_866904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866904 prefixEnd_866904 := by exact prefixLift 866904
  have htrace : WordTrace (prefixWord ++ tailWord_866904) baseStart_866904 baseEnd_866904 := by
    simpa [prefixWord, tailWord_866904, baseEnd_866904] using wordTrace_append hprefix tailTrace_866904
  have hstable : (prefixWord ++ tailWord_866904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866904).length < 2 ^ (prefixWord ++ tailWord_866904).sum := by decide
  have hdescent : baseEnd_866904 < baseStart_866904 := by decide
  rcases family_descends (prefixWord ++ tailWord_866904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866921 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 3, 2, 2]
def baseStart_866921 : Nat := 118140960795 + 866921 * 2 ^ 59
def prefixEnd_866921 : Nat := 4983230072969 + 3 ^ 40 * 866921 * 2
def baseEnd_866921 : Nat := 445147162476507901300609

theorem tailTrace_866921 : CollatzResearch.WordTrace tailWord_866921 prefixEnd_866921 445147162476507901300609 := by
  unfold tailWord_866921
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619206492300750164384617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21079470994867166776256411 31619206492300750164384617)
  ·
    refine ⟨23714404869225562623288463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31619206492300750164384617 23714404869225562623288463)
    ·
      refine ⟨35571607303838343934932695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23714404869225562623288463 35571607303838343934932695)
      ·
        refine ⟨53357410955757515902399043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35571607303838343934932695 53357410955757515902399043)
        ·
          refine ⟨80036116433636273853598565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53357410955757515902399043 80036116433636273853598565)
          ·
            refine ⟨15006771831306801347549731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80036116433636273853598565 15006771831306801347549731)
            ·
              refine ⟨22510157746960202021324597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15006771831306801347549731 22510157746960202021324597)
              ·
                refine ⟨2110327288777518939499181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22510157746960202021324597 2110327288777518939499181)
                ·
                  refine ⟨791372733291569602312193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2110327288777518939499181 791372733291569602312193)
                  ·
                    refine ⟨593529549968677201734145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791372733291569602312193 593529549968677201734145)
                    ·
                      refine ⟨445147162476507901300609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593529549968677201734145 445147162476507901300609)
                      ·
                        rfl

theorem cell23_866921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2, 2].length) (baseStart_866921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866921 prefixEnd_866921 := by exact prefixLift 866921
  have htrace : WordTrace (prefixWord ++ tailWord_866921) baseStart_866921 baseEnd_866921 := by
    simpa [prefixWord, tailWord_866921, baseEnd_866921] using wordTrace_append hprefix tailTrace_866921
  have hstable : (prefixWord ++ tailWord_866921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866921).length < 2 ^ (prefixWord ++ tailWord_866921).sum := by decide
  have hdescent : baseEnd_866921 < baseStart_866921 := by decide
  rcases family_descends (prefixWord ++ tailWord_866921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866924 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_866924 : Nat := 118140960795 + 866924 * 2 ^ 59
def prefixEnd_866924 : Nat := 4983230072969 + 3 ^ 40 * 866924 * 2
def baseEnd_866924 : Nat := 445148702918471389563095

theorem tailTrace_866924 : CollatzResearch.WordTrace tailWord_866924 prefixEnd_866924 445148702918471389563095 := by
  unfold tailWord_866924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809657955644940838371913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21079543940859921117829217 15809657955644940838371913)
  ·
    refine ⟨11857243466733705628778935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15809657955644940838371913 11857243466733705628778935)
    ·
      refine ⟨17785865200100558443168403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11857243466733705628778935 17785865200100558443168403)
      ·
        refine ⟨26678797800150837664752605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17785865200100558443168403 26678797800150837664752605)
        ·
          refine ⟨10004549175056564124282227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26678797800150837664752605 10004549175056564124282227)
          ·
            refine ⟨15006823762584846186423341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004549175056564124282227 15006823762584846186423341)
            ·
              refine ⟨5627558910969317319908753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15006823762584846186423341 5627558910969317319908753)
              ·
                refine ⟨4220669183226987989931565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5627558910969317319908753 4220669183226987989931565)
                ·
                  refine ⟨1582750943710120496224337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4220669183226987989931565 1582750943710120496224337)
                  ·
                    refine ⟨1187063207782590372168253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1582750943710120496224337 1187063207782590372168253)
                    ·
                      refine ⟨445148702918471389563095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187063207782590372168253 445148702918471389563095)
                      ·
                        rfl

theorem cell23_866924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_866924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866924 prefixEnd_866924 := by exact prefixLift 866924
  have htrace : WordTrace (prefixWord ++ tailWord_866924) baseStart_866924 baseEnd_866924 := by
    simpa [prefixWord, tailWord_866924, baseEnd_866924] using wordTrace_append hprefix tailTrace_866924
  have hstable : (prefixWord ++ tailWord_866924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866924).length < 2 ^ (prefixWord ++ tailWord_866924).sum := by decide
  have hdescent : baseEnd_866924 < baseStart_866924 := by decide
  rcases family_descends (prefixWord ++ tailWord_866924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866927 : List Nat := [1, 1, 2, 1, 3, 2, 5, 8]
def baseStart_866927 : Nat := 118140960795 + 866927 * 2 ^ 59
def prefixEnd_866927 : Nat := 4983230072969 + 3 ^ 40 * 866927 * 2
def baseEnd_866927 : Nat := 16487046050386476956503

theorem tailTrace_866927 : CollatzResearch.WordTrace tailWord_866927 prefixEnd_866927 16487046050386476956503 := by
  unfold tailWord_866927
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619425330279013189103035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21079616886852675459402023 31619425330279013189103035)
  ·
    refine ⟨47429137995418519783654553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31619425330279013189103035 47429137995418519783654553)
    ·
      refine ⟨35571853496563889837740915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47429137995418519783654553 35571853496563889837740915)
      ·
        refine ⟨53357780244845834756611373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35571853496563889837740915 53357780244845834756611373)
        ·
          refine ⟨20009167591817188033729265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53357780244845834756611373 20009167591817188033729265)
          ·
            refine ⟨15006875693862891025296949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20009167591817188033729265 15006875693862891025296949)
            ·
              refine ⟨1406894596299646033621589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15006875693862891025296949 1406894596299646033621589)
              ·
                refine ⟨16487046050386476956503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1406894596299646033621589 16487046050386476956503)
                ·
                  rfl

theorem cell23_866927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 8].length) (baseStart_866927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866927 prefixEnd_866927 := by exact prefixLift 866927
  have htrace : WordTrace (prefixWord ++ tailWord_866927) baseStart_866927 baseEnd_866927 := by
    simpa [prefixWord, tailWord_866927, baseEnd_866927] using wordTrace_append hprefix tailTrace_866927
  have hstable : (prefixWord ++ tailWord_866927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866927).length < 2 ^ (prefixWord ++ tailWord_866927).sum := by decide
  have hdescent : baseEnd_866927 < baseStart_866927 := by decide
  rcases family_descends (prefixWord ++ tailWord_866927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866944 : List Nat := [2, 1, 1, 2, 1, 6, 3, 7]
def baseStart_866944 : Nat := 118140960795 + 866944 * 2 ^ 59
def prefixEnd_866944 : Nat := 4983230072969 + 3 ^ 40 * 866944 * 2
def baseEnd_866944 : Nat := 16487369353020789307889

theorem tailTrace_866944 : CollatzResearch.WordTrace tailWord_866944 prefixEnd_866944 16487369353020789307889 := by
  unfold tailWord_866944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810022685608712546235943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21080030247478283394981257 15810022685608712546235943)
  ·
    refine ⟨23715034028413068819353915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15810022685608712546235943 23715034028413068819353915)
    ·
      refine ⟨35572551042619603229030873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23715034028413068819353915 35572551042619603229030873)
      ·
        refine ⟨26679413281964702421773155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35572551042619603229030873 26679413281964702421773155)
        ·
          refine ⟨40019119922947053632659733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26679413281964702421773155 40019119922947053632659733)
          ·
            refine ⟨1875896246388143139030925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40019119922947053632659733 1875896246388143139030925)
            ·
              refine ⟨703461092395553677136597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1875896246388143139030925 703461092395553677136597)
              ·
                refine ⟨16487369353020789307889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 703461092395553677136597 16487369353020789307889)
                ·
                  rfl

theorem cell23_866944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 7].length) (baseStart_866944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_866944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_866944 prefixEnd_866944 := by exact prefixLift 866944
  have htrace : WordTrace (prefixWord ++ tailWord_866944) baseStart_866944 baseEnd_866944 := by
    simpa [prefixWord, tailWord_866944, baseEnd_866944] using wordTrace_append hprefix tailTrace_866944
  have hstable : (prefixWord ++ tailWord_866944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866944).length < 2 ^ (prefixWord ++ tailWord_866944).sum := by decide
  have hdescent : baseEnd_866944 < baseStart_866944 := by decide
  rcases family_descends (prefixWord ++ tailWord_866944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867045 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_867045 : Nat := 118140960795 + 867045 * 2 ^ 59
def prefixEnd_867045 : Nat := 4983230072969 + 3 ^ 40 * 867045 * 2
def baseEnd_867045 : Nat := 445210834077665416150039

theorem tailTrace_867045 : CollatzResearch.WordTrace tailWord_867045 prefixEnd_867045 445210834077665416150039 := by
  unfold tailWord_867045
  simp only [CollatzResearch.WordTrace]
  refine ⟨31623729143851519341898589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21082486095901012894599059 31623729143851519341898589)
  ·
    refine ⟨11858898428944319753211971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31623729143851519341898589 11858898428944319753211971)
    ·
      refine ⟨17788347643416479629817957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858898428944319753211971 17788347643416479629817957)
      ·
        refine ⟨3335315183140589930590867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17788347643416479629817957 3335315183140589930590867)
        ·
          refine ⟨5002972774710884895886301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335315183140589930590867 5002972774710884895886301)
          ·
            refine ⟨1876114790516581835957363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5002972774710884895886301 1876114790516581835957363)
            ·
              refine ⟨2814172185774872753936045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876114790516581835957363 2814172185774872753936045)
              ·
                refine ⟨1055314569665577282726017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814172185774872753936045 1055314569665577282726017)
                ·
                  refine ⟨791485927249182962044513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055314569665577282726017 791485927249182962044513)
                  ·
                    refine ⟨593614445436887221533385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791485927249182962044513 593614445436887221533385)
                    ·
                      refine ⟨445210834077665416150039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593614445436887221533385 445210834077665416150039)
                      ·
                        rfl

theorem cell23_867045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_867045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867045 prefixEnd_867045 := by exact prefixLift 867045
  have htrace : WordTrace (prefixWord ++ tailWord_867045) baseStart_867045 baseEnd_867045 := by
    simpa [prefixWord, tailWord_867045, baseEnd_867045] using wordTrace_append hprefix tailTrace_867045
  have hstable : (prefixWord ++ tailWord_867045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867045).length < 2 ^ (prefixWord ++ tailWord_867045).sum := by decide
  have hdescent : baseEnd_867045 < baseStart_867045 := by decide
  rcases family_descends (prefixWord ++ tailWord_867045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867084 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_867084 : Nat := 118140960795 + 867084 * 2 ^ 59
def prefixEnd_867084 : Nat := 4983230072969 + 3 ^ 40 * 867084 * 2
def baseEnd_867084 : Nat := 445230859823190763562359

theorem tailTrace_867084 : CollatzResearch.WordTrace tailWord_867084 prefixEnd_867084 445230859823190763562359 := by
  unfold tailWord_867084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15812575795355114501284153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21083434393806819335045537 15812575795355114501284153)
  ·
    refine ⟨11859431846516335875963115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15812575795355114501284153 11859431846516335875963115)
    ·
      refine ⟨17789147769774503813944673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11859431846516335875963115 17789147769774503813944673)
      ·
        refine ⟨13341860827330877860458505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17789147769774503813944673 13341860827330877860458505)
        ·
          refine ⟨10006395620498158395343879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341860827330877860458505 10006395620498158395343879)
          ·
            refine ⟨15009593430747237593015819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006395620498158395343879 15009593430747237593015819)
            ·
              refine ⟨22514390146120856389523729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009593430747237593015819 22514390146120856389523729)
              ·
                refine ⟨16885792609590642292142797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22514390146120856389523729 16885792609590642292142797)
                ·
                  refine ⟨6332172228596490859553549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16885792609590642292142797 6332172228596490859553549)
                  ·
                    refine ⟨2374564585723684072332581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6332172228596490859553549 2374564585723684072332581)
                    ·
                      refine ⟨445230859823190763562359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2374564585723684072332581 445230859823190763562359)
                      ·
                        rfl

theorem cell23_867084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_867084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867084 prefixEnd_867084 := by exact prefixLift 867084
  have htrace : WordTrace (prefixWord ++ tailWord_867084) baseStart_867084 baseEnd_867084 := by
    simpa [prefixWord, tailWord_867084, baseEnd_867084] using wordTrace_append hprefix tailTrace_867084
  have hstable : (prefixWord ++ tailWord_867084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867084).length < 2 ^ (prefixWord ++ tailWord_867084).sum := by decide
  have hdescent : baseEnd_867084 < baseStart_867084 := by decide
  rcases family_descends (prefixWord ++ tailWord_867084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867118 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_867118 : Nat := 118140960795 + 867118 * 2 ^ 59
def prefixEnd_867118 : Nat := 4983230072969 + 3 ^ 40 * 867118 * 2
def baseEnd_867118 : Nat := 445248318165443630537203

theorem tailTrace_867118 : CollatzResearch.WordTrace tailWord_867118 prefixEnd_867118 445248318165443630537203 := by
  unfold tailWord_867118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953298959073381601163251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21084261115058035206204005 3953298959073381601163251)
  ·
    refine ⟨5929948438610072401744877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3953298959073381601163251 5929948438610072401744877)
    ·
      refine ⟨2223730664478777150654329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5929948438610072401744877 2223730664478777150654329)
      ·
        refine ⟨1667797998359082862990747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2223730664478777150654329 1667797998359082862990747)
        ·
          refine ⟨2501696997538624294486121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667797998359082862990747 2501696997538624294486121)
          ·
            refine ⟨1876272748153968220864591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501696997538624294486121 1876272748153968220864591)
            ·
              refine ⟨2814409122230952331296887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876272748153968220864591 2814409122230952331296887)
              ·
                refine ⟨4221613683346428496945331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814409122230952331296887 4221613683346428496945331)
                ·
                  refine ⟨6332420525019642745417997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221613683346428496945331 6332420525019642745417997)
                  ·
                    refine ⟨2374657696882366029531749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6332420525019642745417997 2374657696882366029531749)
                    ·
                      refine ⟨445248318165443630537203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2374657696882366029531749 445248318165443630537203)
                      ·
                        rfl

theorem cell23_867118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_867118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867118 prefixEnd_867118 := by exact prefixLift 867118
  have htrace : WordTrace (prefixWord ++ tailWord_867118) baseStart_867118 baseEnd_867118 := by
    simpa [prefixWord, tailWord_867118, baseEnd_867118] using wordTrace_append hprefix tailTrace_867118
  have hstable : (prefixWord ++ tailWord_867118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867118).length < 2 ^ (prefixWord ++ tailWord_867118).sum := by decide
  have hdescent : baseEnd_867118 < baseStart_867118 := by decide
  rcases family_descends (prefixWord ++ tailWord_867118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867121 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_867121 : Nat := 118140960795 + 867121 * 2 ^ 59
def prefixEnd_867121 : Nat := 4983230072969 + 3 ^ 40 * 867121 * 2
def baseEnd_867121 : Nat := 445249858607407118799689

theorem tailTrace_867121 : CollatzResearch.WordTrace tailWord_867121 prefixEnd_867121 445249858607407118799689 := by
  unfold tailWord_867121
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626501091576184321665217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21084334061050789547776811 31626501091576184321665217)
  ·
    refine ⟨23719875818682138241248913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31626501091576184321665217 23719875818682138241248913)
    ·
      refine ⟨17789906864011603680936685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23719875818682138241248913 17789906864011603680936685)
      ·
        refine ⟨6671215074004351380351257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17789906864011603680936685 6671215074004351380351257)
        ·
          refine ⟨5003411305503263535263443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6671215074004351380351257 5003411305503263535263443)
          ·
            refine ⟨7505116958254895302895165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003411305503263535263443 7505116958254895302895165)
            ·
              refine ⟨2814418859345585738585687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7505116958254895302895165 2814418859345585738585687)
              ·
                refine ⟨4221628289018378607878531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814418859345585738585687 4221628289018378607878531)
                ·
                  refine ⟨6332442433527567911817797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221628289018378607878531 6332442433527567911817797)
                  ·
                    refine ⟨1187332956286418983465837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332442433527567911817797 1187332956286418983465837)
                    ·
                      refine ⟨445249858607407118799689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187332956286418983465837 445249858607407118799689)
                      ·
                        rfl

theorem cell23_867121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_867121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867121 prefixEnd_867121 := by exact prefixLift 867121
  have htrace : WordTrace (prefixWord ++ tailWord_867121) baseStart_867121 baseEnd_867121 := by
    simpa [prefixWord, tailWord_867121, baseEnd_867121] using wordTrace_append hprefix tailTrace_867121
  have hstable : (prefixWord ++ tailWord_867121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867121).length < 2 ^ (prefixWord ++ tailWord_867121).sum := by decide
  have hdescent : baseEnd_867121 < baseStart_867121 := by decide
  rcases family_descends (prefixWord ++ tailWord_867121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867144 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_867144 : Nat := 118140960795 + 867144 * 2 ^ 59
def prefixEnd_867144 : Nat := 4983230072969 + 3 ^ 40 * 867144 * 2
def baseEnd_867144 : Nat := 445261668662460528812083

theorem tailTrace_867144 : CollatzResearch.WordTrace tailWord_867144 prefixEnd_867144 445261668662460528812083 := by
  unfold tailWord_867144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813669985246429624876243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21084893313661906166501657 15813669985246429624876243)
  ·
    refine ⟨23720504977869644437314365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15813669985246429624876243 23720504977869644437314365)
    ·
      refine ⟨8895189366701116663992887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23720504977869644437314365 8895189366701116663992887)
      ·
        refine ⟨13342784050051674995989331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895189366701116663992887 13342784050051674995989331)
        ·
          refine ⟨20014176075077512493983997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13342784050051674995989331 20014176075077512493983997)
          ·
            refine ⟨7505316028154067185243999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20014176075077512493983997 7505316028154067185243999)
            ·
              refine ⟨11257974042231100777865999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505316028154067185243999 11257974042231100777865999)
              ·
                refine ⟨16886961063346651166798999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257974042231100777865999 16886961063346651166798999)
                ·
                  refine ⟨25330441595019976750198499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16886961063346651166798999 25330441595019976750198499)
                  ·
                    refine ⟨37995662392529965125297749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25330441595019976750198499 37995662392529965125297749)
                    ·
                      refine ⟨445261668662460528812083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 37995662392529965125297749 445261668662460528812083)
                      ·
                        rfl

theorem cell23_867144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_867144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867144 prefixEnd_867144 := by exact prefixLift 867144
  have htrace : WordTrace (prefixWord ++ tailWord_867144) baseStart_867144 baseEnd_867144 := by
    simpa [prefixWord, tailWord_867144, baseEnd_867144] using wordTrace_append hprefix tailTrace_867144
  have hstable : (prefixWord ++ tailWord_867144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867144).length < 2 ^ (prefixWord ++ tailWord_867144).sum := by decide
  have hdescent : baseEnd_867144 < baseStart_867144 := by decide
  rcases family_descends (prefixWord ++ tailWord_867144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867168 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3]
def baseStart_867168 : Nat := 118140960795 + 867168 * 2 ^ 59
def prefixEnd_867168 : Nat := 4983230072969 + 3 ^ 40 * 867168 * 2
def baseEnd_867168 : Nat := 445273992198168434911973

theorem tailTrace_867168 : CollatzResearch.WordTrace tailWord_867168 prefixEnd_867168 445273992198168434911973 := by
  unfold tailWord_867168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814107661202955674313079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21085476881603940899084105 15814107661202955674313079)
  ·
    refine ⟨23721161491804433511469619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814107661202955674313079 23721161491804433511469619)
    ·
      refine ⟨35581742237706650267204429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721161491804433511469619 35581742237706650267204429)
      ·
        refine ⟨13343153339139993850201661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35581742237706650267204429 13343153339139993850201661)
        ·
          refine ⟨5003682502177497693825623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13343153339139993850201661 5003682502177497693825623)
          ·
            refine ⟨7505523753266246540738435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003682502177497693825623 7505523753266246540738435)
            ·
              refine ⟨11258285629899369811107653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505523753266246540738435 11258285629899369811107653)
              ·
                refine ⟨2110928555606131839582685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11258285629899369811107653 2110928555606131839582685)
                ·
                  refine ⟨791598208352299439843507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2110928555606131839582685 791598208352299439843507)
                  ·
                    refine ⟨1187397312528449159765261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791598208352299439843507 1187397312528449159765261)
                    ·
                      refine ⟨445273992198168434911973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187397312528449159765261 445273992198168434911973)
                      ·
                        rfl

theorem cell23_867168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_867168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867168 prefixEnd_867168 := by exact prefixLift 867168
  have htrace : WordTrace (prefixWord ++ tailWord_867168) baseStart_867168 baseEnd_867168 := by
    simpa [prefixWord, tailWord_867168, baseEnd_867168] using wordTrace_append hprefix tailTrace_867168
  have hstable : (prefixWord ++ tailWord_867168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867168).length < 2 ^ (prefixWord ++ tailWord_867168).sum := by decide
  have hdescent : baseEnd_867168 < baseStart_867168 := by decide
  rcases family_descends (prefixWord ++ tailWord_867168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867211 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5]
def baseStart_867211 : Nat := 118140960795 + 867211 * 2 ^ 59
def prefixEnd_867211 : Nat := 4983230072969 + 3 ^ 40 * 867211 * 2
def baseEnd_867211 : Nat := 445296071866311766674275

theorem tailTrace_867211 : CollatzResearch.WordTrace tailWord_867211 prefixEnd_867211 445296071866311766674275 := by
  unfold tailWord_867211
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629783661250129692441487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21086522440833419794960991 31629783661250129692441487)
  ·
    refine ⟨47444675491875194538662231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31629783661250129692441487 47444675491875194538662231)
    ·
      refine ⟨71167013237812791807993347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47444675491875194538662231 71167013237812791807993347)
      ·
        refine ⟨106750519856719187711990021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71167013237812791807993347 106750519856719187711990021)
        ·
          refine ⟨20015722473134847695998129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106750519856719187711990021 20015722473134847695998129)
          ·
            refine ⟨15011791854851135771998597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20015722473134847695998129 15011791854851135771998597)
            ·
              refine ⟨2814710972784587957249737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15011791854851135771998597 2814710972784587957249737)
              ·
                refine ⟨2111033229588440967937303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814710972784587957249737 2111033229588440967937303)
                ·
                  refine ⟨3166549844382661451905955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111033229588440967937303 3166549844382661451905955)
                  ·
                    refine ⟨4749824766573992177858933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3166549844382661451905955 4749824766573992177858933)
                    ·
                      refine ⟨445296071866311766674275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4749824766573992177858933 445296071866311766674275)
                      ·
                        rfl

theorem cell23_867211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_867211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867211 prefixEnd_867211 := by exact prefixLift 867211
  have htrace : WordTrace (prefixWord ++ tailWord_867211) baseStart_867211 baseEnd_867211 := by
    simpa [prefixWord, tailWord_867211, baseEnd_867211] using wordTrace_append hprefix tailTrace_867211
  have hstable : (prefixWord ++ tailWord_867211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867211).length < 2 ^ (prefixWord ++ tailWord_867211).sum := by decide
  have hdescent : baseEnd_867211 < baseStart_867211 := by decide
  rcases family_descends (prefixWord ++ tailWord_867211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867221 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_867221 : Nat := 118140960795 + 867221 * 2 ^ 59
def prefixEnd_867221 : Nat := 4983230072969 + 3 ^ 40 * 867221 * 2
def baseEnd_867221 : Nat := 445301206672856727549229

theorem tailTrace_867221 : CollatzResearch.WordTrace tailWord_867221 prefixEnd_867221 445301206672856727549229 := by
  unfold tailWord_867221
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630148391213901400305517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21086765594142600933537011 31630148391213901400305517)
  ·
    refine ⟨11861305646705213025114569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31630148391213901400305517 11861305646705213025114569)
    ·
      refine ⟨8895979235028909768835927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11861305646705213025114569 8895979235028909768835927)
      ·
        refine ⟨13343968852543364653253891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895979235028909768835927 13343968852543364653253891)
        ·
          refine ⟨20015953278815046979880837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343968852543364653253891 20015953278815046979880837)
          ·
            refine ⟨3752991239777821308727657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20015953278815046979880837 3752991239777821308727657)
            ·
              refine ⟨2814743429833365981545743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752991239777821308727657 2814743429833365981545743)
              ·
                refine ⟨4222115144750048972318615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814743429833365981545743 4222115144750048972318615)
                ·
                  refine ⟨6333172717125073458477923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222115144750048972318615 6333172717125073458477923)
                  ·
                    refine ⟨9499759075687610187716885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6333172717125073458477923 9499759075687610187716885)
                    ·
                      refine ⟨445301206672856727549229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9499759075687610187716885 445301206672856727549229)
                      ·
                        rfl

theorem cell23_867221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_867221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867221 prefixEnd_867221 := by exact prefixLift 867221
  have htrace : WordTrace (prefixWord ++ tailWord_867221) baseStart_867221 baseEnd_867221 := by
    simpa [prefixWord, tailWord_867221, baseEnd_867221] using wordTrace_append hprefix tailTrace_867221
  have hstable : (prefixWord ++ tailWord_867221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867221).length < 2 ^ (prefixWord ++ tailWord_867221).sum := by decide
  have hdescent : baseEnd_867221 < baseStart_867221 := by decide
  rcases family_descends (prefixWord ++ tailWord_867221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867222 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_867222 : Nat := 118140960795 + 867222 * 2 ^ 59
def prefixEnd_867222 : Nat := 4983230072969 + 3 ^ 40 * 867222 * 2
def baseEnd_867222 : Nat := 148433906717837074545575

theorem tailTrace_867222 : CollatzResearch.WordTrace tailWord_867222 prefixEnd_867222 148433906717837074545575 := by
  unfold tailWord_867222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976886554013142410693245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21086789909473519047394613 1976886554013142410693245)
  ·
    refine ⟨741332457754928404009967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1976886554013142410693245 741332457754928404009967)
    ·
      refine ⟨1111998686632392606014951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741332457754928404009967 1111998686632392606014951)
      ·
        refine ⟨1667998029948588909022427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111998686632392606014951 1667998029948588909022427)
        ·
          refine ⟨2501997044922883363533641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667998029948588909022427 2501997044922883363533641)
          ·
            refine ⟨1876497783692162522650231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501997044922883363533641 1876497783692162522650231)
            ·
              refine ⟨2814746675538243783975347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876497783692162522650231 2814746675538243783975347)
              ·
                refine ⟨4222120013307365675963021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814746675538243783975347 4222120013307365675963021)
                ·
                  refine ⟨1583295004990262128486133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4222120013307365675963021 1583295004990262128486133)
                  ·
                    refine ⟨148433906717837074545575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1583295004990262128486133 148433906717837074545575)
                    ·
                      rfl

theorem cell23_867222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_867222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867222 prefixEnd_867222 := by exact prefixLift 867222
  have htrace : WordTrace (prefixWord ++ tailWord_867222) baseStart_867222 baseEnd_867222 := by
    simpa [prefixWord, tailWord_867222, baseEnd_867222] using wordTrace_append hprefix tailTrace_867222
  have hstable : (prefixWord ++ tailWord_867222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867222).length < 2 ^ (prefixWord ++ tailWord_867222).sum := by decide
  have hdescent : baseEnd_867222 < baseStart_867222 := by decide
  rcases family_descends (prefixWord ++ tailWord_867222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867231 : List Nat := [1, 1, 2, 5, 2, 1, 2, 9]
def baseStart_867231 : Nat := 118140960795 + 867231 * 2 ^ 59
def prefixEnd_867231 : Nat := 4983230072969 + 3 ^ 40 * 867231 * 2
def baseEnd_867231 : Nat := 16492827462200062534229

theorem tailTrace_867231 : CollatzResearch.WordTrace tailWord_867231 prefixEnd_867231 16492827462200062534229 := by
  unfold tailWord_867231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630513121177673108169547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21087008747451782072113031 31630513121177673108169547)
  ·
    refine ⟨47445769681766509662254321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31630513121177673108169547 47445769681766509662254321)
    ·
      refine ⟨35584327261324882246690741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47445769681766509662254321 35584327261324882246690741)
      ·
        refine ⟨3336030680749207710627257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35584327261324882246690741 3336030680749207710627257)
        ·
          refine ⟨2502023010561905782970443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336030680749207710627257 2502023010561905782970443)
          ·
            refine ⟨3753034515842858674455665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502023010561905782970443 3753034515842858674455665)
            ·
              refine ⟨2814775886882144005841749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753034515842858674455665 2814775886882144005841749)
              ·
                refine ⟨16492827462200062534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2814775886882144005841749 16492827462200062534229)
                ·
                  rfl

theorem cell23_867231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 9].length) (baseStart_867231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867231 prefixEnd_867231 := by exact prefixLift 867231
  have htrace : WordTrace (prefixWord ++ tailWord_867231) baseStart_867231 baseEnd_867231 := by
    simpa [prefixWord, tailWord_867231, baseEnd_867231] using wordTrace_append hprefix tailTrace_867231
  have hstable : (prefixWord ++ tailWord_867231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867231).length < 2 ^ (prefixWord ++ tailWord_867231).sum := by decide
  have hdescent : baseEnd_867231 < baseStart_867231 := by decide
  rcases family_descends (prefixWord ++ tailWord_867231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867252 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_867252 : Nat := 118140960795 + 867252 * 2 ^ 59
def prefixEnd_867252 : Nat := 4983230072969 + 3 ^ 40 * 867252 * 2
def baseEnd_867252 : Nat := 148439041524382035420529

theorem tailTrace_867252 : CollatzResearch.WordTrace tailWord_867252 prefixEnd_867252 148439041524382035420529 := by
  unfold tailWord_867252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815639527050796847342005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21087519369401062463122673 15815639527050796847342005)
  ·
    refine ⟨1482716205661012204438313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15815639527050796847342005 1482716205661012204438313)
    ·
      refine ⟨1112037154245759153328735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1482716205661012204438313 1112037154245759153328735)
      ·
        refine ⟨1668055731368638729993103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112037154245759153328735 1668055731368638729993103)
        ·
          refine ⟨2502083597052958094989655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668055731368638729993103 2502083597052958094989655)
          ·
            refine ⟨3753125395579437142484483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502083597052958094989655 3753125395579437142484483)
            ·
              refine ⟨5629688093369155713726725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753125395579437142484483 5629688093369155713726725)
              ·
                refine ⟨1055566517506716696323761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5629688093369155713726725 1055566517506716696323761)
                ·
                  refine ⟨791674888130037522242821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055566517506716696323761 791674888130037522242821)
                  ·
                    refine ⟨148439041524382035420529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 791674888130037522242821 148439041524382035420529)
                    ·
                      rfl

theorem cell23_867252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_867252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867252 prefixEnd_867252 := by exact prefixLift 867252
  have htrace : WordTrace (prefixWord ++ tailWord_867252) baseStart_867252 baseEnd_867252 := by
    simpa [prefixWord, tailWord_867252, baseEnd_867252] using wordTrace_append hprefix tailTrace_867252
  have hstable : (prefixWord ++ tailWord_867252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867252).length < 2 ^ (prefixWord ++ tailWord_867252).sum := by decide
  have hdescent : baseEnd_867252 < baseStart_867252 := by decide
  rcases family_descends (prefixWord ++ tailWord_867252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867275 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 3]
def baseStart_867275 : Nat := 118140960795 + 867275 * 2 ^ 59
def prefixEnd_867275 : Nat := 4983230072969 + 3 ^ 40 * 867275 * 2
def baseEnd_867275 : Nat := 445328934628199516273981

theorem tailTrace_867275 : CollatzResearch.WordTrace tailWord_867275 prefixEnd_867275 445328934628199516273981 := by
  unfold tailWord_867275
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632117933018268622771279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21088078622012179081847519 31632117933018268622771279)
  ·
    refine ⟨47448176899527402934156919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31632117933018268622771279 47448176899527402934156919)
    ·
      refine ⟨71172265349291104401235379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47448176899527402934156919 71172265349291104401235379)
      ·
        refine ⟨106758398023936656601853069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71172265349291104401235379 106758398023936656601853069)
        ·
          refine ⟨40034399258976246225694901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106758398023936656601853069 40034399258976246225694901)
          ·
            refine ⟨3753224930529023083658897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40034399258976246225694901 3753224930529023083658897)
            ·
              refine ⟨2814918697896767312744173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753224930529023083658897 2814918697896767312744173)
              ·
                refine ⟨1055594511711287742279065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814918697896767312744173 1055594511711287742279065)
                ·
                  refine ⟨791695883783465806709299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055594511711287742279065 791695883783465806709299)
                  ·
                    refine ⟨1187543825675198710063949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791695883783465806709299 1187543825675198710063949)
                    ·
                      refine ⟨445328934628199516273981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187543825675198710063949 445328934628199516273981)
                      ·
                        rfl

theorem cell23_867275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 3].length) (baseStart_867275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867275 prefixEnd_867275 := by exact prefixLift 867275
  have htrace : WordTrace (prefixWord ++ tailWord_867275) baseStart_867275 baseEnd_867275 := by
    simpa [prefixWord, tailWord_867275, baseEnd_867275] using wordTrace_append hprefix tailTrace_867275
  have hstable : (prefixWord ++ tailWord_867275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867275).length < 2 ^ (prefixWord ++ tailWord_867275).sum := by decide
  have hdescent : baseEnd_867275 < baseStart_867275 := by decide
  rcases family_descends (prefixWord ++ tailWord_867275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867281 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_867281 : Nat := 118140960795 + 867281 * 2 ^ 59
def prefixEnd_867281 : Nat := 4983230072969 + 3 ^ 40 * 867281 * 2
def baseEnd_867281 : Nat := 445332015512126492798953

theorem tailTrace_867281 : CollatzResearch.WordTrace tailWord_867281 prefixEnd_867281 445332015512126492798953 := by
  unfold tailWord_867281
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632336770996531647489697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21088224513997687764993131 31632336770996531647489697)
  ·
    refine ⟨23724252578247398735617273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31632336770996531647489697 23724252578247398735617273)
    ·
      refine ⟨17793189433685549051712955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23724252578247398735617273 17793189433685549051712955)
      ·
        refine ⟨26689784150528323577569433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17793189433685549051712955 26689784150528323577569433)
        ·
          refine ⟨20017338112896242683177075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26689784150528323577569433 20017338112896242683177075)
          ·
            refine ⟨30026007169344364024765613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20017338112896242683177075 30026007169344364024765613)
            ·
              refine ⟨11259752688504136509287105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30026007169344364024765613 11259752688504136509287105)
              ·
                refine ⟨8444814516378102381965329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11259752688504136509287105 8444814516378102381965329)
                ·
                  refine ⟨6333610887283576786473997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8444814516378102381965329 6333610887283576786473997)
                  ·
                    refine ⟨2375104082731341294927749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6333610887283576786473997 2375104082731341294927749)
                    ·
                      refine ⟨445332015512126492798953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2375104082731341294927749 445332015512126492798953)
                      ·
                        rfl

theorem cell23_867281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_867281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867281 prefixEnd_867281 := by exact prefixLift 867281
  have htrace : WordTrace (prefixWord ++ tailWord_867281) baseStart_867281 baseEnd_867281 := by
    simpa [prefixWord, tailWord_867281, baseEnd_867281] using wordTrace_append hprefix tailTrace_867281
  have hstable : (prefixWord ++ tailWord_867281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867281).length < 2 ^ (prefixWord ++ tailWord_867281).sum := by decide
  have hdescent : baseEnd_867281 < baseStart_867281 := by decide
  rcases family_descends (prefixWord ++ tailWord_867281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867326 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_867326 : Nat := 118140960795 + 867326 * 2 ^ 59
def prefixEnd_867326 : Nat := 4983230072969 + 3 ^ 40 * 867326 * 2
def baseEnd_867326 : Nat := 445355122141578816736247

theorem tailTrace_867326 : CollatzResearch.WordTrace tailWord_867326 prefixEnd_867326 445355122141578816736247 := by
  unfold tailWord_867326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954247256979188041609729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21089318703889002888585221 3954247256979188041609729)
  ·
    refine ⟨2965685442734391031207297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3954247256979188041609729 2965685442734391031207297)
    ·
      refine ⟨2224264082050793273405473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2965685442734391031207297 2224264082050793273405473)
      ·
        refine ⟨1668198061538094955054105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224264082050793273405473 1668198061538094955054105)
        ·
          refine ⟨1251148546153571216290579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668198061538094955054105 1251148546153571216290579)
          ·
            refine ⟨1876722819230356824435869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251148546153571216290579 1876722819230356824435869)
            ·
              refine ⟨703771057211383809163451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1876722819230356824435869 703771057211383809163451)
              ·
                refine ⟨1055656585817075713745177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703771057211383809163451 1055656585817075713745177)
                ·
                  refine ⟨791742439362806785308883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1055656585817075713745177 791742439362806785308883)
                  ·
                    refine ⟨1187613659044210177963325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791742439362806785308883 1187613659044210177963325)
                    ·
                      refine ⟨445355122141578816736247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187613659044210177963325 445355122141578816736247)
                      ·
                        rfl

theorem cell23_867326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_867326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867326 prefixEnd_867326 := by exact prefixLift 867326
  have htrace : WordTrace (prefixWord ++ tailWord_867326) baseStart_867326 baseEnd_867326 := by
    simpa [prefixWord, tailWord_867326, baseEnd_867326] using wordTrace_append hprefix tailTrace_867326
  have hstable : (prefixWord ++ tailWord_867326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867326).length < 2 ^ (prefixWord ++ tailWord_867326).sum := by decide
  have hdescent : baseEnd_867326 < baseStart_867326 := by decide
  rcases family_descends (prefixWord ++ tailWord_867326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867338 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_867338 : Nat := 118140960795 + 867338 * 2 ^ 59
def prefixEnd_867338 : Nat := 4983230072969 + 3 ^ 40 * 867338 * 2
def baseEnd_867338 : Nat := 49484587101048085531799

theorem tailTrace_867338 : CollatzResearch.WordTrace tailWord_867338 prefixEnd_867338 49484587101048085531799 := by
  unfold tailWord_867338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908603932947507595578667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21089610487860020254876445 7908603932947507595578667)
  ·
    refine ⟨11862905899421261393368001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908603932947507595578667 11862905899421261393368001)
    ·
      refine ⟨8897179424565946045026001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11862905899421261393368001 8897179424565946045026001)
      ·
        refine ⟨6672884568424459533769501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8897179424565946045026001 6672884568424459533769501)
        ·
          refine ⟨2502331713159172325163563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6672884568424459533769501 2502331713159172325163563)
          ·
            refine ⟨3753497569738758487745345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502331713159172325163563 3753497569738758487745345)
            ·
              refine ⟨2815123177304068865809009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753497569738758487745345 2815123177304068865809009)
              ·
                refine ⟨2111342382978051649356757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815123177304068865809009 2111342382978051649356757)
                ·
                  refine ⟨49484587101048085531799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2111342382978051649356757 49484587101048085531799)
                  ·
                    rfl

theorem cell23_867338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_867338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867338 prefixEnd_867338 := by exact prefixLift 867338
  have htrace : WordTrace (prefixWord ++ tailWord_867338) baseStart_867338 baseEnd_867338 := by
    simpa [prefixWord, tailWord_867338, baseEnd_867338] using wordTrace_append hprefix tailTrace_867338
  have hstable : (prefixWord ++ tailWord_867338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867338).length < 2 ^ (prefixWord ++ tailWord_867338).sum := by decide
  have hdescent : baseEnd_867338 < baseStart_867338 := by decide
  rcases family_descends (prefixWord ++ tailWord_867338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867378 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_867378 : Nat := 118140960795 + 867378 * 2 ^ 59
def prefixEnd_867378 : Nat := 4983230072969 + 3 ^ 40 * 867378 * 2
def baseEnd_867378 : Nat := 445381823135612613286007

theorem tailTrace_867378 : CollatzResearch.WordTrace tailWord_867378 prefixEnd_867378 445381823135612613286007 := by
  unfold tailWord_867378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908968662911279303442697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21090583101096744809180525 7908968662911279303442697)
  ·
    refine ⟨5931726497183459477582023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7908968662911279303442697 5931726497183459477582023)
    ·
      refine ⟨8897589745775189216373035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5931726497183459477582023 8897589745775189216373035)
      ·
        refine ⟨13346384618662783824559553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897589745775189216373035 13346384618662783824559553)
        ·
          refine ⟨10009788463997087868419665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13346384618662783824559553 10009788463997087868419665)
          ·
            refine ⟨7507341347997815901314749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10009788463997087868419665 7507341347997815901314749)
            ·
              refine ⟨2815253005499180962993031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7507341347997815901314749 2815253005499180962993031)
              ·
                refine ⟨4222879508248771444489547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815253005499180962993031 4222879508248771444489547)
                ·
                  refine ⟨6334319262373157166734321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222879508248771444489547 6334319262373157166734321)
                  ·
                    refine ⟨4750739446779867875050741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6334319262373157166734321 4750739446779867875050741)
                    ·
                      refine ⟨445381823135612613286007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4750739446779867875050741 445381823135612613286007)
                      ·
                        rfl

theorem cell23_867378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_867378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867378 prefixEnd_867378 := by exact prefixLift 867378
  have htrace : WordTrace (prefixWord ++ tailWord_867378) baseStart_867378 baseEnd_867378 := by
    simpa [prefixWord, tailWord_867378, baseEnd_867378] using wordTrace_append hprefix tailTrace_867378
  have hstable : (prefixWord ++ tailWord_867378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867378).length < 2 ^ (prefixWord ++ tailWord_867378).sum := by decide
  have hdescent : baseEnd_867378 < baseStart_867378 := by decide
  rcases family_descends (prefixWord ++ tailWord_867378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867408 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_867408 : Nat := 118140960795 + 867408 * 2 ^ 59
def prefixEnd_867408 : Nat := 4983230072969 + 3 ^ 40 * 867408 * 2
def baseEnd_867408 : Nat := 445397227555247495910869

theorem tailTrace_867408 : CollatzResearch.WordTrace tailWord_867408 prefixEnd_867408 445397227555247495910869 := by
  unfold tailWord_867408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818484420768216168681439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21091312561024288224908585 15818484420768216168681439)
  ·
    refine ⟨23727726631152324253022159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15818484420768216168681439 23727726631152324253022159)
    ·
      refine ⟨35591589946728486379533239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23727726631152324253022159 35591589946728486379533239)
      ·
        refine ⟨53387384920092729569299859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35591589946728486379533239 53387384920092729569299859)
        ·
          refine ⟨80081077380139094353949789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53387384920092729569299859 80081077380139094353949789)
          ·
            refine ⟨30030404017552160382731171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80081077380139094353949789 30030404017552160382731171)
            ·
              refine ⟨45045606026328240574096757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30030404017552160382731171 45045606026328240574096757)
              ·
                refine ⟨4223025564968272553821571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45045606026328240574096757 4223025564968272553821571)
                ·
                  refine ⟨6334538347452408830732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223025564968272553821571 6334538347452408830732357)
                  ·
                    refine ⟨1187725940147326655762317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334538347452408830732357 1187725940147326655762317)
                    ·
                      refine ⟨445397227555247495910869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187725940147326655762317 445397227555247495910869)
                      ·
                        rfl

theorem cell23_867408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_867408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867408 prefixEnd_867408 := by exact prefixLift 867408
  have htrace : WordTrace (prefixWord ++ tailWord_867408) baseStart_867408 baseEnd_867408 := by
    simpa [prefixWord, tailWord_867408, baseEnd_867408] using wordTrace_append hprefix tailTrace_867408
  have hstable : (prefixWord ++ tailWord_867408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867408).length < 2 ^ (prefixWord ++ tailWord_867408).sum := by decide
  have hdescent : baseEnd_867408 < baseStart_867408 := by decide
  rcases family_descends (prefixWord ++ tailWord_867408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867425 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_867425 : Nat := 118140960795 + 867425 * 2 ^ 59
def prefixEnd_867425 : Nat := 4983230072969 + 3 ^ 40 * 867425 * 2
def baseEnd_867425 : Nat := 445405956726373929398291

theorem tailTrace_867425 : CollatzResearch.WordTrace tailWord_867425 prefixEnd_867425 445405956726373929398291 := by
  unfold tailWord_867425
  simp only [CollatzResearch.WordTrace]
  refine ⟨31637588882474844240731729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21091725921649896160487819 31637588882474844240731729)
  ·
    refine ⟨23728191661856133180548797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31637588882474844240731729 23728191661856133180548797)
    ·
      refine ⟨8898071873196049942705799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23728191661856133180548797 8898071873196049942705799)
      ·
        refine ⟨13347107809794074914058699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898071873196049942705799 13347107809794074914058699)
        ·
          refine ⟨20020661714691112371088049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347107809794074914058699 20020661714691112371088049)
          ·
            refine ⟨15015496286018334278316037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20020661714691112371088049 15015496286018334278316037)
            ·
              refine ⟨2815405553628437677184257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15015496286018334278316037 2815405553628437677184257)
              ·
                refine ⟨2111554165221328257888193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815405553628437677184257 2111554165221328257888193)
                ·
                  refine ⟨1583665623915996193416145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111554165221328257888193 1583665623915996193416145)
                  ·
                    refine ⟨1187749217936997145062109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1583665623915996193416145 1187749217936997145062109)
                    ·
                      refine ⟨445405956726373929398291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187749217936997145062109 445405956726373929398291)
                      ·
                        rfl

theorem cell23_867425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_867425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867425 prefixEnd_867425 := by exact prefixLift 867425
  have htrace : WordTrace (prefixWord ++ tailWord_867425) baseStart_867425 baseEnd_867425 := by
    simpa [prefixWord, tailWord_867425, baseEnd_867425] using wordTrace_append hprefix tailTrace_867425
  have hstable : (prefixWord ++ tailWord_867425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867425).length < 2 ^ (prefixWord ++ tailWord_867425).sum := by decide
  have hdescent : baseEnd_867425 < baseStart_867425 := by decide
  rcases family_descends (prefixWord ++ tailWord_867425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867489 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_867489 : Nat := 118140960795 + 867489 * 2 ^ 59
def prefixEnd_867489 : Nat := 4983230072969 + 3 ^ 40 * 867489 * 2
def baseEnd_867489 : Nat := 445438819488261678997997

theorem tailTrace_867489 : CollatzResearch.WordTrace tailWord_867489 prefixEnd_867489 445438819488261678997997 := by
  unfold tailWord_867489
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639923154242983171061521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21093282102828655447374347 31639923154242983171061521)
  ·
    refine ⟨23729942365682237378296141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31639923154242983171061521 23729942365682237378296141)
    ·
      refine ⟨8898728387130839016861053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23729942365682237378296141 8898728387130839016861053)
      ·
        refine ⟨3337023145174064631322895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8898728387130839016861053 3337023145174064631322895)
        ·
          refine ⟨5005534717761096946984343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337023145174064631322895 5005534717761096946984343)
          ·
            refine ⟨7508302076641645420476515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005534717761096946984343 7508302076641645420476515)
            ·
              refine ⟨11262453114962468130714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508302076641645420476515 11262453114962468130714773)
              ·
                refine ⟨527927489763865693627255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11262453114962468130714773 527927489763865693627255)
                ·
                  refine ⟨791891234645798540440883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527927489763865693627255 791891234645798540440883)
                  ·
                    refine ⟨1187836851968697810661325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791891234645798540440883 1187836851968697810661325)
                    ·
                      refine ⟨445438819488261678997997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187836851968697810661325 445438819488261678997997)
                      ·
                        rfl

theorem cell23_867489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_867489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867489 prefixEnd_867489 := by exact prefixLift 867489
  have htrace : WordTrace (prefixWord ++ tailWord_867489) baseStart_867489 baseEnd_867489 := by
    simpa [prefixWord, tailWord_867489, baseEnd_867489] using wordTrace_append hprefix tailTrace_867489
  have hstable : (prefixWord ++ tailWord_867489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867489).length < 2 ^ (prefixWord ++ tailWord_867489).sum := by decide
  have hdescent : baseEnd_867489 < baseStart_867489 := by decide
  rcases family_descends (prefixWord ++ tailWord_867489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867512 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_867512 : Nat := 118140960795 + 867512 * 2 ^ 59
def prefixEnd_867512 : Nat := 4983230072969 + 3 ^ 40 * 867512 * 2
def baseEnd_867512 : Nat := 445450629543315089010391

theorem tailTrace_867512 : CollatzResearch.WordTrace tailWord_867512 prefixEnd_867512 445450629543315089010391 := by
  unfold tailWord_867512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820381016579829049574395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21093841355439772066099193 15820381016579829049574395)
  ·
    refine ⟨23730571524869743574361593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15820381016579829049574395 23730571524869743574361593)
    ·
      refine ⟨17797928643652307680771195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23730571524869743574361593 17797928643652307680771195)
      ·
        refine ⟨26696892965478461521156793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17797928643652307680771195 26696892965478461521156793)
        ·
          refine ⟨20022669724108846140867595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26696892965478461521156793 20022669724108846140867595)
          ·
            refine ⟨30034004586163269211301393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20022669724108846140867595 30034004586163269211301393)
            ·
              refine ⟨22525503439622451908476045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30034004586163269211301393 22525503439622451908476045)
              ·
                refine ⟨8447063789858419465678517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22525503439622451908476045 8447063789858419465678517)
                ·
                  refine ⟨791912230299226824907361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8447063789858419465678517 791912230299226824907361)
                  ·
                    refine ⟨593934172724420118680521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 791912230299226824907361 593934172724420118680521)
                    ·
                      refine ⟨445450629543315089010391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593934172724420118680521 445450629543315089010391)
                      ·
                        rfl

theorem cell23_867512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_867512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867512 prefixEnd_867512 := by exact prefixLift 867512
  have htrace : WordTrace (prefixWord ++ tailWord_867512) baseStart_867512 baseEnd_867512 := by
    simpa [prefixWord, tailWord_867512, baseEnd_867512] using wordTrace_append hprefix tailTrace_867512
  have hstable : (prefixWord ++ tailWord_867512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867512).length < 2 ^ (prefixWord ++ tailWord_867512).sum := by decide
  have hdescent : baseEnd_867512 < baseStart_867512 := by decide
  rcases family_descends (prefixWord ++ tailWord_867512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867533 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_867533 : Nat := 118140960795 + 867533 * 2 ^ 59
def prefixEnd_867533 : Nat := 4983230072969 + 3 ^ 40 * 867533 * 2
def baseEnd_867533 : Nat := 445461412637059506847795

theorem tailTrace_867533 : CollatzResearch.WordTrace tailWord_867533 prefixEnd_867533 445461412637059506847795 := by
  unfold tailWord_867533
  simp only [CollatzResearch.WordTrace]
  refine ⟨31641527966083578685663253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21094351977389052457108835 31641527966083578685663253)
  ·
    refine ⟨1483196623410167750890465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31641527966083578685663253 1483196623410167750890465)
    ·
      refine ⟨1112397467557625813167849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1483196623410167750890465 1112397467557625813167849)
      ·
        refine ⟨834298100668219359875887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112397467557625813167849 834298100668219359875887)
        ·
          refine ⟨1251447151002329039813831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834298100668219359875887 1251447151002329039813831)
          ·
            refine ⟨1877170726503493559720747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251447151002329039813831 1877170726503493559720747)
            ·
              refine ⟨2815756089755240339581121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877170726503493559720747 2815756089755240339581121)
              ·
                refine ⟨2111817067316430254685841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815756089755240339581121 2111817067316430254685841)
                ·
                  refine ⟨1583862800487322691014381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111817067316430254685841 1583862800487322691014381)
                  ·
                    refine ⟨593948550182746009130393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1583862800487322691014381 593948550182746009130393)
                    ·
                      refine ⟨445461412637059506847795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 593948550182746009130393 445461412637059506847795)
                      ·
                        rfl

theorem cell23_867533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_867533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867533 prefixEnd_867533 := by exact prefixLift 867533
  have htrace : WordTrace (prefixWord ++ tailWord_867533) baseStart_867533 baseEnd_867533 := by
    simpa [prefixWord, tailWord_867533, baseEnd_867533] using wordTrace_append hprefix tailTrace_867533
  have hstable : (prefixWord ++ tailWord_867533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867533).length < 2 ^ (prefixWord ++ tailWord_867533).sum := by decide
  have hdescent : baseEnd_867533 < baseStart_867533 := by decide
  rcases family_descends (prefixWord ++ tailWord_867533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867540 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_867540 : Nat := 118140960795 + 867540 * 2 ^ 59
def prefixEnd_867540 : Nat := 4983230072969 + 3 ^ 40 * 867540 * 2
def baseEnd_867540 : Nat := 445465007001640979460263

theorem tailTrace_867540 : CollatzResearch.WordTrace tailWord_867540 prefixEnd_867540 445465007001640979460263 := by
  unfold tailWord_867540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820891638529109440584037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21094522184705479254112049 15820891638529109440584037)
  ·
    refine ⟨2966417182224208020109507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15820891638529109440584037 2966417182224208020109507)
    ·
      refine ⟨4449625773336312030164261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966417182224208020109507 4449625773336312030164261)
      ·
        refine ⟨834304832500558505655799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4449625773336312030164261 834304832500558505655799)
        ·
          refine ⟨1251457248750837758483699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834304832500558505655799 1251457248750837758483699)
          ·
            refine ⟨1877185873126256637725549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251457248750837758483699 1877185873126256637725549)
            ·
              refine ⟨703944702422346239147081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877185873126256637725549 703944702422346239147081)
              ·
                refine ⟨527958526816759679360311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703944702422346239147081 527958526816759679360311)
                ·
                  refine ⟨791937790225139519040467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 527958526816759679360311 791937790225139519040467)
                  ·
                    refine ⟨1187906685337709278560701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 791937790225139519040467 1187906685337709278560701)
                    ·
                      refine ⟨445465007001640979460263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1187906685337709278560701 445465007001640979460263)
                      ·
                        rfl

theorem cell23_867540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_867540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867540 prefixEnd_867540 := by exact prefixLift 867540
  have htrace : WordTrace (prefixWord ++ tailWord_867540) baseStart_867540 baseEnd_867540 := by
    simpa [prefixWord, tailWord_867540, baseEnd_867540] using wordTrace_append hprefix tailTrace_867540
  have hstable : (prefixWord ++ tailWord_867540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867540).length < 2 ^ (prefixWord ++ tailWord_867540).sum := by decide
  have hdescent : baseEnd_867540 < baseStart_867540 := by decide
  rcases family_descends (prefixWord ++ tailWord_867540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867568 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_867568 : Nat := 118140960795 + 867568 * 2 ^ 59
def prefixEnd_867568 : Nat := 4983230072969 + 3 ^ 40 * 867568 * 2
def baseEnd_867568 : Nat := 445479384459966869910133

theorem tailTrace_867568 : CollatzResearch.WordTrace tailWord_867568 prefixEnd_867568 445479384459966869910133 := by
  unfold tailWord_867568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821402260478389831593679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21095203013971186442124905 15821402260478389831593679)
  ·
    refine ⟨23732103390717584747390519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15821402260478389831593679 23732103390717584747390519)
    ·
      refine ⟨35598155086076377121085779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23732103390717584747390519 35598155086076377121085779)
      ·
        refine ⟨53397232629114565681628669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35598155086076377121085779 53397232629114565681628669)
        ·
          refine ⟨20023962235917962130610751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53397232629114565681628669 20023962235917962130610751)
          ·
            refine ⟨30035943353876943195916127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20023962235917962130610751 30035943353876943195916127)
            ·
              refine ⟨45053915030815414793874191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30035943353876943195916127 45053915030815414793874191)
              ·
                refine ⟨67580872546223122190811287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45053915030815414793874191 67580872546223122190811287)
                ·
                  refine ⟨101371308819334683286216931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67580872546223122190811287 101371308819334683286216931)
                  ·
                    refine ⟨152056963229002024929325397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101371308819334683286216931 152056963229002024929325397)
                    ·
                      refine ⟨445479384459966869910133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 152056963229002024929325397 445479384459966869910133)
                      ·
                        rfl

theorem cell23_867568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_867568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867568 prefixEnd_867568 := by exact prefixLift 867568
  have htrace : WordTrace (prefixWord ++ tailWord_867568) baseStart_867568 baseEnd_867568 := by
    simpa [prefixWord, tailWord_867568, baseEnd_867568] using wordTrace_append hprefix tailTrace_867568
  have hstable : (prefixWord ++ tailWord_867568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867568).length < 2 ^ (prefixWord ++ tailWord_867568).sum := by decide
  have hdescent : baseEnd_867568 < baseStart_867568 := by decide
  rcases family_descends (prefixWord ++ tailWord_867568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867619 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 1, 4, 2]
def baseStart_867619 : Nat := 118140960795 + 867619 * 2 ^ 59
def prefixEnd_867619 : Nat := 4983230072969 + 3 ^ 40 * 867619 * 2
def baseEnd_867619 : Nat := 445505571973346170372399

theorem tailTrace_867619 : CollatzResearch.WordTrace tailWord_867619 prefixEnd_867619 445505571973346170372399 := by
  unfold tailWord_867619
  simp only [CollatzResearch.WordTrace]
  refine ⟨31644664643772015373293911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21096443095848010248862607 31644664643772015373293911)
  ·
    refine ⟨47466996965658023059940867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31644664643772015373293911 47466996965658023059940867)
    ·
      refine ⟨71200495448487034589911301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47466996965658023059940867 71200495448487034589911301)
      ·
        refine ⟨13350092896591318985608369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71200495448487034589911301 13350092896591318985608369)
        ·
          refine ⟨10012569672443489239206277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13350092896591318985608369 10012569672443489239206277)
          ·
            refine ⟨1877356813583154232351177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10012569672443489239206277 1877356813583154232351177)
            ·
              refine ⟨1408017610187365674263383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877356813583154232351177 1408017610187365674263383)
              ·
                refine ⟨2112026415281048511395075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408017610187365674263383 2112026415281048511395075)
                ·
                  refine ⟨3168039622921572767092613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112026415281048511395075 3168039622921572767092613)
                  ·
                    refine ⟨594007429297794893829865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3168039622921572767092613 594007429297794893829865)
                    ·
                      refine ⟨445505571973346170372399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594007429297794893829865 445505571973346170372399)
                      ·
                        rfl

theorem cell23_867619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_867619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867619 prefixEnd_867619 := by exact prefixLift 867619
  have htrace : WordTrace (prefixWord ++ tailWord_867619) baseStart_867619 baseEnd_867619 := by
    simpa [prefixWord, tailWord_867619, baseEnd_867619] using wordTrace_append hprefix tailTrace_867619
  have hstable : (prefixWord ++ tailWord_867619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867619).length < 2 ^ (prefixWord ++ tailWord_867619).sum := by decide
  have hdescent : baseEnd_867619 < baseStart_867619 := by decide
  rcases family_descends (prefixWord ++ tailWord_867619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867636 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_867636 : Nat := 118140960795 + 867636 * 2 ^ 59
def prefixEnd_867636 : Nat := 4983230072969 + 3 ^ 40 * 867636 * 2
def baseEnd_867636 : Nat := 445514301144472603859821

theorem tailTrace_867636 : CollatzResearch.WordTrace tailWord_867636 prefixEnd_867636 445514301144472603859821 := by
  unfold tailWord_867636
  simp only [CollatzResearch.WordTrace]
  refine ⟨15822642342355213638331381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21096856456473618184441841 15822642342355213638331381)
  ·
    refine ⟨1483372719595801278593567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15822642342355213638331381 1483372719595801278593567)
    ·
      refine ⟨2225059079393701917890351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483372719595801278593567 2225059079393701917890351)
      ·
        refine ⟨3337588619090552876835527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225059079393701917890351 3337588619090552876835527)
        ·
          refine ⟨5006382928635829315253291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337588619090552876835527 5006382928635829315253291)
          ·
            refine ⟨7509574392953743972879937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006382928635829315253291 7509574392953743972879937)
            ·
              refine ⟨5632180794715307979659953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7509574392953743972879937 5632180794715307979659953)
              ·
                refine ⟨4224135596036480984744965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632180794715307979659953 4224135596036480984744965)
                ·
                  refine ⟨792025424256840184639681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4224135596036480984744965 792025424256840184639681)
                  ·
                    refine ⟨594019068192630138479761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792025424256840184639681 594019068192630138479761)
                    ·
                      refine ⟨445514301144472603859821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594019068192630138479761 445514301144472603859821)
                      ·
                        rfl

theorem cell23_867636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_867636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867636 prefixEnd_867636 := by exact prefixLift 867636
  have htrace : WordTrace (prefixWord ++ tailWord_867636) baseStart_867636 baseEnd_867636 := by
    simpa [prefixWord, tailWord_867636, baseEnd_867636] using wordTrace_append hprefix tailTrace_867636
  have hstable : (prefixWord ++ tailWord_867636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867636).length < 2 ^ (prefixWord ++ tailWord_867636).sum := by decide
  have hdescent : baseEnd_867636 < baseStart_867636 := by decide
  rcases family_descends (prefixWord ++ tailWord_867636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867665 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_867665 : Nat := 118140960795 + 867665 * 2 ^ 59
def prefixEnd_867665 : Nat := 4983230072969 + 3 ^ 40 * 867665 * 2
def baseEnd_867665 : Nat := 445529192083452990397187

theorem tailTrace_867665 : CollatzResearch.WordTrace tailWord_867665 prefixEnd_867665 445529192083452990397187 := by
  unfold tailWord_867665
  simp only [CollatzResearch.WordTrace]
  refine ⟨31646342401605365229468449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21097561601070243486312299 31646342401605365229468449)
  ·
    refine ⟨23734756801204023922101337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31646342401605365229468449 23734756801204023922101337)
    ·
      refine ⟨17801067600903017941576003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23734756801204023922101337 17801067600903017941576003)
      ·
        refine ⟨26701601401354526912364005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17801067600903017941576003 26701601401354526912364005)
        ·
          refine ⟨5006550262753973796068251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26701601401354526912364005 5006550262753973796068251)
          ·
            refine ⟨7509825394130960694102377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006550262753973796068251 7509825394130960694102377)
            ·
              refine ⟨5632369045598220520576783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7509825394130960694102377 5632369045598220520576783)
              ·
                refine ⟨8448553568397330780865175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632369045598220520576783 8448553568397330780865175)
                ·
                  refine ⟨12672830352595996171297763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8448553568397330780865175 12672830352595996171297763)
                  ·
                    refine ⟨19009245528893994256946645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12672830352595996171297763 19009245528893994256946645)
                    ·
                      refine ⟨445529192083452990397187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19009245528893994256946645 445529192083452990397187)
                      ·
                        rfl

theorem cell23_867665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_867665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867665 prefixEnd_867665 := by exact prefixLift 867665
  have htrace : WordTrace (prefixWord ++ tailWord_867665) baseStart_867665 baseEnd_867665 := by
    simpa [prefixWord, tailWord_867665, baseEnd_867665] using wordTrace_append hprefix tailTrace_867665
  have hstable : (prefixWord ++ tailWord_867665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867665).length < 2 ^ (prefixWord ++ tailWord_867665).sum := by decide
  have hdescent : baseEnd_867665 < baseStart_867665 := by decide
  rcases family_descends (prefixWord ++ tailWord_867665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867685 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_867685 : Nat := 118140960795 + 867685 * 2 ^ 59
def prefixEnd_867685 : Nat := 4983230072969 + 3 ^ 40 * 867685 * 2
def baseEnd_867685 : Nat := 148513153898847637382365

theorem tailTrace_867685 : CollatzResearch.WordTrace tailWord_867685 prefixEnd_867685 148513153898847637382365 := by
  unfold tailWord_867685
  simp only [CollatzResearch.WordTrace]
  refine ⟨31647071861532908645196509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21098047907688605763464339 31647071861532908645196509)
  ·
    refine ⟨11867651948074840741948691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31647071861532908645196509 11867651948074840741948691)
    ·
      refine ⟨17801477922112261112923037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867651948074840741948691 17801477922112261112923037)
      ·
        refine ⟨6675554220792097917346139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17801477922112261112923037 6675554220792097917346139)
        ·
          refine ⟨10013331331188146876019209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6675554220792097917346139 10013331331188146876019209)
          ·
            refine ⟨7509998498391110157014407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10013331331188146876019209 7509998498391110157014407)
            ·
              refine ⟨11264997747586665235521611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7509998498391110157014407 11264997747586665235521611)
              ·
                refine ⟨16897496621379997853282417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11264997747586665235521611 16897496621379997853282417)
                ·
                  refine ⟨12673122466034998389961813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16897496621379997853282417 12673122466034998389961813)
                  ·
                    refine ⟨148513153898847637382365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12673122466034998389961813 148513153898847637382365)
                    ·
                      rfl

theorem cell23_867685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_867685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867685 prefixEnd_867685 := by exact prefixLift 867685
  have htrace : WordTrace (prefixWord ++ tailWord_867685) baseStart_867685 baseEnd_867685 := by
    simpa [prefixWord, tailWord_867685, baseEnd_867685] using wordTrace_append hprefix tailTrace_867685
  have hstable : (prefixWord ++ tailWord_867685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867685).length < 2 ^ (prefixWord ++ tailWord_867685).sum := by decide
  have hdescent : baseEnd_867685 < baseStart_867685 := by decide
  rcases family_descends (prefixWord ++ tailWord_867685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867692 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_867692 : Nat := 118140960795 + 867692 * 2 ^ 59
def prefixEnd_867692 : Nat := 4983230072969 + 3 ^ 40 * 867692 * 2
def baseEnd_867692 : Nat := 445543056061124384759563

theorem tailTrace_867692 : CollatzResearch.WordTrace tailWord_867692 prefixEnd_867692 445543056061124384759563 := by
  unfold tailWord_867692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823663586253774420350665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21098218115005032560467553 15823663586253774420350665)
  ·
    refine ⟨11867747689690330815262999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15823663586253774420350665 11867747689690330815262999)
    ·
      refine ⟨17801621534535496222894499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867747689690330815262999 17801621534535496222894499)
      ·
        refine ⟨26702432301803244334341749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17801621534535496222894499 26702432301803244334341749)
        ·
          refine ⟨2503353028294054156344539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26702432301803244334341749 2503353028294054156344539)
          ·
            refine ⟨3755029542441081234516809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503353028294054156344539 3755029542441081234516809)
            ·
              refine ⟨2816272156830810925887607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755029542441081234516809 2816272156830810925887607)
              ·
                refine ⟨4224408235246216388831411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816272156830810925887607 4224408235246216388831411)
                ·
                  refine ⟨6336612352869324583247117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224408235246216388831411 6336612352869324583247117)
                  ·
                    refine ⟨2376229632325996718717669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6336612352869324583247117 2376229632325996718717669)
                    ·
                      refine ⟨445543056061124384759563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2376229632325996718717669 445543056061124384759563)
                      ·
                        rfl

theorem cell23_867692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_867692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867692 prefixEnd_867692 := by exact prefixLift 867692
  have htrace : WordTrace (prefixWord ++ tailWord_867692) baseStart_867692 baseEnd_867692 := by
    simpa [prefixWord, tailWord_867692, baseEnd_867692] using wordTrace_append hprefix tailTrace_867692
  have hstable : (prefixWord ++ tailWord_867692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867692).length < 2 ^ (prefixWord ++ tailWord_867692).sum := by decide
  have hdescent : baseEnd_867692 < baseStart_867692 := by decide
  rcases family_descends (prefixWord ++ tailWord_867692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867705 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_867705 : Nat := 118140960795 + 867705 * 2 ^ 59
def prefixEnd_867705 : Nat := 4983230072969 + 3 ^ 40 * 867705 * 2
def baseEnd_867705 : Nat := 445549731309632833897003

theorem tailTrace_867705 : CollatzResearch.WordTrace tailWord_867705 prefixEnd_867705 445549731309632833897003 := by
  unfold tailWord_867705
  simp only [CollatzResearch.WordTrace]
  refine ⟨31647801321460452060924569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21098534214306968040616379 31647801321460452060924569)
  ·
    refine ⟨23735850991095339045693427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31647801321460452060924569 23735850991095339045693427)
    ·
      refine ⟨35603776486643008568540141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23735850991095339045693427 35603776486643008568540141)
      ·
        refine ⟨13351416182491128213202553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35603776486643008568540141 13351416182491128213202553)
        ·
          refine ⟨10013562136868346159901915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13351416182491128213202553 10013562136868346159901915)
          ·
            refine ⟨15020343205302519239852873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10013562136868346159901915 15020343205302519239852873)
            ·
              refine ⟨11265257403976889429889655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15020343205302519239852873 11265257403976889429889655)
              ·
                refine ⟨16897886105965334144834483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11265257403976889429889655 16897886105965334144834483)
                ·
                  refine ⟨25346829158948001217251725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16897886105965334144834483 25346829158948001217251725)
                  ·
                    refine ⟨9505060934605500456469397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25346829158948001217251725 9505060934605500456469397)
                    ·
                      refine ⟨445549731309632833897003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9505060934605500456469397 445549731309632833897003)
                      ·
                        rfl

theorem cell23_867705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_867705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867705 prefixEnd_867705 := by exact prefixLift 867705
  have htrace : WordTrace (prefixWord ++ tailWord_867705) baseStart_867705 baseEnd_867705 := by
    simpa [prefixWord, tailWord_867705, baseEnd_867705] using wordTrace_append hprefix tailTrace_867705
  have hstable : (prefixWord ++ tailWord_867705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867705).length < 2 ^ (prefixWord ++ tailWord_867705).sum := by decide
  have hdescent : baseEnd_867705 < baseStart_867705 := by decide
  rcases family_descends (prefixWord ++ tailWord_867705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867710 : List Nat := [4, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_867710 : Nat := 118140960795 + 867710 * 2 ^ 59
def prefixEnd_867710 : Nat := 4983230072969 + 3 ^ 40 * 867710 * 2
def baseEnd_867710 : Nat := 49505810968100590481609

theorem tailTrace_867710 : CollatzResearch.WordTrace tailWord_867710 prefixEnd_867710 49505810968100590481609 := by
  unfold tailWord_867710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955997960805292239357073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21098655790961558609904389 3955997960805292239357073)
  ·
    refine ⟨2966998470603969179517805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955997960805292239357073 2966998470603969179517805)
    ·
      refine ⟨1112624426476488442319177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2966998470603969179517805 1112624426476488442319177)
      ·
        refine ⟨834468319857366331739383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112624426476488442319177 834468319857366331739383)
        ·
          refine ⟨1251702479786049497609075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834468319857366331739383 1251702479786049497609075)
          ·
            refine ⟨1877553719679074246413613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251702479786049497609075 1877553719679074246413613)
            ·
              refine ⟨704082644879652842405105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877553719679074246413613 704082644879652842405105)
              ·
                refine ⟨528061983659739631803829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704082644879652842405105 528061983659739631803829)
                ·
                  refine ⟨49505810968100590481609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528061983659739631803829 49505810968100590481609)
                  ·
                    rfl

theorem cell23_867710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_867710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867710 prefixEnd_867710 := by exact prefixLift 867710
  have htrace : WordTrace (prefixWord ++ tailWord_867710) baseStart_867710 baseEnd_867710 := by
    simpa [prefixWord, tailWord_867710, baseEnd_867710] using wordTrace_append hprefix tailTrace_867710
  have hstable : (prefixWord ++ tailWord_867710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867710).length < 2 ^ (prefixWord ++ tailWord_867710).sum := by decide
  have hdescent : baseEnd_867710 < baseStart_867710 := by decide
  rcases family_descends (prefixWord ++ tailWord_867710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867719 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 3, 4]
def baseStart_867719 : Nat := 118140960795 + 867719 * 2 ^ 59
def prefixEnd_867719 : Nat := 4983230072969 + 3 ^ 40 * 867719 * 2
def baseEnd_867719 : Nat := 148518973346265259707313

theorem tailTrace_867719 : CollatzResearch.WordTrace tailWord_867719 prefixEnd_867719 148518973346265259707313 := by
  unfold tailWord_867719
  simp only [CollatzResearch.WordTrace]
  refine ⟨31648311943409732451934211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21098874628939821634622807 31648311943409732451934211)
  ·
    refine ⟨47472467915114598677901317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31648311943409732451934211 47472467915114598677901317)
    ·
      refine ⟨8901087734083987252106497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47472467915114598677901317 8901087734083987252106497)
      ·
        refine ⟨6675815800562990439079873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8901087734083987252106497 6675815800562990439079873)
        ·
          refine ⟨5006861850422242829309905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675815800562990439079873 5006861850422242829309905)
          ·
            refine ⟨3755146387816682121982429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006861850422242829309905 3755146387816682121982429)
            ·
              refine ⟨1408179895431255795743411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3755146387816682121982429 1408179895431255795743411)
              ·
                refine ⟨2112269843146883693615117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408179895431255795743411 2112269843146883693615117)
                ·
                  refine ⟨792101191180081385105669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2112269843146883693615117 792101191180081385105669)
                  ·
                    refine ⟨148518973346265259707313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792101191180081385105669 148518973346265259707313)
                    ·
                      rfl

theorem cell23_867719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_867719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867719 prefixEnd_867719 := by exact prefixLift 867719
  have htrace : WordTrace (prefixWord ++ tailWord_867719) baseStart_867719 baseEnd_867719 := by
    simpa [prefixWord, tailWord_867719, baseEnd_867719] using wordTrace_append hprefix tailTrace_867719
  have hstable : (prefixWord ++ tailWord_867719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867719).length < 2 ^ (prefixWord ++ tailWord_867719).sum := by decide
  have hdescent : baseEnd_867719 < baseStart_867719 := by decide
  rcases family_descends (prefixWord ++ tailWord_867719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867746 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_867746 : Nat := 118140960795 + 867746 * 2 ^ 59
def prefixEnd_867746 : Nat := 4983230072969 + 3 ^ 40 * 867746 * 2
def baseEnd_867746 : Nat := 445570784016467173484315

theorem tailTrace_867746 : CollatzResearch.WordTrace tailWord_867746 prefixEnd_867746 445570784016467173484315 := by
  unfold tailWord_867746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912324178577979015791773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21099531142874610708778061 7912324178577979015791773)
  ·
    refine ⟨2967121566966742130921915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7912324178577979015791773 2967121566966742130921915)
    ·
      refine ⟨4450682350450113196382873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967121566966742130921915 4450682350450113196382873)
      ·
        refine ⟨3338011762837584897287155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4450682350450113196382873 3338011762837584897287155)
        ·
          refine ⟨5007017644256377345930733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338011762837584897287155 5007017644256377345930733)
          ·
            refine ⟨1877631616596141504724025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5007017644256377345930733 1877631616596141504724025)
            ·
              refine ⟨1408223712447106128543019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877631616596141504724025 1408223712447106128543019)
              ·
                refine ⟨2112335568670659192814529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408223712447106128543019 2112335568670659192814529)
                ·
                  refine ⟨1584251676502994394610897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2112335568670659192814529 1584251676502994394610897)
                  ·
                    refine ⟨1188188757377245795958173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1584251676502994394610897 1188188757377245795958173)
                    ·
                      refine ⟨445570784016467173484315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1188188757377245795958173 445570784016467173484315)
                      ·
                        rfl

theorem cell23_867746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_867746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867746 prefixEnd_867746 := by exact prefixLift 867746
  have htrace : WordTrace (prefixWord ++ tailWord_867746) baseStart_867746 baseEnd_867746 := by
    simpa [prefixWord, tailWord_867746, baseEnd_867746] using wordTrace_append hprefix tailTrace_867746
  have hstable : (prefixWord ++ tailWord_867746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867746).length < 2 ^ (prefixWord ++ tailWord_867746).sum := by decide
  have hdescent : baseEnd_867746 < baseStart_867746 := by decide
  rcases family_descends (prefixWord ++ tailWord_867746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867813 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_867813 : Nat := 118140960795 + 867813 * 2 ^ 59
def prefixEnd_867813 : Nat := 4983230072969 + 3 ^ 40 * 867813 * 2
def baseEnd_867813 : Nat := 148535062406772803782169

theorem tailTrace_867813 : CollatzResearch.WordTrace tailWord_867813 prefixEnd_867813 148535062406772803782169 := by
  unfold tailWord_867813
  simp only [CollatzResearch.WordTrace]
  refine ⟨31651740405069186505856093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21101160270046124337237395 31651740405069186505856093)
  ·
    refine ⟨11869402651900944939696035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31651740405069186505856093 11869402651900944939696035)
    ·
      refine ⟨17804103977851417409544053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11869402651900944939696035 17804103977851417409544053)
      ·
        refine ⟨1669134747923570382144755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17804103977851417409544053 1669134747923570382144755)
        ·
          refine ⟨2503702121885355573217133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669134747923570382144755 2503702121885355573217133)
          ·
            refine ⟨938888295707008339956425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2503702121885355573217133 938888295707008339956425)
            ·
              refine ⟨704166221780256254967319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938888295707008339956425 704166221780256254967319)
              ·
                refine ⟨1056249332670384382450979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704166221780256254967319 1056249332670384382450979)
                ·
                  refine ⟨1584373999005576573676469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056249332670384382450979 1584373999005576573676469)
                  ·
                    refine ⟨148535062406772803782169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1584373999005576573676469 148535062406772803782169)
                    ·
                      rfl

theorem cell23_867813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_867813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867813 prefixEnd_867813 := by exact prefixLift 867813
  have htrace : WordTrace (prefixWord ++ tailWord_867813) baseStart_867813 baseEnd_867813 := by
    simpa [prefixWord, tailWord_867813, baseEnd_867813] using wordTrace_append hprefix tailTrace_867813
  have hstable : (prefixWord ++ tailWord_867813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867813).length < 2 ^ (prefixWord ++ tailWord_867813).sum := by decide
  have hdescent : baseEnd_867813 < baseStart_867813 := by decide
  rcases family_descends (prefixWord ++ tailWord_867813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867816 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_867816 : Nat := 118140960795 + 867816 * 2 ^ 59
def prefixEnd_867816 : Nat := 4983230072969 + 3 ^ 40 * 867816 * 2
def baseEnd_867816 : Nat := 445606727662281899608993

theorem tailTrace_867816 : CollatzResearch.WordTrace tailWord_867816 prefixEnd_867816 445606727662281899608993 := by
  unfold tailWord_867816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825924912029159009107651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21101233216038878678810201 15825924912029159009107651)
  ·
    refine ⟨23738887368043738513661477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15825924912029159009107651 23738887368043738513661477)
    ·
      refine ⟨4451041381508200971311527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23738887368043738513661477 4451041381508200971311527)
      ·
        refine ⟨6676562072262301456967291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451041381508200971311527 6676562072262301456967291)
        ·
          refine ⟨10014843108393452185450937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676562072262301456967291 10014843108393452185450937)
          ·
            refine ⟨7511132331295089139088203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10014843108393452185450937 7511132331295089139088203)
            ·
              refine ⟨11266698496942633708632305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511132331295089139088203 11266698496942633708632305)
              ·
                refine ⟨8450023872706975281474229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11266698496942633708632305 8450023872706975281474229)
                ·
                  refine ⟨792189738066278932638209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8450023872706975281474229 792189738066278932638209)
                  ·
                    refine ⟨594142303549709199478657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792189738066278932638209 594142303549709199478657)
                    ·
                      refine ⟨445606727662281899608993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594142303549709199478657 445606727662281899608993)
                      ·
                        rfl

theorem cell23_867816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_867816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867816 prefixEnd_867816 := by exact prefixLift 867816
  have htrace : WordTrace (prefixWord ++ tailWord_867816) baseStart_867816 baseEnd_867816 := by
    simpa [prefixWord, tailWord_867816, baseEnd_867816] using wordTrace_append hprefix tailTrace_867816
  have hstable : (prefixWord ++ tailWord_867816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867816).length < 2 ^ (prefixWord ++ tailWord_867816).sum := by decide
  have hdescent : baseEnd_867816 < baseStart_867816 := by decide
  rcases family_descends (prefixWord ++ tailWord_867816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867822 : List Nat := [4, 1, 2, 1, 2, 1, 12]
def baseStart_867822 : Nat := 118140960795 + 867822 * 2 ^ 59
def prefixEnd_867822 : Nat := 4983230072969 + 3 ^ 40 * 867822 * 2
def baseEnd_867822 : Nat := 5501355661064307112765

theorem tailTrace_867822 : CollatzResearch.WordTrace tailWord_867822 prefixEnd_867822 5501355661064307112765 := by
  unfold tailWord_867822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956508582754572630366715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21101379108024387361955813 3956508582754572630366715)
  ·
    refine ⟨5934762874131858945550073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956508582754572630366715 5934762874131858945550073)
    ·
      refine ⟨4451072155598894209162555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5934762874131858945550073 4451072155598894209162555)
      ·
        refine ⟨6676608233398341313743833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451072155598894209162555 6676608233398341313743833)
        ·
          refine ⟨5007456175048755985307875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676608233398341313743833 5007456175048755985307875)
          ·
            refine ⟨7511184262573133977961813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007456175048755985307875 7511184262573133977961813)
            ·
              refine ⟨5501355661064307112765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 7511184262573133977961813 5501355661064307112765)
              ·
                rfl

theorem cell23_867822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 12].length) (baseStart_867822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867822 prefixEnd_867822 := by exact prefixLift 867822
  have htrace : WordTrace (prefixWord ++ tailWord_867822) baseStart_867822 baseEnd_867822 := by
    simpa [prefixWord, tailWord_867822, baseEnd_867822] using wordTrace_append hprefix tailTrace_867822
  have hstable : (prefixWord ++ tailWord_867822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867822).length < 2 ^ (prefixWord ++ tailWord_867822).sum := by decide
  have hdescent : baseEnd_867822 < baseStart_867822 := by decide
  rcases family_descends (prefixWord ++ tailWord_867822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867826 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_867826 : Nat := 118140960795 + 867826 * 2 ^ 59
def prefixEnd_867826 : Nat := 4983230072969 + 3 ^ 40 * 867826 * 2
def baseEnd_867826 : Nat := 148537287489608953494649

theorem tailTrace_867826 : CollatzResearch.WordTrace tailWord_867826 prefixEnd_867826 148537287489608953494649 := by
  unfold tailWord_867826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913053638505522431519833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21101476369348059817386221 7913053638505522431519833)
  ·
    refine ⟨5934790228879141823639875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913053638505522431519833 5934790228879141823639875)
    ·
      refine ⟨8902185343318712735459813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934790228879141823639875 8902185343318712735459813)
      ·
        refine ⟨1669159751872258637898715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8902185343318712735459813 1669159751872258637898715)
        ·
          refine ⟨2503739627808387956848073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669159751872258637898715 2503739627808387956848073)
          ·
            refine ⟨1877804720856290967636055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2503739627808387956848073 1877804720856290967636055)
            ·
              refine ⟨2816707081284436451454083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877804720856290967636055 2816707081284436451454083)
              ·
                refine ⟨4225060621926654677181125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816707081284436451454083 4225060621926654677181125)
                ·
                  refine ⟨792198866611247751971461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4225060621926654677181125 792198866611247751971461)
                  ·
                    refine ⟨148537287489608953494649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792198866611247751971461 148537287489608953494649)
                    ·
                      rfl

theorem cell23_867826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_867826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867826 prefixEnd_867826 := by exact prefixLift 867826
  have htrace : WordTrace (prefixWord ++ tailWord_867826) baseStart_867826 baseEnd_867826 := by
    simpa [prefixWord, tailWord_867826, baseEnd_867826] using wordTrace_append hprefix tailTrace_867826
  have hstable : (prefixWord ++ tailWord_867826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867826).length < 2 ^ (prefixWord ++ tailWord_867826).sum := by decide
  have hdescent : baseEnd_867826 < baseStart_867826 := by decide
  rcases family_descends (prefixWord ++ tailWord_867826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867940 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_867940 : Nat := 118140960795 + 867940 * 2 ^ 59
def prefixEnd_867940 : Nat := 4983230072969 + 3 ^ 40 * 867940 * 2
def baseEnd_867940 : Nat := 445670399263439414458423

theorem tailTrace_867940 : CollatzResearch.WordTrace tailWord_867940 prefixEnd_867940 445670399263439414458423 := by
  unfold tailWord_867940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828186237804543597864637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21104248317072724797152849 15828186237804543597864637)
  ·
    refine ⟨5935569839176703849199239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15828186237804543597864637 5935569839176703849199239)
    ·
      refine ⟨8903354758765055773798859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935569839176703849199239 8903354758765055773798859)
      ·
        refine ⟨13355032138147583660698289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903354758765055773798859 13355032138147583660698289)
        ·
          refine ⟨10016274103610687745523717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13355032138147583660698289 10016274103610687745523717)
          ·
            refine ⟨1878051394427003952285697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10016274103610687745523717 1878051394427003952285697)
            ·
              refine ⟨1408538545820252964214273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878051394427003952285697 1408538545820252964214273)
              ·
                refine ⟨1056403909365189723160705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408538545820252964214273 1056403909365189723160705)
                ·
                  refine ⟨792302932023892292370529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056403909365189723160705 792302932023892292370529)
                  ·
                    refine ⟨594227199017919219277897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792302932023892292370529 594227199017919219277897)
                    ·
                      refine ⟨445670399263439414458423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594227199017919219277897 445670399263439414458423)
                      ·
                        rfl

theorem cell23_867940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_867940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867940 prefixEnd_867940 := by exact prefixLift 867940
  have htrace : WordTrace (prefixWord ++ tailWord_867940) baseStart_867940 baseEnd_867940 := by
    simpa [prefixWord, tailWord_867940, baseEnd_867940] using wordTrace_append hprefix tailTrace_867940
  have hstable : (prefixWord ++ tailWord_867940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867940).length < 2 ^ (prefixWord ++ tailWord_867940).sum := by decide
  have hdescent : baseEnd_867940 < baseStart_867940 := by decide
  rcases family_descends (prefixWord ++ tailWord_867940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867979 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_867979 : Nat := 118140960795 + 867979 * 2 ^ 59
def prefixEnd_867979 : Nat := 4983230072969 + 3 ^ 40 * 867979 * 2
def baseEnd_867979 : Nat := 445690425008964761870743

theorem tailTrace_867979 : CollatzResearch.WordTrace tailWord_867979 prefixEnd_867979 445690425008964761870743 := by
  unfold tailWord_867979
  simp only [CollatzResearch.WordTrace]
  refine ⟨31657794922467796856398991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21105196614978531237599327 31657794922467796856398991)
  ·
    refine ⟨47486692383701695284598487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31657794922467796856398991 47486692383701695284598487)
    ·
      refine ⟨71230038575552542926897731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47486692383701695284598487 71230038575552542926897731)
      ·
        refine ⟨106845057863328814390346597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71230038575552542926897731 106845057863328814390346597)
        ·
          refine ⟨20033448349374152698189987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106845057863328814390346597 20033448349374152698189987)
          ·
            refine ⟨30050172524061229047284981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20033448349374152698189987 30050172524061229047284981)
            ·
              refine ⟨2817203674130740223182967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30050172524061229047284981 2817203674130740223182967)
              ·
                refine ⟨4225805511196110334774451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817203674130740223182967 4225805511196110334774451)
                ·
                  refine ⟨6338708266794165502161677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225805511196110334774451 6338708266794165502161677)
                  ·
                    refine ⟨2377015600047812063310629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6338708266794165502161677 2377015600047812063310629)
                    ·
                      refine ⟨445690425008964761870743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2377015600047812063310629 445690425008964761870743)
                      ·
                        rfl

theorem cell23_867979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_867979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_867979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_867979 prefixEnd_867979 := by exact prefixLift 867979
  have htrace : WordTrace (prefixWord ++ tailWord_867979) baseStart_867979 baseEnd_867979 := by
    simpa [prefixWord, tailWord_867979, baseEnd_867979] using wordTrace_append hprefix tailTrace_867979
  have hstable : (prefixWord ++ tailWord_867979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867979).length < 2 ^ (prefixWord ++ tailWord_867979).sum := by decide
  have hdescent : baseEnd_867979 < baseStart_867979 := by decide
  rcases family_descends (prefixWord ++ tailWord_867979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868013 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_868013 : Nat := 118140960795 + 868013 * 2 ^ 59
def prefixEnd_868013 : Nat := 4983230072969 + 3 ^ 40 * 868013 * 2
def baseEnd_868013 : Nat := 445707883351217628845587

theorem tailTrace_868013 : CollatzResearch.WordTrace tailWord_868013 prefixEnd_868013 445707883351217628845587 := by
  unfold tailWord_868013
  simp only [CollatzResearch.WordTrace]
  refine ⟨31659035004344620663136693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21106023336229747108757795 31659035004344620663136693)
  ·
    refine ⟨2968034531657308187169065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31659035004344620663136693 2968034531657308187169065)
    ·
      refine ⟨2226025898742981140376799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968034531657308187169065 2226025898742981140376799)
      ·
        refine ⟨3339038848114471710565199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226025898742981140376799 3339038848114471710565199)
        ·
          refine ⟨5008558272171707565847799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339038848114471710565199 5008558272171707565847799)
          ·
            refine ⟨7512837408257561348771699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008558272171707565847799 7512837408257561348771699)
            ·
              refine ⟨11269256112386342023157549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7512837408257561348771699 11269256112386342023157549)
              ·
                refine ⟨4225971042144878258684081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11269256112386342023157549 4225971042144878258684081)
                ·
                  refine ⟨3169478281608658694013061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225971042144878258684081 3169478281608658694013061)
                  ·
                    refine ⟨594277177801623505127449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3169478281608658694013061 594277177801623505127449)
                    ·
                      refine ⟨445707883351217628845587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594277177801623505127449 445707883351217628845587)
                      ·
                        rfl

theorem cell23_868013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_868013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868013 prefixEnd_868013 := by exact prefixLift 868013
  have htrace : WordTrace (prefixWord ++ tailWord_868013) baseStart_868013 baseEnd_868013 := by
    simpa [prefixWord, tailWord_868013, baseEnd_868013] using wordTrace_append hprefix tailTrace_868013
  have hstable : (prefixWord ++ tailWord_868013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868013).length < 2 ^ (prefixWord ++ tailWord_868013).sum := by decide
  have hdescent : baseEnd_868013 < baseStart_868013 := by decide
  rcases family_descends (prefixWord ++ tailWord_868013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868089 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_868089 : Nat := 118140960795 + 868089 * 2 ^ 59
def prefixEnd_868089 : Nat := 4983230072969 + 3 ^ 40 * 868089 * 2
def baseEnd_868089 : Nat := 445746907880959331495237

theorem tailTrace_868089 : CollatzResearch.WordTrace tailWord_868089 prefixEnd_868089 445746907880959331495237 := by
  unfold tailWord_868089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661806952069285642903321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21107871301379523761935547 31661806952069285642903321)
  ·
    refine ⟨23746355214051964232177491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31661806952069285642903321 23746355214051964232177491)
    ·
      refine ⟨35619532821077946348266237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746355214051964232177491 35619532821077946348266237)
      ·
        refine ⟨13357324807904229880599839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35619532821077946348266237 13357324807904229880599839)
        ·
          refine ⟨20035987211856344820899759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13357324807904229880599839 20035987211856344820899759)
          ·
            refine ⟨30053980817784517231349639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20035987211856344820899759 30053980817784517231349639)
            ·
              refine ⟨45080971226676775847024459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30053980817784517231349639 45080971226676775847024459)
              ·
                refine ⟨67621456840015163770536689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45080971226676775847024459 67621456840015163770536689)
                ·
                  refine ⟨50716092630011372827902517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67621456840015163770536689 50716092630011372827902517)
                  ·
                    refine ⟨4754633684063566202615861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50716092630011372827902517 4754633684063566202615861)
                    ·
                      refine ⟨445746907880959331495237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4754633684063566202615861 445746907880959331495237)
                      ·
                        rfl

theorem cell23_868089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_868089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868089 prefixEnd_868089 := by exact prefixLift 868089
  have htrace : WordTrace (prefixWord ++ tailWord_868089) baseStart_868089 baseEnd_868089 := by
    simpa [prefixWord, tailWord_868089, baseEnd_868089] using wordTrace_append hprefix tailTrace_868089
  have hstable : (prefixWord ++ tailWord_868089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868089).length < 2 ^ (prefixWord ++ tailWord_868089).sum := by decide
  have hdescent : baseEnd_868089 < baseStart_868089 := by decide
  rcases family_descends (prefixWord ++ tailWord_868089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868100 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_868100 : Nat := 118140960795 + 868100 * 2 ^ 59
def prefixEnd_868100 : Nat := 4983230072969 + 3 ^ 40 * 868100 * 2
def baseEnd_868100 : Nat := 148584185389386262819229

theorem tailTrace_868100 : CollatzResearch.WordTrace tailWord_868100 prefixEnd_868100 148584185389386262819229 := by
  unfold tailWord_868100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15831104077514717260776877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21108138770019623014369169 15831104077514717260776877)
  ·
    refine ⟨5936664029068018972791329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15831104077514717260776877 5936664029068018972791329)
    ·
      refine ⟨4452498021801014229593497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5936664029068018972791329 4452498021801014229593497)
      ·
        refine ⟨3339373516350760672195123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4452498021801014229593497 3339373516350760672195123)
        ·
          refine ⟨5009060274526141008292685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339373516350760672195123 5009060274526141008292685)
          ·
            refine ⟨1878397602947302878109757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5009060274526141008292685 1878397602947302878109757)
            ·
              refine ⟨704399101105238579291159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1878397602947302878109757 704399101105238579291159)
              ·
                refine ⟨1056598651657857868936739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704399101105238579291159 1056598651657857868936739)
                ·
                  refine ⟨1584897977486786803405109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056598651657857868936739 1584897977486786803405109)
                  ·
                    refine ⟨148584185389386262819229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1584897977486786803405109 148584185389386262819229)
                    ·
                      rfl

theorem cell23_868100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_868100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868100 prefixEnd_868100 := by exact prefixLift 868100
  have htrace : WordTrace (prefixWord ++ tailWord_868100) baseStart_868100 baseEnd_868100 := by
    simpa [prefixWord, tailWord_868100, baseEnd_868100] using wordTrace_append hprefix tailTrace_868100
  have hstable : (prefixWord ++ tailWord_868100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868100).length < 2 ^ (prefixWord ++ tailWord_868100).sum := by decide
  have hdescent : baseEnd_868100 < baseStart_868100 := by decide
  rcases family_descends (prefixWord ++ tailWord_868100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868114 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_868114 : Nat := 118140960795 + 868114 * 2 ^ 59
def prefixEnd_868114 : Nat := 4983230072969 + 3 ^ 40 * 868114 * 2
def baseEnd_868114 : Nat := 445759744897321733682623

theorem tailTrace_868114 : CollatzResearch.WordTrace tailWord_868114 prefixEnd_868114 445759744897321733682623 := by
  unfold tailWord_868114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915679694244678728140849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21108479184652476608375597 7915679694244678728140849)
  ·
    refine ⟨5936759770683509046105637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7915679694244678728140849 5936759770683509046105637)
    ·
      refine ⟨1113142457003157946144807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5936759770683509046105637 1113142457003157946144807)
      ·
        refine ⟨1669713685504736919217211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113142457003157946144807 1669713685504736919217211)
        ·
          refine ⟨2504570528257105378825817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669713685504736919217211 2504570528257105378825817)
          ·
            refine ⟨1878427896192829034119363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2504570528257105378825817 1878427896192829034119363)
            ·
              refine ⟨2817641844289243551179045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878427896192829034119363 2817641844289243551179045)
              ·
                refine ⟨528307845804233165846071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2817641844289243551179045 528307845804233165846071)
                ·
                  refine ⟨792461768706349748769107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528307845804233165846071 792461768706349748769107)
                  ·
                    refine ⟨1188692653059524623153661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 792461768706349748769107 1188692653059524623153661)
                    ·
                      refine ⟨445759744897321733682623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1188692653059524623153661 445759744897321733682623)
                      ·
                        rfl

theorem cell23_868114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_868114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868114 prefixEnd_868114 := by exact prefixLift 868114
  have htrace : WordTrace (prefixWord ++ tailWord_868114) baseStart_868114 baseEnd_868114 := by
    simpa [prefixWord, tailWord_868114, baseEnd_868114] using wordTrace_append hprefix tailTrace_868114
  have hstable : (prefixWord ++ tailWord_868114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868114).length < 2 ^ (prefixWord ++ tailWord_868114).sum := by decide
  have hdescent : baseEnd_868114 < baseStart_868114 := by decide
  rcases family_descends (prefixWord ++ tailWord_868114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868133 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_868133 : Nat := 118140960795 + 868133 * 2 ^ 59
def prefixEnd_868133 : Nat := 4983230072969 + 3 ^ 40 * 868133 * 2
def baseEnd_868133 : Nat := 445769501029757159345035

theorem tailTrace_868133 : CollatzResearch.WordTrace tailWord_868133 prefixEnd_868133 445769501029757159345035 := by
  unfold tailWord_868133
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663411763909881157505053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21108941175939920771670035 31663411763909881157505053)
  ·
    refine ⟨11873779411466205434064395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31663411763909881157505053 11873779411466205434064395)
    ·
      refine ⟨17810669117199308151096593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11873779411466205434064395 17810669117199308151096593)
      ·
        refine ⟨13358001837899481113322445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17810669117199308151096593 13358001837899481113322445)
        ·
          refine ⟨5009250689212305417495917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13358001837899481113322445 5009250689212305417495917)
          ·
            refine ⟨1878469008454614531560969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5009250689212305417495917 1878469008454614531560969)
            ·
              refine ⟨1408851756340960898670727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878469008454614531560969 1408851756340960898670727)
              ·
                refine ⟨2113277634511441348006091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408851756340960898670727 2113277634511441348006091)
                ·
                  refine ⟨3169916451767162022009137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113277634511441348006091 3169916451767162022009137)
                  ·
                    refine ⟨2377437338825371516506853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169916451767162022009137 2377437338825371516506853)
                    ·
                      refine ⟨445769501029757159345035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2377437338825371516506853 445769501029757159345035)
                      ·
                        rfl

theorem cell23_868133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_868133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868133 prefixEnd_868133 := by exact prefixLift 868133
  have htrace : WordTrace (prefixWord ++ tailWord_868133) baseStart_868133 baseEnd_868133 := by
    simpa [prefixWord, tailWord_868133, baseEnd_868133] using wordTrace_append hprefix tailTrace_868133
  have hstable : (prefixWord ++ tailWord_868133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868133).length < 2 ^ (prefixWord ++ tailWord_868133).sum := by decide
  have hdescent : baseEnd_868133 < baseStart_868133 := by decide
  rcases family_descends (prefixWord ++ tailWord_868133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868139 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 9]
def baseStart_868139 : Nat := 118140960795 + 868139 * 2 ^ 59
def prefixEnd_868139 : Nat := 4983230072969 + 3 ^ 40 * 868139 * 2
def baseEnd_868139 : Nat := 148590860637894711956669

theorem tailTrace_868139 : CollatzResearch.WordTrace tailWord_868139 prefixEnd_868139 148590860637894711956669 := by
  unfold tailWord_868139
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663630601888144182223471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21109087067925429454815647 31663630601888144182223471)
  ·
    refine ⟨47495445902832216273335207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31663630601888144182223471 47495445902832216273335207)
    ·
      refine ⟨71243168854248324410002811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47495445902832216273335207 71243168854248324410002811)
      ·
        refine ⟨106864753281372486615004217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71243168854248324410002811 106864753281372486615004217)
        ·
          refine ⟨80148564961029364961253163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106864753281372486615004217 80148564961029364961253163)
          ·
            refine ⟨120222847441544047441879745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80148564961029364961253163 120222847441544047441879745)
            ·
              refine ⟨90167135581158035581409809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120222847441544047441879745 90167135581158035581409809)
              ·
                refine ⟨67625351685868526686057357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90167135581158035581409809 67625351685868526686057357)
                ·
                  refine ⟨25359506882200697507271509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67625351685868526686057357 25359506882200697507271509)
                  ·
                    refine ⟨148590860637894711956669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25359506882200697507271509 148590860637894711956669)
                    ·
                      rfl

theorem cell23_868139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_868139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868139 prefixEnd_868139 := by exact prefixLift 868139
  have htrace : WordTrace (prefixWord ++ tailWord_868139) baseStart_868139 baseEnd_868139 := by
    simpa [prefixWord, tailWord_868139, baseEnd_868139] using wordTrace_append hprefix tailTrace_868139
  have hstable : (prefixWord ++ tailWord_868139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868139).length < 2 ^ (prefixWord ++ tailWord_868139).sum := by decide
  have hdescent : baseEnd_868139 < baseStart_868139 := by decide
  rcases family_descends (prefixWord ++ tailWord_868139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868150 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_868150 : Nat := 118140960795 + 868150 * 2 ^ 59
def prefixEnd_868150 : Nat := 4983230072969 + 3 ^ 40 * 868150 * 2
def baseEnd_868150 : Nat := 445778230200883592832457

theorem tailTrace_868150 : CollatzResearch.WordTrace tailWord_868150 prefixEnd_868150 445778230200883592832457 := by
  unfold tailWord_868150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979001987803018316304619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21109354536565528707249269 1979001987803018316304619)
  ·
    refine ⟨2968502981704527474456929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1979001987803018316304619 2968502981704527474456929)
    ·
      refine ⟨2226377236278395605842697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968502981704527474456929 2226377236278395605842697)
      ·
        refine ⟨1669782927208796704382023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2226377236278395605842697 1669782927208796704382023)
        ·
          refine ⟨2504674390813195056573035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669782927208796704382023 2504674390813195056573035)
          ·
            refine ⟨3757011586219792584859553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504674390813195056573035 3757011586219792584859553)
            ·
              refine ⟨2817758689664844438644665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3757011586219792584859553 2817758689664844438644665)
              ·
                refine ⟨2113319017248633328983499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817758689664844438644665 2113319017248633328983499)
                ·
                  refine ⟨3169978525872949993475249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113319017248633328983499 3169978525872949993475249)
                  ·
                    refine ⟨2377483894404712495106437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3169978525872949993475249 2377483894404712495106437)
                    ·
                      refine ⟨445778230200883592832457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2377483894404712495106437 445778230200883592832457)
                      ·
                        rfl

theorem cell23_868150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_868150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868150 prefixEnd_868150 := by exact prefixLift 868150
  have htrace : WordTrace (prefixWord ++ tailWord_868150) baseStart_868150 baseEnd_868150 := by
    simpa [prefixWord, tailWord_868150, baseEnd_868150] using wordTrace_append hprefix tailTrace_868150
  have hstable : (prefixWord ++ tailWord_868150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868150).length < 2 ^ (prefixWord ++ tailWord_868150).sum := by decide
  have hdescent : baseEnd_868150 < baseStart_868150 := by decide
  rcases family_descends (prefixWord ++ tailWord_868150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868154 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2]
def baseStart_868154 : Nat := 118140960795 + 868154 * 2 ^ 59
def prefixEnd_868154 : Nat := 4983230072969 + 3 ^ 40 * 868154 * 2
def baseEnd_868154 : Nat := 445780284123501577182439

theorem tailTrace_868154 : CollatzResearch.WordTrace tailWord_868154 prefixEnd_868154 445780284123501577182439 := by
  unfold tailWord_868154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916044424208450436004879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21109451797889201162679677 7916044424208450436004879)
  ·
    refine ⟨11874066636312675654007319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7916044424208450436004879 11874066636312675654007319)
    ·
      refine ⟨17811099954469013481010979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11874066636312675654007319 17811099954469013481010979)
      ·
        refine ⟨26716649931703520221516469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17811099954469013481010979 26716649931703520221516469)
        ·
          refine ⟨2504685931097205020767169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26716649931703520221516469 2504685931097205020767169)
          ·
            refine ⟨1878514448322903765575377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2504685931097205020767169 1878514448322903765575377)
            ·
              refine ⟨1408885836242177824181533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878514448322903765575377 1408885836242177824181533)
              ·
                refine ⟨528332188590816684068075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1408885836242177824181533 528332188590816684068075)
                ·
                  refine ⟨792498282886225026102113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528332188590816684068075 792498282886225026102113)
                  ·
                    refine ⟨594373712164668769576585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792498282886225026102113 594373712164668769576585)
                    ·
                      refine ⟨445780284123501577182439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594373712164668769576585 445780284123501577182439)
                      ·
                        rfl

theorem cell23_868154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_868154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868154 prefixEnd_868154 := by exact prefixLift 868154
  have htrace : WordTrace (prefixWord ++ tailWord_868154) baseStart_868154 baseEnd_868154 := by
    simpa [prefixWord, tailWord_868154, baseEnd_868154] using wordTrace_append hprefix tailTrace_868154
  have hstable : (prefixWord ++ tailWord_868154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868154).length < 2 ^ (prefixWord ++ tailWord_868154).sum := by decide
  have hdescent : baseEnd_868154 < baseStart_868154 := by decide
  rcases family_descends (prefixWord ++ tailWord_868154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868157 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_868157 : Nat := 118140960795 + 868157 * 2 ^ 59
def prefixEnd_868157 : Nat := 4983230072969 + 3 ^ 40 * 868157 * 2
def baseEnd_868157 : Nat := 445781824565465065444925

theorem tailTrace_868157 : CollatzResearch.WordTrace tailWord_868157 prefixEnd_868157 445781824565465065444925 := by
  unfold tailWord_868157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31664287115822933256378725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21109524743881955504252483 31664287115822933256378725)
  ·
    refine ⟨5937053834216799985571011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31664287115822933256378725 5937053834216799985571011)
    ·
      refine ⟨8905580751325199978356517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937053834216799985571011 8905580751325199978356517)
      ·
        refine ⟨1669796390873474995941847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8905580751325199978356517 1669796390873474995941847)
        ·
          refine ⟨2504694586310212493912771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669796390873474995941847 2504694586310212493912771)
          ·
            refine ⟨3757041879465318740869157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504694586310212493912771 3757041879465318740869157)
            ·
              refine ⟨704445352399747263912967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3757041879465318740869157 704445352399747263912967)
              ·
                refine ⟨1056668028599620895869451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704445352399747263912967 1056668028599620895869451)
                ·
                  refine ⟨1585002042899431343804177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1056668028599620895869451 1585002042899431343804177)
                  ·
                    refine ⟨1188751532174573507853133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585002042899431343804177 1188751532174573507853133)
                    ·
                      refine ⟨445781824565465065444925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1188751532174573507853133 445781824565465065444925)
                      ·
                        rfl

theorem cell23_868157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_868157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868157 prefixEnd_868157 := by exact prefixLift 868157
  have htrace : WordTrace (prefixWord ++ tailWord_868157) baseStart_868157 baseEnd_868157 := by
    simpa [prefixWord, tailWord_868157, baseEnd_868157] using wordTrace_append hprefix tailTrace_868157
  have hstable : (prefixWord ++ tailWord_868157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868157).length < 2 ^ (prefixWord ++ tailWord_868157).sum := by decide
  have hdescent : baseEnd_868157 < baseStart_868157 := by decide
  rcases family_descends (prefixWord ++ tailWord_868157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868186 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_868186 : Nat := 118140960795 + 868186 * 2 ^ 59
def prefixEnd_868186 : Nat := 4983230072969 + 3 ^ 40 * 868186 * 2
def baseEnd_868186 : Nat := 148598905168148483994097

theorem tailTrace_868186 : CollatzResearch.WordTrace tailWord_868186 prefixEnd_868186 148598905168148483994097 := by
  unfold tailWord_868186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916336208179467802296103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21110229888478580806122941 7916336208179467802296103)
  ·
    refine ⟨11874504312269201703444155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7916336208179467802296103 11874504312269201703444155)
    ·
      refine ⟨17811756468403802555166233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11874504312269201703444155 17811756468403802555166233)
      ·
        refine ⟨13358817351302851916374675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17811756468403802555166233 13358817351302851916374675)
        ·
          refine ⟨20038226026954277874562013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358817351302851916374675 20038226026954277874562013)
          ·
            refine ⟨7514334760107854202960755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20038226026954277874562013 7514334760107854202960755)
            ·
              refine ⟨11271502140161781304441133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514334760107854202960755 11271502140161781304441133)
              ·
                refine ⟨4226813302560667989165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11271502140161781304441133 4226813302560667989165425)
                ·
                  refine ⟨3170109976920500991874069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4226813302560667989165425 3170109976920500991874069)
                  ·
                    refine ⟨148598905168148483994097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3170109976920500991874069 148598905168148483994097)
                    ·
                      rfl

theorem cell23_868186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_868186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868186 prefixEnd_868186 := by exact prefixLift 868186
  have htrace : WordTrace (prefixWord ++ tailWord_868186) baseStart_868186 baseEnd_868186 := by
    simpa [prefixWord, tailWord_868186, baseEnd_868186] using wordTrace_append hprefix tailTrace_868186
  have hstable : (prefixWord ++ tailWord_868186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868186).length < 2 ^ (prefixWord ++ tailWord_868186).sum := by decide
  have hdescent : baseEnd_868186 < baseStart_868186 := by decide
  rcases family_descends (prefixWord ++ tailWord_868186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868213 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_868213 : Nat := 118140960795 + 868213 * 2 ^ 59
def prefixEnd_868213 : Nat := 4983230072969 + 3 ^ 40 * 868213 * 2
def baseEnd_868213 : Nat := 445810579482116846344667

theorem tailTrace_868213 : CollatzResearch.WordTrace tailWord_868213 prefixEnd_868213 445810579482116846344667 := by
  unfold tailWord_868213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666329603620054820417293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21110886402413369880278195 31666329603620054820417293)
  ·
    refine ⟨11874873601357520557656485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31666329603620054820417293 11874873601357520557656485)
    ·
      refine ⟨2226538800254535104560591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11874873601357520557656485 2226538800254535104560591)
      ·
        refine ⟨3339808200381802656840887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226538800254535104560591 3339808200381802656840887)
        ·
          refine ⟨5009712300572703985261331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339808200381802656840887 5009712300572703985261331)
          ·
            refine ⟨7514568450859055977891997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009712300572703985261331 7514568450859055977891997)
            ·
              refine ⟨2817963169072145991709499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7514568450859055977891997 2817963169072145991709499)
              ·
                refine ⟨4226944753608218987564249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817963169072145991709499 4226944753608218987564249)
                ·
                  refine ⟨3170208565206164240673187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4226944753608218987564249 3170208565206164240673187)
                  ·
                    refine ⟨4755312847809246361009781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3170208565206164240673187 4755312847809246361009781)
                    ·
                      refine ⟨445810579482116846344667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4755312847809246361009781 445810579482116846344667)
                      ·
                        rfl

theorem cell23_868213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_868213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868213 prefixEnd_868213 := by exact prefixLift 868213
  have htrace : WordTrace (prefixWord ++ tailWord_868213) baseStart_868213 baseEnd_868213 := by
    simpa [prefixWord, tailWord_868213, baseEnd_868213] using wordTrace_append hprefix tailTrace_868213
  have hstable : (prefixWord ++ tailWord_868213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868213).length < 2 ^ (prefixWord ++ tailWord_868213).sum := by decide
  have hdescent : baseEnd_868213 < baseStart_868213 := by decide
  rcases family_descends (prefixWord ++ tailWord_868213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868238 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_868238 : Nat := 118140960795 + 868238 * 2 ^ 59
def prefixEnd_868238 : Nat := 4983230072969 + 3 ^ 40 * 868238 * 2
def baseEnd_868238 : Nat := 445823416498479248532053

theorem tailTrace_868238 : CollatzResearch.WordTrace tailWord_868238 prefixEnd_868238 445823416498479248532053 := by
  unfold tailWord_868238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958405178566185511259671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21111494285686322726718245 3958405178566185511259671)
  ·
    refine ⟨5937607767849278266889507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3958405178566185511259671 5937607767849278266889507)
    ·
      refine ⟨8906411651773917400334261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937607767849278266889507 8906411651773917400334261)
      ·
        refine ⟨834976092353804756281337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8906411651773917400334261 834976092353804756281337)
        ·
          refine ⟨626232069265353567211003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834976092353804756281337 626232069265353567211003)
          ·
            refine ⟨939348103898030350816505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626232069265353567211003 939348103898030350816505)
            ·
              refine ⟨704511077923522763112379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939348103898030350816505 704511077923522763112379)
              ·
                refine ⟨1056766616885284144668569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704511077923522763112379 1056766616885284144668569)
                ·
                  refine ⟨792574962663963108501427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056766616885284144668569 792574962663963108501427)
                  ·
                    refine ⟨1188862443995944662752141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 792574962663963108501427 1188862443995944662752141)
                    ·
                      refine ⟨445823416498479248532053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1188862443995944662752141 445823416498479248532053)
                      ·
                        rfl

theorem cell23_868238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_868238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868238 prefixEnd_868238 := by exact prefixLift 868238
  have htrace : WordTrace (prefixWord ++ tailWord_868238) baseStart_868238 baseEnd_868238 := by
    simpa [prefixWord, tailWord_868238, baseEnd_868238] using wordTrace_append hprefix tailTrace_868238
  have hstable : (prefixWord ++ tailWord_868238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868238).length < 2 ^ (prefixWord ++ tailWord_868238).sum := by decide
  have hdescent : baseEnd_868238 < baseStart_868238 := by decide
  rcases family_descends (prefixWord ++ tailWord_868238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868244 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_868244 : Nat := 118140960795 + 868244 * 2 ^ 59
def prefixEnd_868244 : Nat := 4983230072969 + 3 ^ 40 * 868244 * 2
def baseEnd_868244 : Nat := 445826497382406225057025

theorem tailTrace_868244 : CollatzResearch.WordTrace tailWord_868244 prefixEnd_868244 445826497382406225057025 := by
  unfold tailWord_868244
  simp only [CollatzResearch.WordTrace]
  refine ⟨15833730133253873557397893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21111640177671831409863857 15833730133253873557397893)
  ·
    refine ⟨2968824399985101292012105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15833730133253873557397893 2968824399985101292012105)
    ·
      refine ⟨2226618299988825969009079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968824399985101292012105 2226618299988825969009079)
      ·
        refine ⟨3339927449983238953513619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226618299988825969009079 3339927449983238953513619)
        ·
          refine ⟨5009891174974858430270429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339927449983238953513619 5009891174974858430270429)
          ·
            refine ⟨1878709190615571911351411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5009891174974858430270429 1878709190615571911351411)
            ·
              refine ⟨2818063785923357867027117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878709190615571911351411 2818063785923357867027117)
              ·
                refine ⟨1056773919721259200135169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2818063785923357867027117 1056773919721259200135169)
                ·
                  refine ⟨792580439790944400101377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1056773919721259200135169 792580439790944400101377)
                  ·
                    refine ⟨594435329843208300076033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792580439790944400101377 594435329843208300076033)
                    ·
                      refine ⟨445826497382406225057025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594435329843208300076033 445826497382406225057025)
                      ·
                        rfl

theorem cell23_868244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_868244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868244 prefixEnd_868244 := by exact prefixLift 868244
  have htrace : WordTrace (prefixWord ++ tailWord_868244) baseStart_868244 baseEnd_868244 := by
    simpa [prefixWord, tailWord_868244, baseEnd_868244] using wordTrace_append hprefix tailTrace_868244
  have hstable : (prefixWord ++ tailWord_868244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868244).length < 2 ^ (prefixWord ++ tailWord_868244).sum := by decide
  have hdescent : baseEnd_868244 < baseStart_868244 := by decide
  rcases family_descends (prefixWord ++ tailWord_868244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868256 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_868256 : Nat := 118140960795 + 868256 * 2 ^ 59
def prefixEnd_868256 : Nat := 4983230072969 + 3 ^ 40 * 868256 * 2
def baseEnd_868256 : Nat := 445832659150260178106969

theorem tailTrace_868256 : CollatzResearch.WordTrace tailWord_868256 prefixEnd_868256 445832659150260178106969 := by
  unfold tailWord_868256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15833948971232136582116311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21111931961642848776155081 15833948971232136582116311)
  ·
    refine ⟨23750923456848204873174467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15833948971232136582116311 23750923456848204873174467)
    ·
      refine ⟨35626385185272307309761701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23750923456848204873174467 35626385185272307309761701)
      ·
        refine ⟨6679947222238557620580319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35626385185272307309761701 6679947222238557620580319)
        ·
          refine ⟨10019920833357836430870479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679947222238557620580319 10019920833357836430870479)
          ·
            refine ⟨15029881250036754646305719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019920833357836430870479 15029881250036754646305719)
            ·
              refine ⟨22544821875055131969458579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15029881250036754646305719 22544821875055131969458579)
              ·
                refine ⟨33817232812582697954187869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22544821875055131969458579 33817232812582697954187869)
                ·
                  refine ⟨12681462304718511732820451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33817232812582697954187869 12681462304718511732820451)
                  ·
                    refine ⟨19022193457077767599230677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12681462304718511732820451 19022193457077767599230677)
                    ·
                      refine ⟨445832659150260178106969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19022193457077767599230677 445832659150260178106969)
                      ·
                        rfl

theorem cell23_868256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_868256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868256 prefixEnd_868256 := by exact prefixLift 868256
  have htrace : WordTrace (prefixWord ++ tailWord_868256) baseStart_868256 baseEnd_868256 := by
    simpa [prefixWord, tailWord_868256, baseEnd_868256] using wordTrace_append hprefix tailTrace_868256
  have hstable : (prefixWord ++ tailWord_868256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868256).length < 2 ^ (prefixWord ++ tailWord_868256).sum := by decide
  have hdescent : baseEnd_868256 < baseStart_868256 := by decide
  rcases family_descends (prefixWord ++ tailWord_868256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868273 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_868273 : Nat := 118140960795 + 868273 * 2 ^ 59
def prefixEnd_868273 : Nat := 4983230072969 + 3 ^ 40 * 868273 * 2
def baseEnd_868273 : Nat := 445841388321386611594391

theorem tailTrace_868273 : CollatzResearch.WordTrace tailWord_868273 prefixEnd_868273 445841388321386611594391 := by
  unfold tailWord_868273
  simp only [CollatzResearch.WordTrace]
  refine ⟨31668517983402685067601473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21112345322268456711734315 31668517983402685067601473)
  ·
    refine ⟨23751388487552013800701105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31668517983402685067601473 23751388487552013800701105)
    ·
      refine ⟨17813541365664010350525829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23751388487552013800701105 17813541365664010350525829)
      ·
        refine ⟨3340039006062001940723593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17813541365664010350525829 3340039006062001940723593)
        ·
          refine ⟨2505029254546501455542695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340039006062001940723593 2505029254546501455542695)
          ·
            refine ⟨3757543881819752183314043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505029254546501455542695 3757543881819752183314043)
            ·
              refine ⟨5636315822729628274971065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757543881819752183314043 5636315822729628274971065)
              ·
                refine ⟨4227236867047221206228299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636315822729628274971065 4227236867047221206228299)
                ·
                  refine ⟨6340855300570831809342449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227236867047221206228299 6340855300570831809342449)
                  ·
                    refine ⟨4755641475428123857006837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340855300570831809342449 4755641475428123857006837)
                    ·
                      refine ⟨445841388321386611594391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4755641475428123857006837 445841388321386611594391)
                      ·
                        rfl

theorem cell23_868273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_868273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868273 prefixEnd_868273 := by exact prefixLift 868273
  have htrace : WordTrace (prefixWord ++ tailWord_868273) baseStart_868273 baseEnd_868273 := by
    simpa [prefixWord, tailWord_868273, baseEnd_868273] using wordTrace_append hprefix tailTrace_868273
  have hstable : (prefixWord ++ tailWord_868273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868273).length < 2 ^ (prefixWord ++ tailWord_868273).sum := by decide
  have hdescent : baseEnd_868273 < baseStart_868273 := by decide
  rcases family_descends (prefixWord ++ tailWord_868273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868300 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_868300 : Nat := 118140960795 + 868300 * 2 ^ 59
def prefixEnd_868300 : Nat := 4983230072969 + 3 ^ 40 * 868300 * 2
def baseEnd_868300 : Nat := 445855252299058005956767

theorem tailTrace_868300 : CollatzResearch.WordTrace tailWord_868300 prefixEnd_868300 445855252299058005956767 := by
  unfold tailWord_868300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834751377152434339417177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21113001836203245785889569 15834751377152434339417177)
  ·
    refine ⟨11876063532864325754562883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15834751377152434339417177 11876063532864325754562883)
    ·
      refine ⟨17814095299296488631844325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876063532864325754562883 17814095299296488631844325)
      ·
        refine ⟨3340142868618091618470811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17814095299296488631844325 3340142868618091618470811)
        ·
          refine ⟨5010214302927137427706217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340142868618091618470811 5010214302927137427706217)
          ·
            refine ⟨3757660727195353070779663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5010214302927137427706217 3757660727195353070779663)
            ·
              refine ⟨5636491090793029606169495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757660727195353070779663 5636491090793029606169495)
              ·
                refine ⟨8454736636189544409254243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636491090793029606169495 8454736636189544409254243)
                ·
                  refine ⟨12682104954284316613881365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8454736636189544409254243 12682104954284316613881365)
                  ·
                    refine ⟨594473669732077341275689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12682104954284316613881365 594473669732077341275689)
                    ·
                      refine ⟨445855252299058005956767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594473669732077341275689 445855252299058005956767)
                      ·
                        rfl

theorem cell23_868300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_868300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868300 prefixEnd_868300 := by exact prefixLift 868300
  have htrace : WordTrace (prefixWord ++ tailWord_868300) baseStart_868300 baseEnd_868300 := by
    simpa [prefixWord, tailWord_868300, baseEnd_868300] using wordTrace_append hprefix tailTrace_868300
  have hstable : (prefixWord ++ tailWord_868300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868300).length < 2 ^ (prefixWord ++ tailWord_868300).sum := by decide
  have hdescent : baseEnd_868300 < baseStart_868300 := by decide
  rcases family_descends (prefixWord ++ tailWord_868300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868303 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_868303 : Nat := 118140960795 + 868303 * 2 ^ 59
def prefixEnd_868303 : Nat := 4983230072969 + 3 ^ 40 * 868303 * 2
def baseEnd_868303 : Nat := 445856792741021494219253

theorem tailTrace_868303 : CollatzResearch.WordTrace tailWord_868303 prefixEnd_868303 445856792741021494219253 := by
  unfold tailWord_868303
  simp only [CollatzResearch.WordTrace]
  refine ⟨31669612173294000191193563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21113074782196000127462375 31669612173294000191193563)
  ·
    refine ⟨47504418259941000286790345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31669612173294000191193563 47504418259941000286790345)
    ·
      refine ⟨35628313694955750215092759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47504418259941000286790345 35628313694955750215092759)
      ·
        refine ⟨53442470542433625322639139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35628313694955750215092759 53442470542433625322639139)
        ·
          refine ⟨80163705813650437983958709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53442470542433625322639139 80163705813650437983958709)
          ·
            refine ⟨7515347420029728560996129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80163705813650437983958709 7515347420029728560996129)
            ·
              refine ⟨5636510565022296420747097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7515347420029728560996129 5636510565022296420747097)
              ·
                refine ⟨4227382923766722315560323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636510565022296420747097 4227382923766722315560323)
                ·
                  refine ⟨6341074385650083473340485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227382923766722315560323 6341074385650083473340485)
                  ·
                    refine ⟨1188951447309390651251341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6341074385650083473340485 1188951447309390651251341)
                    ·
                      refine ⟨445856792741021494219253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1188951447309390651251341 445856792741021494219253)
                      ·
                        rfl

theorem cell23_868303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_868303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868303 prefixEnd_868303 := by exact prefixLift 868303
  have htrace : WordTrace (prefixWord ++ tailWord_868303) baseStart_868303 baseEnd_868303 := by
    simpa [prefixWord, tailWord_868303, baseEnd_868303] using wordTrace_append hprefix tailTrace_868303
  have hstable : (prefixWord ++ tailWord_868303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868303).length < 2 ^ (prefixWord ++ tailWord_868303).sum := by decide
  have hdescent : baseEnd_868303 < baseStart_868303 := by decide
  rcases family_descends (prefixWord ++ tailWord_868303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868360 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_868360 : Nat := 118140960795 + 868360 * 2 ^ 59
def prefixEnd_868360 : Nat := 4983230072969 + 3 ^ 40 * 868360 * 2
def baseEnd_868360 : Nat := 445886061138327771206491

theorem tailTrace_868360 : CollatzResearch.WordTrace tailWord_868360 prefixEnd_868360 445886061138327771206491 := by
  unfold tailWord_868360
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835845567043749463009267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21114460756058332617345689 15835845567043749463009267)
  ·
    refine ⟨23753768350565624194513901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15835845567043749463009267 23753768350565624194513901)
    ·
      refine ⟨8907663131462109072942713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23753768350565624194513901 8907663131462109072942713)
      ·
        refine ⟨6680747348596581804707035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8907663131462109072942713 6680747348596581804707035)
        ·
          refine ⟨10021121022894872707060553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680747348596581804707035 10021121022894872707060553)
          ·
            refine ⟨7515840767171154530295415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10021121022894872707060553 7515840767171154530295415)
            ·
              refine ⟨11273761150756731795443123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7515840767171154530295415 11273761150756731795443123)
              ·
                refine ⟨16910641726135097693164685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11273761150756731795443123 16910641726135097693164685)
                ·
                  refine ⟨6341490647300661634936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16910641726135097693164685 6341490647300661634936757)
                  ·
                    refine ⟨594514748184437028275321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6341490647300661634936757 594514748184437028275321)
                    ·
                      refine ⟨445886061138327771206491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594514748184437028275321 445886061138327771206491)
                      ·
                        rfl

theorem cell23_868360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_868360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868360 prefixEnd_868360 := by exact prefixLift 868360
  have htrace : WordTrace (prefixWord ++ tailWord_868360) baseStart_868360 baseEnd_868360 := by
    simpa [prefixWord, tailWord_868360, baseEnd_868360] using wordTrace_append hprefix tailTrace_868360
  have hstable : (prefixWord ++ tailWord_868360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868360).length < 2 ^ (prefixWord ++ tailWord_868360).sum := by decide
  have hdescent : baseEnd_868360 < baseStart_868360 := by decide
  rcases family_descends (prefixWord ++ tailWord_868360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868383 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 3, 6]
def baseStart_868383 : Nat := 118140960795 + 868383 * 2 ^ 59
def prefixEnd_868383 : Nat := 4983230072969 + 3 ^ 40 * 868383 * 2
def baseEnd_868383 : Nat := 148632623731127060406295

theorem tailTrace_868383 : CollatzResearch.WordTrace tailWord_868383 prefixEnd_868383 148632623731127060406295 := by
  unfold tailWord_868383
  simp only [CollatzResearch.WordTrace]
  refine ⟨31672530013004173854105803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21115020008669449236070535 31672530013004173854105803)
  ·
    refine ⟨47508795019506260781158705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31672530013004173854105803 47508795019506260781158705)
    ·
      refine ⟨35631596264629695585869029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47508795019506260781158705 35631596264629695585869029)
      ·
        refine ⟨6680924299618067922350443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35631596264629695585869029 6680924299618067922350443)
        ·
          refine ⟨10021386449427101883525665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680924299618067922350443 10021386449427101883525665)
          ·
            refine ⟨7516039837070326412644249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10021386449427101883525665 7516039837070326412644249)
            ·
              refine ⟨5637029877802744809483187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7516039837070326412644249 5637029877802744809483187)
              ·
                refine ⟨8455544816704117214224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637029877802744809483187 8455544816704117214224781)
                ·
                  refine ⟨3170829306264043955334293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8455544816704117214224781 3170829306264043955334293)
                  ·
                    refine ⟨148632623731127060406295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3170829306264043955334293 148632623731127060406295)
                    ·
                      rfl

theorem cell23_868383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_868383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868383 prefixEnd_868383 := by exact prefixLift 868383
  have htrace : WordTrace (prefixWord ++ tailWord_868383) baseStart_868383 baseEnd_868383 := by
    simpa [prefixWord, tailWord_868383, baseEnd_868383] using wordTrace_append hprefix tailTrace_868383
  have hstable : (prefixWord ++ tailWord_868383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868383).length < 2 ^ (prefixWord ++ tailWord_868383).sum := by decide
  have hdescent : baseEnd_868383 < baseStart_868383 := by decide
  rcases family_descends (prefixWord ++ tailWord_868383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868393 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_868393 : Nat := 118140960795 + 868393 * 2 ^ 59
def prefixEnd_868393 : Nat := 4983230072969 + 3 ^ 40 * 868393 * 2
def baseEnd_868393 : Nat := 445903005999926142093839

theorem tailTrace_868393 : CollatzResearch.WordTrace tailWord_868393 prefixEnd_868393 445903005999926142093839 := by
  unfold tailWord_868393
  simp only [CollatzResearch.WordTrace]
  refine ⟨31672894742967945561969833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21115263161978630374646555 31672894742967945561969833)
  ·
    refine ⟨23754671057225959171477375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31672894742967945561969833 23754671057225959171477375)
    ·
      refine ⟨35632006585838938757216063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23754671057225959171477375 35632006585838938757216063)
      ·
        refine ⟨53448009878758408135824095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35632006585838938757216063 53448009878758408135824095)
        ·
          refine ⟨80172014818137612203736143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53448009878758408135824095 80172014818137612203736143)
          ·
            refine ⟨120258022227206418305604215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80172014818137612203736143 120258022227206418305604215)
            ·
              refine ⟨180387033340809627458406323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120258022227206418305604215 180387033340809627458406323)
              ·
                refine ⟨270580550011214441187609485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180387033340809627458406323 270580550011214441187609485)
                ·
                  refine ⟨101467706254205415445353557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270580550011214441187609485 101467706254205415445353557)
                  ·
                    refine ⟨1189074682666469712250237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101467706254205415445353557 1189074682666469712250237)
                    ·
                      refine ⟨445903005999926142093839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189074682666469712250237 445903005999926142093839)
                      ·
                        rfl

theorem cell23_868393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_868393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868393 prefixEnd_868393 := by exact prefixLift 868393
  have htrace : WordTrace (prefixWord ++ tailWord_868393) baseStart_868393 baseEnd_868393 := by
    simpa [prefixWord, tailWord_868393, baseEnd_868393] using wordTrace_append hprefix tailTrace_868393
  have hstable : (prefixWord ++ tailWord_868393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868393).length < 2 ^ (prefixWord ++ tailWord_868393).sum := by decide
  have hdescent : baseEnd_868393 < baseStart_868393 := by decide
  rcases family_descends (prefixWord ++ tailWord_868393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868394 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_868394 : Nat := 118140960795 + 868394 * 2 ^ 59
def prefixEnd_868394 : Nat := 4983230072969 + 3 ^ 40 * 868394 * 2
def baseEnd_868394 : Nat := 445903519480580638181335

theorem tailTrace_868394 : CollatzResearch.WordTrace tailWord_868394 prefixEnd_868394 445903519480580638181335 := by
  unfold tailWord_868394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918232803991080683189059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21115287477309548488504157 7918232803991080683189059)
  ·
    refine ⟨11877349205986621024783589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918232803991080683189059 11877349205986621024783589)
    ·
      refine ⟨2227002976122491442146923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11877349205986621024783589 2227002976122491442146923)
      ·
        refine ⟨3340504464183737163220385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227002976122491442146923 3340504464183737163220385)
        ·
          refine ⟨2505378348137802872415289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340504464183737163220385 2505378348137802872415289)
          ·
            refine ⟨1879033761103352154311467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505378348137802872415289 1879033761103352154311467)
            ·
              refine ⟨2818550641655028231467201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879033761103352154311467 2818550641655028231467201)
              ·
                refine ⟨2113912981241271173600401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818550641655028231467201 2113912981241271173600401)
                ·
                  refine ⟨1585434735930953380200301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2113912981241271173600401 1585434735930953380200301)
                  ·
                    refine ⟨594538025974107517575113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1585434735930953380200301 594538025974107517575113)
                    ·
                      refine ⟨445903519480580638181335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594538025974107517575113 445903519480580638181335)
                      ·
                        rfl

theorem cell23_868394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_868394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868394 prefixEnd_868394 := by exact prefixLift 868394
  have htrace : WordTrace (prefixWord ++ tailWord_868394) baseStart_868394 baseEnd_868394 := by
    simpa [prefixWord, tailWord_868394, baseEnd_868394] using wordTrace_append hprefix tailTrace_868394
  have hstable : (prefixWord ++ tailWord_868394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868394).length < 2 ^ (prefixWord ++ tailWord_868394).sum := by decide
  have hdescent : baseEnd_868394 < baseStart_868394 := by decide
  rcases family_descends (prefixWord ++ tailWord_868394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868400 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_868400 : Nat := 118140960795 + 868400 * 2 ^ 59
def prefixEnd_868400 : Nat := 4983230072969 + 3 ^ 40 * 868400 * 2
def baseEnd_868400 : Nat := 148635533454835871568769

theorem tailTrace_868400 : CollatzResearch.WordTrace tailWord_868400 prefixEnd_868400 148635533454835871568769 := by
  unfold tailWord_868400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836575026971292878737327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21115433369295057171649769 15836575026971292878737327)
  ·
    refine ⟨23754862540456939318105991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15836575026971292878737327 23754862540456939318105991)
    ·
      refine ⟨35632293810685408977158987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23754862540456939318105991 35632293810685408977158987)
      ·
        refine ⟨53448440716028113465738481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35632293810685408977158987 53448440716028113465738481)
        ·
          refine ⟨40086330537021085099303861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53448440716028113465738481 40086330537021085099303861)
          ·
            refine ⟨3758093487845726728059737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40086330537021085099303861 3758093487845726728059737)
            ·
              refine ⟨2818570115884295046044803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3758093487845726728059737 2818570115884295046044803)
              ·
                refine ⟨4227855173826442569067205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818570115884295046044803 4227855173826442569067205)
                ·
                  refine ⟨792722845092457981700101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4227855173826442569067205 792722845092457981700101)
                  ·
                    refine ⟨148635533454835871568769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792722845092457981700101 148635533454835871568769)
                    ·
                      rfl

theorem cell23_868400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_868400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868400 prefixEnd_868400 := by exact prefixLift 868400
  have htrace : WordTrace (prefixWord ++ tailWord_868400) baseStart_868400 baseEnd_868400 := by
    simpa [prefixWord, tailWord_868400, baseEnd_868400] using wordTrace_append hprefix tailTrace_868400
  have hstable : (prefixWord ++ tailWord_868400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868400).length < 2 ^ (prefixWord ++ tailWord_868400).sum := by decide
  have hdescent : baseEnd_868400 < baseStart_868400 := by decide
  rcases family_descends (prefixWord ++ tailWord_868400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868401 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 1, 1, 3]
def baseStart_868401 : Nat := 118140960795 + 868401 * 2 ^ 59
def prefixEnd_868401 : Nat := 4983230072969 + 3 ^ 40 * 868401 * 2
def baseEnd_868401 : Nat := 445907113845162110793803

theorem tailTrace_868401 : CollatzResearch.WordTrace tailWord_868401 prefixEnd_868401 445907113845162110793803 := by
  unfold tailWord_868401
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673186526938962928261057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21115457684625975285507371 31673186526938962928261057)
  ·
    refine ⟨23754889895204222196195793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31673186526938962928261057 23754889895204222196195793)
    ·
      refine ⟨17816167421403166647146845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23754889895204222196195793 17816167421403166647146845)
      ·
        refine ⟨6681062783026187492680067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17816167421403166647146845 6681062783026187492680067)
        ·
          refine ⟨10021594174539281239020101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681062783026187492680067 10021594174539281239020101)
          ·
            refine ⟨1879048907726115232316269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10021594174539281239020101 1879048907726115232316269)
            ·
              refine ⟨704643340397293212118601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1879048907726115232316269 704643340397293212118601)
              ·
                refine ⟨528482505297969909088951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704643340397293212118601 528482505297969909088951)
                ·
                  refine ⟨792723757946954863633427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528482505297969909088951 792723757946954863633427)
                  ·
                    refine ⟨1189085636920432295450141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 792723757946954863633427 1189085636920432295450141)
                    ·
                      refine ⟨445907113845162110793803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189085636920432295450141 445907113845162110793803)
                      ·
                        rfl

theorem cell23_868401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_868401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868401 prefixEnd_868401 := by exact prefixLift 868401
  have htrace : WordTrace (prefixWord ++ tailWord_868401) baseStart_868401 baseEnd_868401 := by
    simpa [prefixWord, tailWord_868401, baseEnd_868401] using wordTrace_append hprefix tailTrace_868401
  have hstable : (prefixWord ++ tailWord_868401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868401).length < 2 ^ (prefixWord ++ tailWord_868401).sum := by decide
  have hdescent : baseEnd_868401 < baseStart_868401 := by decide
  rcases family_descends (prefixWord ++ tailWord_868401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868403 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_868403 : Nat := 118140960795 + 868403 * 2 ^ 59
def prefixEnd_868403 : Nat := 4983230072969 + 3 ^ 40 * 868403 * 2
def baseEnd_868403 : Nat := 445908140806471102968793

theorem tailTrace_868403 : CollatzResearch.WordTrace tailWord_868403 prefixEnd_868403 445908140806471102968793 := by
  unfold tailWord_868403
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673259472931717269833863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21115506315287811513222575 31673259472931717269833863)
  ·
    refine ⟨47509889209397575904750795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31673259472931717269833863 47509889209397575904750795)
    ·
      refine ⟨71264833814096363857126193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47509889209397575904750795 71264833814096363857126193)
      ·
        refine ⟨53448625360572272892844645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71264833814096363857126193 53448625360572272892844645)
        ·
          refine ⟨10021617255107301167408371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53448625360572272892844645 10021617255107301167408371)
          ·
            refine ⟨15032425882660951751112557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021617255107301167408371 15032425882660951751112557)
            ·
              refine ⟨5637159705997856906667209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15032425882660951751112557 5637159705997856906667209)
              ·
                refine ⟨4227869779498392680000407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5637159705997856906667209 4227869779498392680000407)
                ·
                  refine ⟨6341804669247589020000611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227869779498392680000407 6341804669247589020000611)
                  ·
                    refine ⟨9512707003871383530000917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6341804669247589020000611 9512707003871383530000917)
                    ·
                      refine ⟨445908140806471102968793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9512707003871383530000917 445908140806471102968793)
                      ·
                        rfl

theorem cell23_868403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_868403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868403 prefixEnd_868403 := by exact prefixLift 868403
  have htrace : WordTrace (prefixWord ++ tailWord_868403) baseStart_868403 baseEnd_868403 := by
    simpa [prefixWord, tailWord_868403, baseEnd_868403] using wordTrace_append hprefix tailTrace_868403
  have hstable : (prefixWord ++ tailWord_868403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868403).length < 2 ^ (prefixWord ++ tailWord_868403).sum := by decide
  have hdescent : baseEnd_868403 < baseStart_868403 := by decide
  rcases family_descends (prefixWord ++ tailWord_868403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868410 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_868410 : Nat := 118140960795 + 868410 * 2 ^ 59
def prefixEnd_868410 : Nat := 4983230072969 + 3 ^ 40 * 868410 * 2
def baseEnd_868410 : Nat := 445911735171052575581261

theorem tailTrace_868410 : CollatzResearch.WordTrace tailWord_868410 prefixEnd_868410 445911735171052575581261 := by
  unfold tailWord_868410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918378695976589366334671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21115676522604238310225789 7918378695976589366334671)
  ·
    refine ⟨11877568043964884049502007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918378695976589366334671 11877568043964884049502007)
    ·
      refine ⟨17816352065947326074253011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11877568043964884049502007 17816352065947326074253011)
      ·
        refine ⟨26724528098920989111379517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17816352065947326074253011 26724528098920989111379517)
        ·
          refine ⟨10021698037095370916767319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26724528098920989111379517 10021698037095370916767319)
          ·
            refine ⟨15032547055643056375150979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021698037095370916767319 15032547055643056375150979)
            ·
              refine ⟨22548820583464584562726469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15032547055643056375150979 22548820583464584562726469)
              ·
                refine ⟨4227903859399609605511213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22548820583464584562726469 4227903859399609605511213)
                ·
                  refine ⟨1585463947274853602066705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4227903859399609605511213 1585463947274853602066705)
                  ·
                    refine ⟨1189097960456140201550029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585463947274853602066705 1189097960456140201550029)
                    ·
                      refine ⟨445911735171052575581261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189097960456140201550029 445911735171052575581261)
                      ·
                        rfl

theorem cell23_868410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_868410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868410 prefixEnd_868410 := by exact prefixLift 868410
  have htrace : WordTrace (prefixWord ++ tailWord_868410) baseStart_868410 baseEnd_868410 := by
    simpa [prefixWord, tailWord_868410, baseEnd_868410] using wordTrace_append hprefix tailTrace_868410
  have hstable : (prefixWord ++ tailWord_868410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868410).length < 2 ^ (prefixWord ++ tailWord_868410).sum := by decide
  have hdescent : baseEnd_868410 < baseStart_868410 := by decide
  rcases family_descends (prefixWord ++ tailWord_868410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868440 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_868440 : Nat := 118140960795 + 868440 * 2 ^ 59
def prefixEnd_868440 : Nat := 4983230072969 + 3 ^ 40 * 868440 * 2
def baseEnd_868440 : Nat := 445927139590687458206123

theorem tailTrace_868440 : CollatzResearch.WordTrace tailWord_868440 prefixEnd_868440 445927139590687458206123 := by
  unfold tailWord_868440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15837304486898836294465387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21116405982531781725953849 15837304486898836294465387)
  ·
    refine ⟨23755956730348254441698081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15837304486898836294465387 23755956730348254441698081)
    ·
      refine ⟨17816967547761190831273561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23755956730348254441698081 17816967547761190831273561)
      ·
        refine ⟨13362725660820893123455171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17816967547761190831273561 13362725660820893123455171)
        ·
          refine ⟨20044088491231339685182757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362725660820893123455171 20044088491231339685182757)
          ·
            refine ⟨3758266592105876190971767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20044088491231339685182757 3758266592105876190971767)
            ·
              refine ⟨5637399888158814286457651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758266592105876190971767 5637399888158814286457651)
              ·
                refine ⟨8456099832238221429686477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637399888158814286457651 8456099832238221429686477)
                ·
                  refine ⟨3171037437089333036132429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8456099832238221429686477 3171037437089333036132429)
                  ·
                    refine ⟨1189139038908499888549661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171037437089333036132429 1189139038908499888549661)
                    ·
                      refine ⟨445927139590687458206123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189139038908499888549661 445927139590687458206123)
                      ·
                        rfl

theorem cell23_868440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_868440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868440 prefixEnd_868440 := by exact prefixLift 868440
  have htrace : WordTrace (prefixWord ++ tailWord_868440) baseStart_868440 baseEnd_868440 := by
    simpa [prefixWord, tailWord_868440, baseEnd_868440] using wordTrace_append hprefix tailTrace_868440
  have hstable : (prefixWord ++ tailWord_868440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868440).length < 2 ^ (prefixWord ++ tailWord_868440).sum := by decide
  have hdescent : baseEnd_868440 < baseStart_868440 := by decide
  rcases family_descends (prefixWord ++ tailWord_868440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868458 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_868458 : Nat := 118140960795 + 868458 * 2 ^ 59
def prefixEnd_868458 : Nat := 4983230072969 + 3 ^ 40 * 868458 * 2
def baseEnd_868458 : Nat := 445936382242468387781041

theorem tailTrace_868458 : CollatzResearch.WordTrace tailWord_868458 prefixEnd_868458 445936382242468387781041 := by
  unfold tailWord_868458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918816371933115415771507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21116843658488307775390685 7918816371933115415771507)
  ·
    refine ⟨11878224557899673123657261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918816371933115415771507 11878224557899673123657261)
    ·
      refine ⟨4454334209212377421371473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11878224557899673123657261 4454334209212377421371473)
      ·
        refine ⟨3340750656909283066028605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454334209212377421371473 3340750656909283066028605)
        ·
          refine ⟨1252781496340981149760727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3340750656909283066028605 1252781496340981149760727)
          ·
            refine ⟨1879172244511471724641091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252781496340981149760727 1879172244511471724641091)
            ·
              refine ⟨2818758366767207586961637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879172244511471724641091 2818758366767207586961637)
              ·
                refine ⟨528517193768851422555307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2818758366767207586961637 528517193768851422555307)
                ·
                  refine ⟨792775790653277133832961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528517193768851422555307 792775790653277133832961)
                  ·
                    refine ⟨594581842989957850374721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 792775790653277133832961 594581842989957850374721)
                    ·
                      refine ⟨445936382242468387781041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594581842989957850374721 445936382242468387781041)
                      ·
                        rfl

theorem cell23_868458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_868458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868458 prefixEnd_868458 := by exact prefixLift 868458
  have htrace : WordTrace (prefixWord ++ tailWord_868458) baseStart_868458 baseEnd_868458 := by
    simpa [prefixWord, tailWord_868458, baseEnd_868458] using wordTrace_append hprefix tailTrace_868458
  have hstable : (prefixWord ++ tailWord_868458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868458).length < 2 ^ (prefixWord ++ tailWord_868458).sum := by decide
  have hdescent : baseEnd_868458 < baseStart_868458 := by decide
  rcases family_descends (prefixWord ++ tailWord_868458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868484 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_868484 : Nat := 118140960795 + 868484 * 2 ^ 59
def prefixEnd_868484 : Nat := 4983230072969 + 3 ^ 40 * 868484 * 2
def baseEnd_868484 : Nat := 445949732739485286055921

theorem tailTrace_868484 : CollatzResearch.WordTrace tailWord_868484 prefixEnd_868484 445949732739485286055921 := by
  unfold tailWord_868484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15838106892819134051766253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21117475857092178735688337 15838106892819134051766253)
  ·
    refine ⟨5939290084807175269412345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15838106892819134051766253 5939290084807175269412345)
    ·
      refine ⟨4454467563605381452059259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5939290084807175269412345 4454467563605381452059259)
      ·
        refine ⟨6681701345408072178088889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4454467563605381452059259 6681701345408072178088889)
        ·
          refine ⟨5011276009056054133566667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6681701345408072178088889 5011276009056054133566667)
          ·
            refine ⟨7516914013584081200350001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011276009056054133566667 7516914013584081200350001)
            ·
              refine ⟨5637685510188060900262501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7516914013584081200350001 5637685510188060900262501)
              ·
                refine ⟨1057066033160261418799219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5637685510188060900262501 1057066033160261418799219)
                ·
                  refine ⟨1585599049740392128198829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057066033160261418799219 1585599049740392128198829)
                  ·
                    refine ⟨594599643652647048074561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1585599049740392128198829 594599643652647048074561)
                    ·
                      refine ⟨445949732739485286055921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594599643652647048074561 445949732739485286055921)
                      ·
                        rfl

theorem cell23_868484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_868484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868484 prefixEnd_868484 := by exact prefixLift 868484
  have htrace : WordTrace (prefixWord ++ tailWord_868484) baseStart_868484 baseEnd_868484 := by
    simpa [prefixWord, tailWord_868484, baseEnd_868484] using wordTrace_append hprefix tailTrace_868484
  have hstable : (prefixWord ++ tailWord_868484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868484).length < 2 ^ (prefixWord ++ tailWord_868484).sum := by decide
  have hdescent : baseEnd_868484 < baseStart_868484 := by decide
  rcases family_descends (prefixWord ++ tailWord_868484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868502 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_868502 : Nat := 118140960795 + 868502 * 2 ^ 59
def prefixEnd_868502 : Nat := 4983230072969 + 3 ^ 40 * 868502 * 2
def baseEnd_868502 : Nat := 148652991797088738543613

theorem tailTrace_868502 : CollatzResearch.WordTrace tailWord_868502 prefixEnd_868502 148652991797088738543613 := by
  unfold tailWord_868502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979804393723316073605485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21117913533048704785125173 1979804393723316073605485)
  ·
    refine ⟨742426647646243527602057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1979804393723316073605485 742426647646243527602057)
    ·
      refine ⟨556819985734682645701543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742426647646243527602057 556819985734682645701543)
      ·
        refine ⟨835229978602023968552315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556819985734682645701543 835229978602023968552315)
        ·
          refine ⟨1252844967903035952828473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835229978602023968552315 1252844967903035952828473)
          ·
            refine ⟨939633725927276964621355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252844967903035952828473 939633725927276964621355)
            ·
              refine ⟨1409450588890915446932033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939633725927276964621355 1409450588890915446932033)
              ·
                refine ⟨1057087941668186585199025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409450588890915446932033 1057087941668186585199025)
                ·
                  refine ⟨792815956251139938899269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057087941668186585199025 792815956251139938899269)
                  ·
                    refine ⟨148652991797088738543613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792815956251139938899269 148652991797088738543613)
                    ·
                      rfl

theorem cell23_868502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_868502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868502 prefixEnd_868502 := by exact prefixLift 868502
  have htrace : WordTrace (prefixWord ++ tailWord_868502) baseStart_868502 baseEnd_868502 := by
    simpa [prefixWord, tailWord_868502, baseEnd_868502] using wordTrace_append hprefix tailTrace_868502
  have hstable : (prefixWord ++ tailWord_868502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868502).length < 2 ^ (prefixWord ++ tailWord_868502).sum := by decide
  have hdescent : baseEnd_868502 < baseStart_868502 := by decide
  rcases family_descends (prefixWord ++ tailWord_868502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868587 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 6, 2]
def baseStart_868587 : Nat := 118140960795 + 868587 * 2 ^ 59
def prefixEnd_868587 : Nat := 4983230072969 + 3 ^ 40 * 868587 * 2
def baseEnd_868587 : Nat := 446002621246898383067947

theorem tailTrace_868587 : CollatzResearch.WordTrace tailWord_868587 prefixEnd_868587 446002621246898383067947 := by
  unfold tailWord_868587
  simp only [CollatzResearch.WordTrace]
  refine ⟨31679970504265116694532015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21119980336176744463021343 31679970504265116694532015)
  ·
    refine ⟨47519955756397675041798023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31679970504265116694532015 47519955756397675041798023)
    ·
      refine ⟨71279933634596512562697035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47519955756397675041798023 71279933634596512562697035)
      ·
        refine ⟨106919900451894768844045553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71279933634596512562697035 106919900451894768844045553)
        ·
          refine ⟨80189925338921076633034165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106919900451894768844045553 80189925338921076633034165)
          ·
            refine ⟨7517805500523850934346953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80189925338921076633034165 7517805500523850934346953)
            ·
              refine ⟨5638354125392888200760215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7517805500523850934346953 5638354125392888200760215)
              ·
                refine ⟨8457531188089332301140323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638354125392888200760215 8457531188089332301140323)
                ·
                  refine ⟨12686296782133998451710485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8457531188089332301140323 12686296782133998451710485)
                  ·
                    refine ⟨594670161662531177423929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12686296782133998451710485 594670161662531177423929)
                    ·
                      refine ⟨446002621246898383067947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594670161662531177423929 446002621246898383067947)
                      ·
                        rfl

theorem cell23_868587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6, 2].length) (baseStart_868587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868587 prefixEnd_868587 := by exact prefixLift 868587
  have htrace : WordTrace (prefixWord ++ tailWord_868587) baseStart_868587 baseEnd_868587 := by
    simpa [prefixWord, tailWord_868587, baseEnd_868587] using wordTrace_append hprefix tailTrace_868587
  have hstable : (prefixWord ++ tailWord_868587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868587).length < 2 ^ (prefixWord ++ tailWord_868587).sum := by decide
  have hdescent : baseEnd_868587 < baseStart_868587 := by decide
  rcases family_descends (prefixWord ++ tailWord_868587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868600 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_868600 : Nat := 118140960795 + 868600 * 2 ^ 59
def prefixEnd_868600 : Nat := 4983230072969 + 3 ^ 40 * 868600 * 2
def baseEnd_868600 : Nat := 446009296495406832205387

theorem tailTrace_868600 : CollatzResearch.WordTrace tailWord_868600 prefixEnd_868600 446009296495406832205387 := by
  unfold tailWord_868600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15840222326609009957377627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21120296435478679943170169 15840222326609009957377627)
  ·
    refine ⟨23760333489913514936066441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15840222326609009957377627 23760333489913514936066441)
    ·
      refine ⟨17820250117435136202049831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23760333489913514936066441 17820250117435136202049831)
      ·
        refine ⟨26730375176152704303074747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17820250117435136202049831 26730375176152704303074747)
        ·
          refine ⟨40095562764229056454612121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26730375176152704303074747 40095562764229056454612121)
          ·
            refine ⟨30071672073171792340959091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40095562764229056454612121 30071672073171792340959091)
            ·
              refine ⟨45107508109757688511438637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30071672073171792340959091 45107508109757688511438637)
              ·
                refine ⟨16915315541159133191789489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45107508109757688511438637 16915315541159133191789489)
                ·
                  refine ⟨12686486655869349893842117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16915315541159133191789489 12686486655869349893842117)
                  ·
                    refine ⟨2378716247975503105095397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12686486655869349893842117 2378716247975503105095397)
                    ·
                      refine ⟨446009296495406832205387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2378716247975503105095397 446009296495406832205387)
                      ·
                        rfl

theorem cell23_868600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_868600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868600 prefixEnd_868600 := by exact prefixLift 868600
  have htrace : WordTrace (prefixWord ++ tailWord_868600) baseStart_868600 baseEnd_868600 := by
    simpa [prefixWord, tailWord_868600, baseEnd_868600] using wordTrace_append hprefix tailTrace_868600
  have hstable : (prefixWord ++ tailWord_868600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868600).length < 2 ^ (prefixWord ++ tailWord_868600).sum := by decide
  have hdescent : baseEnd_868600 < baseStart_868600 := by decide
  rcases family_descends (prefixWord ++ tailWord_868600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868604 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_868604 : Nat := 118140960795 + 868604 * 2 ^ 59
def prefixEnd_868604 : Nat := 4983230072969 + 3 ^ 40 * 868604 * 2
def baseEnd_868604 : Nat := 446011350418024816555369

theorem tailTrace_868604 : CollatzResearch.WordTrace tailWord_868604 prefixEnd_868604 446011350418024816555369 := by
  unfold tailWord_868604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15840295272601764298950433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21120393696802352398600577 15840295272601764298950433)
  ·
    refine ⟨11880221454451323224212825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15840295272601764298950433 11880221454451323224212825)
    ·
      refine ⟨8910166090838492418159619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11880221454451323224212825 8910166090838492418159619)
      ·
        refine ⟨13365249136257738627239429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910166090838492418159619 13365249136257738627239429)
        ·
          refine ⟨2505984213048325992607393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13365249136257738627239429 2505984213048325992607393)
          ·
            refine ⟨1879488159786244494455545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505984213048325992607393 1879488159786244494455545)
            ·
              refine ⟨1409616119839683370841659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879488159786244494455545 1409616119839683370841659)
              ·
                refine ⟨2114424179759525056262489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409616119839683370841659 2114424179759525056262489)
                ·
                  refine ⟨1585818134819643792196867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2114424179759525056262489 1585818134819643792196867)
                  ·
                    refine ⟨2378727202229465688295301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1585818134819643792196867 2378727202229465688295301)
                    ·
                      refine ⟨446011350418024816555369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2378727202229465688295301 446011350418024816555369)
                      ·
                        rfl

theorem cell23_868604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_868604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868604 prefixEnd_868604 := by exact prefixLift 868604
  have htrace : WordTrace (prefixWord ++ tailWord_868604) baseStart_868604 baseEnd_868604 := by
    simpa [prefixWord, tailWord_868604, baseEnd_868604] using wordTrace_append hprefix tailTrace_868604
  have hstable : (prefixWord ++ tailWord_868604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868604).length < 2 ^ (prefixWord ++ tailWord_868604).sum := by decide
  have hdescent : baseEnd_868604 < baseStart_868604 := by decide
  rcases family_descends (prefixWord ++ tailWord_868604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868631 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 1, 4]
def baseStart_868631 : Nat := 118140960795 + 868631 * 2 ^ 59
def prefixEnd_868631 : Nat := 4983230072969 + 3 ^ 40 * 868631 * 2
def baseEnd_868631 : Nat := 148675071465232070305915

theorem tailTrace_868631 : CollatzResearch.WordTrace tailWord_868631 prefixEnd_868631 148675071465232070305915 := by
  unfold tailWord_868631
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681575316105712209133747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21121050210737141472755831 31681575316105712209133747)
  ·
    refine ⟨47522362974158568313700621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31681575316105712209133747 47522362974158568313700621)
    ·
      refine ⟨17820886115309463117637733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47522362974158568313700621 17820886115309463117637733)
      ·
        refine ⟨3341416146620524334557075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17820886115309463117637733 3341416146620524334557075)
        ·
          refine ⟨5012124219930786501835613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341416146620524334557075 5012124219930786501835613)
          ·
            refine ⟨1879546582474044938188355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5012124219930786501835613 1879546582474044938188355)
            ·
              refine ⟨2819319873711067407282533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879546582474044938188355 2819319873711067407282533)
              ·
                refine ⟨528622476320825138865475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2819319873711067407282533 528622476320825138865475)
                ·
                  refine ⟨792933714481237708298213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528622476320825138865475 792933714481237708298213)
                  ·
                    refine ⟨148675071465232070305915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 792933714481237708298213 148675071465232070305915)
                    ·
                      rfl

theorem cell23_868631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_868631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868631 prefixEnd_868631 := by exact prefixLift 868631
  have htrace : WordTrace (prefixWord ++ tailWord_868631) baseStart_868631 baseEnd_868631 := by
    simpa [prefixWord, tailWord_868631, baseEnd_868631] using wordTrace_append hprefix tailTrace_868631
  have hstable : (prefixWord ++ tailWord_868631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868631).length < 2 ^ (prefixWord ++ tailWord_868631).sum := by decide
  have hdescent : baseEnd_868631 < baseStart_868631 := by decide
  rcases family_descends (prefixWord ++ tailWord_868631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868638 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_868638 : Nat := 118140960795 + 868638 * 2 ^ 59
def prefixEnd_868638 : Nat := 4983230072969 + 3 ^ 40 * 868638 * 2
def baseEnd_868638 : Nat := 446028808760277683530213

theorem tailTrace_868638 : CollatzResearch.WordTrace tailWord_868638 prefixEnd_868638 446028808760277683530213 := by
  unfold tailWord_868638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960228828385044050579821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21121220418053568269759045 3960228828385044050579821)
  ·
    refine ⟨1485085810644391518967433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3960228828385044050579821 1485085810644391518967433)
    ·
      refine ⟨1113814357983293639225575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485085810644391518967433 1113814357983293639225575)
      ·
        refine ⟨1670721536974940458838363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113814357983293639225575 1670721536974940458838363)
        ·
          refine ⟨2506082305462410688257545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670721536974940458838363 2506082305462410688257545)
          ·
            refine ⟨1879561729096808016193159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2506082305462410688257545 1879561729096808016193159)
            ·
              refine ⟨2819342593645212024289739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879561729096808016193159 2819342593645212024289739)
              ·
                refine ⟨4229013890467818036434609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819342593645212024289739 4229013890467818036434609)
                ·
                  refine ⟨3171760417850863527325957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229013890467818036434609 3171760417850863527325957)
                  ·
                    refine ⟨594705078347036911373617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3171760417850863527325957 594705078347036911373617)
                    ·
                      refine ⟨446028808760277683530213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594705078347036911373617 446028808760277683530213)
                      ·
                        rfl

theorem cell23_868638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_868638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868638 prefixEnd_868638 := by exact prefixLift 868638
  have htrace : WordTrace (prefixWord ++ tailWord_868638) baseStart_868638 baseEnd_868638 := by
    simpa [prefixWord, tailWord_868638, baseEnd_868638] using wordTrace_append hprefix tailTrace_868638
  have hstable : (prefixWord ++ tailWord_868638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868638).length < 2 ^ (prefixWord ++ tailWord_868638).sum := by decide
  have hdescent : baseEnd_868638 < baseStart_868638 := by decide
  rcases family_descends (prefixWord ++ tailWord_868638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868658 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_868658 : Nat := 118140960795 + 868658 * 2 ^ 59
def prefixEnd_868658 : Nat := 4983230072969 + 3 ^ 40 * 868658 * 2
def baseEnd_868658 : Nat := 446039078373367605280121

theorem tailTrace_868658 : CollatzResearch.WordTrace tailWord_868658 prefixEnd_868658 446039078373367605280121 := by
  unfold tailWord_868658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7920640021751973955091657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21121706724671930546911085 7920640021751973955091657)
  ·
    refine ⟨5940480016313980466318743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7920640021751973955091657 5940480016313980466318743)
    ·
      refine ⟨8910720024470970699478115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940480016313980466318743 8910720024470970699478115)
      ·
        refine ⟨13366080036706456049217173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910720024470970699478115 13366080036706456049217173)
        ·
          refine ⟨626535001720615127307055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13366080036706456049217173 626535001720615127307055)
          ·
            refine ⟨939802502580922690960583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626535001720615127307055 939802502580922690960583)
            ·
              refine ⟨1409703753871384036440875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939802502580922690960583 1409703753871384036440875)
              ·
                refine ⟨2114555630807076054661313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409703753871384036440875 2114555630807076054661313)
                ·
                  refine ⟨1585916723105307040995985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2114555630807076054661313 1585916723105307040995985)
                  ·
                    refine ⟨1189437542328980280746989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1585916723105307040995985 1189437542328980280746989)
                    ·
                      refine ⟨446039078373367605280121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189437542328980280746989 446039078373367605280121)
                      ·
                        rfl

theorem cell23_868658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_868658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868658 prefixEnd_868658 := by exact prefixLift 868658
  have htrace : WordTrace (prefixWord ++ tailWord_868658) baseStart_868658 baseEnd_868658 := by
    simpa [prefixWord, tailWord_868658, baseEnd_868658] using wordTrace_append hprefix tailTrace_868658
  have hstable : (prefixWord ++ tailWord_868658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868658).length < 2 ^ (prefixWord ++ tailWord_868658).sum := by decide
  have hdescent : baseEnd_868658 < baseStart_868658 := by decide
  rcases family_descends (prefixWord ++ tailWord_868658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868707 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_868707 : Nat := 118140960795 + 868707 * 2 ^ 59
def prefixEnd_868707 : Nat := 4983230072969 + 3 ^ 40 * 868707 * 2
def baseEnd_868707 : Nat := 446064238925437913567395

theorem tailTrace_868707 : CollatzResearch.WordTrace tailWord_868707 prefixEnd_868707 446064238925437913567395 := by
  unfold tailWord_868707
  simp only [CollatzResearch.WordTrace]
  refine ⟨31684347263830377188900375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21122898175886918125933583 31684347263830377188900375)
  ·
    refine ⟨47526520895745565783350563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31684347263830377188900375 47526520895745565783350563)
    ·
      refine ⟨71289781343618348675025845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47526520895745565783350563 71289781343618348675025845)
      ·
        refine ⟨6683417000964220188283673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71289781343618348675025845 6683417000964220188283673)
        ·
          refine ⟨5012562750723165141212755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6683417000964220188283673 5012562750723165141212755)
          ·
            refine ⟨7518844126084747711819133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012562750723165141212755 7518844126084747711819133)
            ·
              refine ⟨2819566547281780391932175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7518844126084747711819133 2819566547281780391932175)
              ·
                refine ⟨4229349820922670587898263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819566547281780391932175 4229349820922670587898263)
                ·
                  refine ⟨6344024731384005881847395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229349820922670587898263 6344024731384005881847395)
                  ·
                    refine ⟨9516037097076008822771093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344024731384005881847395 9516037097076008822771093)
                    ·
                      refine ⟨446064238925437913567395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9516037097076008822771093 446064238925437913567395)
                      ·
                        rfl

theorem cell23_868707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_868707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868707 prefixEnd_868707 := by exact prefixLift 868707
  have htrace : WordTrace (prefixWord ++ tailWord_868707) baseStart_868707 baseEnd_868707 := by
    simpa [prefixWord, tailWord_868707, baseEnd_868707] using wordTrace_append hprefix tailTrace_868707
  have hstable : (prefixWord ++ tailWord_868707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868707).length < 2 ^ (prefixWord ++ tailWord_868707).sum := by decide
  have hdescent : baseEnd_868707 < baseStart_868707 := by decide
  rcases family_descends (prefixWord ++ tailWord_868707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868711 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_868711 : Nat := 118140960795 + 868711 * 2 ^ 59
def prefixEnd_868711 : Nat := 4983230072969 + 3 ^ 40 * 868711 * 2
def baseEnd_868711 : Nat := 446066292848055897917377

theorem tailTrace_868711 : CollatzResearch.WordTrace tailWord_868711 prefixEnd_868711 446066292848055897917377 := by
  unfold tailWord_868711
  simp only [CollatzResearch.WordTrace]
  refine ⟨31684493155815885872045987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21122995437210590581363991 31684493155815885872045987)
  ·
    refine ⟨47526739733723828808068981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31684493155815885872045987 47526739733723828808068981)
    ·
      refine ⟨4455631850036608950756467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47526739733723828808068981 4455631850036608950756467)
      ·
        refine ⟨6683447775054913426134701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455631850036608950756467 6683447775054913426134701)
        ·
          refine ⟨2506292915645592534800513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6683447775054913426134701 2506292915645592534800513)
          ·
            refine ⟨1879719686734194401100385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2506292915645592534800513 1879719686734194401100385)
            ·
              refine ⟨1409789765050645800825289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1879719686734194401100385 1409789765050645800825289)
              ·
                refine ⟨1057342323787984350618967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409789765050645800825289 1057342323787984350618967)
                ·
                  refine ⟨1586013485681976525928451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057342323787984350618967 1586013485681976525928451)
                  ·
                    refine ⟨2379020228522964788892677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1586013485681976525928451 2379020228522964788892677)
                    ·
                      refine ⟨446066292848055897917377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2379020228522964788892677 446066292848055897917377)
                      ·
                        rfl

theorem cell23_868711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_868711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868711 prefixEnd_868711 := by exact prefixLift 868711
  have htrace : WordTrace (prefixWord ++ tailWord_868711) baseStart_868711 baseEnd_868711 := by
    simpa [prefixWord, tailWord_868711, baseEnd_868711] using wordTrace_append hprefix tailTrace_868711
  have hstable : (prefixWord ++ tailWord_868711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868711).length < 2 ^ (prefixWord ++ tailWord_868711).sum := by decide
  have hdescent : baseEnd_868711 < baseStart_868711 := by decide
  rcases family_descends (prefixWord ++ tailWord_868711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868717 : List Nat := [1, 5, 1, 1, 1, 2, 3, 9]
def baseStart_868717 : Nat := 118140960795 + 868717 * 2 ^ 59
def prefixEnd_868717 : Nat := 4983230072969 + 3 ^ 40 * 868717 * 2
def baseEnd_868717 : Nat := 16521087915999365720087

theorem tailTrace_868717 : CollatzResearch.WordTrace tailWord_868717 prefixEnd_868717 16521087915999365720087 := by
  unfold tailWord_868717
  simp only [CollatzResearch.WordTrace]
  refine ⟨31684711993794148896764405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21123141329196099264509603 31684711993794148896764405)
  ·
    refine ⟨2970441749418201459071663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31684711993794148896764405 2970441749418201459071663)
    ·
      refine ⟨4455662624127302188607495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970441749418201459071663 4455662624127302188607495)
      ·
        refine ⟨6683493936190953282911243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455662624127302188607495 6683493936190953282911243)
        ·
          refine ⟨10025240904286429924366865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6683493936190953282911243 10025240904286429924366865)
          ·
            refine ⟨7518930678214822443275149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10025240904286429924366865 7518930678214822443275149)
            ·
              refine ⟨2819599004330558416228181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7518930678214822443275149 2819599004330558416228181)
              ·
                refine ⟨16521087915999365720087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2819599004330558416228181 16521087915999365720087)
                ·
                  rfl

theorem cell23_868717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 9].length) (baseStart_868717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868717 prefixEnd_868717 := by exact prefixLift 868717
  have htrace : WordTrace (prefixWord ++ tailWord_868717) baseStart_868717 baseEnd_868717 := by
    simpa [prefixWord, tailWord_868717, baseEnd_868717] using wordTrace_append hprefix tailTrace_868717
  have hstable : (prefixWord ++ tailWord_868717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868717).length < 2 ^ (prefixWord ++ tailWord_868717).sum := by decide
  have hdescent : baseEnd_868717 < baseStart_868717 := by decide
  rcases family_descends (prefixWord ++ tailWord_868717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868761 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 3]
def baseStart_868761 : Nat := 118140960795 + 868761 * 2 ^ 59
def prefixEnd_868761 : Nat := 4983230072969 + 3 ^ 40 * 868761 * 2
def baseEnd_868761 : Nat := 446091966880780702292147

theorem tailTrace_868761 : CollatzResearch.WordTrace tailWord_868761 prefixEnd_868761 446091966880780702292147 := by
  unfold tailWord_868761
  simp only [CollatzResearch.WordTrace]
  refine ⟨31686316805634744411366137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21124211203756496274244091 31686316805634744411366137)
  ·
    refine ⟨23764737604226058308524603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31686316805634744411366137 23764737604226058308524603)
    ·
      refine ⟨35647106406339087462786905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23764737604226058308524603 35647106406339087462786905)
      ·
        refine ⟨26735329804754315597090179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35647106406339087462786905 26735329804754315597090179)
        ·
          refine ⟨40102994707131473395635269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26735329804754315597090179 40102994707131473395635269)
          ·
            refine ⟨7519311507587151261681613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40102994707131473395635269 7519311507587151261681613)
            ·
              refine ⟨2819741815345181723130605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7519311507587151261681613 2819741815345181723130605)
              ·
                refine ⟨1057403180754443146173977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2819741815345181723130605 1057403180754443146173977)
                ·
                  refine ⟨793052385565832359630483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057403180754443146173977 793052385565832359630483)
                  ·
                    refine ⟨1189578578348748539445725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 793052385565832359630483 1189578578348748539445725)
                    ·
                      refine ⟨446091966880780702292147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189578578348748539445725 446091966880780702292147)
                      ·
                        rfl

theorem cell23_868761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_868761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868761 prefixEnd_868761 := by exact prefixLift 868761
  have htrace : WordTrace (prefixWord ++ tailWord_868761) baseStart_868761 baseEnd_868761 := by
    simpa [prefixWord, tailWord_868761, baseEnd_868761] using wordTrace_append hprefix tailTrace_868761
  have hstable : (prefixWord ++ tailWord_868761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868761).length < 2 ^ (prefixWord ++ tailWord_868761).sum := by decide
  have hdescent : baseEnd_868761 < baseStart_868761 := by decide
  rcases family_descends (prefixWord ++ tailWord_868761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868765 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_868765 : Nat := 118140960795 + 868765 * 2 ^ 59
def prefixEnd_868765 : Nat := 4983230072969 + 3 ^ 40 * 868765 * 2
def baseEnd_868765 : Nat := 446094020803398686642129

theorem tailTrace_868765 : CollatzResearch.WordTrace tailWord_868765 prefixEnd_868765 446094020803398686642129 := by
  unfold tailWord_868765
  simp only [CollatzResearch.WordTrace]
  refine ⟨31686462697620253094511749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21124308465080168729674499 31686462697620253094511749)
  ·
    refine ⟨5941211755803797455220953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31686462697620253094511749 5941211755803797455220953)
    ·
      refine ⟨4455908816852848091415715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5941211755803797455220953 4455908816852848091415715)
      ·
        refine ⟨6683863225279272137123573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455908816852848091415715 6683863225279272137123573)
        ·
          refine ⟨626612177369931762855335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6683863225279272137123573 626612177369931762855335)
          ·
            refine ⟨939918266054897644283003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626612177369931762855335 939918266054897644283003)
            ·
              refine ⟨1409877399082346466424505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939918266054897644283003 1409877399082346466424505)
              ·
                refine ⟨1057408049311759849818379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409877399082346466424505 1057408049311759849818379)
                ·
                  refine ⟨1586112073967639774727569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057408049311759849818379 1586112073967639774727569)
                  ·
                    refine ⟨1189584055475729831045677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1586112073967639774727569 1189584055475729831045677)
                    ·
                      refine ⟨446094020803398686642129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1189584055475729831045677 446094020803398686642129)
                      ·
                        rfl

theorem cell23_868765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_868765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868765 prefixEnd_868765 := by exact prefixLift 868765
  have htrace : WordTrace (prefixWord ++ tailWord_868765) baseStart_868765 baseEnd_868765 := by
    simpa [prefixWord, tailWord_868765, baseEnd_868765] using wordTrace_append hprefix tailTrace_868765
  have hstable : (prefixWord ++ tailWord_868765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868765).length < 2 ^ (prefixWord ++ tailWord_868765).sum := by decide
  have hdescent : baseEnd_868765 < baseStart_868765 := by decide
  rcases family_descends (prefixWord ++ tailWord_868765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868771 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 3, 3, 2]
def baseStart_868771 : Nat := 118140960795 + 868771 * 2 ^ 59
def prefixEnd_868771 : Nat := 4983230072969 + 3 ^ 40 * 868771 * 2
def baseEnd_868771 : Nat := 446097101687325663167101

theorem tailTrace_868771 : CollatzResearch.WordTrace tailWord_868771 prefixEnd_868771 446097101687325663167101 := by
  unfold tailWord_868771
  simp only [CollatzResearch.WordTrace]
  refine ⟨31686681535598516119230167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21124454357065677412820111 31686681535598516119230167)
  ·
    refine ⟨47530022303397774178845251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31686681535598516119230167 47530022303397774178845251)
    ·
      refine ⟨71295033455096661268267877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47530022303397774178845251 71295033455096661268267877)
      ·
        refine ⟨13367818772830623987800227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71295033455096661268267877 13367818772830623987800227)
        ·
          refine ⟨20051728159245935981700341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13367818772830623987800227 20051728159245935981700341)
          ·
            refine ⟨1879849514929306498284407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20051728159245935981700341 1879849514929306498284407)
            ·
              refine ⟨2819774272393959747426611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879849514929306498284407 2819774272393959747426611)
              ·
                refine ⟨4229661408590939621139917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819774272393959747426611 4229661408590939621139917)
                ·
                  refine ⟨1586123028221602357927469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4229661408590939621139917 1586123028221602357927469)
                  ·
                    refine ⟨594796135583100884222801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586123028221602357927469 594796135583100884222801)
                    ·
                      refine ⟨446097101687325663167101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594796135583100884222801 446097101687325663167101)
                      ·
                        rfl

theorem cell23_868771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_868771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868771 prefixEnd_868771 := by exact prefixLift 868771
  have htrace : WordTrace (prefixWord ++ tailWord_868771) baseStart_868771 baseEnd_868771 := by
    simpa [prefixWord, tailWord_868771, baseEnd_868771] using wordTrace_append hprefix tailTrace_868771
  have hstable : (prefixWord ++ tailWord_868771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868771).length < 2 ^ (prefixWord ++ tailWord_868771).sum := by decide
  have hdescent : baseEnd_868771 < baseStart_868771 := by decide
  rcases family_descends (prefixWord ++ tailWord_868771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868874 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_868874 : Nat := 118140960795 + 868874 * 2 ^ 59
def prefixEnd_868874 : Nat := 4983230072969 + 3 ^ 40 * 868874 * 2
def baseEnd_868874 : Nat := 446149990194738760179127

theorem tailTrace_868874 : CollatzResearch.WordTrace tailWord_868874 prefixEnd_868874 446149990194738760179127 := by
  unfold tailWord_868874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922609563556341177557419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21126958836150243140153117 7922609563556341177557419)
  ·
    refine ⟨11883914345334511766336129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7922609563556341177557419 11883914345334511766336129)
    ·
      refine ⟨8912935759000883824752097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11883914345334511766336129 8912935759000883824752097)
      ·
        refine ⟨6684701819250662868564073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8912935759000883824752097 6684701819250662868564073)
        ·
          refine ⟨5013526364437997151423055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6684701819250662868564073 5013526364437997151423055)
          ·
            refine ⟨7520289546656995727134583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013526364437997151423055 7520289546656995727134583)
            ·
              refine ⟨11280434319985493590701875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7520289546656995727134583 11280434319985493590701875)
              ·
                refine ⟨16920651479978240386052813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11280434319985493590701875 16920651479978240386052813)
                ·
                  refine ⟨6345244304991840144769805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16920651479978240386052813 6345244304991840144769805)
                  ·
                    refine ⟨2379466614371940054288677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6345244304991840144769805 2379466614371940054288677)
                    ·
                      refine ⟨446149990194738760179127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2379466614371940054288677 446149990194738760179127)
                      ·
                        rfl

theorem cell23_868874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_868874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868874 prefixEnd_868874 := by exact prefixLift 868874
  have htrace : WordTrace (prefixWord ++ tailWord_868874) baseStart_868874 baseEnd_868874 := by
    simpa [prefixWord, tailWord_868874, baseEnd_868874] using wordTrace_append hprefix tailTrace_868874
  have hstable : (prefixWord ++ tailWord_868874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868874).length < 2 ^ (prefixWord ++ tailWord_868874).sum := by decide
  have hdescent : baseEnd_868874 < baseStart_868874 := by decide
  rcases family_descends (prefixWord ++ tailWord_868874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868909 : List Nat := [1, 5, 4, 1, 1, 1, 3, 2, 5]
def baseStart_868909 : Nat := 118140960795 + 868909 * 2 ^ 59
def prefixEnd_868909 : Nat := 4983230072969 + 3 ^ 40 * 868909 * 2
def baseEnd_868909 : Nat := 49574218001960680360163

theorem tailTrace_868909 : CollatzResearch.WordTrace tailWord_868909 prefixEnd_868909 49574218001960680360163 := by
  unfold tailWord_868909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31691714809098565687753781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21127809872732377125169187 31691714809098565687753781)
  ·
    refine ⟨2971098263352990533226917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31691714809098565687753781 2971098263352990533226917)
    ·
      refine ⟨557080924378685724980047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2971098263352990533226917 557080924378685724980047)
      ·
        refine ⟨835621386568028587470071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557080924378685724980047 835621386568028587470071)
        ·
          refine ⟨1253432079852042881205107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835621386568028587470071 1253432079852042881205107)
          ·
            refine ⟨1880148119778064321807661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253432079852042881205107 1880148119778064321807661)
            ·
              refine ⟨705055544916774120677873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880148119778064321807661 705055544916774120677873)
              ·
                refine ⟨528791658687580590508405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705055544916774120677873 528791658687580590508405)
                ·
                  refine ⟨49574218001960680360163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528791658687580590508405 49574218001960680360163)
                  ·
                    rfl

theorem cell23_868909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_868909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868909 prefixEnd_868909 := by exact prefixLift 868909
  have htrace : WordTrace (prefixWord ++ tailWord_868909) baseStart_868909 baseEnd_868909 := by
    simpa [prefixWord, tailWord_868909, baseEnd_868909] using wordTrace_append hprefix tailTrace_868909
  have hstable : (prefixWord ++ tailWord_868909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868909).length < 2 ^ (prefixWord ++ tailWord_868909).sum := by decide
  have hdescent : baseEnd_868909 < baseStart_868909 := by decide
  rcases family_descends (prefixWord ++ tailWord_868909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868914 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_868914 : Nat := 118140960795 + 868914 * 2 ^ 59
def prefixEnd_868914 : Nat := 4983230072969 + 3 ^ 40 * 868914 * 2
def baseEnd_868914 : Nat := 49574503268990955964327

theorem tailTrace_868914 : CollatzResearch.WordTrace tailWord_868914 prefixEnd_868914 49574503268990955964327 := by
  unfold tailWord_868914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7922974293520112885421449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21127931449386967694457197 7922974293520112885421449)
  ·
    refine ⟨5942230720140084664066087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7922974293520112885421449 5942230720140084664066087)
    ·
      refine ⟨8913346080210126996099131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5942230720140084664066087 8913346080210126996099131)
      ·
        refine ⟨13370019120315190494148697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8913346080210126996099131 13370019120315190494148697)
        ·
          refine ⟨10027514340236392870611523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13370019120315190494148697 10027514340236392870611523)
          ·
            refine ⟨15041271510354589305917285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027514340236392870611523 15041271510354589305917285)
            ·
              refine ⟨2820238408191485494859491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15041271510354589305917285 2820238408191485494859491)
              ·
                refine ⟨4230357612287228242289237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820238408191485494859491 4230357612287228242289237)
                ·
                  refine ⟨49574503268990955964327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4230357612287228242289237 49574503268990955964327)
                  ·
                    rfl

theorem cell23_868914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_868914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_868914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_868914 prefixEnd_868914 := by exact prefixLift 868914
  have htrace : WordTrace (prefixWord ++ tailWord_868914) baseStart_868914 baseEnd_868914 := by
    simpa [prefixWord, tailWord_868914, baseEnd_868914] using wordTrace_append hprefix tailTrace_868914
  have hstable : (prefixWord ++ tailWord_868914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868914).length < 2 ^ (prefixWord ++ tailWord_868914).sum := by decide
  have hdescent : baseEnd_868914 < baseStart_868914 := by decide
  rcases family_descends (prefixWord ++ tailWord_868914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869002 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_869002 : Nat := 118140960795 + 869002 * 2 ^ 59
def prefixEnd_869002 : Nat := 4983230072969 + 3 ^ 40 * 869002 * 2
def baseEnd_869002 : Nat := 446215715718514259378539

theorem tailTrace_869002 : CollatzResearch.WordTrace tailWord_869002 prefixEnd_869002 446215715718514259378539 := by
  unfold tailWord_869002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923776699440410642722315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21130071198507761713926173 7923776699440410642722315)
  ·
    refine ⟨11885665049160615964083473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7923776699440410642722315 11885665049160615964083473)
    ·
      refine ⟨8914248786870461973062605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11885665049160615964083473 8914248786870461973062605)
      ·
        refine ⟨3342843295076423239898477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8914248786870461973062605 3342843295076423239898477)
        ·
          refine ⟨1253566235653658714961929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3342843295076423239898477 1253566235653658714961929)
          ·
            refine ⟨940174676740244036221447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253566235653658714961929 940174676740244036221447)
            ·
              refine ⟨1410262015110366054332171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940174676740244036221447 1410262015110366054332171)
              ·
                refine ⟨2115393022665549081498257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410262015110366054332171 2115393022665549081498257)
                ·
                  refine ⟨1586544766999161811123693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2115393022665549081498257 1586544766999161811123693)
                  ·
                    refine ⟨594954287624685679171385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1586544766999161811123693 594954287624685679171385)
                    ·
                      refine ⟨446215715718514259378539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 594954287624685679171385 446215715718514259378539)
                      ·
                        rfl

theorem cell23_869002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_869002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869002 prefixEnd_869002 := by exact prefixLift 869002
  have htrace : WordTrace (prefixWord ++ tailWord_869002) baseStart_869002 baseEnd_869002 := by
    simpa [prefixWord, tailWord_869002, baseEnd_869002] using wordTrace_append hprefix tailTrace_869002
  have hstable : (prefixWord ++ tailWord_869002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869002).length < 2 ^ (prefixWord ++ tailWord_869002).sum := by decide
  have hdescent : baseEnd_869002 < baseStart_869002 := by decide
  rcases family_descends (prefixWord ++ tailWord_869002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869012 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_869012 : Nat := 118140960795 + 869012 * 2 ^ 59
def prefixEnd_869012 : Nat := 4983230072969 + 3 ^ 40 * 869012 * 2
def baseEnd_869012 : Nat := 148740283508353073417831

theorem tailTrace_869012 : CollatzResearch.WordTrace tailWord_869012 prefixEnd_869012 148740283508353073417831 := by
  unfold tailWord_869012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15847735763862707139376645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21130314351816942852502193 15847735763862707139376645)
  ·
    refine ⟨2971450455724257588633121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15847735763862707139376645 2971450455724257588633121)
    ·
      refine ⟨2228587841793193191474841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2971450455724257588633121 2228587841793193191474841)
      ·
        refine ⟨1671440881344894893606131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2228587841793193191474841 1671440881344894893606131)
        ·
          refine ⟨2507161322017342340409197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671440881344894893606131 2507161322017342340409197)
          ·
            refine ⟨940185495756503377653449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2507161322017342340409197 940185495756503377653449)
            ·
              refine ⟨705139121817377533240087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940185495756503377653449 705139121817377533240087)
              ·
                refine ⟨1057708682726066299860131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705139121817377533240087 1057708682726066299860131)
                ·
                  refine ⟨1586563024089099449790197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057708682726066299860131 1586563024089099449790197)
                  ·
                    refine ⟨148740283508353073417831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1586563024089099449790197 148740283508353073417831)
                    ·
                      rfl

theorem cell23_869012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_869012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869012 prefixEnd_869012 := by exact prefixLift 869012
  have htrace : WordTrace (prefixWord ++ tailWord_869012) baseStart_869012 baseEnd_869012 := by
    simpa [prefixWord, tailWord_869012, baseEnd_869012] using wordTrace_append hprefix tailTrace_869012
  have hstable : (prefixWord ++ tailWord_869012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869012).length < 2 ^ (prefixWord ++ tailWord_869012).sum := by decide
  have hdescent : baseEnd_869012 < baseStart_869012 := by decide
  rcases family_descends (prefixWord ++ tailWord_869012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869045 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_869045 : Nat := 118140960795 + 869045 * 2 ^ 59
def prefixEnd_869045 : Nat := 4983230072969 + 3 ^ 40 * 869045 * 2
def baseEnd_869045 : Nat := 446237795386657591140841

theorem tailTrace_869045 : CollatzResearch.WordTrace tailWord_869045 prefixEnd_869045 446237795386657591140841 := by
  unfold tailWord_869045
  simp only [CollatzResearch.WordTrace]
  refine ⟨31696675136605860914704589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21131116757737240609803059 31696675136605860914704589)
  ·
    refine ⟨11886253176227197843014221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31696675136605860914704589 11886253176227197843014221)
    ·
      refine ⟨4457344941085199191130333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11886253176227197843014221 4457344941085199191130333)
      ·
        refine ⟨1671504352906949696673875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4457344941085199191130333 1671504352906949696673875)
        ·
          refine ⟨2507256529360424545010813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671504352906949696673875 2507256529360424545010813)
          ·
            refine ⟨940221198510159204379055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2507256529360424545010813 940221198510159204379055)
            ·
              refine ⟨1410331797765238806568583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940221198510159204379055 1410331797765238806568583)
              ·
                refine ⟨2115497696647858209852875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410331797765238806568583 2115497696647858209852875)
                ·
                  refine ⟨3173246544971787314779313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115497696647858209852875 3173246544971787314779313)
                  ·
                    refine ⟨2379934908728840486084485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3173246544971787314779313 2379934908728840486084485)
                    ·
                      refine ⟨446237795386657591140841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2379934908728840486084485 446237795386657591140841)
                      ·
                        rfl

theorem cell23_869045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_869045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869045 prefixEnd_869045 := by exact prefixLift 869045
  have htrace : WordTrace (prefixWord ++ tailWord_869045) baseStart_869045 baseEnd_869045 := by
    simpa [prefixWord, tailWord_869045, baseEnd_869045] using wordTrace_append hprefix tailTrace_869045
  have hstable : (prefixWord ++ tailWord_869045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869045).length < 2 ^ (prefixWord ++ tailWord_869045).sum := by decide
  have hdescent : baseEnd_869045 < baseStart_869045 := by decide
  rcases family_descends (prefixWord ++ tailWord_869045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869122 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_869122 : Nat := 118140960795 + 869122 * 2 ^ 59
def prefixEnd_869122 : Nat := 4983230072969 + 3 ^ 40 * 869122 * 2
def baseEnd_869122 : Nat := 446277333397053789877987

theorem tailTrace_869122 : CollatzResearch.WordTrace tailWord_869122 prefixEnd_869122 446277333397053789877987 := by
  unfold tailWord_869122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924870889331725766314405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21132989038217935376838413 7924870889331725766314405)
  ·
    refine ⟨1485913291749698581183951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7924870889331725766314405 1485913291749698581183951)
    ·
      refine ⟨2228869937624547871775927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485913291749698581183951 2228869937624547871775927)
      ·
        refine ⟨3343304906436821807663891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228869937624547871775927 3343304906436821807663891)
        ·
          refine ⟨5014957359655232711495837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343304906436821807663891 5014957359655232711495837)
          ·
            refine ⟨1880609009870712266810939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5014957359655232711495837 1880609009870712266810939)
            ·
              refine ⟨2820913514806068400216409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880609009870712266810939 2820913514806068400216409)
              ·
                refine ⟨2115685136104551300162307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820913514806068400216409 2115685136104551300162307)
                ·
                  refine ⟨3173527704156826950243461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115685136104551300162307 3173527704156826950243461)
                  ·
                    refine ⟨595036444529405053170649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173527704156826950243461 595036444529405053170649)
                    ·
                      refine ⟨446277333397053789877987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595036444529405053170649 446277333397053789877987)
                      ·
                        rfl

theorem cell23_869122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_869122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869122 prefixEnd_869122 := by exact prefixLift 869122
  have htrace : WordTrace (prefixWord ++ tailWord_869122) baseStart_869122 baseEnd_869122 := by
    simpa [prefixWord, tailWord_869122, baseEnd_869122] using wordTrace_append hprefix tailTrace_869122
  have hstable : (prefixWord ++ tailWord_869122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869122).length < 2 ^ (prefixWord ++ tailWord_869122).sum := by decide
  have hdescent : baseEnd_869122 < baseStart_869122 := by decide
  rcases family_descends (prefixWord ++ tailWord_869122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869161 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_869161 : Nat := 118140960795 + 869161 * 2 ^ 59
def prefixEnd_869161 : Nat := 4983230072969 + 3 ^ 40 * 869161 * 2
def baseEnd_869161 : Nat := 446297359142579137290307

theorem tailTrace_869161 : CollatzResearch.WordTrace tailWord_869161 prefixEnd_869161 446297359142579137290307 := by
  unfold tailWord_869161
  simp only [CollatzResearch.WordTrace]
  refine ⟨31700906004185612725927337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21133937336123741817284891 31700906004185612725927337)
  ·
    refine ⟨23775679503139209544445503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31700906004185612725927337 23775679503139209544445503)
    ·
      refine ⟨35663519254708814316668255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23775679503139209544445503 35663519254708814316668255)
      ·
        refine ⟨53495278882063221475002383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35663519254708814316668255 53495278882063221475002383)
        ·
          refine ⟨80242918323094832212503575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53495278882063221475002383 80242918323094832212503575)
          ·
            refine ⟨120364377484642248318755363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80242918323094832212503575 120364377484642248318755363)
            ·
              refine ⟨180546566226963372478133045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120364377484642248318755363 180546566226963372478133045)
              ·
                refine ⟨16926240583777816169824973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180546566226963372478133045 16926240583777816169824973)
                ·
                  refine ⟨6347340218916681063684365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16926240583777816169824973 6347340218916681063684365)
                  ·
                    refine ⟨2380252582093755398881637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6347340218916681063684365 2380252582093755398881637)
                    ·
                      refine ⟨446297359142579137290307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2380252582093755398881637 446297359142579137290307)
                      ·
                        rfl

theorem cell23_869161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_869161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869161 prefixEnd_869161 := by exact prefixLift 869161
  have htrace : WordTrace (prefixWord ++ tailWord_869161) baseStart_869161 baseEnd_869161 := by
    simpa [prefixWord, tailWord_869161, baseEnd_869161] using wordTrace_append hprefix tailTrace_869161
  have hstable : (prefixWord ++ tailWord_869161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869161).length < 2 ^ (prefixWord ++ tailWord_869161).sum := by decide
  have hdescent : baseEnd_869161 < baseStart_869161 := by decide
  rcases family_descends (prefixWord ++ tailWord_869161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869190 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_869190 : Nat := 118140960795 + 869190 * 2 ^ 59
def prefixEnd_869190 : Nat := 4983230072969 + 3 ^ 40 * 869190 * 2
def baseEnd_869190 : Nat := 446312250081559523827675

theorem tailTrace_869190 : CollatzResearch.WordTrace tailWord_869190 prefixEnd_869190 446312250081559523827675 := by
  unfold tailWord_869190
  simp only [CollatzResearch.WordTrace]
  refine ⟨990686366283767208710407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21134642480720367119155349 990686366283767208710407)
  ·
    refine ⟨1486029549425650813065611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990686366283767208710407 1486029549425650813065611)
    ·
      refine ⟨2229044324138476219598417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486029549425650813065611 2229044324138476219598417)
      ·
        refine ⟨1671783243103857164698813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229044324138476219598417 1671783243103857164698813)
        ·
          refine ⟨626918716163946436762055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1671783243103857164698813 626918716163946436762055)
          ·
            refine ⟨940378074245919655143083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626918716163946436762055 940378074245919655143083)
            ·
              refine ⟨1410567111368879482714625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940378074245919655143083 1410567111368879482714625)
              ·
                refine ⟨1057925333526659612035969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410567111368879482714625 1057925333526659612035969)
                ·
                  refine ⟨793444000144994709026977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1057925333526659612035969 793444000144994709026977)
                  ·
                    refine ⟨595083000108746031770233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 793444000144994709026977 595083000108746031770233)
                    ·
                      refine ⟨446312250081559523827675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595083000108746031770233 446312250081559523827675)
                      ·
                        rfl

theorem cell23_869190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_869190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869190 prefixEnd_869190 := by exact prefixLift 869190
  have htrace : WordTrace (prefixWord ++ tailWord_869190) baseStart_869190 baseEnd_869190 := by
    simpa [prefixWord, tailWord_869190, baseEnd_869190] using wordTrace_append hprefix tailTrace_869190
  have hstable : (prefixWord ++ tailWord_869190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869190).length < 2 ^ (prefixWord ++ tailWord_869190).sum := by decide
  have hdescent : baseEnd_869190 < baseStart_869190 := by decide
  rcases family_descends (prefixWord ++ tailWord_869190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869205 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_869205 : Nat := 118140960795 + 869205 * 2 ^ 59
def prefixEnd_869205 : Nat := 4983230072969 + 3 ^ 40 * 869205 * 2
def baseEnd_869205 : Nat := 148773317430458988380035

theorem tailTrace_869205 : CollatzResearch.WordTrace tailWord_869205 prefixEnd_869205 148773317430458988380035 := by
  unfold tailWord_869205
  simp only [CollatzResearch.WordTrace]
  refine ⟨31702510816026208240529069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21135007210684138827019379 31702510816026208240529069)
  ·
    refine ⟨11888441556009828090198401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31702510816026208240529069 11888441556009828090198401)
    ·
      refine ⟨8916331167007371067648801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11888441556009828090198401 8916331167007371067648801)
      ·
        refine ⟨6687248375255528300736601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8916331167007371067648801 6687248375255528300736601)
        ·
          refine ⟨5015436281441646225552451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6687248375255528300736601 5015436281441646225552451)
          ·
            refine ⟨7523154422162469338328677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015436281441646225552451 7523154422162469338328677)
            ·
              refine ⟨1410591454155463000936627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7523154422162469338328677 1410591454155463000936627)
              ·
                refine ⟨2115887181233194501404941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410591454155463000936627 2115887181233194501404941)
                ·
                  refine ⟨793457692962447938026853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2115887181233194501404941 793457692962447938026853)
                  ·
                    refine ⟨148773317430458988380035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 793457692962447938026853 148773317430458988380035)
                    ·
                      rfl

theorem cell23_869205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_869205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869205 prefixEnd_869205 := by exact prefixLift 869205
  have htrace : WordTrace (prefixWord ++ tailWord_869205) baseStart_869205 baseEnd_869205 := by
    simpa [prefixWord, tailWord_869205, baseEnd_869205] using wordTrace_append hprefix tailTrace_869205
  have hstable : (prefixWord ++ tailWord_869205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869205).length < 2 ^ (prefixWord ++ tailWord_869205).sum := by decide
  have hdescent : baseEnd_869205 < baseStart_869205 := by decide
  rcases family_descends (prefixWord ++ tailWord_869205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869212 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_869212 : Nat := 118140960795 + 869212 * 2 ^ 59
def prefixEnd_869212 : Nat := 4983230072969 + 3 ^ 40 * 869212 * 2
def baseEnd_869212 : Nat := 446323546655958437752573

theorem tailTrace_869212 : CollatzResearch.WordTrace tailWord_869212 prefixEnd_869212 446323546655958437752573 := by
  unfold tailWord_869212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851383063500424218016945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21135177418000565624022593 15851383063500424218016945)
  ·
    refine ⟨11888537297625318163512709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15851383063500424218016945 11888537297625318163512709)
    ·
      refine ⟨2229100743304747155658633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11888537297625318163512709 2229100743304747155658633)
      ·
        refine ⟨1671825557478560366743975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229100743304747155658633 1671825557478560366743975)
        ·
          refine ⟨2507738336217840550115963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671825557478560366743975 2507738336217840550115963)
          ·
            refine ⟨3761607504326760825173945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507738336217840550115963 3761607504326760825173945)
            ·
              refine ⟨2821205628245070618880459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761607504326760825173945 2821205628245070618880459)
              ·
                refine ⟨4231808442367605928320689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821205628245070618880459 4231808442367605928320689)
                ·
                  refine ⟨3173856331775704446240517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231808442367605928320689 3173856331775704446240517)
                  ·
                    refine ⟨595098062207944583670097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3173856331775704446240517 595098062207944583670097)
                    ·
                      refine ⟨446323546655958437752573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 595098062207944583670097 446323546655958437752573)
                      ·
                        rfl

theorem cell23_869212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_869212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869212 prefixEnd_869212 := by exact prefixLift 869212
  have htrace : WordTrace (prefixWord ++ tailWord_869212) baseStart_869212 baseEnd_869212 := by
    simpa [prefixWord, tailWord_869212, baseEnd_869212] using wordTrace_append hprefix tailTrace_869212
  have hstable : (prefixWord ++ tailWord_869212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869212).length < 2 ^ (prefixWord ++ tailWord_869212).sum := by decide
  have hdescent : baseEnd_869212 < baseStart_869212 := by decide
  rcases family_descends (prefixWord ++ tailWord_869212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869228 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_869228 : Nat := 118140960795 + 869228 * 2 ^ 59
def prefixEnd_869228 : Nat := 4983230072969 + 3 ^ 40 * 869228 * 2
def baseEnd_869228 : Nat := 446331762346430375152499

theorem tailTrace_869228 : CollatzResearch.WordTrace tailWord_869228 prefixEnd_869228 446331762346430375152499 := by
  unfold tailWord_869228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851674847471441584308169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21135566463295255445744225 15851674847471441584308169)
  ·
    refine ⟨11888756135603581188231127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15851674847471441584308169 11888756135603581188231127)
    ·
      refine ⟨17833134203405371782346691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11888756135603581188231127 17833134203405371782346691)
      ·
        refine ⟨26749701305108057673520037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833134203405371782346691 26749701305108057673520037)
        ·
          refine ⟨5015568994707760813785007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26749701305108057673520037 5015568994707760813785007)
          ·
            refine ⟨7523353492061641220677511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015568994707760813785007 7523353492061641220677511)
            ·
              refine ⟨11285030238092461831016267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523353492061641220677511 11285030238092461831016267)
              ·
                refine ⟨16927545357138692746524401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285030238092461831016267 16927545357138692746524401)
                ·
                  refine ⟨12695659017854019559893301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16927545357138692746524401 12695659017854019559893301)
                  ·
                    refine ⟨1190218032923814333739997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12695659017854019559893301 1190218032923814333739997)
                    ·
                      refine ⟨446331762346430375152499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1190218032923814333739997 446331762346430375152499)
                      ·
                        rfl

theorem cell23_869228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_869228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869228 prefixEnd_869228 := by exact prefixLift 869228
  have htrace : WordTrace (prefixWord ++ tailWord_869228) baseStart_869228 baseEnd_869228 := by
    simpa [prefixWord, tailWord_869228, baseEnd_869228] using wordTrace_append hprefix tailTrace_869228
  have hstable : (prefixWord ++ tailWord_869228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869228).length < 2 ^ (prefixWord ++ tailWord_869228).sum := by decide
  have hdescent : baseEnd_869228 < baseStart_869228 := by decide
  rcases family_descends (prefixWord ++ tailWord_869228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869231 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 9]
def baseStart_869231 : Nat := 118140960795 + 869231 * 2 ^ 59
def prefixEnd_869231 : Nat := 4983230072969 + 3 ^ 40 * 869231 * 2
def baseEnd_869231 : Nat := 148777767596131287804995

theorem tailTrace_869231 : CollatzResearch.WordTrace tailWord_869231 prefixEnd_869231 148777767596131287804995 := by
  unfold tailWord_869231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703459113932014680975547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21135639409288009787317031 31703459113932014680975547)
  ·
    refine ⟨47555188670898022021463321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31703459113932014680975547 47555188670898022021463321)
    ·
      refine ⟨35666391503173516516097491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47555188670898022021463321 35666391503173516516097491)
      ·
        refine ⟨53499587254760274774146237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35666391503173516516097491 53499587254760274774146237)
        ·
          refine ⟨20062345220535103040304839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53499587254760274774146237 20062345220535103040304839)
          ·
            refine ⟨30093517830802654560457259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20062345220535103040304839 30093517830802654560457259)
            ·
              refine ⟨45140276746203981840685889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30093517830802654560457259 45140276746203981840685889)
              ·
                refine ⟨33855207559652986380514417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45140276746203981840685889 33855207559652986380514417)
                ·
                  refine ⟨25391405669739739785385813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33855207559652986380514417 25391405669739739785385813)
                  ·
                    refine ⟨148777767596131287804995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 25391405669739739785385813 148777767596131287804995)
                    ·
                      rfl

theorem cell23_869231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_869231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869231 prefixEnd_869231 := by exact prefixLift 869231
  have htrace : WordTrace (prefixWord ++ tailWord_869231) baseStart_869231 baseEnd_869231 := by
    simpa [prefixWord, tailWord_869231, baseEnd_869231] using wordTrace_append hprefix tailTrace_869231
  have hstable : (prefixWord ++ tailWord_869231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869231).length < 2 ^ (prefixWord ++ tailWord_869231).sum := by decide
  have hdescent : baseEnd_869231 < baseStart_869231 := by decide
  rcases family_descends (prefixWord ++ tailWord_869231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869245 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_869245 : Nat := 118140960795 + 869245 * 2 ^ 59
def prefixEnd_869245 : Nat := 4983230072969 + 3 ^ 40 * 869245 * 2
def baseEnd_869245 : Nat := 446340491517556808639921

theorem tailTrace_869245 : CollatzResearch.WordTrace tailWord_869245 prefixEnd_869245 446340491517556808639921 := by
  unfold tailWord_869245
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703969735881295071985189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21135979823920863381323459 31703969735881295071985189)
  ·
    refine ⟨5944494325477742825997223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31703969735881295071985189 5944494325477742825997223)
    ·
      refine ⟨8916741488216614238995835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5944494325477742825997223 8916741488216614238995835)
      ·
        refine ⟨13375112232324921358493753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8916741488216614238995835 13375112232324921358493753)
        ·
          refine ⟨10031334174243691018870315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13375112232324921358493753 10031334174243691018870315)
          ·
            refine ⟨15047001261365536528305473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031334174243691018870315 15047001261365536528305473)
            ·
              refine ⟨11285250946024152396229105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15047001261365536528305473 11285250946024152396229105)
              ·
                refine ⟨8463938209518114297171829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11285250946024152396229105 8463938209518114297171829)
                ·
                  refine ⟨793494207142323215359859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8463938209518114297171829 793494207142323215359859)
                  ·
                    refine ⟨1190241310713484823039789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 793494207142323215359859 1190241310713484823039789)
                    ·
                      refine ⟨446340491517556808639921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1190241310713484823039789 446340491517556808639921)
                      ·
                        rfl

theorem cell23_869245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_869245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_869245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_869245 prefixEnd_869245 := by exact prefixLift 869245
  have htrace : WordTrace (prefixWord ++ tailWord_869245) baseStart_869245 baseEnd_869245 := by
    simpa [prefixWord, tailWord_869245, baseEnd_869245] using wordTrace_append hprefix tailTrace_869245
  have hstable : (prefixWord ++ tailWord_869245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869245).length < 2 ^ (prefixWord ++ tailWord_869245).sum := by decide
  have hdescent : baseEnd_869245 < baseStart_869245 := by decide
  rcases family_descends (prefixWord ++ tailWord_869245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
