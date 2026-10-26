import V185TrunkScan23Chunk0976

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5784049 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_5784049 : Nat := 118140960795 + 5784049 * 2 ^ 59
def prefixEnd_5784049 : Nat := 4983230072969 + 3 ^ 40 * 5784049 * 2
def baseEnd_5784049 : Nat := 2969997266157545615387149

theorem tailTrace_5784049 : CollatzResearch.WordTrace tailWord_5784049 prefixEnd_5784049 2969997266157545615387149 := by
  unfold tailWord_5784049
  simp only [CollatzResearch.WordTrace]
  refine ⟨210961598222385784768595201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140641065481590523179063467 210961598222385784768595201)
  ·
    refine ⟨158221198666789338576446401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210961598222385784768595201 158221198666789338576446401)
    ·
      refine ⟨118665899000092003932334801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158221198666789338576446401 118665899000092003932334801)
      ·
        refine ⟨88999424250069002949251101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118665899000092003932334801 88999424250069002949251101)
        ·
          refine ⟨33374784093775876105969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88999424250069002949251101 33374784093775876105969163)
          ·
            refine ⟨50062176140663814158953745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33374784093775876105969163 50062176140663814158953745)
            ·
              refine ⟨37546632105497860619215309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50062176140663814158953745 37546632105497860619215309)
              ·
                refine ⟨14079987039561697732205741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37546632105497860619215309 14079987039561697732205741)
                ·
                  refine ⟨5279995139835636649577153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14079987039561697732205741 5279995139835636649577153)
                  ·
                    refine ⟨3959996354876727487182865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5279995139835636649577153 3959996354876727487182865)
                    ·
                      refine ⟨2969997266157545615387149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959996354876727487182865 2969997266157545615387149)
                      ·
                        rfl

theorem cell23_5784049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_5784049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784049 prefixEnd_5784049 := by exact prefixLift 5784049
  have htrace : WordTrace (prefixWord ++ tailWord_5784049) baseStart_5784049 baseEnd_5784049 := by
    simpa [prefixWord, tailWord_5784049, baseEnd_5784049] using wordTrace_append hprefix tailTrace_5784049
  have hstable : (prefixWord ++ tailWord_5784049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784049).length < 2 ^ (prefixWord ++ tailWord_5784049).sum := by decide
  have hdescent : baseEnd_5784049 < baseStart_5784049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784070 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5784070 : Nat := 118140960795 + 5784070 * 2 ^ 59
def prefixEnd_5784070 : Nat := 4983230072969 + 3 ^ 40 * 5784070 * 2
def baseEnd_5784070 : Nat := 2970008049251290033224553

theorem tailTrace_5784070 : CollatzResearch.WordTrace tailWord_5784070 prefixEnd_5784070 2970008049251290033224553 := by
  unfold tailWord_5784070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592573879853428292347177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140641576103539803570073109 6592573879853428292347177)
  ·
    refine ⟨4944430409890071219260383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6592573879853428292347177 4944430409890071219260383)
    ·
      refine ⟨7416645614835106828890575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944430409890071219260383 7416645614835106828890575)
      ·
        refine ⟨11124968422252660243335863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416645614835106828890575 11124968422252660243335863)
        ·
          refine ⟨16687452633378990365003795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124968422252660243335863 16687452633378990365003795)
          ·
            refine ⟨25031178950068485547505693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16687452633378990365003795 25031178950068485547505693)
            ·
              refine ⟨9386692106275682080314635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25031178950068485547505693 9386692106275682080314635)
              ·
                refine ⟨14080038159413523120471953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9386692106275682080314635 14080038159413523120471953)
                ·
                  refine ⟨10560028619560142340353965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14080038159413523120471953 10560028619560142340353965)
                  ·
                    refine ⟨3960010732335053377632737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10560028619560142340353965 3960010732335053377632737)
                    ·
                      refine ⟨2970008049251290033224553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960010732335053377632737 2970008049251290033224553)
                      ·
                        rfl

theorem cell23_5784070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5784070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784070 prefixEnd_5784070 := by exact prefixLift 5784070
  have htrace : WordTrace (prefixWord ++ tailWord_5784070) baseStart_5784070 baseEnd_5784070 := by
    simpa [prefixWord, tailWord_5784070, baseEnd_5784070] using wordTrace_append hprefix tailTrace_5784070
  have hstable : (prefixWord ++ tailWord_5784070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784070).length < 2 ^ (prefixWord ++ tailWord_5784070).sum := by decide
  have hdescent : baseEnd_5784070 < baseStart_5784070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784099 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 3]
def baseStart_5784099 : Nat := 118140960795 + 5784099 * 2 ^ 59
def prefixEnd_5784099 : Nat := 4983230072969 + 3 ^ 40 * 5784099 * 2
def baseEnd_5784099 : Nat := 2970022940190270419761919

theorem tailTrace_5784099 : CollatzResearch.WordTrace tailWord_5784099 prefixEnd_5784099 2970022940190270419761919 := by
  unfold tailWord_5784099
  simp only [CollatzResearch.WordTrace]
  refine ⟨210963421872204643307915351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140642281248136428871943567 210963421872204643307915351)
  ·
    refine ⟨316445132808306964961873027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210963421872204643307915351 316445132808306964961873027)
    ·
      refine ⟨474667699212460447442809541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316445132808306964961873027 474667699212460447442809541)
      ·
        refine ⟨89000193602336333895526789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 474667699212460447442809541 89000193602336333895526789)
        ·
          refine ⟨16687536300438062605411273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89000193602336333895526789 16687536300438062605411273)
          ·
            refine ⟨12515652225328546954058455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16687536300438062605411273 12515652225328546954058455)
            ·
              refine ⟨18773478337992820431087683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12515652225328546954058455 18773478337992820431087683)
              ·
                refine ⟨28160217506989230646631525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18773478337992820431087683 28160217506989230646631525)
                ·
                  refine ⟨5280040782560480746243411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28160217506989230646631525 5280040782560480746243411)
                  ·
                    refine ⟨7920061173840721119365117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5280040782560480746243411 7920061173840721119365117)
                    ·
                      refine ⟨2970022940190270419761919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7920061173840721119365117 2970022940190270419761919)
                      ·
                        rfl

theorem cell23_5784099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_5784099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784099 prefixEnd_5784099 := by exact prefixLift 5784099
  have htrace : WordTrace (prefixWord ++ tailWord_5784099) baseStart_5784099 baseEnd_5784099 := by
    simpa [prefixWord, tailWord_5784099, baseEnd_5784099] using wordTrace_append hprefix tailTrace_5784099
  have hstable : (prefixWord ++ tailWord_5784099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784099).length < 2 ^ (prefixWord ++ tailWord_5784099).sum := by decide
  have hdescent : baseEnd_5784099 < baseStart_5784099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784115 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 2, 6]
def baseStart_5784115 : Nat := 118140960795 + 5784115 * 2 ^ 59
def prefixEnd_5784115 : Nat := 4983230072969 + 3 ^ 40 * 5784115 * 2
def baseEnd_5784115 : Nat := 990010385293580785720615

theorem tailTrace_5784115 : CollatzResearch.WordTrace tailWord_5784115 prefixEnd_5784115 990010385293580785720615 := by
  unfold tailWord_5784115
  simp only [CollatzResearch.WordTrace]
  refine ⟨210964005440146678040497799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140642670293431118693665199 210964005440146678040497799)
  ·
    refine ⟨316446008160220017060746699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210964005440146678040497799 316446008160220017060746699)
    ·
      refine ⟨474669012240330025591120049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316446008160220017060746699 474669012240330025591120049)
      ·
        refine ⟨356001759180247519193340037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474669012240330025591120049 356001759180247519193340037)
        ·
          refine ⟨66750329846296409848751257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356001759180247519193340037 66750329846296409848751257)
          ·
            refine ⟨50062747384722307386563443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66750329846296409848751257 50062747384722307386563443)
            ·
              refine ⟨75094121077083461079845165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50062747384722307386563443 75094121077083461079845165)
              ·
                refine ⟨28160295403906297904941937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75094121077083461079845165 28160295403906297904941937)
                ·
                  refine ⟨21120221552929723428706453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28160295403906297904941937 21120221552929723428706453)
                  ·
                    refine ⟨990010385293580785720615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21120221552929723428706453 990010385293580785720615)
                    ·
                      rfl

theorem cell23_5784115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_5784115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784115 prefixEnd_5784115 := by exact prefixLift 5784115
  have htrace : WordTrace (prefixWord ++ tailWord_5784115) baseStart_5784115 baseEnd_5784115 := by
    simpa [prefixWord, tailWord_5784115, baseEnd_5784115] using wordTrace_append hprefix tailTrace_5784115
  have hstable : (prefixWord ++ tailWord_5784115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784115).length < 2 ^ (prefixWord ++ tailWord_5784115).sum := by decide
  have hdescent : baseEnd_5784115 < baseStart_5784115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784139 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 4, 2, 2]
def baseStart_5784139 : Nat := 118140960795 + 5784139 * 2 ^ 59
def prefixEnd_5784139 : Nat := 4983230072969 + 3 ^ 40 * 5784139 * 2
def baseEnd_5784139 : Nat := 2970043479416450263261735

theorem tailTrace_5784139 : CollatzResearch.WordTrace tailWord_5784139 prefixEnd_5784139 2970043479416450263261735 := by
  unfold tailWord_5784139
  simp only [CollatzResearch.WordTrace]
  refine ⟨210964880792059730139371471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140643253861373153426247647 210964880792059730139371471)
  ·
    refine ⟨316447321188089595209057207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210964880792059730139371471 316447321188089595209057207)
    ·
      refine ⟨474670981782134392813585811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316447321188089595209057207 474670981782134392813585811)
      ·
        refine ⟨712006472673201589220378717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474670981782134392813585811 712006472673201589220378717)
        ·
          refine ⟨267002427252450595957642019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 712006472673201589220378717 267002427252450595957642019)
          ·
            refine ⟨400503640878675893936463029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267002427252450595957642019 400503640878675893936463029)
            ·
              refine ⟨37547216332375865056543409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400503640878675893936463029 37547216332375865056543409)
              ·
                refine ⟨28160412249281898792407557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37547216332375865056543409 28160412249281898792407557)
                ·
                  refine ⟨5280077296740356023576417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28160412249281898792407557 5280077296740356023576417)
                  ·
                    refine ⟨3960057972555267017682313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280077296740356023576417 3960057972555267017682313)
                    ·
                      refine ⟨2970043479416450263261735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960057972555267017682313 2970043479416450263261735)
                      ·
                        rfl

theorem cell23_5784139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2, 2].length) (baseStart_5784139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784139 prefixEnd_5784139 := by exact prefixLift 5784139
  have htrace : WordTrace (prefixWord ++ tailWord_5784139) baseStart_5784139 baseEnd_5784139 := by
    simpa [prefixWord, tailWord_5784139, baseEnd_5784139] using wordTrace_append hprefix tailTrace_5784139
  have hstable : (prefixWord ++ tailWord_5784139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784139).length < 2 ^ (prefixWord ++ tailWord_5784139).sum := by decide
  have hdescent : baseEnd_5784139 < baseStart_5784139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784172 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_5784172 : Nat := 118140960795 + 5784172 * 2 ^ 59
def prefixEnd_5784172 : Nat := 4983230072969 + 3 ^ 40 * 5784172 * 2
def baseEnd_5784172 : Nat := 2970060424278048634149083

theorem tailTrace_5784172 : CollatzResearch.WordTrace tailWord_5784172 prefixEnd_5784172 2970060424278048634149083 := by
  unfold tailWord_5784172
  simp only [CollatzResearch.WordTrace]
  refine ⟨105483042200470088387661385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140644056267293451183548513 105483042200470088387661385)
  ·
    refine ⟨79112281650352566290746039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105483042200470088387661385 79112281650352566290746039)
    ·
      refine ⟨118668422475528849436119059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79112281650352566290746039 118668422475528849436119059)
      ·
        refine ⟨178002633713293274154178589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118668422475528849436119059 178002633713293274154178589)
        ·
          refine ⟨66750987642484977807816971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178002633713293274154178589 66750987642484977807816971)
          ·
            refine ⟨100126481463727466711725457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66750987642484977807816971 100126481463727466711725457)
            ·
              refine ⟨75094861097795600033794093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100126481463727466711725457 75094861097795600033794093)
              ·
                refine ⟨28160572911673350012672785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75094861097795600033794093 28160572911673350012672785)
                ·
                  refine ⟨21120429683755012509504589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28160572911673350012672785 21120429683755012509504589)
                  ·
                    refine ⟨7920161131408129691064221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21120429683755012509504589 7920161131408129691064221)
                    ·
                      refine ⟨2970060424278048634149083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7920161131408129691064221 2970060424278048634149083)
                      ·
                        rfl

theorem cell23_5784172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_5784172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784172 prefixEnd_5784172 := by exact prefixLift 5784172
  have htrace : WordTrace (prefixWord ++ tailWord_5784172) baseStart_5784172 baseEnd_5784172 := by
    simpa [prefixWord, tailWord_5784172, baseEnd_5784172] using wordTrace_append hprefix tailTrace_5784172
  have hstable : (prefixWord ++ tailWord_5784172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784172).length < 2 ^ (prefixWord ++ tailWord_5784172).sum := by decide
  have hdescent : baseEnd_5784172 < baseStart_5784172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784173 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_5784173 : Nat := 118140960795 + 5784173 * 2 ^ 59
def prefixEnd_5784173 : Nat := 4983230072969 + 3 ^ 40 * 5784173 * 2
def baseEnd_5784173 : Nat := 2970060937758703130236579

theorem tailTrace_5784173 : CollatzResearch.WordTrace tailWord_5784173 prefixEnd_5784173 2970060937758703130236579 := by
  unfold tailWord_5784173
  simp only [CollatzResearch.WordTrace]
  refine ⟨210966120873936553946109173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140644080582624369297406115 210966120873936553946109173)
  ·
    refine ⟨19778073831931551932447735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210966120873936553946109173 19778073831931551932447735)
    ·
      refine ⟨29667110747897327898671603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19778073831931551932447735 29667110747897327898671603)
      ·
        refine ⟨44500666121845991848007405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29667110747897327898671603 44500666121845991848007405)
        ·
          refine ⟨16687749795692246943002777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44500666121845991848007405 16687749795692246943002777)
          ·
            refine ⟨12515812346769185207252083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16687749795692246943002777 12515812346769185207252083)
            ·
              refine ⟨18773718520153777810878125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12515812346769185207252083 18773718520153777810878125)
              ·
                refine ⟨7040144445057666679079297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18773718520153777810878125 7040144445057666679079297)
                ·
                  refine ⟨5280108333793250009309473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040144445057666679079297 5280108333793250009309473)
                  ·
                    refine ⟨3960081250344937506982105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280108333793250009309473 3960081250344937506982105)
                    ·
                      refine ⟨2970060937758703130236579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960081250344937506982105 2970060937758703130236579)
                      ·
                        rfl

theorem cell23_5784173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_5784173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784173 prefixEnd_5784173 := by exact prefixLift 5784173
  have htrace : WordTrace (prefixWord ++ tailWord_5784173) baseStart_5784173 baseEnd_5784173 := by
    simpa [prefixWord, tailWord_5784173, baseEnd_5784173] using wordTrace_append hprefix tailTrace_5784173
  have hstable : (prefixWord ++ tailWord_5784173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784173).length < 2 ^ (prefixWord ++ tailWord_5784173).sum := by decide
  have hdescent : baseEnd_5784173 < baseStart_5784173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784175 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 7]
def baseStart_5784175 : Nat := 118140960795 + 5784175 * 2 ^ 59
def prefixEnd_5784175 : Nat := 4983230072969 + 3 ^ 40 * 5784175 * 2
def baseEnd_5784175 : Nat := 990020654906670707470523

theorem tailTrace_5784175 : CollatzResearch.WordTrace tailWord_5784175 prefixEnd_5784175 990020654906670707470523 := by
  unfold tailWord_5784175
  simp only [CollatzResearch.WordTrace]
  refine ⟨210966193819929308287681979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140644129213286205525121319 210966193819929308287681979)
  ·
    refine ⟨316449290729893962431522969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210966193819929308287681979 316449290729893962431522969)
    ·
      refine ⟨237336968047420471823642227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316449290729893962431522969 237336968047420471823642227)
      ·
        refine ⟨356005452071130707735463341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237336968047420471823642227 356005452071130707735463341)
        ·
          refine ⟨133502044526674015400798753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356005452071130707735463341 133502044526674015400798753)
          ·
            refine ⟨100126533395005511550599065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133502044526674015400798753 100126533395005511550599065)
            ·
              refine ⟨75094900046254133662949299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100126533395005511550599065 75094900046254133662949299)
              ·
                refine ⟨112642350069381200494423949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75094900046254133662949299 112642350069381200494423949)
                ·
                  refine ⟨42240881276017950185408981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112642350069381200494423949 42240881276017950185408981)
                  ·
                    refine ⟨990020654906670707470523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42240881276017950185408981 990020654906670707470523)
                    ·
                      rfl

theorem cell23_5784175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_5784175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784175 prefixEnd_5784175 := by exact prefixLift 5784175
  have htrace : WordTrace (prefixWord ++ tailWord_5784175) baseStart_5784175 baseEnd_5784175 := by
    simpa [prefixWord, tailWord_5784175, baseEnd_5784175] using wordTrace_append hprefix tailTrace_5784175
  have hstable : (prefixWord ++ tailWord_5784175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784175).length < 2 ^ (prefixWord ++ tailWord_5784175).sum := by decide
  have hdescent : baseEnd_5784175 < baseStart_5784175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784192 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_5784192 : Nat := 118140960795 + 5784192 * 2 ^ 59
def prefixEnd_5784192 : Nat := 4983230072969 + 3 ^ 40 * 5784192 * 2
def baseEnd_5784192 : Nat := 990023564630379518632997

theorem tailTrace_5784192 : CollatzResearch.WordTrace tailWord_5784192 prefixEnd_5784192 990023564630379518632997 := by
  unfold tailWord_5784192
  simp only [CollatzResearch.WordTrace]
  refine ⟨105483406930433860095525415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140644542573911813460700553 105483406930433860095525415)
  ·
    refine ⟨158225110395650790143288123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105483406930433860095525415 158225110395650790143288123)
    ·
      refine ⟨237337665593476185214932185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158225110395650790143288123 237337665593476185214932185)
      ·
        refine ⟨178003249195107138911199139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237337665593476185214932185 178003249195107138911199139)
        ·
          refine ⟨267004873792660708366798709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178003249195107138911199139 267004873792660708366798709)
          ·
            refine ⟨25031706918061941409387379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267004873792660708366798709 25031706918061941409387379)
            ·
              refine ⟨37547560377092912114081069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25031706918061941409387379 37547560377092912114081069)
              ·
                refine ⟨14080335141409842042780401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37547560377092912114081069 14080335141409842042780401)
                ·
                  refine ⟨10560251356057381532085301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14080335141409842042780401 10560251356057381532085301)
                  ·
                    refine ⟨990023564630379518632997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10560251356057381532085301 990023564630379518632997)
                    ·
                      rfl

theorem cell23_5784192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_5784192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784192 prefixEnd_5784192 := by exact prefixLift 5784192
  have htrace : WordTrace (prefixWord ++ tailWord_5784192) baseStart_5784192 baseEnd_5784192 := by
    simpa [prefixWord, tailWord_5784192, baseEnd_5784192] using wordTrace_append hprefix tailTrace_5784192
  have hstable : (prefixWord ++ tailWord_5784192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784192).length < 2 ^ (prefixWord ++ tailWord_5784192).sum := by decide
  have hdescent : baseEnd_5784192 < baseStart_5784192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784194 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5784194 : Nat := 118140960795 + 5784194 * 2 ^ 59
def prefixEnd_5784194 : Nat := 4983230072969 + 3 ^ 40 * 5784194 * 2
def baseEnd_5784194 : Nat := 2970071720852447548073983

theorem tailTrace_5784194 : CollatzResearch.WordTrace tailWord_5784194 prefixEnd_5784194 2970071720852447548073983 := by
  unfold tailWord_5784194
  simp only [CollatzResearch.WordTrace]
  refine ⟨52741721701715118633155909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140644591204573649688415757 52741721701715118633155909)
  ·
    refine ⟨9889072819071584743716733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52741721701715118633155909 9889072819071584743716733)
    ·
      refine ⟨3708402307151844278893775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9889072819071584743716733 3708402307151844278893775)
      ·
        refine ⟨5562603460727766418340663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708402307151844278893775 5562603460727766418340663)
        ·
          refine ⟨8343905191091649627510995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5562603460727766418340663 8343905191091649627510995)
          ·
            refine ⟨12515857786637474441266493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343905191091649627510995 12515857786637474441266493)
            ·
              refine ⟨4693446669989052915474935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12515857786637474441266493 4693446669989052915474935)
              ·
                refine ⟨7040170004983579373212403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693446669989052915474935 7040170004983579373212403)
                ·
                  refine ⟨10560255007475369059818605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7040170004983579373212403 10560255007475369059818605)
                  ·
                    refine ⟨3960095627803263397431977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10560255007475369059818605 3960095627803263397431977)
                    ·
                      refine ⟨2970071720852447548073983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960095627803263397431977 2970071720852447548073983)
                      ·
                        rfl

theorem cell23_5784194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5784194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784194 prefixEnd_5784194 := by exact prefixLift 5784194
  have htrace : WordTrace (prefixWord ++ tailWord_5784194) baseStart_5784194 baseEnd_5784194 := by
    simpa [prefixWord, tailWord_5784194, baseEnd_5784194] using wordTrace_append hprefix tailTrace_5784194
  have hstable : (prefixWord ++ tailWord_5784194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784194).length < 2 ^ (prefixWord ++ tailWord_5784194).sum := by decide
  have hdescent : baseEnd_5784194 < baseStart_5784194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784239 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 3, 4]
def baseStart_5784239 : Nat := 118140960795 + 5784239 * 2 ^ 59
def prefixEnd_5784239 : Nat := 4983230072969 + 3 ^ 40 * 5784239 * 2
def baseEnd_5784239 : Nat := 990031609160633290670425

theorem tailTrace_5784239 : CollatzResearch.WordTrace tailWord_5784239 prefixEnd_5784239 990031609160633290670425 := by
  unfold tailWord_5784239
  simp only [CollatzResearch.WordTrace]
  refine ⟨210968528091697447218011771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140645685394464964812007847 210968528091697447218011771)
  ·
    refine ⟨316452792137546170827017657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210968528091697447218011771 316452792137546170827017657)
    ·
      refine ⟨237339594103159628120263243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316452792137546170827017657 237339594103159628120263243)
      ·
        refine ⟨356009391154739442180394865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237339594103159628120263243 356009391154739442180394865)
        ·
          refine ⟨267007043366054581635296149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356009391154739442180394865 267007043366054581635296149)
          ·
            refine ⟨12515955157783808514154507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 267007043366054581635296149 12515955157783808514154507)
            ·
              refine ⟨18773932736675712771231761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12515955157783808514154507 18773932736675712771231761)
              ·
                refine ⟨14080449552506784578423821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18773932736675712771231761 14080449552506784578423821)
                ·
                  refine ⟨5280168582190044216908933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14080449552506784578423821 5280168582190044216908933)
                  ·
                    refine ⟨990031609160633290670425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280168582190044216908933 990031609160633290670425)
                    ·
                      rfl

theorem cell23_5784239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_5784239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784239 prefixEnd_5784239 := by exact prefixLift 5784239
  have htrace : WordTrace (prefixWord ++ tailWord_5784239) baseStart_5784239 baseEnd_5784239 := by
    simpa [prefixWord, tailWord_5784239, baseEnd_5784239] using wordTrace_append hprefix tailTrace_5784239
  have hstable : (prefixWord ++ tailWord_5784239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784239).length < 2 ^ (prefixWord ++ tailWord_5784239).sum := by decide
  have hdescent : baseEnd_5784239 < baseStart_5784239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784252 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 8]
def baseStart_5784252 : Nat := 118140960795 + 5784252 * 2 ^ 59
def prefixEnd_5784252 : Nat := 4983230072969 + 3 ^ 40 * 5784252 * 2
def baseEnd_5784252 : Nat := 330011278081156480127635

theorem tailTrace_5784252 : CollatzResearch.WordTrace tailWord_5784252 prefixEnd_5784252 330011278081156480127635 := by
  unfold tailWord_5784252
  simp only [CollatzResearch.WordTrace]
  refine ⟨105484501120325175219117505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140646001493766900292156673 105484501120325175219117505)
  ·
    refine ⟨79113375840243881414338129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105484501120325175219117505 79113375840243881414338129)
    ·
      refine ⟨59335031880182911060753597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79113375840243881414338129 59335031880182911060753597)
      ·
        refine ⟨22250636955068591647782599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59335031880182911060753597 22250636955068591647782599)
        ·
          refine ⟨33375955432602887471673899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22250636955068591647782599 33375955432602887471673899)
          ·
            refine ⟨50063933148904331207510849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33375955432602887471673899 50063933148904331207510849)
            ·
              refine ⟨37547949861678248405633137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50063933148904331207510849 37547949861678248405633137)
              ·
                refine ⟨28160962396258686304224853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37547949861678248405633137 28160962396258686304224853)
                ·
                  refine ⟨330011278081156480127635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28160962396258686304224853 330011278081156480127635)
                  ·
                    rfl

theorem cell23_5784252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_5784252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784252 prefixEnd_5784252 := by exact prefixLift 5784252
  have htrace : WordTrace (prefixWord ++ tailWord_5784252) baseStart_5784252 baseEnd_5784252 := by
    simpa [prefixWord, tailWord_5784252, baseEnd_5784252] using wordTrace_append hprefix tailTrace_5784252
  have hstable : (prefixWord ++ tailWord_5784252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784252).length < 2 ^ (prefixWord ++ tailWord_5784252).sum := by decide
  have hdescent : baseEnd_5784252 < baseStart_5784252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784256 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 1, 4]
def baseStart_5784256 : Nat := 118140960795 + 5784256 * 2 ^ 59
def prefixEnd_5784256 : Nat := 4983230072969 + 3 ^ 40 * 5784256 * 2
def baseEnd_5784256 : Nat := 990034518884342101832899

theorem tailTrace_5784256 : CollatzResearch.WordTrace tailWord_5784256 prefixEnd_5784256 990034518884342101832899 := by
  unfold tailWord_5784256
  simp only [CollatzResearch.WordTrace]
  refine ⟨105484574066317929560690311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140646098755090572747587081 105484574066317929560690311)
  ·
    refine ⟨158226861099476894341035467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105484574066317929560690311 158226861099476894341035467)
    ·
      refine ⟨237340291649215341511553201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158226861099476894341035467 237340291649215341511553201)
      ·
        refine ⟨178005218736911506133664901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237340291649215341511553201 178005218736911506133664901)
        ·
          refine ⟨33375978513170907400062169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178005218736911506133664901 33375978513170907400062169)
          ·
            refine ⟨25031983884878180550046627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33375978513170907400062169 25031983884878180550046627)
            ·
              refine ⟨37547975827317270825069941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25031983884878180550046627 37547975827317270825069941)
              ·
                refine ⟨3520122733810994139850307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37547975827317270825069941 3520122733810994139850307)
                ·
                  refine ⟨5280184100716491209775461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520122733810994139850307 5280184100716491209775461)
                  ·
                    refine ⟨990034518884342101832899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280184100716491209775461 990034518884342101832899)
                    ·
                      rfl

theorem cell23_5784256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 4].length) (baseStart_5784256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784256 prefixEnd_5784256 := by exact prefixLift 5784256
  have htrace : WordTrace (prefixWord ++ tailWord_5784256) baseStart_5784256 baseEnd_5784256 := by
    simpa [prefixWord, tailWord_5784256, baseEnd_5784256] using wordTrace_append hprefix tailTrace_5784256
  have hstable : (prefixWord ++ tailWord_5784256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784256).length < 2 ^ (prefixWord ++ tailWord_5784256).sum := by decide
  have hdescent : baseEnd_5784256 < baseStart_5784256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784306 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_5784306 : Nat := 118140960795 + 5784306 * 2 ^ 59
def prefixEnd_5784306 : Nat := 4983230072969 + 3 ^ 40 * 5784306 * 2
def baseEnd_5784306 : Nat := 2970129230685751109873467

theorem tailTrace_5784306 : CollatzResearch.WordTrace tailWord_5784306 prefixEnd_5784306 2970129230685751109873467 := by
  unfold tailWord_5784306
  simp only [CollatzResearch.WordTrace]
  refine ⟨52742742945613679415175193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140647314521636478440467181 52742742945613679415175193)
  ·
    refine ⟨39557057209210259561381395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52742742945613679415175193 39557057209210259561381395)
    ·
      refine ⟨59335585813815389342072093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39557057209210259561381395 59335585813815389342072093)
      ·
        refine ⟨22250844680180771003277035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59335585813815389342072093 22250844680180771003277035)
        ·
          refine ⟨33376267020271156504915553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22250844680180771003277035 33376267020271156504915553)
          ·
            refine ⟨25032200265203367378686665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33376267020271156504915553 25032200265203367378686665)
            ·
              refine ⟨18774150198902525534014999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25032200265203367378686665 18774150198902525534014999)
              ·
                refine ⟨28161225298353788301022499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18774150198902525534014999 28161225298353788301022499)
                ·
                  refine ⟨42241837947530682451533749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28161225298353788301022499 42241837947530682451533749)
                  ·
                    refine ⟨3960172307581001479831289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42241837947530682451533749 3960172307581001479831289)
                    ·
                      refine ⟨2970129230685751109873467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960172307581001479831289 2970129230685751109873467)
                      ·
                        rfl

theorem cell23_5784306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_5784306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784306 prefixEnd_5784306 := by exact prefixLift 5784306
  have htrace : WordTrace (prefixWord ++ tailWord_5784306) baseStart_5784306 baseEnd_5784306 := by
    simpa [prefixWord, tailWord_5784306, baseEnd_5784306] using wordTrace_append hprefix tailTrace_5784306
  have hstable : (prefixWord ++ tailWord_5784306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784306).length < 2 ^ (prefixWord ++ tailWord_5784306).sum := by decide
  have hdescent : baseEnd_5784306 < baseStart_5784306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784312 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_5784312 : Nat := 118140960795 + 5784312 * 2 ^ 59
def prefixEnd_5784312 : Nat := 4983230072969 + 3 ^ 40 * 5784312 * 2
def baseEnd_5784312 : Nat := 990044103856559362132813

theorem tailTrace_5784312 : CollatzResearch.WordTrace tailWord_5784312 prefixEnd_5784312 990044103856559362132813 := by
  unfold tailWord_5784312
  simp only [CollatzResearch.WordTrace]
  refine ⟨105485595310216490342709595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140647460413621987123612793 105485595310216490342709595)
  ·
    refine ⟨158228392965324735514064393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105485595310216490342709595 158228392965324735514064393)
    ·
      refine ⟨118671294723993551635548295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158228392965324735514064393 118671294723993551635548295)
      ·
        refine ⟨178006942085990327453322443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118671294723993551635548295 178006942085990327453322443)
        ·
          refine ⟨267010413128985491179983665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178006942085990327453322443 267010413128985491179983665)
          ·
            refine ⟨200257809846739118384987749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267010413128985491179983665 200257809846739118384987749)
            ·
              refine ⟨37548339346263584697185203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200257809846739118384987749 37548339346263584697185203)
              ·
                refine ⟨56322509019395377045777805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37548339346263584697185203 56322509019395377045777805)
                ·
                  refine ⟨21120940882273266392166677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56322509019395377045777805 21120940882273266392166677)
                  ·
                    refine ⟨990044103856559362132813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21120940882273266392166677 990044103856559362132813)
                    ·
                      rfl

theorem cell23_5784312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_5784312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784312 prefixEnd_5784312 := by exact prefixLift 5784312
  have htrace : WordTrace (prefixWord ++ tailWord_5784312) baseStart_5784312 baseEnd_5784312 := by
    simpa [prefixWord, tailWord_5784312, baseEnd_5784312] using wordTrace_append hprefix tailTrace_5784312
  have hstable : (prefixWord ++ tailWord_5784312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784312).length < 2 ^ (prefixWord ++ tailWord_5784312).sum := by decide
  have hdescent : baseEnd_5784312 < baseStart_5784312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784329 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_5784329 : Nat := 118140960795 + 5784329 * 2 ^ 59
def prefixEnd_5784329 : Nat := 4983230072969 + 3 ^ 40 * 5784329 * 2
def baseEnd_5784329 : Nat := 990047013580268173295287

theorem tailTrace_5784329 : CollatzResearch.WordTrace tailWord_5784329 prefixEnd_5784329 990047013580268173295287 := by
  unfold tailWord_5784329
  simp only [CollatzResearch.WordTrace]
  refine ⟨210971810661371392588788041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140647873774247595059192027 210971810661371392588788041)
  ·
    refine ⟨158228857996028544441591031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210971810661371392588788041 158228857996028544441591031)
    ·
      refine ⟨237343286994042816662386547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158228857996028544441591031 237343286994042816662386547)
      ·
        refine ⟨356014930491064224993579821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237343286994042816662386547 356014930491064224993579821)
        ·
          refine ⟨133505598934149084372592433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356014930491064224993579821 133505598934149084372592433)
          ·
            refine ⟨100129199200611813279444325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133505598934149084372592433 100129199200611813279444325)
            ·
              refine ⟨18774224850114714989895811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100129199200611813279444325 18774224850114714989895811)
              ·
                refine ⟨28161337275172072484843717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18774224850114714989895811 28161337275172072484843717)
                ·
                  refine ⟨5280250739094763590908197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28161337275172072484843717 5280250739094763590908197)
                  ·
                    refine ⟨990047013580268173295287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280250739094763590908197 990047013580268173295287)
                    ·
                      rfl

theorem cell23_5784329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_5784329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784329 prefixEnd_5784329 := by exact prefixLift 5784329
  have htrace : WordTrace (prefixWord ++ tailWord_5784329) baseStart_5784329 baseEnd_5784329 := by
    simpa [prefixWord, tailWord_5784329, baseEnd_5784329] using wordTrace_append hprefix tailTrace_5784329
  have hstable : (prefixWord ++ tailWord_5784329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784329).length < 2 ^ (prefixWord ++ tailWord_5784329).sum := by decide
  have hdescent : baseEnd_5784329 < baseStart_5784329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784330 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_5784330 : Nat := 118140960795 + 5784330 * 2 ^ 59
def prefixEnd_5784330 : Nat := 4983230072969 + 3 ^ 40 * 5784330 * 2
def baseEnd_5784330 : Nat := 2970141554221459015973357

theorem tailTrace_5784330 : CollatzResearch.WordTrace tailWord_5784330 prefixEnd_5784330 2970141554221459015973357 := by
  unfold tailWord_5784330
  simp only [CollatzResearch.WordTrace]
  refine ⟨52742961783591942439893611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140647898089578513173049629 52742961783591942439893611)
  ·
    refine ⟨79114442675387913659840417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52742961783591942439893611 79114442675387913659840417)
    ·
      refine ⟨59335832006540935244880313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79114442675387913659840417 59335832006540935244880313)
      ·
        refine ⟨44501874004905701433660235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59335832006540935244880313 44501874004905701433660235)
        ·
          refine ⟨66752811007358552150490353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44501874004905701433660235 66752811007358552150490353)
          ·
            refine ⟨50064608255518914112867765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66752811007358552150490353 50064608255518914112867765)
            ·
              refine ⟨4693557023954898198081353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50064608255518914112867765 4693557023954898198081353)
              ·
                refine ⟨3520167767966173648561015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693557023954898198081353 3520167767966173648561015)
                ·
                  refine ⟨5280251651949260472841523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520167767966173648561015 5280251651949260472841523)
                  ·
                    refine ⟨7920377477923890709262285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5280251651949260472841523 7920377477923890709262285)
                    ·
                      refine ⟨2970141554221459015973357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7920377477923890709262285 2970141554221459015973357)
                      ·
                        rfl

theorem cell23_5784330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_5784330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784330 prefixEnd_5784330 := by exact prefixLift 5784330
  have htrace : WordTrace (prefixWord ++ tailWord_5784330) baseStart_5784330 baseEnd_5784330 := by
    simpa [prefixWord, tailWord_5784330, baseEnd_5784330] using wordTrace_append hprefix tailTrace_5784330
  have hstable : (prefixWord ++ tailWord_5784330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784330).length < 2 ^ (prefixWord ++ tailWord_5784330).sum := by decide
  have hdescent : baseEnd_5784330 < baseStart_5784330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784339 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3]
def baseStart_5784339 : Nat := 118140960795 + 5784339 * 2 ^ 59
def prefixEnd_5784339 : Nat := 4983230072969 + 3 ^ 40 * 5784339 * 2
def baseEnd_5784339 : Nat := 2970146175547349480760815

theorem tailTrace_5784339 : CollatzResearch.WordTrace tailWord_5784339 prefixEnd_5784339 2970146175547349480760815 := by
  unfold tailWord_5784339
  simp only [CollatzResearch.WordTrace]
  refine ⟨210972175391335164296652071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140648116927556776197768047 210972175391335164296652071)
  ·
    refine ⟨316458263087002746444978107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210972175391335164296652071 316458263087002746444978107)
    ·
      refine ⟨474687394630504119667467161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316458263087002746444978107 474687394630504119667467161)
      ·
        refine ⟨356015545972878089750600371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474687394630504119667467161 356015545972878089750600371)
        ·
          refine ⟨534023318959317134625900557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356015545972878089750600371 534023318959317134625900557)
          ·
            refine ⟨200258744609743925484712709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534023318959317134625900557 200258744609743925484712709)
            ·
              refine ⟨37548514614326986028383633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200258744609743925484712709 37548514614326986028383633)
              ·
                refine ⟨28161385960745239521287725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37548514614326986028383633 28161385960745239521287725)
                ·
                  refine ⟨10560519735279464820482897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28161385960745239521287725 10560519735279464820482897)
                  ·
                    refine ⟨7920389801459598615362173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10560519735279464820482897 7920389801459598615362173)
                    ·
                      refine ⟨2970146175547349480760815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7920389801459598615362173 2970146175547349480760815)
                      ·
                        rfl

theorem cell23_5784339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_5784339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784339 prefixEnd_5784339 := by exact prefixLift 5784339
  have htrace : WordTrace (prefixWord ++ tailWord_5784339) baseStart_5784339 baseEnd_5784339 := by
    simpa [prefixWord, tailWord_5784339, baseEnd_5784339] using wordTrace_append hprefix tailTrace_5784339
  have hstable : (prefixWord ++ tailWord_5784339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784339).length < 2 ^ (prefixWord ++ tailWord_5784339).sum := by decide
  have hdescent : baseEnd_5784339 < baseStart_5784339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784346 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_5784346 : Nat := 118140960795 + 5784346 * 2 ^ 59
def prefixEnd_5784346 : Nat := 4983230072969 + 3 ^ 40 * 5784346 * 2
def baseEnd_5784346 : Nat := 990049923303976984457761

theorem tailTrace_5784346 : CollatzResearch.WordTrace tailWord_5784346 prefixEnd_5784346 990049923303976984457761 := by
  unfold tailWord_5784346
  simp only [CollatzResearch.WordTrace]
  refine ⟨52743107675577451123039223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140648287134873202994771261 52743107675577451123039223)
  ·
    refine ⟨79114661513366176684558835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52743107675577451123039223 79114661513366176684558835)
    ·
      refine ⟨118671992270049265026838253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79114661513366176684558835 118671992270049265026838253)
      ·
        refine ⟨44501997101268474385064345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118671992270049265026838253 44501997101268474385064345)
        ·
          refine ⟨33376497825951355788798259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44501997101268474385064345 33376497825951355788798259)
          ·
            refine ⟨50064746738927033683197389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33376497825951355788798259 50064746738927033683197389)
            ·
              refine ⟨18774280027097637631199021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50064746738927033683197389 18774280027097637631199021)
              ·
                refine ⟨7040355010161614111699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18774280027097637631199021 7040355010161614111699633)
                ·
                  refine ⟨5280266257621210583774725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040355010161614111699633 5280266257621210583774725)
                  ·
                    refine ⟨990049923303976984457761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5280266257621210583774725 990049923303976984457761)
                    ·
                      rfl

theorem cell23_5784346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_5784346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784346 prefixEnd_5784346 := by exact prefixLift 5784346
  have htrace : WordTrace (prefixWord ++ tailWord_5784346) baseStart_5784346 baseEnd_5784346 := by
    simpa [prefixWord, tailWord_5784346, baseEnd_5784346] using wordTrace_append hprefix tailTrace_5784346
  have hstable : (prefixWord ++ tailWord_5784346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784346).length < 2 ^ (prefixWord ++ tailWord_5784346).sum := by decide
  have hdescent : baseEnd_5784346 < baseStart_5784346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784366 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5784366 : Nat := 118140960795 + 5784366 * 2 ^ 59
def prefixEnd_5784366 : Nat := 4983230072969 + 3 ^ 40 * 5784366 * 2
def baseEnd_5784366 : Nat := 2970160039525020875123191

theorem tailTrace_5784366 : CollatzResearch.WordTrace tailWord_5784366 prefixEnd_5784366 2970160039525020875123191 := by
  unfold tailWord_5784366
  simp only [CollatzResearch.WordTrace]
  refine ⟨26371645020279668488485619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140648773441491565271923301 26371645020279668488485619)
  ·
    refine ⟨39557467530419502732728429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26371645020279668488485619 39557467530419502732728429)
    ·
      refine ⟨14834050323907313524773161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39557467530419502732728429 14834050323907313524773161)
      ·
        refine ⟨11125537742930485143579871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14834050323907313524773161 11125537742930485143579871)
        ·
          refine ⟨16688306614395727715369807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125537742930485143579871 16688306614395727715369807)
          ·
            refine ⟨25032459921593591573054711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16688306614395727715369807 25032459921593591573054711)
            ·
              refine ⟨37548689882390387359582067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25032459921593591573054711 37548689882390387359582067)
              ·
                refine ⟨56323034823585581039373101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37548689882390387359582067 56323034823585581039373101)
                ·
                  refine ⟨21121138058844592889764913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56323034823585581039373101 21121138058844592889764913)
                  ·
                    refine ⟨15840853544133444667323685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21121138058844592889764913 15840853544133444667323685)
                    ·
                      refine ⟨2970160039525020875123191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15840853544133444667323685 2970160039525020875123191)
                      ·
                        rfl

theorem cell23_5784366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5784366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784366 prefixEnd_5784366 := by exact prefixLift 5784366
  have htrace : WordTrace (prefixWord ++ tailWord_5784366) baseStart_5784366 baseEnd_5784366 := by
    simpa [prefixWord, tailWord_5784366, baseEnd_5784366] using wordTrace_append hprefix tailTrace_5784366
  have hstable : (prefixWord ++ tailWord_5784366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784366).length < 2 ^ (prefixWord ++ tailWord_5784366).sum := by decide
  have hdescent : baseEnd_5784366 < baseStart_5784366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784370 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_5784370 : Nat := 118140960795 + 5784370 * 2 ^ 59
def prefixEnd_5784370 : Nat := 4983230072969 + 3 ^ 40 * 5784370 * 2
def baseEnd_5784370 : Nat := 2970162093447638859473173

theorem tailTrace_5784370 : CollatzResearch.WordTrace tailWord_5784370 prefixEnd_5784370 2970162093447638859473173 := by
  unfold tailWord_5784370
  simp only [CollatzResearch.WordTrace]
  refine ⟨52743326513555714147757641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140648870702815237727353709 52743326513555714147757641)
  ·
    refine ⟨39557494885166785610818231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52743326513555714147757641 39557494885166785610818231)
    ·
      refine ⟨59336242327750178416227347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39557494885166785610818231 59336242327750178416227347)
      ·
        refine ⟨89004363491625267624341021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59336242327750178416227347 89004363491625267624341021)
        ·
          refine ⟨33376636309359475359127883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89004363491625267624341021 33376636309359475359127883)
          ·
            refine ⟨50064954464039213038691825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33376636309359475359127883 50064954464039213038691825)
            ·
              refine ⟨37548715848029409779018869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50064954464039213038691825 37548715848029409779018869)
              ·
                refine ⟨3520192110752757166783019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37548715848029409779018869 3520192110752757166783019)
                ·
                  refine ⟨5280288166129135750174529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520192110752757166783019 5280288166129135750174529)
                  ·
                    refine ⟨3960216124596851812630897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280288166129135750174529 3960216124596851812630897)
                    ·
                      refine ⟨2970162093447638859473173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960216124596851812630897 2970162093447638859473173)
                      ·
                        rfl

theorem cell23_5784370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_5784370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784370 prefixEnd_5784370 := by exact prefixLift 5784370
  have htrace : WordTrace (prefixWord ++ tailWord_5784370) baseStart_5784370 baseEnd_5784370 := by
    simpa [prefixWord, tailWord_5784370, baseEnd_5784370] using wordTrace_append hprefix tailTrace_5784370
  have hstable : (prefixWord ++ tailWord_5784370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784370).length < 2 ^ (prefixWord ++ tailWord_5784370).sum := by decide
  have hdescent : baseEnd_5784370 < baseStart_5784370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784429 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5784429 : Nat := 118140960795 + 5784429 * 2 ^ 59
def prefixEnd_5784429 : Nat := 4983230072969 + 3 ^ 40 * 5784429 * 2
def baseEnd_5784429 : Nat := 2970192388806254128635401

theorem tailTrace_5784429 : CollatzResearch.WordTrace tailWord_5784429 prefixEnd_5784429 2970192388806254128635401 := by
  unfold tailWord_5784429
  simp only [CollatzResearch.WordTrace]
  refine ⟨210975457961009109667428341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140650305307339406444952227 210975457961009109667428341)
  ·
    refine ⟨19778949183844604031321407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210975457961009109667428341 19778949183844604031321407)
    ·
      refine ⟨29668423775766906046982111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19778949183844604031321407 29668423775766906046982111)
      ·
        refine ⟨44502635663650359070473167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29668423775766906046982111 44502635663650359070473167)
        ·
          refine ⟨66753953495475538605709751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44502635663650359070473167 66753953495475538605709751)
          ·
            refine ⟨100130930243213307908564627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66753953495475538605709751 100130930243213307908564627)
            ·
              refine ⟨150196395364819961862846941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100130930243213307908564627 150196395364819961862846941)
              ·
                refine ⟨56323648261807485698567603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150196395364819961862846941 56323648261807485698567603)
                ·
                  refine ⟨84485472392711228547851405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56323648261807485698567603 84485472392711228547851405)
                  ·
                    refine ⟨31682052147266710705444277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84485472392711228547851405 31682052147266710705444277)
                    ·
                      refine ⟨2970192388806254128635401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31682052147266710705444277 2970192388806254128635401)
                      ·
                        rfl

theorem cell23_5784429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5784429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784429 prefixEnd_5784429 := by exact prefixLift 5784429
  have htrace : WordTrace (prefixWord ++ tailWord_5784429) baseStart_5784429 baseEnd_5784429 := by
    simpa [prefixWord, tailWord_5784429, baseEnd_5784429] using wordTrace_append hprefix tailTrace_5784429
  have hstable : (prefixWord ++ tailWord_5784429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784429).length < 2 ^ (prefixWord ++ tailWord_5784429).sum := by decide
  have hdescent : baseEnd_5784429 < baseStart_5784429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784456 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5784456 : Nat := 118140960795 + 5784456 * 2 ^ 59
def prefixEnd_5784456 : Nat := 4983230072969 + 3 ^ 40 * 5784456 * 2
def baseEnd_5784456 : Nat := 2970206252783925522997777

theorem tailTrace_5784456 : CollatzResearch.WordTrace tailWord_5784456 prefixEnd_5784456 2970206252783925522997777 := by
  unfold tailWord_5784456
  simp only [CollatzResearch.WordTrace]
  refine ⟨105488221365955646639330611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140650961821274195519107481 105488221365955646639330611)
  ·
    refine ⟨158232332048933469958995917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105488221365955646639330611 158232332048933469958995917)
    ·
      refine ⟨59337124518350051234623469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158232332048933469958995917 59337124518350051234623469)
      ·
        refine ⟨22251421694381269212983801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59337124518350051234623469 22251421694381269212983801)
        ·
          refine ⟨16688566270785951909737851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22251421694381269212983801 16688566270785951909737851)
          ·
            refine ⟨25032849406178927864606777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16688566270785951909737851 25032849406178927864606777)
            ·
              refine ⟨18774637054634195898455083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25032849406178927864606777 18774637054634195898455083)
              ·
                refine ⟨28161955581951293847682625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18774637054634195898455083 28161955581951293847682625)
                ·
                  refine ⟨21121466686463470385761969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28161955581951293847682625 21121466686463470385761969)
                  ·
                    refine ⟨15841100014847602789321477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21121466686463470385761969 15841100014847602789321477)
                    ·
                      refine ⟨2970206252783925522997777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15841100014847602789321477 2970206252783925522997777)
                      ·
                        rfl

theorem cell23_5784456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5784456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784456 prefixEnd_5784456 := by exact prefixLift 5784456
  have htrace : WordTrace (prefixWord ++ tailWord_5784456) baseStart_5784456 baseEnd_5784456 := by
    simpa [prefixWord, tailWord_5784456, baseEnd_5784456] using wordTrace_append hprefix tailTrace_5784456
  have hstable : (prefixWord ++ tailWord_5784456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784456).length < 2 ^ (prefixWord ++ tailWord_5784456).sum := by decide
  have hdescent : baseEnd_5784456 < baseStart_5784456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784489 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_5784489 : Nat := 118140960795 + 5784489 * 2 ^ 59
def prefixEnd_5784489 : Nat := 4983230072969 + 3 ^ 40 * 5784489 * 2
def baseEnd_5784489 : Nat := 2970223197645523893885125

theorem tailTrace_5784489 : CollatzResearch.WordTrace tailWord_5784489 prefixEnd_5784489 2970223197645523893885125 := by
  unfold tailWord_5784489
  simp only [CollatzResearch.WordTrace]
  refine ⟨210977646340791739914612521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140651764227194493276408347 210977646340791739914612521)
  ·
    refine ⟨158233234755593804935959391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210977646340791739914612521 158233234755593804935959391)
    ·
      refine ⟨237349852133390707403939087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158233234755593804935959391 237349852133390707403939087)
      ·
        refine ⟨356024778200086061105908631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237349852133390707403939087 356024778200086061105908631)
        ·
          refine ⟨534037167300129091658862947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356024778200086061105908631 534037167300129091658862947)
          ·
            refine ⟨801055750950193637488294421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534037167300129091658862947 801055750950193637488294421)
            ·
              refine ⟨37549488325790326757263801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 801055750950193637488294421 37549488325790326757263801)
              ·
                refine ⟨28162116244342745067947851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37549488325790326757263801 28162116244342745067947851)
                ·
                  refine ⟨42243174366514117601921777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28162116244342745067947851 42243174366514117601921777)
                  ·
                    refine ⟨31682380774885588201441333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42243174366514117601921777 31682380774885588201441333)
                    ·
                      refine ⟨2970223197645523893885125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31682380774885588201441333 2970223197645523893885125)
                      ·
                        rfl

theorem cell23_5784489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_5784489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784489 prefixEnd_5784489 := by exact prefixLift 5784489
  have htrace : WordTrace (prefixWord ++ tailWord_5784489) baseStart_5784489 baseEnd_5784489 := by
    simpa [prefixWord, tailWord_5784489, baseEnd_5784489] using wordTrace_append hprefix tailTrace_5784489
  have hstable : (prefixWord ++ tailWord_5784489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784489).length < 2 ^ (prefixWord ++ tailWord_5784489).sum := by decide
  have hdescent : baseEnd_5784489 < baseStart_5784489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784499 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_5784499 : Nat := 118140960795 + 5784499 * 2 ^ 59
def prefixEnd_5784499 : Nat := 4983230072969 + 3 ^ 40 * 5784499 * 2
def baseEnd_5784499 : Nat := 2970228332452068854760079

theorem tailTrace_5784499 : CollatzResearch.WordTrace tailWord_5784499 prefixEnd_5784499 2970228332452068854760079 := by
  unfold tailWord_5784499
  simp only [CollatzResearch.WordTrace]
  refine ⟨210978011070755511622476551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140652007380503674414984367 210978011070755511622476551)
  ·
    refine ⟨316467016606133267433714827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210978011070755511622476551 316467016606133267433714827)
    ·
      refine ⟨474700524909199901150572241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316467016606133267433714827 474700524909199901150572241)
      ·
        refine ⟨356025393681899925862929181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474700524909199901150572241 356025393681899925862929181)
        ·
          refine ⟨133509522630712472198598443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356025393681899925862929181 133509522630712472198598443)
          ·
            refine ⟨200264283946068708297897665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133509522630712472198598443 200264283946068708297897665)
            ·
              refine ⟨150198212959551531223423249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200264283946068708297897665 150198212959551531223423249)
              ·
                refine ⟨112648659719663648417567437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150198212959551531223423249 112648659719663648417567437)
                ·
                  refine ⟨42243247394873868156587789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112648659719663648417567437 42243247394873868156587789)
                  ·
                    refine ⟨15841217773077700558720421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42243247394873868156587789 15841217773077700558720421)
                    ·
                      refine ⟨2970228332452068854760079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15841217773077700558720421 2970228332452068854760079)
                      ·
                        rfl

theorem cell23_5784499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_5784499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784499 prefixEnd_5784499 := by exact prefixLift 5784499
  have htrace : WordTrace (prefixWord ++ tailWord_5784499) baseStart_5784499 baseEnd_5784499 := by
    simpa [prefixWord, tailWord_5784499, baseEnd_5784499] using wordTrace_append hprefix tailTrace_5784499
  have hstable : (prefixWord ++ tailWord_5784499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784499).length < 2 ^ (prefixWord ++ tailWord_5784499).sum := by decide
  have hdescent : baseEnd_5784499 < baseStart_5784499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784500 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5784500 : Nat := 118140960795 + 5784500 * 2 ^ 59
def prefixEnd_5784500 : Nat := 4983230072969 + 3 ^ 40 * 5784500 * 2
def baseEnd_5784500 : Nat := 330025427325858150094175

theorem tailTrace_5784500 : CollatzResearch.WordTrace tailWord_5784500 prefixEnd_5784500 330025427325858150094175 := by
  unfold tailWord_5784500
  simp only [CollatzResearch.WordTrace]
  refine ⟨105489023771875944396631477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140652031695834592528841969 105489023771875944396631477)
  ·
    refine ⟨9889595978613369787184201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105489023771875944396631477 9889595978613369787184201)
    ·
      refine ⟨7417196983960027340388151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9889595978613369787184201 7417196983960027340388151)
      ·
        refine ⟨11125795475940041010582227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417196983960027340388151 11125795475940041010582227)
        ·
          refine ⟨16688693213910061515873341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125795475940041010582227 16688693213910061515873341)
          ·
            refine ⟨6258259955216273068452503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16688693213910061515873341 6258259955216273068452503)
            ·
              refine ⟨9387389932824409602678755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258259955216273068452503 9387389932824409602678755)
              ·
                refine ⟨14081084899236614404018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387389932824409602678755 14081084899236614404018133)
                ·
                  refine ⟨330025427325858150094175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14081084899236614404018133 330025427325858150094175)
                  ·
                    rfl

theorem cell23_5784500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5784500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784500 prefixEnd_5784500 := by exact prefixLift 5784500
  have htrace : WordTrace (prefixWord ++ tailWord_5784500) baseStart_5784500 baseEnd_5784500 := by
    simpa [prefixWord, tailWord_5784500, baseEnd_5784500] using wordTrace_append hprefix tailTrace_5784500
  have hstable : (prefixWord ++ tailWord_5784500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784500).length < 2 ^ (prefixWord ++ tailWord_5784500).sum := by decide
  have hdescent : baseEnd_5784500 < baseStart_5784500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784633 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_5784633 : Nat := 118140960795 + 5784633 * 2 ^ 59
def prefixEnd_5784633 : Nat := 4983230072969 + 3 ^ 40 * 5784633 * 2
def baseEnd_5784633 : Nat := 990099046286590443494821

theorem tailTrace_5784633 : CollatzResearch.WordTrace tailWord_5784633 prefixEnd_5784633 990099046286590443494821 := by
  unfold tailWord_5784633
  simp only [CollatzResearch.WordTrace]
  refine ⟨210982898452270052507854553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140655265634846701671903035 210982898452270052507854553)
  ·
    refine ⟨158237173839202539380890915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210982898452270052507854553 158237173839202539380890915)
    ·
      refine ⟨237355760758803809071336373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158237173839202539380890915 237355760758803809071336373)
      ·
        refine ⟨22252102571137857100437785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237355760758803809071336373 22252102571137857100437785)
        ·
          refine ⟨16689076928353392825328339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22252102571137857100437785 16689076928353392825328339)
          ·
            refine ⟨25033615392530089237992509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16689076928353392825328339 25033615392530089237992509)
            ·
              refine ⟨9387605772198783464247191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25033615392530089237992509 9387605772198783464247191)
              ·
                refine ⟨14081408658298175196370787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387605772198783464247191 14081408658298175196370787)
                ·
                  refine ⟨21122112987447262794556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14081408658298175196370787 21122112987447262794556181)
                  ·
                    refine ⟨990099046286590443494821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21122112987447262794556181 990099046286590443494821)
                    ·
                      rfl

theorem cell23_5784633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_5784633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784633 prefixEnd_5784633 := by exact prefixLift 5784633
  have htrace : WordTrace (prefixWord ++ tailWord_5784633) baseStart_5784633 baseEnd_5784633 := by
    simpa [prefixWord, tailWord_5784633, baseEnd_5784633] using wordTrace_append hprefix tailTrace_5784633
  have hstable : (prefixWord ++ tailWord_5784633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784633).length < 2 ^ (prefixWord ++ tailWord_5784633).sum := by decide
  have hdescent : baseEnd_5784633 < baseStart_5784633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784640 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2]
def baseStart_5784640 : Nat := 118140960795 + 5784640 * 2 ^ 59
def prefixEnd_5784640 : Nat := 4983230072969 + 3 ^ 40 * 5784640 * 2
def baseEnd_5784640 : Nat := 2970300733224352803096931

theorem tailTrace_5784640 : CollatzResearch.WordTrace tailWord_5784640 prefixEnd_5784640 2970300733224352803096931 := by
  unfold tailWord_5784640
  simp only [CollatzResearch.WordTrace]
  refine ⟨105491576881622346351679687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140655435842163128468906249 105491576881622346351679687)
  ·
    refine ⟨158237365322433519527519531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105491576881622346351679687 158237365322433519527519531)
    ·
      refine ⟨237356047983650279291279297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158237365322433519527519531 237356047983650279291279297)
      ·
        refine ⟨178017035987737709468459473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237356047983650279291279297 178017035987737709468459473)
        ·
          refine ⟨133512776990803282101344605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178017035987737709468459473 133512776990803282101344605)
          ·
            refine ⟨50067291371551230788004227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133512776990803282101344605 50067291371551230788004227)
            ·
              refine ⟨75100937057326846182006341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50067291371551230788004227 75100937057326846182006341)
              ·
                refine ⟨14081425698248783659126189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75100937057326846182006341 14081425698248783659126189)
                ·
                  refine ⟨5280534636843293872172321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14081425698248783659126189 5280534636843293872172321)
                  ·
                    refine ⟨3960400977632470404129241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280534636843293872172321 3960400977632470404129241)
                    ·
                      refine ⟨2970300733224352803096931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960400977632470404129241 2970300733224352803096931)
                      ·
                        rfl

theorem cell23_5784640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_5784640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784640 prefixEnd_5784640 := by exact prefixLift 5784640
  have htrace : WordTrace (prefixWord ++ tailWord_5784640) baseStart_5784640 baseEnd_5784640 := by
    simpa [prefixWord, tailWord_5784640, baseEnd_5784640] using wordTrace_append hprefix tailTrace_5784640
  have hstable : (prefixWord ++ tailWord_5784640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784640).length < 2 ^ (prefixWord ++ tailWord_5784640).sum := by decide
  have hdescent : baseEnd_5784640 < baseStart_5784640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784660 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_5784660 : Nat := 118140960795 + 5784660 * 2 ^ 59
def prefixEnd_5784660 : Nat := 4983230072969 + 3 ^ 40 * 5784660 * 2
def baseEnd_5784660 : Nat := 2970311002837442724846839

theorem tailTrace_5784660 : CollatzResearch.WordTrace tailWord_5784660 prefixEnd_5784660 2970311002837442724846839 := by
  unfold tailWord_5784660
  simp only [CollatzResearch.WordTrace]
  refine ⟨105491941611586118059543717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140655922148781490746058289 105491941611586118059543717)
  ·
    refine ⟨19779739052172397136164447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105491941611586118059543717 19779739052172397136164447)
    ·
      refine ⟨29669608578258595704246671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19779739052172397136164447 29669608578258595704246671)
      ·
        refine ⟨44504412867387893556370007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29669608578258595704246671 44504412867387893556370007)
        ·
          refine ⟨66756619301081840334555011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44504412867387893556370007 66756619301081840334555011)
          ·
            refine ⟨100134928951622760501832517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66756619301081840334555011 100134928951622760501832517)
            ·
              refine ⟨18775299178429267594093597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100134928951622760501832517 18775299178429267594093597)
              ·
                refine ⟨7040737191910975347785099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18775299178429267594093597 7040737191910975347785099)
                ·
                  refine ⟨10561105787866463021677649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7040737191910975347785099 10561105787866463021677649)
                  ·
                    refine ⟨7920829340899847266258237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10561105787866463021677649 7920829340899847266258237)
                    ·
                      refine ⟨2970311002837442724846839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7920829340899847266258237 2970311002837442724846839)
                      ·
                        rfl

theorem cell23_5784660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_5784660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784660 prefixEnd_5784660 := by exact prefixLift 5784660
  have htrace : WordTrace (prefixWord ++ tailWord_5784660) baseStart_5784660 baseEnd_5784660 := by
    simpa [prefixWord, tailWord_5784660, baseEnd_5784660] using wordTrace_append hprefix tailTrace_5784660
  have hstable : (prefixWord ++ tailWord_5784660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784660).length < 2 ^ (prefixWord ++ tailWord_5784660).sum := by decide
  have hdescent : baseEnd_5784660 < baseStart_5784660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784674 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5784674 : Nat := 118140960795 + 5784674 * 2 ^ 59
def prefixEnd_5784674 : Nat := 4983230072969 + 3 ^ 40 * 5784674 * 2
def baseEnd_5784674 : Nat := 2970318191566605670071775

theorem tailTrace_5784674 : CollatzResearch.WordTrace tailWord_5784674 prefixEnd_5784674 2970318191566605670071775 := by
  unfold tailWord_5784674
  simp only [CollatzResearch.WordTrace]
  refine ⟨52746098461280379127524269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140656262563414344340064717 52746098461280379127524269)
  ·
    refine ⟨19779786922980142172821601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52746098461280379127524269 19779786922980142172821601)
    ·
      refine ⟨14834840192235106629616201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19779786922980142172821601 14834840192235106629616201)
      ·
        refine ⟨11126130144176329972212151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14834840192235106629616201 11126130144176329972212151)
        ·
          refine ⟨16689195216264494958318227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11126130144176329972212151 16689195216264494958318227)
          ·
            refine ⟨25033792824396742437477341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16689195216264494958318227 25033792824396742437477341)
            ·
              refine ⟨9387672309148778414054003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25033792824396742437477341 9387672309148778414054003)
              ·
                refine ⟨14081508463723167621081005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387672309148778414054003 14081508463723167621081005)
                ·
                  refine ⟨5280565673896187857905377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14081508463723167621081005 5280565673896187857905377)
                  ·
                    refine ⟨3960424255422140893429033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280565673896187857905377 3960424255422140893429033)
                    ·
                      refine ⟨2970318191566605670071775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960424255422140893429033 2970318191566605670071775)
                      ·
                        rfl

theorem cell23_5784674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5784674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784674 prefixEnd_5784674 := by exact prefixLift 5784674
  have htrace : WordTrace (prefixWord ++ tailWord_5784674) baseStart_5784674 baseEnd_5784674 := by
    simpa [prefixWord, tailWord_5784674, baseEnd_5784674] using wordTrace_append hprefix tailTrace_5784674
  have hstable : (prefixWord ++ tailWord_5784674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784674).length < 2 ^ (prefixWord ++ tailWord_5784674).sum := by decide
  have hdescent : baseEnd_5784674 < baseStart_5784674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784676 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_5784676 : Nat := 118140960795 + 5784676 * 2 ^ 59
def prefixEnd_5784676 : Nat := 4983230072969 + 3 ^ 40 * 5784676 * 2
def baseEnd_5784676 : Nat := 990106406175971554082255

theorem tailTrace_5784676 : CollatzResearch.WordTrace tailWord_5784676 prefixEnd_5784676 990106406175971554082255 := by
  unfold tailWord_5784676
  simp only [CollatzResearch.WordTrace]
  refine ⟨105492233395557135425834941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140656311194076180567779921 105492233395557135425834941)
  ·
    refine ⟨39559587523333925784688103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105492233395557135425834941 39559587523333925784688103)
    ·
      refine ⟨59339381285000888677032155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39559587523333925784688103 59339381285000888677032155)
      ·
        refine ⟨89009071927501333015548233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59339381285000888677032155 89009071927501333015548233)
        ·
          refine ⟨66756803945625999761661175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89009071927501333015548233 66756803945625999761661175)
          ·
            refine ⟨100135205918438999642491763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66756803945625999761661175 100135205918438999642491763)
            ·
              refine ⟨150202808877658499463737645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100135205918438999642491763 150202808877658499463737645)
              ·
                refine ⟨56326053329121937298901617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150202808877658499463737645 56326053329121937298901617)
                ·
                  refine ⟨42244539996841452974176213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56326053329121937298901617 42244539996841452974176213)
                  ·
                    refine ⟨990106406175971554082255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42244539996841452974176213 990106406175971554082255)
                    ·
                      rfl

theorem cell23_5784676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_5784676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784676 prefixEnd_5784676 := by exact prefixLift 5784676
  have htrace : WordTrace (prefixWord ++ tailWord_5784676) baseStart_5784676 baseEnd_5784676 := by
    simpa [prefixWord, tailWord_5784676, baseEnd_5784676] using wordTrace_append hprefix tailTrace_5784676
  have hstable : (prefixWord ++ tailWord_5784676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784676).length < 2 ^ (prefixWord ++ tailWord_5784676).sum := by decide
  have hdescent : baseEnd_5784676 < baseStart_5784676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784680 : List Nat := [2, 1, 4, 4, 1, 1, 2, 8]
def baseStart_5784680 : Nat := 118140960795 + 5784680 * 2 ^ 59
def prefixEnd_5784680 : Nat := 4983230072969 + 3 ^ 40 * 5784680 * 2
def baseEnd_5784680 : Nat := 110011898979649357281361

theorem tailTrace_5784680 : CollatzResearch.WordTrace tailWord_5784680 prefixEnd_5784680 110011898979649357281361 := by
  unfold tailWord_5784680
  simp only [CollatzResearch.WordTrace]
  refine ⟨105492306341549889767407747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140656408455399853023210329 105492306341549889767407747)
  ·
    refine ⟨158238459512324834651111621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105492306341549889767407747 158238459512324834651111621)
    ·
      refine ⟨29669711158560906497083429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158238459512324834651111621 29669711158560906497083429)
      ·
        refine ⟨5563070842230169968203143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29669711158560906497083429 5563070842230169968203143)
        ·
          refine ⟨8344606263345254952304715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563070842230169968203143 8344606263345254952304715)
          ·
            refine ⟨12516909395017882428457073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8344606263345254952304715 12516909395017882428457073)
            ·
              refine ⟨9387682046263411821342805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12516909395017882428457073 9387682046263411821342805)
              ·
                refine ⟨110011898979649357281361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9387682046263411821342805 110011898979649357281361)
                ·
                  rfl

theorem cell23_5784680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 8].length) (baseStart_5784680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784680 prefixEnd_5784680 := by exact prefixLift 5784680
  have htrace : WordTrace (prefixWord ++ tailWord_5784680) baseStart_5784680 baseEnd_5784680 := by
    simpa [prefixWord, tailWord_5784680, baseEnd_5784680] using wordTrace_append hprefix tailTrace_5784680
  have hstable : (prefixWord ++ tailWord_5784680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784680).length < 2 ^ (prefixWord ++ tailWord_5784680).sum := by decide
  have hdescent : baseEnd_5784680 < baseStart_5784680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784700 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_5784700 : Nat := 118140960795 + 5784700 * 2 ^ 59
def prefixEnd_5784700 : Nat := 4983230072969 + 3 ^ 40 * 5784700 * 2
def baseEnd_5784700 : Nat := 2970331542063622568346655

theorem tailTrace_5784700 : CollatzResearch.WordTrace tailWord_5784700 prefixEnd_5784700 2970331542063622568346655 := by
  unfold tailWord_5784700
  simp only [CollatzResearch.WordTrace]
  refine ⟨105492671071513661475271777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140656894762018215300362369 105492671071513661475271777)
  ·
    refine ⟨79119503303635246106453833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105492671071513661475271777 79119503303635246106453833)
    ·
      refine ⟨59339627477726434579840375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79119503303635246106453833 59339627477726434579840375)
      ·
        refine ⟨89009441216589651869760563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59339627477726434579840375 89009441216589651869760563)
        ·
          refine ⟨133514161824884477804640845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89009441216589651869760563 133514161824884477804640845)
          ·
            refine ⟨50067810684331679176740317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133514161824884477804640845 50067810684331679176740317)
            ·
              refine ⟨18775429006624379691277619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50067810684331679176740317 18775429006624379691277619)
              ·
                refine ⟨28163143509936569536916429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18775429006624379691277619 28163143509936569536916429)
                ·
                  refine ⟨10561178816226213576343661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28163143509936569536916429 10561178816226213576343661)
                  ·
                    refine ⟨3960442056084830091128873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10561178816226213576343661 3960442056084830091128873)
                    ·
                      refine ⟨2970331542063622568346655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960442056084830091128873 2970331542063622568346655)
                      ·
                        rfl

theorem cell23_5784700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_5784700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784700 prefixEnd_5784700 := by exact prefixLift 5784700
  have htrace : WordTrace (prefixWord ++ tailWord_5784700) baseStart_5784700 baseEnd_5784700 := by
    simpa [prefixWord, tailWord_5784700, baseEnd_5784700] using wordTrace_append hprefix tailTrace_5784700
  have hstable : (prefixWord ++ tailWord_5784700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784700).length < 2 ^ (prefixWord ++ tailWord_5784700).sum := by decide
  have hdescent : baseEnd_5784700 < baseStart_5784700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784733 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_5784733 : Nat := 118140960795 + 5784733 * 2 ^ 59
def prefixEnd_5784733 : Nat := 4983230072969 + 3 ^ 40 * 5784733 * 2
def baseEnd_5784733 : Nat := 2970348486925220939234003

theorem tailTrace_5784733 : CollatzResearch.WordTrace tailWord_5784733 prefixEnd_5784733 2970348486925220939234003 := by
  unfold tailWord_5784733
  simp only [CollatzResearch.WordTrace]
  refine ⟨210986545751907769586494853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140657697167938513057663235 210986545751907769586494853)
  ·
    refine ⟨39559977328482706797467785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210986545751907769586494853 39559977328482706797467785)
    ·
      refine ⟨29669982996362030098100839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39559977328482706797467785 29669982996362030098100839)
      ·
        refine ⟨44504974494543045147151259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29669982996362030098100839 44504974494543045147151259)
        ·
          refine ⟨66757461741814567720726889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44504974494543045147151259 66757461741814567720726889)
          ·
            refine ⟨50068096306360925790545167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66757461741814567720726889 50068096306360925790545167)
            ·
              refine ⟨75102144459541388685817751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50068096306360925790545167 75102144459541388685817751)
              ·
                refine ⟨112653216689312083028726627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75102144459541388685817751 112653216689312083028726627)
                ·
                  refine ⟨168979825033968124543089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112653216689312083028726627 168979825033968124543089941)
                  ·
                    refine ⟨7920929298467255837957341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168979825033968124543089941 7920929298467255837957341)
                    ·
                      refine ⟨2970348486925220939234003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7920929298467255837957341 2970348486925220939234003)
                      ·
                        rfl

theorem cell23_5784733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_5784733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784733 prefixEnd_5784733 := by exact prefixLift 5784733
  have htrace : WordTrace (prefixWord ++ tailWord_5784733) baseStart_5784733 baseEnd_5784733 := by
    simpa [prefixWord, tailWord_5784733, baseEnd_5784733] using wordTrace_append hprefix tailTrace_5784733
  have hstable : (prefixWord ++ tailWord_5784733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784733).length < 2 ^ (prefixWord ++ tailWord_5784733).sum := by decide
  have hdescent : baseEnd_5784733 < baseStart_5784733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784753 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 9]
def baseStart_5784753 : Nat := 118140960795 + 5784753 * 2 ^ 59
def prefixEnd_5784753 : Nat := 4983230072969 + 3 ^ 40 * 5784753 * 2
def baseEnd_5784753 : Nat := 330039861837590095664879

theorem tailTrace_5784753 : CollatzResearch.WordTrace tailWord_5784753 prefixEnd_5784753 330039861837590095664879 := by
  unfold tailWord_5784753
  simp only [CollatzResearch.WordTrace]
  refine ⟨210987275211835313002222913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140658183474556875334815275 210987275211835313002222913)
  ·
    refine ⟨158240456408876484751667185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210987275211835313002222913 158240456408876484751667185)
    ·
      refine ⟨118680342306657363563750389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158240456408876484751667185 118680342306657363563750389)
      ·
        refine ⟨11126282091249127834101599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118680342306657363563750389 11126282091249127834101599)
        ·
          refine ⟨16689423136873691751152399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11126282091249127834101599 16689423136873691751152399)
          ·
            refine ⟨25034134705310537626728599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16689423136873691751152399 25034134705310537626728599)
            ·
              refine ⟨37551202057965806440092899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25034134705310537626728599 37551202057965806440092899)
              ·
                refine ⟨56326803086948709660139349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37551202057965806440092899 56326803086948709660139349)
                ·
                  refine ⟨330039861837590095664879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56326803086948709660139349 330039861837590095664879)
                  ·
                    rfl

theorem cell23_5784753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_5784753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784753 prefixEnd_5784753 := by exact prefixLift 5784753
  have htrace : WordTrace (prefixWord ++ tailWord_5784753) baseStart_5784753 baseEnd_5784753 := by
    simpa [prefixWord, tailWord_5784753, baseEnd_5784753] using wordTrace_append hprefix tailTrace_5784753
  have hstable : (prefixWord ++ tailWord_5784753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784753).length < 2 ^ (prefixWord ++ tailWord_5784753).sum := by decide
  have hdescent : baseEnd_5784753 < baseStart_5784753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784843 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 8]
def baseStart_5784843 : Nat := 118140960795 + 5784843 * 2 ^ 59
def prefixEnd_5784843 : Nat := 4983230072969 + 3 ^ 40 * 5784843 * 2
def baseEnd_5784843 : Nat := 330044996644135056539833

theorem tailTrace_5784843 : CollatzResearch.WordTrace tailWord_5784843 prefixEnd_5784843 330044996644135056539833 := by
  unfold tailWord_5784843
  simp only [CollatzResearch.WordTrace]
  refine ⟨210990557781509258372999183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140660371854339505581999455 210990557781509258372999183)
  ·
    refine ⟨316485836672263887559498775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210990557781509258372999183 316485836672263887559498775)
    ·
      refine ⟨474728755008395831339248163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316485836672263887559498775 474728755008395831339248163)
      ·
        refine ⟨712093132512593747008872245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474728755008395831339248163 712093132512593747008872245)
        ·
          refine ⟨66758731173055663782081773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 712093132512593747008872245 66758731173055663782081773)
          ·
            refine ⟨25034524189895873918280665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66758731173055663782081773 25034524189895873918280665)
            ·
              refine ⟨18775893142421905438710499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25034524189895873918280665 18775893142421905438710499)
              ·
                refine ⟨28163839713632858158065749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18775893142421905438710499 28163839713632858158065749)
                ·
                  refine ⟨330044996644135056539833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28163839713632858158065749 330044996644135056539833)
                  ·
                    rfl

theorem cell23_5784843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 8].length) (baseStart_5784843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784843 prefixEnd_5784843 := by exact prefixLift 5784843
  have htrace : WordTrace (prefixWord ++ tailWord_5784843) baseStart_5784843 baseEnd_5784843 := by
    simpa [prefixWord, tailWord_5784843, baseEnd_5784843] using wordTrace_append hprefix tailTrace_5784843
  have hstable : (prefixWord ++ tailWord_5784843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784843).length < 2 ^ (prefixWord ++ tailWord_5784843).sum := by decide
  have hdescent : baseEnd_5784843 < baseStart_5784843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784874 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5784874 : Nat := 118140960795 + 5784874 * 2 ^ 59
def prefixEnd_5784874 : Nat := 4983230072969 + 3 ^ 40 * 5784874 * 2
def baseEnd_5784874 : Nat := 2970420887697504887570855

theorem tailTrace_5784874 : CollatzResearch.WordTrace tailWord_5784874 prefixEnd_5784874 2970420887697504887570855 := by
  unfold tailWord_5784874
  simp only [CollatzResearch.WordTrace]
  refine ⟨52747922111099237666844419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140661125629597967111585117 52747922111099237666844419)
  ·
    refine ⟨79121883166648856500266629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52747922111099237666844419 79121883166648856500266629)
    ·
      refine ⟨14835353093746660593799993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79121883166648856500266629 14835353093746660593799993)
      ·
        refine ⟨11126514820309995445349995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14835353093746660593799993 11126514820309995445349995)
        ·
          refine ⟨16689772230464993168024993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11126514820309995445349995 16689772230464993168024993)
          ·
            refine ⟨12517329172848744876018745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16689772230464993168024993 12517329172848744876018745)
            ·
              refine ⟨9387996879636558657014059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12517329172848744876018745 9387996879636558657014059)
              ·
                refine ⟨14081995319454837985521089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387996879636558657014059 14081995319454837985521089)
                ·
                  refine ⟨10561496489591128489140817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14081995319454837985521089 10561496489591128489140817)
                  ·
                    refine ⟨7921122367193346366855613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10561496489591128489140817 7921122367193346366855613)
                    ·
                      refine ⟨2970420887697504887570855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921122367193346366855613 2970420887697504887570855)
                      ·
                        rfl

theorem cell23_5784874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5784874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784874 prefixEnd_5784874 := by exact prefixLift 5784874
  have htrace : WordTrace (prefixWord ++ tailWord_5784874) baseStart_5784874 baseEnd_5784874 := by
    simpa [prefixWord, tailWord_5784874, baseEnd_5784874] using wordTrace_append hprefix tailTrace_5784874
  have hstable : (prefixWord ++ tailWord_5784874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784874).length < 2 ^ (prefixWord ++ tailWord_5784874).sum := by decide
  have hdescent : baseEnd_5784874 < baseStart_5784874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784910 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_5784910 : Nat := 118140960795 + 5784910 * 2 ^ 59
def prefixEnd_5784910 : Nat := 4983230072969 + 3 ^ 40 * 5784910 * 2
def baseEnd_5784910 : Nat := 2970439373001066746720689

theorem tailTrace_5784910 : CollatzResearch.WordTrace tailWord_5784910 prefixEnd_5784910 2970439373001066746720689 := by
  unfold tailWord_5784910
  simp only [CollatzResearch.WordTrace]
  refine ⟨26374125184033316101961023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140662000981511019210458789 26374125184033316101961023)
  ·
    refine ⟨39561187776049974152941535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26374125184033316101961023 39561187776049974152941535)
    ·
      refine ⟨59341781664074961229412303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39561187776049974152941535 59341781664074961229412303)
      ·
        refine ⟨89012672496112441844118455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59341781664074961229412303 89012672496112441844118455)
        ·
          refine ⟨133519008744168662766177683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89012672496112441844118455 133519008744168662766177683)
          ·
            refine ⟨200278513116252994149266525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133519008744168662766177683 200278513116252994149266525)
            ·
              refine ⟨75104442418594872805974947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200278513116252994149266525 75104442418594872805974947)
              ·
                refine ⟨112656663627892309208962421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75104442418594872805974947 112656663627892309208962421)
                ·
                  refine ⟨10561562215114903988340227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112656663627892309208962421 10561562215114903988340227)
                  ·
                    refine ⟨15842343322672355982510341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10561562215114903988340227 15842343322672355982510341)
                    ·
                      refine ⟨2970439373001066746720689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15842343322672355982510341 2970439373001066746720689)
                      ·
                        rfl

theorem cell23_5784910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_5784910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784910 prefixEnd_5784910 := by exact prefixLift 5784910
  have htrace : WordTrace (prefixWord ++ tailWord_5784910) baseStart_5784910 baseEnd_5784910 := by
    simpa [prefixWord, tailWord_5784910, baseEnd_5784910] using wordTrace_append hprefix tailTrace_5784910
  have hstable : (prefixWord ++ tailWord_5784910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784910).length < 2 ^ (prefixWord ++ tailWord_5784910).sum := by decide
  have hdescent : baseEnd_5784910 < baseStart_5784910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784920 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_5784920 : Nat := 118140960795 + 5784920 * 2 ^ 59
def prefixEnd_5784920 : Nat := 4983230072969 + 3 ^ 40 * 5784920 * 2
def baseEnd_5784920 : Nat := 990148169269203902531881

theorem tailTrace_5784920 : CollatzResearch.WordTrace tailWord_5784920 prefixEnd_5784920 990148169269203902531881 := by
  unfold tailWord_5784920
  simp only [CollatzResearch.WordTrace]
  refine ⟨105496683101115150261776107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140662244134820200349034809 105496683101115150261776107)
  ·
    refine ⟨158245024651672725392664161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105496683101115150261776107 158245024651672725392664161)
    ·
      refine ⟨118683768488754544044498121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158245024651672725392664161 118683768488754544044498121)
      ·
        refine ⟨89012826366565908033373591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118683768488754544044498121 89012826366565908033373591)
        ·
          refine ⟨133519239549848862050060387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89012826366565908033373591 133519239549848862050060387)
          ·
            refine ⟨200278859324773293075090581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133519239549848862050060387 200278859324773293075090581)
            ·
              refine ⟨9388071530848748112894871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200278859324773293075090581 9388071530848748112894871)
              ·
                refine ⟨14082107296273122169342307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388071530848748112894871 14082107296273122169342307)
                ·
                  refine ⟨21123160944409683254013461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14082107296273122169342307 21123160944409683254013461)
                  ·
                    refine ⟨990148169269203902531881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21123160944409683254013461 990148169269203902531881)
                    ·
                      rfl

theorem cell23_5784920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_5784920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784920 prefixEnd_5784920 := by exact prefixLift 5784920
  have htrace : WordTrace (prefixWord ++ tailWord_5784920) baseStart_5784920 baseEnd_5784920 := by
    simpa [prefixWord, tailWord_5784920, baseEnd_5784920] using wordTrace_append hprefix tailTrace_5784920
  have hstable : (prefixWord ++ tailWord_5784920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784920).length < 2 ^ (prefixWord ++ tailWord_5784920).sum := by decide
  have hdescent : baseEnd_5784920 < baseStart_5784920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784925 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5784925 : Nat := 118140960795 + 5784925 * 2 ^ 59
def prefixEnd_5784925 : Nat := 4983230072969 + 3 ^ 40 * 5784925 * 2
def baseEnd_5784925 : Nat := 2970447075210884188033121

theorem tailTrace_5784925 : CollatzResearch.WordTrace tailWord_5784925 prefixEnd_5784925 2970447075210884188033121 := by
  unfold tailWord_5784925
  simp only [CollatzResearch.WordTrace]
  refine ⟨210993548567212186377484229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140662365711474790918322819 210993548567212186377484229)
  ·
    refine ⟨39561290356352284945778293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210993548567212186377484229 39561290356352284945778293)
    ·
      refine ⟨3708870970908026713666715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39561290356352284945778293 3708870970908026713666715)
      ·
        refine ⟨5563306456362040070500073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3708870970908026713666715 5563306456362040070500073)
        ·
          refine ⟨4172479842271530052875055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5563306456362040070500073 4172479842271530052875055)
          ·
            refine ⟨6258719763407295079312583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172479842271530052875055 6258719763407295079312583)
            ·
              refine ⟨9388079645110942618968875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258719763407295079312583 9388079645110942618968875)
              ·
                refine ⟨14082119467666413928453313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388079645110942618968875 14082119467666413928453313)
                ·
                  refine ⟨10561589600749810446339985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14082119467666413928453313 10561589600749810446339985)
                  ·
                    refine ⟨7921192200562357834754989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10561589600749810446339985 7921192200562357834754989)
                    ·
                      refine ⟨2970447075210884188033121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921192200562357834754989 2970447075210884188033121)
                      ·
                        rfl

theorem cell23_5784925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5784925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784925 prefixEnd_5784925 := by exact prefixLift 5784925
  have htrace : WordTrace (prefixWord ++ tailWord_5784925) baseStart_5784925 baseEnd_5784925 := by
    simpa [prefixWord, tailWord_5784925, baseEnd_5784925] using wordTrace_append hprefix tailTrace_5784925
  have hstable : (prefixWord ++ tailWord_5784925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784925).length < 2 ^ (prefixWord ++ tailWord_5784925).sum := by decide
  have hdescent : baseEnd_5784925 < baseStart_5784925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784938 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5784938 : Nat := 118140960795 + 5784938 * 2 ^ 59
def prefixEnd_5784938 : Nat := 4983230072969 + 3 ^ 40 * 5784938 * 2
def baseEnd_5784938 : Nat := 2970453750459392637170561

theorem tailTrace_5784938 : CollatzResearch.WordTrace tailWord_5784938 prefixEnd_5784938 2970453750459392637170561 := by
  unfold tailWord_5784938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52748505679041272399426867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140662681810776726398471645 52748505679041272399426867)
  ·
    refine ⟨79122758518561908599140301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52748505679041272399426867 79122758518561908599140301)
    ·
      refine ⟨29671034444460715724677613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79122758518561908599140301 29671034444460715724677613)
      ·
        refine ⟨11126637916672768396754105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29671034444460715724677613 11126637916672768396754105)
        ·
          refine ⟨8344978437504576297565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11126637916672768396754105 8344978437504576297565579)
          ·
            refine ⟨12517467656256864446348369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8344978437504576297565579 12517467656256864446348369)
            ·
              refine ⟨9388100742192648334761277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12517467656256864446348369 9388100742192648334761277)
              ·
                refine ⟨3520537778322243125535479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9388100742192648334761277 3520537778322243125535479)
                ·
                  refine ⟨5280806667483364688303219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520537778322243125535479 5280806667483364688303219)
                  ·
                    refine ⟨7921210001225047032454829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5280806667483364688303219 7921210001225047032454829)
                    ·
                      refine ⟨2970453750459392637170561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921210001225047032454829 2970453750459392637170561)
                      ·
                        rfl

theorem cell23_5784938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5784938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784938 prefixEnd_5784938 := by exact prefixLift 5784938
  have htrace : WordTrace (prefixWord ++ tailWord_5784938) baseStart_5784938 baseEnd_5784938 := by
    simpa [prefixWord, tailWord_5784938, baseEnd_5784938] using wordTrace_append hprefix tailTrace_5784938
  have hstable : (prefixWord ++ tailWord_5784938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784938).length < 2 ^ (prefixWord ++ tailWord_5784938).sum := by decide
  have hdescent : baseEnd_5784938 < baseStart_5784938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784960 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_5784960 : Nat := 118140960795 + 5784960 * 2 ^ 59
def prefixEnd_5784960 : Nat := 4983230072969 + 3 ^ 40 * 5784960 * 2
def baseEnd_5784960 : Nat := 2970465047033791551095459

theorem tailTrace_5784960 : CollatzResearch.WordTrace tailWord_5784960 prefixEnd_5784960 2970465047033791551095459 := by
  unfold tailWord_5784960
  simp only [CollatzResearch.WordTrace]
  refine ⟨105497412561042693677504167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140663216748056924903338889 105497412561042693677504167)
  ·
    refine ⟨158246118841564040516256251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105497412561042693677504167 158246118841564040516256251)
    ·
      refine ⟨237369178262346060774384377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158246118841564040516256251 237369178262346060774384377)
      ·
        refine ⟨178026883696759545580788283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237369178262346060774384377 178026883696759545580788283)
        ·
          refine ⟨267040325545139318371182425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178026883696759545580788283 267040325545139318371182425)
          ·
            refine ⟨200280244158854488778386819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267040325545139318371182425 200280244158854488778386819)
            ·
              refine ⟨300420366238281733167580229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200280244158854488778386819 300420366238281733167580229)
              ·
                refine ⟨56328818669677824968921293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300420366238281733167580229 56328818669677824968921293)
                ·
                  refine ⟨21123307001129184363345485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56328818669677824968921293 21123307001129184363345485)
                  ·
                    refine ⟨7921240125423444136254557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21123307001129184363345485 7921240125423444136254557)
                    ·
                      refine ⟨2970465047033791551095459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921240125423444136254557 2970465047033791551095459)
                      ·
                        rfl

theorem cell23_5784960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_5784960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784960 prefixEnd_5784960 := by exact prefixLift 5784960
  have htrace : WordTrace (prefixWord ++ tailWord_5784960) baseStart_5784960 baseEnd_5784960 := by
    simpa [prefixWord, tailWord_5784960, baseEnd_5784960] using wordTrace_append hprefix tailTrace_5784960
  have hstable : (prefixWord ++ tailWord_5784960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784960).length < 2 ^ (prefixWord ++ tailWord_5784960).sum := by decide
  have hdescent : baseEnd_5784960 < baseStart_5784960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784984 : List Nat := [2, 1, 2, 5, 2, 2, 2, 7]
def baseStart_5784984 : Nat := 118140960795 + 5784984 * 2 ^ 59
def prefixEnd_5784984 : Nat := 4983230072969 + 3 ^ 40 * 5784984 * 2
def baseEnd_5784984 : Nat := 110017680391462942859087

theorem tailTrace_5784984 : CollatzResearch.WordTrace tailWord_5784984 prefixEnd_5784984 110017680391462942859087 := by
  unfold tailWord_5784984
  simp only [CollatzResearch.WordTrace]
  refine ⟨105497850236999219726941003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140663800315998959635921337 105497850236999219726941003)
  ·
    refine ⟨158246775355498829590411505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105497850236999219726941003 158246775355498829590411505)
    ·
      refine ⟨118685081516624122192808629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158246775355498829590411505 118685081516624122192808629)
      ·
        refine ⟨11126726392183511455575809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118685081516624122192808629 11126726392183511455575809)
        ·
          refine ⟨8345044794137633591681857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11126726392183511455575809 8345044794137633591681857)
          ·
            refine ⟨6258783595603225193761393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345044794137633591681857 6258783595603225193761393)
            ·
              refine ⟨4694087696702418895321045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6258783595603225193761393 4694087696702418895321045)
              ·
                refine ⟨110017680391462942859087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4694087696702418895321045 110017680391462942859087)
                ·
                  rfl

theorem cell23_5784984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 7].length) (baseStart_5784984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784984 prefixEnd_5784984 := by exact prefixLift 5784984
  have htrace : WordTrace (prefixWord ++ tailWord_5784984) baseStart_5784984 baseEnd_5784984 := by
    simpa [prefixWord, tailWord_5784984, baseEnd_5784984] using wordTrace_append hprefix tailTrace_5784984
  have hstable : (prefixWord ++ tailWord_5784984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784984).length < 2 ^ (prefixWord ++ tailWord_5784984).sum := by decide
  have hdescent : baseEnd_5784984 < baseStart_5784984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784994 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5784994 : Nat := 118140960795 + 5784994 * 2 ^ 59
def prefixEnd_5784994 : Nat := 4983230072969 + 3 ^ 40 * 5784994 * 2
def baseEnd_5784994 : Nat := 2970482505376044418070303

theorem tailTrace_5784994 : CollatzResearch.WordTrace tailWord_5784994 prefixEnd_5784994 2970482505376044418070303 := by
  unfold tailWord_5784994
  simp only [CollatzResearch.WordTrace]
  refine ⟨52749016300990552790436509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140664043469308140774497357 52749016300990552790436509)
  ·
    refine ⟨19780881112871457296413691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52749016300990552790436509 19780881112871457296413691)
    ·
      refine ⟨29671321669307185944620537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19780881112871457296413691 29671321669307185944620537)
      ·
        refine ⟨22253491251980389458465403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29671321669307185944620537 22253491251980389458465403)
        ·
          refine ⟨33380236877970584187698105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22253491251980389458465403 33380236877970584187698105)
          ·
            refine ⟨25035177658477938140773579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33380236877970584187698105 25035177658477938140773579)
            ·
              refine ⟨37552766487716907211160369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25035177658477938140773579 37552766487716907211160369)
              ·
                refine ⟨28164574865787680408370277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37552766487716907211160369 28164574865787680408370277)
                ·
                  refine ⟨5280857787335190076569427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28164574865787680408370277 5280857787335190076569427)
                  ·
                    refine ⟨7921286681002785114854141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5280857787335190076569427 7921286681002785114854141)
                    ·
                      refine ⟨2970482505376044418070303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921286681002785114854141 2970482505376044418070303)
                      ·
                        rfl

theorem cell23_5784994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5784994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784994 prefixEnd_5784994 := by exact prefixLift 5784994
  have htrace : WordTrace (prefixWord ++ tailWord_5784994) baseStart_5784994 baseEnd_5784994 := by
    simpa [prefixWord, tailWord_5784994, baseEnd_5784994] using wordTrace_append hprefix tailTrace_5784994
  have hstable : (prefixWord ++ tailWord_5784994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784994).length < 2 ^ (prefixWord ++ tailWord_5784994).sum := by decide
  have hdescent : baseEnd_5784994 < baseStart_5784994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785004 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_5785004 : Nat := 118140960795 + 5785004 * 2 ^ 59
def prefixEnd_5785004 : Nat := 4983230072969 + 3 ^ 40 * 5785004 * 2
def baseEnd_5785004 : Nat := 2970487640182589378945257

theorem tailTrace_5785004 : CollatzResearch.WordTrace tailWord_5785004 prefixEnd_5785004 2970487640182589378945257 := by
  unfold tailWord_5785004
  simp only [CollatzResearch.WordTrace]
  refine ⟨105498214966962991434805033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140664286622617321913073377 105498214966962991434805033)
  ·
    refine ⟨79123661225222243576103775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105498214966962991434805033 79123661225222243576103775)
    ·
      refine ⟨118685491837833365364155663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79123661225222243576103775 118685491837833365364155663)
      ·
        refine ⟨178028237756750048046233495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118685491837833365364155663 178028237756750048046233495)
        ·
          refine ⟨267042356635125072069350243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178028237756750048046233495 267042356635125072069350243)
          ·
            refine ⟨400563534952687608104025365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267042356635125072069350243 400563534952687608104025365)
            ·
              refine ⟨18776415700907231629876189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 400563534952687608104025365 18776415700907231629876189)
              ·
                refine ⟨7041155887840211861203571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18776415700907231629876189 7041155887840211861203571)
                ·
                  refine ⟨10561733831760317791805357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041155887840211861203571 10561733831760317791805357)
                  ·
                    refine ⟨3960650186910119171927009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10561733831760317791805357 3960650186910119171927009)
                    ·
                      refine ⟨2970487640182589378945257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960650186910119171927009 2970487640182589378945257)
                      ·
                        rfl

theorem cell23_5785004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_5785004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785004 prefixEnd_5785004 := by exact prefixLift 5785004
  have htrace : WordTrace (prefixWord ++ tailWord_5785004) baseStart_5785004 baseEnd_5785004 := by
    simpa [prefixWord, tailWord_5785004, baseEnd_5785004] using wordTrace_append hprefix tailTrace_5785004
  have hstable : (prefixWord ++ tailWord_5785004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785004).length < 2 ^ (prefixWord ++ tailWord_5785004).sum := by decide
  have hdescent : baseEnd_5785004 < baseStart_5785004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785010 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_5785010 : Nat := 118140960795 + 5785010 * 2 ^ 59
def prefixEnd_5785010 : Nat := 4983230072969 + 3 ^ 40 * 5785010 * 2
def baseEnd_5785010 : Nat := 990163573688838785156743

theorem tailTrace_5785010 : CollatzResearch.WordTrace tailWord_5785010 prefixEnd_5785010 990163573688838785156743 := by
  unfold tailWord_5785010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52749162192976061473582121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140664432514602830596218989 52749162192976061473582121)
  ·
    refine ⟨39561871644732046105186591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52749162192976061473582121 39561871644732046105186591)
    ·
      refine ⟨59342807467098069157779887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39561871644732046105186591 59342807467098069157779887)
      ·
        refine ⟨89014211200647103736669831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59342807467098069157779887 89014211200647103736669831)
        ·
          refine ⟨133521316800970655605004747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89014211200647103736669831 133521316800970655605004747)
          ·
            refine ⟨200281975201455983407507121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133521316800970655605004747 200281975201455983407507121)
            ·
              refine ⟨150211481401091987555630341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200281975201455983407507121 150211481401091987555630341)
              ·
                refine ⟨28164652762704747666680689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150211481401091987555630341 28164652762704747666680689)
                ·
                  refine ⟨21123489572028560750010517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28164652762704747666680689 21123489572028560750010517)
                  ·
                    refine ⟨990163573688838785156743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21123489572028560750010517 990163573688838785156743)
                    ·
                      rfl

theorem cell23_5785010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_5785010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785010 prefixEnd_5785010 := by exact prefixLift 5785010
  have htrace : WordTrace (prefixWord ++ tailWord_5785010) baseStart_5785010 baseEnd_5785010 := by
    simpa [prefixWord, tailWord_5785010, baseEnd_5785010] using wordTrace_append hprefix tailTrace_5785010
  have hstable : (prefixWord ++ tailWord_5785010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785010).length < 2 ^ (prefixWord ++ tailWord_5785010).sum := by decide
  have hdescent : baseEnd_5785010 < baseStart_5785010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785028 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5785028 : Nat := 118140960795 + 5785028 * 2 ^ 59
def prefixEnd_5785028 : Nat := 4983230072969 + 3 ^ 40 * 5785028 * 2
def baseEnd_5785028 : Nat := 2970499963718297285045147

theorem tailTrace_5785028 : CollatzResearch.WordTrace tailWord_5785028 prefixEnd_5785028 2970499963718297285045147 := by
  unfold tailWord_5785028
  simp only [CollatzResearch.WordTrace]
  refine ⟨105498652642919517484241869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140664870190559356645655825 105498652642919517484241869)
  ·
    refine ⟨39561994741094819056590701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105498652642919517484241869 39561994741094819056590701)
    ·
      refine ⟨14835748027910557146221513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39561994741094819056590701 14835748027910557146221513)
      ·
        refine ⟨11126811020932917859666135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14835748027910557146221513 11126811020932917859666135)
        ·
          refine ⟨16690216531399376789499203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11126811020932917859666135 16690216531399376789499203)
          ·
            refine ⟨25035324797099065184248805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16690216531399376789499203 25035324797099065184248805)
            ·
              refine ⟨4694123399456074722046651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25035324797099065184248805 4694123399456074722046651)
              ·
                refine ⟨7041185099184112083069977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694123399456074722046651 7041185099184112083069977)
                ·
                  refine ⟨5280888824388084062302483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7041185099184112083069977 5280888824388084062302483)
                  ·
                    refine ⟨7921333236582126093453725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5280888824388084062302483 7921333236582126093453725)
                    ·
                      refine ⟨2970499963718297285045147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921333236582126093453725 2970499963718297285045147)
                      ·
                        rfl

theorem cell23_5785028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5785028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785028 prefixEnd_5785028 := by exact prefixLift 5785028
  have htrace : WordTrace (prefixWord ++ tailWord_5785028) baseStart_5785028 baseEnd_5785028 := by
    simpa [prefixWord, tailWord_5785028, baseEnd_5785028] using wordTrace_append hprefix tailTrace_5785028
  have hstable : (prefixWord ++ tailWord_5785028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785028).length < 2 ^ (prefixWord ++ tailWord_5785028).sum := by decide
  have hdescent : baseEnd_5785028 < baseStart_5785028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785107 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4]
def baseStart_5785107 : Nat := 118140960795 + 5785107 * 2 ^ 59
def prefixEnd_5785107 : Nat := 4983230072969 + 3 ^ 40 * 5785107 * 2
def baseEnd_5785107 : Nat := 2970540528690002475957283

theorem tailTrace_5785107 : CollatzResearch.WordTrace tailWord_5785107 prefixEnd_5785107 2970540528690002475957283 := by
  unfold tailWord_5785107
  simp only [CollatzResearch.WordTrace]
  refine ⟨211000186652552831460609575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140666791101701887640406383 211000186652552831460609575)
  ·
    refine ⟨316500279978829247190914363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211000186652552831460609575 316500279978829247190914363)
    ·
      refine ⟨474750419968243870786371545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316500279978829247190914363 474750419968243870786371545)
      ·
        refine ⟨356062814976182903089778659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474750419968243870786371545 356062814976182903089778659)
        ·
          refine ⟨534094222464274354634667989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356062814976182903089778659 534094222464274354634667989)
          ·
            refine ⟨12517833339006430186750031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 534094222464274354634667989 12517833339006430186750031)
            ·
              refine ⟨18776750008509645280125047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12517833339006430186750031 18776750008509645280125047)
              ·
                refine ⟨28165125012764467920187571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18776750008509645280125047 28165125012764467920187571)
                ·
                  refine ⟨42247687519146701880281357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28165125012764467920187571 42247687519146701880281357)
                  ·
                    refine ⟨15842882819680013205105509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42247687519146701880281357 15842882819680013205105509)
                    ·
                      refine ⟨2970540528690002475957283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15842882819680013205105509 2970540528690002475957283)
                      ·
                        rfl

theorem cell23_5785107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_5785107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785107 prefixEnd_5785107 := by exact prefixLift 5785107
  have htrace : WordTrace (prefixWord ++ tailWord_5785107) baseStart_5785107 baseEnd_5785107 := by
    simpa [prefixWord, tailWord_5785107, baseEnd_5785107] using wordTrace_append hprefix tailTrace_5785107
  have hstable : (prefixWord ++ tailWord_5785107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785107).length < 2 ^ (prefixWord ++ tailWord_5785107).sum := by decide
  have hdescent : baseEnd_5785107 < baseStart_5785107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785108 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 5]
def baseStart_5785108 : Nat := 118140960795 + 5785108 * 2 ^ 59
def prefixEnd_5785108 : Nat := 4983230072969 + 3 ^ 40 * 5785108 * 2
def baseEnd_5785108 : Nat := 330060115796739663560531

theorem tailTrace_5785108 : CollatzResearch.WordTrace tailWord_5785108 prefixEnd_5785108 330060115796739663560531 := by
  unfold tailWord_5785108
  simp only [CollatzResearch.WordTrace]
  refine ⟨105500111562774604315697989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140666815417032805754263985 105500111562774604315697989)
  ·
    refine ⟨19781270918020238309193373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105500111562774604315697989 19781270918020238309193373)
    ·
      refine ⟨7417976594257589365947515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19781270918020238309193373 7417976594257589365947515)
      ·
        refine ⟨11126964891386384048921273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417976594257589365947515 11126964891386384048921273)
        ·
          refine ⟨8345223668539788036690955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11126964891386384048921273 8345223668539788036690955)
          ·
            refine ⟨12517835502809682055036433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345223668539788036690955 12517835502809682055036433)
            ·
              refine ⟨9388376627107261541277325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12517835502809682055036433 9388376627107261541277325)
              ·
                refine ⟨3520641235165223077978997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9388376627107261541277325 3520641235165223077978997)
                ·
                  refine ⟨330060115796739663560531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3520641235165223077978997 330060115796739663560531)
                  ·
                    rfl

theorem cell23_5785108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_5785108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785108 prefixEnd_5785108 := by exact prefixLift 5785108
  have htrace : WordTrace (prefixWord ++ tailWord_5785108) baseStart_5785108 baseEnd_5785108 := by
    simpa [prefixWord, tailWord_5785108, baseEnd_5785108] using wordTrace_append hprefix tailTrace_5785108
  have hstable : (prefixWord ++ tailWord_5785108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785108).length < 2 ^ (prefixWord ++ tailWord_5785108).sum := by decide
  have hdescent : baseEnd_5785108 < baseStart_5785108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785157 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_5785157 : Nat := 118140960795 + 5785157 * 2 ^ 59
def prefixEnd_5785157 : Nat := 4983230072969 + 3 ^ 40 * 5785157 * 2
def baseEnd_5785157 : Nat := 2970566202722727280332053

theorem tailTrace_5785157 : CollatzResearch.WordTrace tailWord_5785157 prefixEnd_5785157 2970566202722727280332053 := by
  unfold tailWord_5785157
  simp only [CollatzResearch.WordTrace]
  refine ⟨211002010302371689999929725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140668006868247793333286483 211002010302371689999929725)
  ·
    refine ⟨79125753863389383749973647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211002010302371689999929725 79125753863389383749973647)
    ·
      refine ⟨118688630795084075624960471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79125753863389383749973647 118688630795084075624960471)
      ·
        refine ⟨178032946192626113437440707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118688630795084075624960471 178032946192626113437440707)
        ·
          refine ⟨267049419288939170156161061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178032946192626113437440707 267049419288939170156161061)
          ·
            refine ⟨50071766116676094404280199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267049419288939170156161061 50071766116676094404280199)
            ·
              refine ⟨75107649175014141606420299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50071766116676094404280199 75107649175014141606420299)
              ·
                refine ⟨112661473762521212409630449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75107649175014141606420299 112661473762521212409630449)
                ·
                  refine ⟨84496105321890909307222837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112661473762521212409630449 84496105321890909307222837)
                  ·
                    refine ⟨7921509873927272747552141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84496105321890909307222837 7921509873927272747552141)
                    ·
                      refine ⟨2970566202722727280332053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921509873927272747552141 2970566202722727280332053)
                      ·
                        rfl

theorem cell23_5785157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_5785157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785157 prefixEnd_5785157 := by exact prefixLift 5785157
  have htrace : WordTrace (prefixWord ++ tailWord_5785157) baseStart_5785157 baseEnd_5785157 := by
    simpa [prefixWord, tailWord_5785157, baseEnd_5785157] using wordTrace_append hprefix tailTrace_5785157
  have hstable : (prefixWord ++ tailWord_5785157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785157).length < 2 ^ (prefixWord ++ tailWord_5785157).sum := by decide
  have hdescent : baseEnd_5785157 < baseStart_5785157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785191 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_5785191 : Nat := 118140960795 + 5785191 * 2 ^ 59
def prefixEnd_5785191 : Nat := 4983230072969 + 3 ^ 40 * 5785191 * 2
def baseEnd_5785191 : Nat := 2970583661064980147306897

theorem tailTrace_5785191 : CollatzResearch.WordTrace tailWord_5785191 prefixEnd_5785191 2970583661064980147306897 := by
  unfold tailWord_5785191
  simp only [CollatzResearch.WordTrace]
  refine ⟨211003250384248513806667427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140668833589499009204444951 211003250384248513806667427)
  ·
    refine ⟨316504875576372770710001141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211003250384248513806667427 316504875576372770710001141)
    ·
      refine ⟨29672332085284947254062607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316504875576372770710001141 29672332085284947254062607)
      ·
        refine ⟨44508498127927420881093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29672332085284947254062607 44508498127927420881093911)
        ·
          refine ⟨66762747191891131321640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44508498127927420881093911 66762747191891131321640867)
          ·
            refine ⟨100144120787836696982461301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66762747191891131321640867 100144120787836696982461301)
            ·
              refine ⟨9388511323859690342105747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100144120787836696982461301 9388511323859690342105747)
              ·
                refine ⟨14082766985789535513158621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388511323859690342105747 14082766985789535513158621)
                ·
                  refine ⟨5281037619671075817434483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14082766985789535513158621 5281037619671075817434483)
                  ·
                    refine ⟨7921556429506613726151725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5281037619671075817434483 7921556429506613726151725)
                    ·
                      refine ⟨2970583661064980147306897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921556429506613726151725 2970583661064980147306897)
                      ·
                        rfl

theorem cell23_5785191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_5785191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785191 prefixEnd_5785191 := by exact prefixLift 5785191
  have htrace : WordTrace (prefixWord ++ tailWord_5785191) baseStart_5785191 baseEnd_5785191 := by
    simpa [prefixWord, tailWord_5785191, baseEnd_5785191] using wordTrace_append hprefix tailTrace_5785191
  have hstable : (prefixWord ++ tailWord_5785191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785191).length < 2 ^ (prefixWord ++ tailWord_5785191).sum := by decide
  have hdescent : baseEnd_5785191 < baseStart_5785191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785198 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_5785198 : Nat := 118140960795 + 5785198 * 2 ^ 59
def prefixEnd_5785198 : Nat := 4983230072969 + 3 ^ 40 * 5785198 * 2
def baseEnd_5785198 : Nat := 330065250603284624435485

theorem tailTrace_5785198 : CollatzResearch.WordTrace tailWord_5785198 prefixEnd_5785198 330065250603284624435485 := by
  unfold tailWord_5785198
  simp only [CollatzResearch.WordTrace]
  refine ⟨26375438211902894250271531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140669003796815436001448165 26375438211902894250271531)
  ·
    refine ⟨39563157317854341375407297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26375438211902894250271531 39563157317854341375407297)
    ·
      refine ⟨29672367988390756031555473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39563157317854341375407297 29672367988390756031555473)
      ·
        refine ⟨22254275991293067023666605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29672367988390756031555473 22254275991293067023666605)
        ·
          refine ⟨8345353496734900133874977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22254275991293067023666605 8345353496734900133874977)
          ·
            refine ⟨6259015122551175100406233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345353496734900133874977 6259015122551175100406233)
            ·
              refine ⟨4694261341913381325304675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6259015122551175100406233 4694261341913381325304675)
              ·
                refine ⟨7041392012870071987957013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694261341913381325304675 7041392012870071987957013)
                ·
                  refine ⟨330065250603284624435485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7041392012870071987957013 330065250603284624435485)
                  ·
                    rfl

theorem cell23_5785198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_5785198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785198 prefixEnd_5785198 := by exact prefixLift 5785198
  have htrace : WordTrace (prefixWord ++ tailWord_5785198) baseStart_5785198 baseEnd_5785198 := by
    simpa [prefixWord, tailWord_5785198, baseEnd_5785198] using wordTrace_append hprefix tailTrace_5785198
  have hstable : (prefixWord ++ tailWord_5785198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785198).length < 2 ^ (prefixWord ++ tailWord_5785198).sum := by decide
  have hdescent : baseEnd_5785198 < baseStart_5785198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785207 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 1, 6]
def baseStart_5785207 : Nat := 118140960795 + 5785207 * 2 ^ 59
def prefixEnd_5785207 : Nat := 4983230072969 + 3 ^ 40 * 5785207 * 2
def baseEnd_5785207 : Nat := 990197292251817361568941

theorem tailTrace_5785207 : CollatzResearch.WordTrace tailWord_5785207 prefixEnd_5785207 990197292251817361568941 := by
  unfold tailWord_5785207
  simp only [CollatzResearch.WordTrace]
  refine ⟨211003833952190548539249875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140669222634793699026166583 211003833952190548539249875)
  ·
    refine ⟨316505750928285822808874813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211003833952190548539249875 316505750928285822808874813)
    ·
      refine ⟨118689656598107183553328055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316505750928285822808874813 118689656598107183553328055)
      ·
        refine ⟨178034484897160775329992083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118689656598107183553328055 178034484897160775329992083)
        ·
          refine ⟨267051727345741162994988125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178034484897160775329992083 267051727345741162994988125)
          ·
            refine ⟨100144397754652936123120547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267051727345741162994988125 100144397754652936123120547)
            ·
              refine ⟨150216596631979404184680821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100144397754652936123120547 150216596631979404184680821)
              ·
                refine ⟨14082805934248069142313827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150216596631979404184680821 14082805934248069142313827)
                ·
                  refine ⟨21124208901372103713470741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14082805934248069142313827 21124208901372103713470741)
                  ·
                    refine ⟨990197292251817361568941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21124208901372103713470741 990197292251817361568941)
                    ·
                      rfl

theorem cell23_5785207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_5785207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785207 prefixEnd_5785207 := by exact prefixLift 5785207
  have htrace : WordTrace (prefixWord ++ tailWord_5785207) baseStart_5785207 baseEnd_5785207 := by
    simpa [prefixWord, tailWord_5785207, baseEnd_5785207] using wordTrace_append hprefix tailTrace_5785207
  have hstable : (prefixWord ++ tailWord_5785207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785207).length < 2 ^ (prefixWord ++ tailWord_5785207).sum := by decide
  have hdescent : baseEnd_5785207 < baseStart_5785207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785261 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_5785261 : Nat := 118140960795 + 5785261 * 2 ^ 59
def prefixEnd_5785261 : Nat := 4983230072969 + 3 ^ 40 * 5785261 * 2
def baseEnd_5785261 : Nat := 2970619604710794873431575

theorem tailTrace_5785261 : CollatzResearch.WordTrace tailWord_5785261 prefixEnd_5785261 2970619604710794873431575 := by
  unfold tailWord_5785261
  simp only [CollatzResearch.WordTrace]
  refine ⟨211005803493994915761715637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140670535662663277174477091 211005803493994915761715637)
  ·
    refine ⟨19781794077562023352660841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211005803493994915761715637 19781794077562023352660841)
    ·
      refine ⟨14836345558171517514495631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19781794077562023352660841 14836345558171517514495631)
      ·
        refine ⟨22254518337257276271743447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14836345558171517514495631 22254518337257276271743447)
        ·
          refine ⟨33381777505885914407615171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22254518337257276271743447 33381777505885914407615171)
          ·
            refine ⟨50072666258828871611422757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33381777505885914407615171 50072666258828871611422757)
            ·
              refine ⟨9388624923530413427141767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50072666258828871611422757 9388624923530413427141767)
              ·
                refine ⟨14082937385295620140712651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388624923530413427141767 14082937385295620140712651)
                ·
                  refine ⟨21124406077943430211068977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14082937385295620140712651 21124406077943430211068977)
                  ·
                    refine ⟨15843304558457572658301733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21124406077943430211068977 15843304558457572658301733)
                    ·
                      refine ⟨2970619604710794873431575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15843304558457572658301733 2970619604710794873431575)
                      ·
                        rfl

theorem cell23_5785261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_5785261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785261 prefixEnd_5785261 := by exact prefixLift 5785261
  have htrace : WordTrace (prefixWord ++ tailWord_5785261) baseStart_5785261 baseEnd_5785261 := by
    simpa [prefixWord, tailWord_5785261, baseEnd_5785261] using wordTrace_append hprefix tailTrace_5785261
  have hstable : (prefixWord ++ tailWord_5785261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785261).length < 2 ^ (prefixWord ++ tailWord_5785261).sum := by decide
  have hdescent : baseEnd_5785261 < baseStart_5785261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785264 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_5785264 : Nat := 118140960795 + 5785264 * 2 ^ 59
def prefixEnd_5785264 : Nat := 4983230072969 + 3 ^ 40 * 5785264 * 2
def baseEnd_5785264 : Nat := 2970621145152758361694061

theorem tailTrace_5785264 : CollatzResearch.WordTrace tailWord_5785264 prefixEnd_5785264 2970621145152758361694061 := by
  unfold tailWord_5785264
  simp only [CollatzResearch.WordTrace]
  refine ⟨105502956456492023637037423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140670608608656031516049897 105502956456492023637037423)
  ·
    refine ⟨158254434684738035455556135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105502956456492023637037423 158254434684738035455556135)
    ·
      refine ⟨237381652027107053183334203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158254434684738035455556135 237381652027107053183334203)
      ·
        refine ⟨356072478040660579775001305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237381652027107053183334203 356072478040660579775001305)
        ·
          refine ⟨267054358530495434831250979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356072478040660579775001305 267054358530495434831250979)
          ·
            refine ⟨400581537795743152246876469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267054358530495434831250979 400581537795743152246876469)
            ·
              refine ⟨37554519168350920523144669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400581537795743152246876469 37554519168350920523144669)
              ·
                refine ⟨14082944688131595196179251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37554519168350920523144669 14082944688131595196179251)
                ·
                  refine ⟨21124417032197392794268877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14082944688131595196179251 21124417032197392794268877)
                  ·
                    refine ⟨7921656387074022297850829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21124417032197392794268877 7921656387074022297850829)
                    ·
                      refine ⟨2970621145152758361694061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921656387074022297850829 2970621145152758361694061)
                      ·
                        rfl

theorem cell23_5785264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_5785264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785264 prefixEnd_5785264 := by exact prefixLift 5785264
  have htrace : WordTrace (prefixWord ++ tailWord_5785264) baseStart_5785264 baseEnd_5785264 := by
    simpa [prefixWord, tailWord_5785264, baseEnd_5785264] using wordTrace_append hprefix tailTrace_5785264
  have hstable : (prefixWord ++ tailWord_5785264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785264).length < 2 ^ (prefixWord ++ tailWord_5785264).sum := by decide
  have hdescent : baseEnd_5785264 < baseStart_5785264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785267 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 7]
def baseStart_5785267 : Nat := 118140960795 + 5785267 * 2 ^ 59
def prefixEnd_5785267 : Nat := 4983230072969 + 3 ^ 40 * 5785267 * 2
def baseEnd_5785267 : Nat := 990207561864907283318849

theorem tailTrace_5785267 : CollatzResearch.WordTrace tailWord_5785267 prefixEnd_5785267 990207561864907283318849 := by
  unfold tailWord_5785267
  simp only [CollatzResearch.WordTrace]
  refine ⟨211006022331973178786434055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140670681554648785857622703 211006022331973178786434055)
  ·
    refine ⟨316509033497959768179651083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211006022331973178786434055 316509033497959768179651083)
    ·
      refine ⟨474763550246939652269476625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316509033497959768179651083 474763550246939652269476625)
      ·
        refine ⟨356072662685204739202107469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474763550246939652269476625 356072662685204739202107469)
        ·
          refine ⟨133527248506951777200790301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356072662685204739202107469 133527248506951777200790301)
          ·
            refine ⟨50072718190106916450296363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133527248506951777200790301 50072718190106916450296363)
            ·
              refine ⟨75109077285160374675444545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50072718190106916450296363 75109077285160374675444545)
              ·
                refine ⟨56331807963870281006583409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75109077285160374675444545 56331807963870281006583409)
                ·
                  refine ⟨42248855972902710754937557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56331807963870281006583409 42248855972902710754937557)
                  ·
                    refine ⟨990207561864907283318849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42248855972902710754937557 990207561864907283318849)
                    ·
                      rfl

theorem cell23_5785267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_5785267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785267 prefixEnd_5785267 := by exact prefixLift 5785267
  have htrace : WordTrace (prefixWord ++ tailWord_5785267) baseStart_5785267 baseEnd_5785267 := by
    simpa [prefixWord, tailWord_5785267, baseEnd_5785267] using wordTrace_append hprefix tailTrace_5785267
  have hstable : (prefixWord ++ tailWord_5785267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785267).length < 2 ^ (prefixWord ++ tailWord_5785267).sum := by decide
  have hdescent : baseEnd_5785267 < baseStart_5785267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785282 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5785282 : Nat := 118140960795 + 5785282 * 2 ^ 59
def prefixEnd_5785282 : Nat := 4983230072969 + 3 ^ 40 * 5785282 * 2
def baseEnd_5785282 : Nat := 2970630387804539291268979

theorem tailTrace_5785282 : CollatzResearch.WordTrace tailWord_5785282 prefixEnd_5785282 2970630387804539291268979 := by
  unfold tailWord_5785282
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751642356729709087057525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140671046284612557565486733 52751642356729709087057525)
  ·
    refine ⟨4945466470943410226911643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52751642356729709087057525 4945466470943410226911643)
    ·
      refine ⟨7418199706415115340367465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4945466470943410226911643 7418199706415115340367465)
      ·
        refine ⟨5563649779811336505275599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7418199706415115340367465 5563649779811336505275599)
        ·
          refine ⟨8345474669717004757913399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563649779811336505275599 8345474669717004757913399)
          ·
            refine ⟨12518212004575507136870099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345474669717004757913399 12518212004575507136870099)
            ·
              refine ⟨18777318006863260705305149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518212004575507136870099 18777318006863260705305149)
              ·
                refine ⟨7041494252573722764489431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18777318006863260705305149 7041494252573722764489431)
                ·
                  refine ⟨10562241378860584146734147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041494252573722764489431 10562241378860584146734147)
                  ·
                    refine ⟨15843362068290876220101221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10562241378860584146734147 15843362068290876220101221)
                    ·
                      refine ⟨2970630387804539291268979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15843362068290876220101221 2970630387804539291268979)
                      ·
                        rfl

theorem cell23_5785282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5785282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785282 prefixEnd_5785282 := by exact prefixLift 5785282
  have htrace : WordTrace (prefixWord ++ tailWord_5785282) baseStart_5785282 baseEnd_5785282 := by
    simpa [prefixWord, tailWord_5785282, baseEnd_5785282] using wordTrace_append hprefix tailTrace_5785282
  have hstable : (prefixWord ++ tailWord_5785282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785282).length < 2 ^ (prefixWord ++ tailWord_5785282).sum := by decide
  have hdescent : baseEnd_5785282 < baseStart_5785282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785298 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_5785298 : Nat := 118140960795 + 5785298 * 2 ^ 59
def prefixEnd_5785298 : Nat := 4983230072969 + 3 ^ 40 * 5785298 * 2
def baseEnd_5785298 : Nat := 2970638603495011228668905

theorem tailTrace_5785298 : CollatzResearch.WordTrace tailWord_5785298 prefixEnd_5785298 2970638603495011228668905 := by
  unfold tailWord_5785298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52751788248715217770203137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140671435329907247387208365 52751788248715217770203137)
  ·
    refine ⟨39563841186536413327652353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52751788248715217770203137 39563841186536413327652353)
    ·
      refine ⟨29672880889902309995739265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39563841186536413327652353 29672880889902309995739265)
      ·
        refine ⟨22254660667426732496804449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29672880889902309995739265 22254660667426732496804449)
        ·
          refine ⟨16690995500570049372603337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22254660667426732496804449 16690995500570049372603337)
          ·
            refine ⟨12518246625427537029452503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16690995500570049372603337 12518246625427537029452503)
            ·
              refine ⟨18777369938141305544178755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518246625427537029452503 18777369938141305544178755)
              ·
                refine ⟨28166054907211958316268133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18777369938141305544178755 28166054907211958316268133)
                ·
                  refine ⟨5281135295102242184300275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28166054907211958316268133 5281135295102242184300275)
                  ·
                    refine ⟨7921702942653363276450413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5281135295102242184300275 7921702942653363276450413)
                    ·
                      refine ⟨2970638603495011228668905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921702942653363276450413 2970638603495011228668905)
                      ·
                        rfl

theorem cell23_5785298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_5785298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785298 prefixEnd_5785298 := by exact prefixLift 5785298
  have htrace : WordTrace (prefixWord ++ tailWord_5785298) baseStart_5785298 baseEnd_5785298 := by
    simpa [prefixWord, tailWord_5785298, baseEnd_5785298] using wordTrace_append hprefix tailTrace_5785298
  have hstable : (prefixWord ++ tailWord_5785298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785298).length < 2 ^ (prefixWord ++ tailWord_5785298).sum := by decide
  have hdescent : baseEnd_5785298 < baseStart_5785298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785315 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5785315 : Nat := 118140960795 + 5785315 * 2 ^ 59
def prefixEnd_5785315 : Nat := 4983230072969 + 3 ^ 40 * 5785315 * 2
def baseEnd_5785315 : Nat := 2970647332666137662156327

theorem tailTrace_5785315 : CollatzResearch.WordTrace tailWord_5785315 prefixEnd_5785315 2970647332666137662156327 := by
  unfold tailWord_5785315
  simp only [CollatzResearch.WordTrace]
  refine ⟨211007773035799282984181399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140671848690532855322787599 211007773035799282984181399)
  ·
    refine ⟨316511659553698924476272099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211007773035799282984181399 316511659553698924476272099)
    ·
      refine ⟨474767489330548386714408149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316511659553698924476272099 474767489330548386714408149)
      ·
        refine ⟨11127363031184727813618941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 474767489330548386714408149 11127363031184727813618941)
        ·
          refine ⟨4172761136694272930107103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11127363031184727813618941 4172761136694272930107103)
          ·
            refine ⟨6259141705041409395160655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172761136694272930107103 6259141705041409395160655)
            ·
              refine ⟨9388712557562114092740983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259141705041409395160655 9388712557562114092740983)
              ·
                refine ⟨14083068836343171139111475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388712557562114092740983 14083068836343171139111475)
                ·
                  refine ⟨21124603254514756708667213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14083068836343171139111475 21124603254514756708667213)
                  ·
                    refine ⟨7921726220443033765750205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21124603254514756708667213 7921726220443033765750205)
                    ·
                      refine ⟨2970647332666137662156327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921726220443033765750205 2970647332666137662156327)
                      ·
                        rfl

theorem cell23_5785315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5785315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785315 prefixEnd_5785315 := by exact prefixLift 5785315
  have htrace : WordTrace (prefixWord ++ tailWord_5785315) baseStart_5785315 baseEnd_5785315 := by
    simpa [prefixWord, tailWord_5785315, baseEnd_5785315] using wordTrace_append hprefix tailTrace_5785315
  have hstable : (prefixWord ++ tailWord_5785315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785315).length < 2 ^ (prefixWord ++ tailWord_5785315).sum := by decide
  have hdescent : baseEnd_5785315 < baseStart_5785315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785324 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_5785324 : Nat := 118140960795 + 5785324 * 2 ^ 59
def prefixEnd_5785324 : Nat := 4983230072969 + 3 ^ 40 * 5785324 * 2
def baseEnd_5785324 : Nat := 2970651953992028126943785

theorem tailTrace_5785324 : CollatzResearch.WordTrace tailWord_5785324 prefixEnd_5785324 2970651953992028126943785 := by
  unfold tailWord_5785324
  simp only [CollatzResearch.WordTrace]
  refine ⟨105504050646383338760629513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140672067528511118347506017 105504050646383338760629513)
  ·
    refine ⟨79128037984787504070472135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105504050646383338760629513 79128037984787504070472135)
    ·
      refine ⟨118692056977181256105708203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79128037984787504070472135 118692056977181256105708203)
      ·
        refine ⟨178038085465771884158562305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118692056977181256105708203 178038085465771884158562305)
        ·
          refine ⟨133528564099328913118921729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178038085465771884158562305 133528564099328913118921729)
          ·
            refine ⟨100146423074496684839191297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133528564099328913118921729 100146423074496684839191297)
            ·
              refine ⟨75109817305872513629393473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100146423074496684839191297 75109817305872513629393473)
              ·
                refine ⟨56332362979404385222045105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75109817305872513629393473 56332362979404385222045105)
                ·
                  refine ⟨42249272234553288916533829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56332362979404385222045105 42249272234553288916533829)
                  ·
                    refine ⟨7921738543978741671850093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42249272234553288916533829 7921738543978741671850093)
                    ·
                      refine ⟨2970651953992028126943785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7921738543978741671850093 2970651953992028126943785)
                      ·
                        rfl

theorem cell23_5785324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_5785324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785324 prefixEnd_5785324 := by exact prefixLift 5785324
  have htrace : WordTrace (prefixWord ++ tailWord_5785324) baseStart_5785324 baseEnd_5785324 := by
    simpa [prefixWord, tailWord_5785324, baseEnd_5785324] using wordTrace_append hprefix tailTrace_5785324
  have hstable : (prefixWord ++ tailWord_5785324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785324).length < 2 ^ (prefixWord ++ tailWord_5785324).sum := by decide
  have hdescent : baseEnd_5785324 < baseStart_5785324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785325 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_5785325 : Nat := 118140960795 + 5785325 * 2 ^ 59
def prefixEnd_5785325 : Nat := 4983230072969 + 3 ^ 40 * 5785325 * 2
def baseEnd_5785325 : Nat := 2970652467472682623031281

theorem tailTrace_5785325 : CollatzResearch.WordTrace tailWord_5785325 prefixEnd_5785325 2970652467472682623031281 := by
  unfold tailWord_5785325
  simp only [CollatzResearch.WordTrace]
  refine ⟨211008137765763054692045429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140672091843842036461363619 211008137765763054692045429)
  ·
    refine ⟨19782012915540286377379259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211008137765763054692045429 19782012915540286377379259)
    ·
      refine ⟨29673019373310429566068889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19782012915540286377379259 29673019373310429566068889)
      ·
        refine ⟨22254764529982822174551667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29673019373310429566068889 22254764529982822174551667)
        ·
          refine ⟨33382146794974233261827501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22254764529982822174551667 33382146794974233261827501)
          ·
            refine ⟨12518305048115337473185313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33382146794974233261827501 12518305048115337473185313)
            ·
              refine ⟨9388728786086503104888985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12518305048115337473185313 9388728786086503104888985)
              ·
                refine ⟨7041546589564877328666739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9388728786086503104888985 7041546589564877328666739)
                ·
                  refine ⟨10562319884347315993000109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041546589564877328666739 10562319884347315993000109)
                  ·
                    refine ⟨3960869956630243497375041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10562319884347315993000109 3960869956630243497375041)
                    ·
                      refine ⟨2970652467472682623031281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960869956630243497375041 2970652467472682623031281)
                      ·
                        rfl

theorem cell23_5785325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_5785325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785325 prefixEnd_5785325 := by exact prefixLift 5785325
  have htrace : WordTrace (prefixWord ++ tailWord_5785325) baseStart_5785325 baseEnd_5785325 := by
    simpa [prefixWord, tailWord_5785325, baseEnd_5785325] using wordTrace_append hprefix tailTrace_5785325
  have hstable : (prefixWord ++ tailWord_5785325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785325).length < 2 ^ (prefixWord ++ tailWord_5785325).sum := by decide
  have hdescent : baseEnd_5785325 < baseStart_5785325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785350 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5785350 : Nat := 118140960795 + 5785350 * 2 ^ 59
def prefixEnd_5785350 : Nat := 4983230072969 + 3 ^ 40 * 5785350 * 2
def baseEnd_5785350 : Nat := 2970665304489045025218667

theorem tailTrace_5785350 : CollatzResearch.WordTrace tailWord_5785350 prefixEnd_5785350 2970665304489045025218667 := by
  unfold tailWord_5785350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594032799708515123803297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140672699727114989307803669 6594032799708515123803297)
  ·
    refine ⟨4945524599781386342852473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6594032799708515123803297 4945524599781386342852473)
    ·
      refine ⟨3709143449836039757139355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4945524599781386342852473 3709143449836039757139355)
      ·
        refine ⟨5563715174754059635709033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709143449836039757139355 5563715174754059635709033)
        ·
          refine ⟨4172786381065544726781775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5563715174754059635709033 4172786381065544726781775)
          ·
            refine ⟨6259179571598317090172663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172786381065544726781775 6259179571598317090172663)
            ·
              refine ⟨9388769357397475635258995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259179571598317090172663 9388769357397475635258995)
              ·
                refine ⟨14083154036096213452888493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388769357397475635258995 14083154036096213452888493)
                ·
                  refine ⟨5281182763536080044833185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14083154036096213452888493 5281182763536080044833185)
                  ·
                    refine ⟨3960887072652060033624889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5281182763536080044833185 3960887072652060033624889)
                    ·
                      refine ⟨2970665304489045025218667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960887072652060033624889 2970665304489045025218667)
                      ·
                        rfl

theorem cell23_5785350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5785350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785350 prefixEnd_5785350 := by exact prefixLift 5785350
  have htrace : WordTrace (prefixWord ++ tailWord_5785350) baseStart_5785350 baseEnd_5785350 := by
    simpa [prefixWord, tailWord_5785350, baseEnd_5785350] using wordTrace_append hprefix tailTrace_5785350
  have hstable : (prefixWord ++ tailWord_5785350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785350).length < 2 ^ (prefixWord ++ tailWord_5785350).sum := by decide
  have hdescent : baseEnd_5785350 < baseStart_5785350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785411 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4]
def baseStart_5785411 : Nat := 118140960795 + 5785411 * 2 ^ 59
def prefixEnd_5785411 : Nat := 4983230072969 + 3 ^ 40 * 5785411 * 2
def baseEnd_5785411 : Nat := 2970696626808969286555885

theorem tailTrace_5785411 : CollatzResearch.WordTrace tailWord_5785411 prefixEnd_5785411 2970696626808969286555885 := by
  unfold tailWord_5785411
  simp only [CollatzResearch.WordTrace]
  refine ⟨211011274443451491379676087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140674182962300994253117391 211011274443451491379676087)
  ·
    refine ⟨316516911665177237069514131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211011274443451491379676087 316516911665177237069514131)
    ·
      refine ⟨474775367497765855604271197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316516911665177237069514131 474775367497765855604271197)
      ·
        refine ⟨178040762811662195851601699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474775367497765855604271197 178040762811662195851601699)
        ·
          refine ⟨267061144217493293777402549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178040762811662195851601699 267061144217493293777402549)
          ·
            refine ⟨25036982270389996291631489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267061144217493293777402549 25036982270389996291631489)
            ·
              refine ⟨18777736702792497218723617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25036982270389996291631489 18777736702792497218723617)
              ·
                refine ⟨14083302527094372914042713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18777736702792497218723617 14083302527094372914042713)
                ·
                  refine ⟨10562476895320779685532035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14083302527094372914042713 10562476895320779685532035)
                  ·
                    refine ⟨15843715342981169528298053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10562476895320779685532035 15843715342981169528298053)
                    ·
                      refine ⟨2970696626808969286555885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15843715342981169528298053 2970696626808969286555885)
                      ·
                        rfl

theorem cell23_5785411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_5785411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785411 prefixEnd_5785411 := by exact prefixLift 5785411
  have htrace : WordTrace (prefixWord ++ tailWord_5785411) baseStart_5785411 baseEnd_5785411 := by
    simpa [prefixWord, tailWord_5785411, baseEnd_5785411] using wordTrace_append hprefix tailTrace_5785411
  have hstable : (prefixWord ++ tailWord_5785411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785411).length < 2 ^ (prefixWord ++ tailWord_5785411).sum := by decide
  have hdescent : baseEnd_5785411 < baseStart_5785411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785424 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_5785424 : Nat := 118140960795 + 5785424 * 2 ^ 59
def prefixEnd_5785424 : Nat := 4983230072969 + 3 ^ 40 * 5785424 * 2
def baseEnd_5785424 : Nat := 2970703302057477735693325

theorem tailTrace_5785424 : CollatzResearch.WordTrace tailWord_5785424 prefixEnd_5785424 2970703302057477735693325 := by
  unfold tailWord_5785424
  simp only [CollatzResearch.WordTrace]
  refine ⟨105505874296202197299949663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140674499061602929733266217 105505874296202197299949663)
  ·
    refine ⟨158258811444303295949924495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105505874296202197299949663 158258811444303295949924495)
    ·
      refine ⟨237388217166454943924886743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158258811444303295949924495 237388217166454943924886743)
      ·
        refine ⟨356082325749682415887330115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237388217166454943924886743 356082325749682415887330115)
        ·
          refine ⟨534123488624523623830995173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356082325749682415887330115 534123488624523623830995173)
          ·
            refine ⟨100148154117098179468311595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 534123488624523623830995173 100148154117098179468311595)
            ·
              refine ⟨150222231175647269202467393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100148154117098179468311595 150222231175647269202467393)
              ·
                refine ⟨112666673381735451901850545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150222231175647269202467393 112666673381735451901850545)
                ·
                  refine ⟨84500005036301588926387909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112666673381735451901850545 84500005036301588926387909)
                  ·
                    refine ⟨15843750944306547923697733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84500005036301588926387909 15843750944306547923697733)
                    ·
                      refine ⟨2970703302057477735693325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15843750944306547923697733 2970703302057477735693325)
                      ·
                        rfl

theorem cell23_5785424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_5785424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785424 prefixEnd_5785424 := by exact prefixLift 5785424
  have htrace : WordTrace (prefixWord ++ tailWord_5785424) baseStart_5785424 baseEnd_5785424 := by
    simpa [prefixWord, tailWord_5785424, baseEnd_5785424] using wordTrace_append hprefix tailTrace_5785424
  have hstable : (prefixWord ++ tailWord_5785424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785424).length < 2 ^ (prefixWord ++ tailWord_5785424).sum := by decide
  have hdescent : baseEnd_5785424 < baseStart_5785424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785428 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_5785428 : Nat := 118140960795 + 5785428 * 2 ^ 59
def prefixEnd_5785428 : Nat := 4983230072969 + 3 ^ 40 * 5785428 * 2
def baseEnd_5785428 : Nat := 2970705355980095720043307

theorem tailTrace_5785428 : CollatzResearch.WordTrace tailWord_5785428 prefixEnd_5785428 2970705355980095720043307 := by
  unfold tailWord_5785428
  simp only [CollatzResearch.WordTrace]
  refine ⟨105505947242194951641522469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140674596322926602188696625 105505947242194951641522469)
  ·
    refine ⟨19782365107911553432785463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105505947242194951641522469 19782365107911553432785463)
    ·
      refine ⟨29673547661867330149178195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19782365107911553432785463 29673547661867330149178195)
      ·
        refine ⟨44510321492800995223767293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29673547661867330149178195 44510321492800995223767293)
        ·
          refine ⟨16691370559800373208912735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44510321492800995223767293 16691370559800373208912735)
          ·
            refine ⟨25037055839700559813369103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16691370559800373208912735 25037055839700559813369103)
            ·
              refine ⟨37555583759550839720053655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25037055839700559813369103 37555583759550839720053655)
              ·
                refine ⟨56333375639326259580080483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37555583759550839720053655 56333375639326259580080483)
                ·
                  refine ⟨84500063458989389370120725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56333375639326259580080483 84500063458989389370120725)
                  ·
                    refine ⟨3960940474640127626724409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84500063458989389370120725 3960940474640127626724409)
                    ·
                      refine ⟨2970705355980095720043307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3960940474640127626724409 2970705355980095720043307)
                      ·
                        rfl

theorem cell23_5785428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_5785428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785428 prefixEnd_5785428 := by exact prefixLift 5785428
  have htrace : WordTrace (prefixWord ++ tailWord_5785428) baseStart_5785428 baseEnd_5785428 := by
    simpa [prefixWord, tailWord_5785428, baseEnd_5785428] using wordTrace_append hprefix tailTrace_5785428
  have hstable : (prefixWord ++ tailWord_5785428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785428).length < 2 ^ (prefixWord ++ tailWord_5785428).sum := by decide
  have hdescent : baseEnd_5785428 < baseStart_5785428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785498 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_5785498 : Nat := 118140960795 + 5785498 * 2 ^ 59
def prefixEnd_5785498 : Nat := 4983230072969 + 3 ^ 40 * 5785498 * 2
def baseEnd_5785498 : Nat := 990247099875303482055995

theorem tailTrace_5785498 : CollatzResearch.WordTrace tailWord_5785498 prefixEnd_5785498 990247099875303482055995 := by
  unfold tailWord_5785498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52753611898534076309523287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140676298396090870158728765 52753611898534076309523287)
  ·
    refine ⟨79130417847801114464284931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52753611898534076309523287 79130417847801114464284931)
    ·
      refine ⟨118695626771701671696427397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79130417847801114464284931 118695626771701671696427397)
      ·
        refine ⟨22255430019694063443080137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118695626771701671696427397 22255430019694063443080137)
        ·
          refine ⟨16691572514770547582310103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22255430019694063443080137 16691572514770547582310103)
          ·
            refine ⟨25037358772155821373465155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16691572514770547582310103 25037358772155821373465155)
            ·
              refine ⟨37556038158233732060197733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25037358772155821373465155 37556038158233732060197733)
              ·
                refine ⟨7041757154668824761287075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37556038158233732060197733 7041757154668824761287075)
                ·
                  refine ⟨10562635732003237141930613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041757154668824761287075 10562635732003237141930613)
                  ·
                    refine ⟨990247099875303482055995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10562635732003237141930613 990247099875303482055995)
                    ·
                      rfl

theorem cell23_5785498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_5785498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785498 prefixEnd_5785498 := by exact prefixLift 5785498
  have htrace : WordTrace (prefixWord ++ tailWord_5785498) baseStart_5785498 baseEnd_5785498 := by
    simpa [prefixWord, tailWord_5785498, baseEnd_5785498] using wordTrace_append hprefix tailTrace_5785498
  have hstable : (prefixWord ++ tailWord_5785498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785498).length < 2 ^ (prefixWord ++ tailWord_5785498).sum := by decide
  have hdescent : baseEnd_5785498 < baseStart_5785498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785528 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_5785528 : Nat := 118140960795 + 5785528 * 2 ^ 59
def prefixEnd_5785528 : Nat := 4983230072969 + 3 ^ 40 * 5785528 * 2
def baseEnd_5785528 : Nat := 990252234681848442930949

theorem tailTrace_5785528 : CollatzResearch.WordTrace tailWord_5785528 prefixEnd_5785528 990252234681848442930949 := by
  unfold tailWord_5785528
  simp only [CollatzResearch.WordTrace]
  refine ⟨105507770892013810180842619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140677027856018413574456825 105507770892013810180842619)
  ·
    refine ⟨158261656338020715271263929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105507770892013810180842619 158261656338020715271263929)
    ·
      refine ⟨118696242253515536453447947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158261656338020715271263929 118696242253515536453447947)
      ·
        refine ⟨178044363380273304680171921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118696242253515536453447947 178044363380273304680171921)
        ·
          refine ⟨133533272535204978510128941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178044363380273304680171921 133533272535204978510128941)
          ·
            refine ⟨50074977200701866941298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133533272535204978510128941 50074977200701866941298353)
            ·
              refine ⟨37556232900526400205973765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50074977200701866941298353 37556232900526400205973765)
              ·
                refine ⟨7041793668848700038620081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37556232900526400205973765 7041793668848700038620081)
                ·
                  refine ⟨5281345251636525028965061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7041793668848700038620081 5281345251636525028965061)
                  ·
                    refine ⟨990252234681848442930949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5281345251636525028965061 990252234681848442930949)
                    ·
                      rfl

theorem cell23_5785528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_5785528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785528 prefixEnd_5785528 := by exact prefixLift 5785528
  have htrace : WordTrace (prefixWord ++ tailWord_5785528) baseStart_5785528 baseEnd_5785528 := by
    simpa [prefixWord, tailWord_5785528, baseEnd_5785528] using wordTrace_append hprefix tailTrace_5785528
  have hstable : (prefixWord ++ tailWord_5785528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785528).length < 2 ^ (prefixWord ++ tailWord_5785528).sum := by decide
  have hdescent : baseEnd_5785528 < baseStart_5785528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785565 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5785565 : Nat := 118140960795 + 5785565 * 2 ^ 59
def prefixEnd_5785565 : Nat := 4983230072969 + 3 ^ 40 * 5785565 * 2
def baseEnd_5785565 : Nat := 2970775702829761684030177

theorem tailTrace_5785565 : CollatzResearch.WordTrace tailWord_5785565 prefixEnd_5785565 2970775702829761684030177 := by
  unfold tailWord_5785565
  simp only [CollatzResearch.WordTrace]
  refine ⟨211016891284893575680782149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140677927523262383787188099 211016891284893575680782149)
  ·
    refine ⟨39565667115917545440146653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211016891284893575680782149 39565667115917545440146653)
    ·
      refine ⟨14837125168469079540054995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39565667115917545440146653 14837125168469079540054995)
      ·
        refine ⟨22255687752703619310082493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14837125168469079540054995 22255687752703619310082493)
        ·
          refine ⟨8345882907263857241280935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22255687752703619310082493 8345882907263857241280935)
          ·
            refine ⟨12518824360895785861921403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345882907263857241280935 12518824360895785861921403)
            ·
              refine ⟨18778236541343678792882105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518824360895785861921403 18778236541343678792882105)
              ·
                refine ⟨14083677406007759094661579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18778236541343678792882105 14083677406007759094661579)
                ·
                  refine ⟨21125516109011638641992369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14083677406007759094661579 21125516109011638641992369)
                  ·
                    refine ⟨15844137081758728981494277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21125516109011638641992369 15844137081758728981494277)
                    ·
                      refine ⟨2970775702829761684030177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15844137081758728981494277 2970775702829761684030177)
                      ·
                        rfl

theorem cell23_5785565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5785565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785565 prefixEnd_5785565 := by exact prefixLift 5785565
  have htrace : WordTrace (prefixWord ++ tailWord_5785565) baseStart_5785565 baseEnd_5785565 := by
    simpa [prefixWord, tailWord_5785565, baseEnd_5785565] using wordTrace_append hprefix tailTrace_5785565
  have hstable : (prefixWord ++ tailWord_5785565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785565).length < 2 ^ (prefixWord ++ tailWord_5785565).sum := by decide
  have hdescent : baseEnd_5785565 < baseStart_5785565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785568 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3]
def baseStart_5785568 : Nat := 118140960795 + 5785568 * 2 ^ 59
def prefixEnd_5785568 : Nat := 4983230072969 + 3 ^ 40 * 5785568 * 2
def baseEnd_5785568 : Nat := 2970777243271725172292663

theorem tailTrace_5785568 : CollatzResearch.WordTrace tailWord_5785568 prefixEnd_5785568 2970777243271725172292663 := by
  unfold tailWord_5785568
  simp only [CollatzResearch.WordTrace]
  refine ⟨105508500351941353596570679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140678000469255138128760905 105508500351941353596570679)
  ·
    refine ⟨158262750527912030394856019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105508500351941353596570679 158262750527912030394856019)
    ·
      refine ⟨237394125791868045592284029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158262750527912030394856019 237394125791868045592284029)
      ·
        refine ⟨89022797171950517097106511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237394125791868045592284029 89022797171950517097106511)
        ·
          refine ⟨133534195757925775645659767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89022797171950517097106511 133534195757925775645659767)
          ·
            refine ⟨200301293636888663468489651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133534195757925775645659767 200301293636888663468489651)
            ·
              refine ⟨300451940455332995202734477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200301293636888663468489651 300451940455332995202734477)
              ·
                refine ⟨112669477670749873201025429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300451940455332995202734477 112669477670749873201025429)
                ·
                  refine ⟨5281381765816400306298067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112669477670749873201025429 5281381765816400306298067)
                  ·
                    refine ⟨7922072648724600459447101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5281381765816400306298067 7922072648724600459447101)
                    ·
                      refine ⟨2970777243271725172292663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7922072648724600459447101 2970777243271725172292663)
                      ·
                        rfl

theorem cell23_5785568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_5785568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785568 prefixEnd_5785568 := by exact prefixLift 5785568
  have htrace : WordTrace (prefixWord ++ tailWord_5785568) baseStart_5785568 baseEnd_5785568 := by
    simpa [prefixWord, tailWord_5785568, baseEnd_5785568] using wordTrace_append hprefix tailTrace_5785568
  have hstable : (prefixWord ++ tailWord_5785568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785568).length < 2 ^ (prefixWord ++ tailWord_5785568).sum := by decide
  have hdescent : baseEnd_5785568 < baseStart_5785568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785625 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 4, 2, 2]
def baseStart_5785625 : Nat := 118140960795 + 5785625 * 2 ^ 59
def prefixEnd_5785625 : Nat := 4983230072969 + 3 ^ 40 * 5785625 * 2
def baseEnd_5785625 : Nat := 2970806511669031449279901

theorem tailTrace_5785625 : CollatzResearch.WordTrace tailWord_5785625 prefixEnd_5785625 2970806511669031449279901 := by
  unfold tailWord_5785625
  simp only [CollatzResearch.WordTrace]
  refine ⟨211019079664676205927966329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140679386443117470618644219 211019079664676205927966329)
  ·
    refine ⟨158264309748507154445974747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211019079664676205927966329 158264309748507154445974747)
    ·
      refine ⟨237396464622760731668962121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158264309748507154445974747 237396464622760731668962121)
      ·
        refine ⟨178047348467070548751721591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237396464622760731668962121 178047348467070548751721591)
        ·
          refine ⟨267071022700605823127582387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178047348467070548751721591 267071022700605823127582387)
          ·
            refine ⟨400606534050908734691373581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267071022700605823127582387 400606534050908734691373581)
            ·
              refine ⟨150227450269090775509265093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400606534050908734691373581 150227450269090775509265093)
              ·
                refine ⟨28167646925454520407987205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150227450269090775509265093 28167646925454520407987205)
                ·
                  refine ⟨5281433798522722576497601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28167646925454520407987205 5281433798522722576497601)
                  ·
                    refine ⟨3961075348892041932373201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5281433798522722576497601 3961075348892041932373201)
                    ·
                      refine ⟨2970806511669031449279901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961075348892041932373201 2970806511669031449279901)
                      ·
                        rfl

theorem cell23_5785625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_5785625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785625 prefixEnd_5785625 := by exact prefixLift 5785625
  have htrace : WordTrace (prefixWord ++ tailWord_5785625) baseStart_5785625 baseEnd_5785625 := by
    simpa [prefixWord, tailWord_5785625, baseEnd_5785625] using wordTrace_append hprefix tailTrace_5785625
  have hstable : (prefixWord ++ tailWord_5785625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785625).length < 2 ^ (prefixWord ++ tailWord_5785625).sum := by decide
  have hdescent : baseEnd_5785625 < baseStart_5785625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785629 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_5785629 : Nat := 118140960795 + 5785629 * 2 ^ 59
def prefixEnd_5785629 : Nat := 4983230072969 + 3 ^ 40 * 5785629 * 2
def baseEnd_5785629 : Nat := 2970808565591649433629883

theorem tailTrace_5785629 : CollatzResearch.WordTrace tailWord_5785629 prefixEnd_5785629 2970808565591649433629883 := by
  unfold tailWord_5785629
  simp only [CollatzResearch.WordTrace]
  refine ⟨211019225556661714611111941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140679483704441143074074627 211019225556661714611111941)
  ·
    refine ⟨39566104791874071489583489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211019225556661714611111941 39566104791874071489583489)
    ·
      refine ⟨29674578593905553617187617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39566104791874071489583489 29674578593905553617187617)
      ·
        refine ⟨22255933945429165212890713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29674578593905553617187617 22255933945429165212890713)
        ·
          refine ⟨16691950459071873909668035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22255933945429165212890713 16691950459071873909668035)
          ·
            refine ⟨25037925688607810864502053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16691950459071873909668035 25037925688607810864502053)
            ·
              refine ⟨4694611066613964537094135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25037925688607810864502053 4694611066613964537094135)
              ·
                refine ⟨7041916599920946805641203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694611066613964537094135 7041916599920946805641203)
                ·
                  refine ⟨10562874899881420208461805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041916599920946805641203 10562874899881420208461805)
                  ·
                    refine ⟨3961078087455532578173177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10562874899881420208461805 3961078087455532578173177)
                    ·
                      refine ⟨2970808565591649433629883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961078087455532578173177 2970808565591649433629883)
                      ·
                        rfl

theorem cell23_5785629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_5785629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785629 prefixEnd_5785629 := by exact prefixLift 5785629
  have htrace : WordTrace (prefixWord ++ tailWord_5785629) baseStart_5785629 baseEnd_5785629 := by
    simpa [prefixWord, tailWord_5785629, baseEnd_5785629] using wordTrace_append hprefix tailTrace_5785629
  have hstable : (prefixWord ++ tailWord_5785629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785629).length < 2 ^ (prefixWord ++ tailWord_5785629).sum := by decide
  have hdescent : baseEnd_5785629 < baseStart_5785629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785631 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 9]
def baseStart_5785631 : Nat := 118140960795 + 5785631 * 2 ^ 59
def prefixEnd_5785631 : Nat := 4983230072969 + 3 ^ 40 * 5785631 * 2
def baseEnd_5785631 : Nat := 330089954728106491756097

theorem tailTrace_5785631 : CollatzResearch.WordTrace tailWord_5785631 prefixEnd_5785631 330089954728106491756097 := by
  unfold tailWord_5785631
  simp only [CollatzResearch.WordTrace]
  refine ⟨211019298502654468952684747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140679532335102979301789831 211019298502654468952684747)
  ·
    refine ⟨316528947753981703429027121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211019298502654468952684747 316528947753981703429027121)
    ·
      refine ⟨237396710815486277571770341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316528947753981703429027121 237396710815486277571770341)
      ·
        refine ⟨44511883277903677044706939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237396710815486277571770341 44511883277903677044706939)
        ·
          refine ⟨66767824916855515567060409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44511883277903677044706939 66767824916855515567060409)
          ·
            refine ⟨50075868687641636675295307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66767824916855515567060409 50075868687641636675295307)
            ·
              refine ⟨75113803031462455012942961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50075868687641636675295307 75113803031462455012942961)
              ·
                refine ⟨56335352273596841259707221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75113803031462455012942961 56335352273596841259707221)
                ·
                  refine ⟨330089954728106491756097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56335352273596841259707221 330089954728106491756097)
                  ·
                    rfl

theorem cell23_5785631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 9].length) (baseStart_5785631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785631 prefixEnd_5785631 := by exact prefixLift 5785631
  have htrace : WordTrace (prefixWord ++ tailWord_5785631) baseStart_5785631 baseEnd_5785631 := by
    simpa [prefixWord, tailWord_5785631, baseEnd_5785631] using wordTrace_append hprefix tailTrace_5785631
  have hstable : (prefixWord ++ tailWord_5785631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785631).length < 2 ^ (prefixWord ++ tailWord_5785631).sum := by decide
  have hdescent : baseEnd_5785631 < baseStart_5785631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785636 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5785636 : Nat := 118140960795 + 5785636 * 2 ^ 59
def prefixEnd_5785636 : Nat := 4983230072969 + 3 ^ 40 * 5785636 * 2
def baseEnd_5785636 : Nat := 2970812159956230906242351

theorem tailTrace_5785636 : CollatzResearch.WordTrace tailWord_5785636 prefixEnd_5785636 2970812159956230906242351 := by
  unfold tailWord_5785636
  simp only [CollatzResearch.WordTrace]
  refine ⟨105509740433818177403308381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140679653911757569871077841 105509740433818177403308381)
  ·
    refine ⟨39566152662681816526240643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105509740433818177403308381 39566152662681816526240643)
    ·
      refine ⟨59349228994022724789360965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39566152662681816526240643 59349228994022724789360965)
      ·
        refine ⟨11127980436379260898005181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59349228994022724789360965 11127980436379260898005181)
        ·
          refine ⟨4172992663642222836751943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11127980436379260898005181 4172992663642222836751943)
          ·
            refine ⟨6259488995463334255127915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4172992663642222836751943 6259488995463334255127915)
            ·
              refine ⟨9389233493195001382691873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259488995463334255127915 9389233493195001382691873)
              ·
                refine ⟨7041925119896251037018905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9389233493195001382691873 7041925119896251037018905)
                ·
                  refine ⟨5281443839922188277764179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7041925119896251037018905 5281443839922188277764179)
                  ·
                    refine ⟨7922165759883282416646269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5281443839922188277764179 7922165759883282416646269)
                    ·
                      refine ⟨2970812159956230906242351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7922165759883282416646269 2970812159956230906242351)
                      ·
                        rfl

theorem cell23_5785636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5785636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785636 prefixEnd_5785636 := by exact prefixLift 5785636
  have htrace : WordTrace (prefixWord ++ tailWord_5785636) baseStart_5785636 baseEnd_5785636 := by
    simpa [prefixWord, tailWord_5785636, baseEnd_5785636] using wordTrace_append hprefix tailTrace_5785636
  have hstable : (prefixWord ++ tailWord_5785636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785636).length < 2 ^ (prefixWord ++ tailWord_5785636).sum := by decide
  have hdescent : baseEnd_5785636 < baseStart_5785636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785648 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 7]
def baseStart_5785648 : Nat := 118140960795 + 5785648 * 2 ^ 59
def prefixEnd_5785648 : Nat := 4983230072969 + 3 ^ 40 * 5785648 * 2
def baseEnd_5785648 : Nat := 330090924636009428810255

theorem tailTrace_5785648 : CollatzResearch.WordTrace tailWord_5785648 prefixEnd_5785648 330090924636009428810255 := by
  unfold tailWord_5785648
  simp only [CollatzResearch.WordTrace]
  refine ⟨105509959271796440428026799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140679945695728587237369065 105509959271796440428026799)
  ·
    refine ⟨158264938907694660642040199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105509959271796440428026799 158264938907694660642040199)
    ·
      refine ⟨237397408361541990963060299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158264938907694660642040199 237397408361541990963060299)
      ·
        refine ⟨356096112542312986444590449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237397408361541990963060299 356096112542312986444590449)
        ·
          refine ⟨267072084406734739833442837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356096112542312986444590449 267072084406734739833442837)
          ·
            refine ⟨12519003956565690929692633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 267072084406734739833442837 12519003956565690929692633)
            ·
              refine ⟨9389252967424268197269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12519003956565690929692633 9389252967424268197269475)
              ·
                refine ⟨14083879451136402295904213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9389252967424268197269475 14083879451136402295904213)
                ·
                  refine ⟨330090924636009428810255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14083879451136402295904213 330090924636009428810255)
                  ·
                    rfl

theorem cell23_5785648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_5785648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785648 prefixEnd_5785648 := by exact prefixLift 5785648
  have htrace : WordTrace (prefixWord ++ tailWord_5785648) baseStart_5785648 baseEnd_5785648 := by
    simpa [prefixWord, tailWord_5785648, baseEnd_5785648] using wordTrace_append hprefix tailTrace_5785648
  have hstable : (prefixWord ++ tailWord_5785648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785648).length < 2 ^ (prefixWord ++ tailWord_5785648).sum := by decide
  have hdescent : baseEnd_5785648 < baseStart_5785648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785678 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_5785678 : Nat := 118140960795 + 5785678 * 2 ^ 59
def prefixEnd_5785678 : Nat := 4983230072969 + 3 ^ 40 * 5785678 * 2
def baseEnd_5785678 : Nat := 990277908714573247305719

theorem tailTrace_5785678 : CollatzResearch.WordTrace tailWord_5785678 prefixEnd_5785678 990277908714573247305719 := by
  unfold tailWord_5785678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26377626591685524497455711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140680675155656130653097125 26377626591685524497455711)
  ·
    refine ⟨39566439887528286746183567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26377626591685524497455711 39566439887528286746183567)
    ·
      refine ⟨59349659831292430119275351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39566439887528286746183567 59349659831292430119275351)
      ·
        refine ⟨89024489746938645178913027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59349659831292430119275351 89024489746938645178913027)
        ·
          refine ⟨133536734620407967768369541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89024489746938645178913027 133536734620407967768369541)
          ·
            refine ⟨25038137741326493956569289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133536734620407967768369541 25038137741326493956569289)
            ·
              refine ⟨18778603305994870467426967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25038137741326493956569289 18778603305994870467426967)
              ·
                refine ⟨28167904958992305701140451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18778603305994870467426967 28167904958992305701140451)
                ·
                  refine ⟨42251857438488458551710677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28167904958992305701140451 42251857438488458551710677)
                  ·
                    refine ⟨990277908714573247305719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42251857438488458551710677 990277908714573247305719)
                    ·
                      rfl

theorem cell23_5785678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_5785678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785678 prefixEnd_5785678 := by exact prefixLift 5785678
  have htrace : WordTrace (prefixWord ++ tailWord_5785678) baseStart_5785678 baseEnd_5785678 := by
    simpa [prefixWord, tailWord_5785678, baseEnd_5785678] using wordTrace_append hprefix tailTrace_5785678
  have hstable : (prefixWord ++ tailWord_5785678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785678).length < 2 ^ (prefixWord ++ tailWord_5785678).sum := by decide
  have hdescent : baseEnd_5785678 < baseStart_5785678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785735 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_5785735 : Nat := 118140960795 + 5785735 * 2 ^ 59
def prefixEnd_5785735 : Nat := 4983230072969 + 3 ^ 40 * 5785735 * 2
def baseEnd_5785735 : Nat := 2970862994541026018904395

theorem tailTrace_5785735 : CollatzResearch.WordTrace tailWord_5785735 prefixEnd_5785735 2970862994541026018904395 := by
  unfold tailWord_5785735
  simp only [CollatzResearch.WordTrace]
  refine ⟨211023091694277694714470659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140682061129518463142980439 211023091694277694714470659)
  ·
    refine ⟨316534637541416542071705989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211023091694277694714470659 316534637541416542071705989)
    ·
      refine ⟨59350244539015601638444873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316534637541416542071705989 59350244539015601638444873)
      ·
        refine ⟨44512683404261701228833655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59350244539015601638444873 44512683404261701228833655)
        ·
          refine ⟨66769025106392551843250483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44512683404261701228833655 66769025106392551843250483)
          ·
            refine ⟨100153537659588827764875725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66769025106392551843250483 100153537659588827764875725)
            ·
              refine ⟨37557576622345810411828397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100153537659588827764875725 37557576622345810411828397)
              ·
                refine ⟨14084091233379678904435649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37557576622345810411828397 14084091233379678904435649)
                ·
                  refine ⟨10563068425034759178326737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14084091233379678904435649 10563068425034759178326737)
                  ·
                    refine ⟨7922301318776069383745053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10563068425034759178326737 7922301318776069383745053)
                    ·
                      refine ⟨2970862994541026018904395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7922301318776069383745053 2970862994541026018904395)
                      ·
                        rfl

theorem cell23_5785735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_5785735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785735 prefixEnd_5785735 := by exact prefixLift 5785735
  have htrace : WordTrace (prefixWord ++ tailWord_5785735) baseStart_5785735 baseEnd_5785735 := by
    simpa [prefixWord, tailWord_5785735, baseEnd_5785735] using wordTrace_append hprefix tailTrace_5785735
  have hstable : (prefixWord ++ tailWord_5785735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785735).length < 2 ^ (prefixWord ++ tailWord_5785735).sum := by decide
  have hdescent : baseEnd_5785735 < baseStart_5785735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785759 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 1, 4]
def baseStart_5785759 : Nat := 118140960795 + 5785759 * 2 ^ 59
def prefixEnd_5785759 : Nat := 4983230072969 + 3 ^ 40 * 5785759 * 2
def baseEnd_5785759 : Nat := 990291772692244641668095

theorem tailTrace_5785759 : CollatzResearch.WordTrace tailWord_5785759 prefixEnd_5785759 990291772692244641668095 := by
  unfold tailWord_5785759
  simp only [CollatzResearch.WordTrace]
  refine ⟨211023967046190746813344331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140682644697460497875562887 211023967046190746813344331)
  ·
    refine ⟨316535950569286120220016497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211023967046190746813344331 316535950569286120220016497)
    ·
      refine ⟨237401962926964590165012373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316535950569286120220016497 237401962926964590165012373)
      ·
        refine ⟨11128217012201465163984955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 237401962926964590165012373 11128217012201465163984955)
        ·
          refine ⟨16692325518302197745977433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11128217012201465163984955 16692325518302197745977433)
          ·
            refine ⟨12519244138726648309483075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16692325518302197745977433 12519244138726648309483075)
            ·
              refine ⟨18778866208089972464224613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519244138726648309483075 18778866208089972464224613)
              ·
                refine ⟨3521037414016869837042115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18778866208089972464224613 3521037414016869837042115)
                ·
                  refine ⟨5281556121025304755563173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521037414016869837042115 5281556121025304755563173)
                  ·
                    refine ⟨990291772692244641668095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5281556121025304755563173 990291772692244641668095)
                    ·
                      rfl

theorem cell23_5785759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 4].length) (baseStart_5785759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785759 prefixEnd_5785759 := by exact prefixLift 5785759
  have htrace : WordTrace (prefixWord ++ tailWord_5785759) baseStart_5785759 baseEnd_5785759 := by
    simpa [prefixWord, tailWord_5785759, baseEnd_5785759] using wordTrace_append hprefix tailTrace_5785759
  have hstable : (prefixWord ++ tailWord_5785759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785759).length < 2 ^ (prefixWord ++ tailWord_5785759).sum := by decide
  have hdescent : baseEnd_5785759 < baseStart_5785759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785775 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 1, 5, 2]
def baseStart_5785775 : Nat := 118140960795 + 5785775 * 2 ^ 59
def prefixEnd_5785775 : Nat := 4983230072969 + 3 ^ 40 * 5785775 * 2
def baseEnd_5785775 : Nat := 2970883533767205862404211

theorem tailTrace_5785775 : CollatzResearch.WordTrace tailWord_5785775 prefixEnd_5785775 2970883533767205862404211 := by
  unfold tailWord_5785775
  simp only [CollatzResearch.WordTrace]
  refine ⟨211024550614132781545926779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140683033742755187697284519 211024550614132781545926779)
  ·
    refine ⟨316536825921199172318890169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211024550614132781545926779 316536825921199172318890169)
    ·
      refine ⟨237402619440899379239167627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316536825921199172318890169 237402619440899379239167627)
      ·
        refine ⟨356103929161349068858751441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237402619440899379239167627 356103929161349068858751441)
        ·
          refine ⟨267077946871011801644063581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356103929161349068858751441 267077946871011801644063581)
          ·
            refine ⟨100154230076629425616523843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267077946871011801644063581 100154230076629425616523843)
            ·
              refine ⟨150231345114944138424785765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100154230076629425616523843 150231345114944138424785765)
              ·
                refine ⟨28168377209052025954647331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150231345114944138424785765 28168377209052025954647331)
                ·
                  refine ⟨42252565813578038931970997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28168377209052025954647331 42252565813578038931970997)
                  ·
                    refine ⟨3961178045022941149872281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42252565813578038931970997 3961178045022941149872281)
                    ·
                      refine ⟨2970883533767205862404211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961178045022941149872281 2970883533767205862404211)
                      ·
                        rfl

theorem cell23_5785775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5, 2].length) (baseStart_5785775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785775 prefixEnd_5785775 := by exact prefixLift 5785775
  have htrace : WordTrace (prefixWord ++ tailWord_5785775) baseStart_5785775 baseEnd_5785775 := by
    simpa [prefixWord, tailWord_5785775, baseEnd_5785775] using wordTrace_append hprefix tailTrace_5785775
  have hstable : (prefixWord ++ tailWord_5785775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785775).length < 2 ^ (prefixWord ++ tailWord_5785775).sum := by decide
  have hdescent : baseEnd_5785775 < baseStart_5785775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785778 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_5785778 : Nat := 118140960795 + 5785778 * 2 ^ 59
def prefixEnd_5785778 : Nat := 4983230072969 + 3 ^ 40 * 5785778 * 2
def baseEnd_5785778 : Nat := 2970885074209169350666697

theorem tailTrace_5785778 : CollatzResearch.WordTrace tailWord_5785778 prefixEnd_5785778 2970885074209169350666697 := by
  unfold tailWord_5785778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52756165008280478264571497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140683106688747942038857325 52756165008280478264571497)
  ·
    refine ⟨39567123756210358698428623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52756165008280478264571497 39567123756210358698428623)
    ·
      refine ⟨59350685634315538047642935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39567123756210358698428623 59350685634315538047642935)
      ·
        refine ⟨89026028451473307071464403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59350685634315538047642935 89026028451473307071464403)
        ·
          refine ⟨133539042677209960607196605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89026028451473307071464403 133539042677209960607196605)
          ·
            refine ⟨50077141003953735227698727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133539042677209960607196605 50077141003953735227698727)
            ·
              refine ⟨75115711505930602841548091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50077141003953735227698727 75115711505930602841548091)
              ·
                refine ⟨112673567258895904262322137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75115711505930602841548091 112673567258895904262322137)
                ·
                  refine ⟨84505175444171928196741603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112673567258895904262322137 84505175444171928196741603)
                  ·
                    refine ⟨126757763166257892295112405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84505175444171928196741603 126757763166257892295112405)
                    ·
                      refine ⟨2970885074209169350666697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126757763166257892295112405 2970885074209169350666697)
                      ·
                        rfl

theorem cell23_5785778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_5785778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785778 prefixEnd_5785778 := by exact prefixLift 5785778
  have htrace : WordTrace (prefixWord ++ tailWord_5785778) baseStart_5785778 baseEnd_5785778 := by
    simpa [prefixWord, tailWord_5785778, baseEnd_5785778] using wordTrace_append hprefix tailTrace_5785778
  have hstable : (prefixWord ++ tailWord_5785778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785778).length < 2 ^ (prefixWord ++ tailWord_5785778).sum := by decide
  have hdescent : baseEnd_5785778 < baseStart_5785778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785785 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_5785785 : Nat := 118140960795 + 5785785 * 2 ^ 59
def prefixEnd_5785785 : Nat := 4983230072969 + 3 ^ 40 * 5785785 * 2
def baseEnd_5785785 : Nat := 990296222857916941093055

theorem tailTrace_5785785 : CollatzResearch.WordTrace tailWord_5785785 prefixEnd_5785785 990296222857916941093055 := by
  unfold tailWord_5785785
  simp only [CollatzResearch.WordTrace]
  refine ⟨211024915344096553253790809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140683276896064368835860539 211024915344096553253790809)
  ·
    refine ⟨158268686508072414940343107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211024915344096553253790809 158268686508072414940343107)
    ·
      refine ⟨237403029762108622410514661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158268686508072414940343107 237403029762108622410514661)
      ·
        refine ⟨44513068080395366701971499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237403029762108622410514661 44513068080395366701971499)
        ·
          refine ⟨66769602120593050052957249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44513068080395366701971499 66769602120593050052957249)
          ·
            refine ⟨50077201590444787539717937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66769602120593050052957249 50077201590444787539717937)
            ·
              refine ⟨37557901192833590654788453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50077201590444787539717937 37557901192833590654788453)
              ·
                refine ⟨7042106473656298247772835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37557901192833590654788453 7042106473656298247772835)
                ·
                  refine ⟨10563159710484447371659253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042106473656298247772835 10563159710484447371659253)
                  ·
                    refine ⟨990296222857916941093055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10563159710484447371659253 990296222857916941093055)
                    ·
                      rfl

theorem cell23_5785785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_5785785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785785 prefixEnd_5785785 := by exact prefixLift 5785785
  have htrace : WordTrace (prefixWord ++ tailWord_5785785) baseStart_5785785 baseEnd_5785785 := by
    simpa [prefixWord, tailWord_5785785, baseEnd_5785785] using wordTrace_append hprefix tailTrace_5785785
  have hstable : (prefixWord ++ tailWord_5785785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785785).length < 2 ^ (prefixWord ++ tailWord_5785785).sum := by decide
  have hdescent : baseEnd_5785785 < baseStart_5785785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785792 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2]
def baseStart_5785792 : Nat := 118140960795 + 5785792 * 2 ^ 59
def prefixEnd_5785792 : Nat := 4983230072969 + 3 ^ 40 * 5785792 * 2
def baseEnd_5785792 : Nat := 2970892262938332295891633

theorem tailTrace_5785792 : CollatzResearch.WordTrace tailWord_5785792 prefixEnd_5785792 2970892262938332295891633 := by
  unfold tailWord_5785792
  simp only [CollatzResearch.WordTrace]
  refine ⟨105512585327535596724647815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140683447103380795632863753 105512585327535596724647815)
  ·
    refine ⟨158268877991303395086971723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105512585327535596724647815 158268877991303395086971723)
    ·
      refine ⟨237403316986955092630457585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158268877991303395086971723 237403316986955092630457585)
      ·
        refine ⟨178052487740216319472843189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237403316986955092630457585 178052487740216319472843189)
        ·
          refine ⟨16692420725645279950579049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178052487740216319472843189 16692420725645279950579049)
          ·
            refine ⟨12519315544233959962934287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16692420725645279950579049 12519315544233959962934287)
            ·
              refine ⟨18778973316350939944401431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519315544233959962934287 18778973316350939944401431)
              ·
                refine ⟨28168459974526409916602147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18778973316350939944401431 28168459974526409916602147)
                ·
                  refine ⟨42252689961789614874903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28168459974526409916602147 42252689961789614874903221)
                  ·
                    refine ⟨3961189683917776394522177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42252689961789614874903221 3961189683917776394522177)
                    ·
                      refine ⟨2970892262938332295891633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961189683917776394522177 2970892262938332295891633)
                      ·
                        rfl

theorem cell23_5785792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_5785792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785792 prefixEnd_5785792 := by exact prefixLift 5785792
  have htrace : WordTrace (prefixWord ++ tailWord_5785792) baseStart_5785792 baseEnd_5785792 := by
    simpa [prefixWord, tailWord_5785792, baseEnd_5785792] using wordTrace_append hprefix tailTrace_5785792
  have hstable : (prefixWord ++ tailWord_5785792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785792).length < 2 ^ (prefixWord ++ tailWord_5785792).sum := by decide
  have hdescent : baseEnd_5785792 < baseStart_5785792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785808 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_5785808 : Nat := 118140960795 + 5785808 * 2 ^ 59
def prefixEnd_5785808 : Nat := 4983230072969 + 3 ^ 40 * 5785808 * 2
def baseEnd_5785808 : Nat := 2970900478628804233291559

theorem tailTrace_5785808 : CollatzResearch.WordTrace tailWord_5785808 prefixEnd_5785808 2970900478628804233291559 := by
  unfold tailWord_5785808
  simp only [CollatzResearch.WordTrace]
  refine ⟨105512877111506614090939039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140683836148675485454585385 105512877111506614090939039)
  ·
    refine ⟨158269315667259921136408559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105512877111506614090939039 158269315667259921136408559)
    ·
      refine ⟨237403973500889881704612839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158269315667259921136408559 237403973500889881704612839)
      ·
        refine ⟨356105960251334822556919259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237403973500889881704612839 356105960251334822556919259)
        ·
          refine ⟨534158940377002233835378889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356105960251334822556919259 534158940377002233835378889)
          ·
            refine ⟨400619205282751675376534167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534158940377002233835378889 400619205282751675376534167)
            ·
              refine ⟨600928807924127513064801251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400619205282751675376534167 600928807924127513064801251)
              ·
                refine ⟨901393211886191269597201877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600928807924127513064801251 901393211886191269597201877)
                ·
                  refine ⟨21126403403582607881184419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 901393211886191269597201877 21126403403582607881184419)
                  ·
                    refine ⟨31689605105373911821776629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21126403403582607881184419 31689605105373911821776629)
                    ·
                      refine ⟨2970900478628804233291559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31689605105373911821776629 2970900478628804233291559)
                      ·
                        rfl

theorem cell23_5785808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_5785808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785808 prefixEnd_5785808 := by exact prefixLift 5785808
  have htrace : WordTrace (prefixWord ++ tailWord_5785808) baseStart_5785808 baseEnd_5785808 := by
    simpa [prefixWord, tailWord_5785808, baseEnd_5785808] using wordTrace_append hprefix tailTrace_5785808
  have hstable : (prefixWord ++ tailWord_5785808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785808).length < 2 ^ (prefixWord ++ tailWord_5785808).sum := by decide
  have hdescent : baseEnd_5785808 < baseStart_5785808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785825 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_5785825 : Nat := 118140960795 + 5785825 * 2 ^ 59
def prefixEnd_5785825 : Nat := 4983230072969 + 3 ^ 40 * 5785825 * 2
def baseEnd_5785825 : Nat := 2970909207799930666778981

theorem tailTrace_5785825 : CollatzResearch.WordTrace tailWord_5785825 prefixEnd_5785825 2970909207799930666778981 := by
  unfold tailWord_5785825
  simp only [CollatzResearch.WordTrace]
  refine ⟨211026374263951640085246929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140684249509301093390164619 211026374263951640085246929)
  ·
    refine ⟨158269780697963730063935197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211026374263951640085246929 158269780697963730063935197)
    ·
      refine ⟨59351167761736398773975699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158269780697963730063935197 59351167761736398773975699)
      ·
        refine ⟨89026751642604598160963549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59351167761736398773975699 89026751642604598160963549)
        ·
          refine ⟨33385031865976724310361331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89026751642604598160963549 33385031865976724310361331)
          ·
            refine ⟨50077547798965086465541997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33385031865976724310361331 50077547798965086465541997)
            ·
              refine ⟨18779080424611907424578249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50077547798965086465541997 18779080424611907424578249)
              ·
                refine ⟨14084310318458930568433687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18779080424611907424578249 14084310318458930568433687)
                ·
                  refine ⟨21126465477688395852650531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14084310318458930568433687 21126465477688395852650531)
                  ·
                    refine ⟨31689698216532593778975797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21126465477688395852650531 31689698216532593778975797)
                    ·
                      refine ⟨2970909207799930666778981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31689698216532593778975797 2970909207799930666778981)
                      ·
                        rfl

theorem cell23_5785825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_5785825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785825 prefixEnd_5785825 := by exact prefixLift 5785825
  have htrace : WordTrace (prefixWord ++ tailWord_5785825) baseStart_5785825 baseEnd_5785825 := by
    simpa [prefixWord, tailWord_5785825, baseEnd_5785825] using wordTrace_append hprefix tailTrace_5785825
  have hstable : (prefixWord ++ tailWord_5785825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785825).length < 2 ^ (prefixWord ++ tailWord_5785825).sum := by decide
  have hdescent : baseEnd_5785825 < baseStart_5785825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785828 : List Nat := [2, 3, 1, 1, 1, 2, 1, 12]
def baseStart_5785828 : Nat := 118140960795 + 5785828 * 2 ^ 59
def prefixEnd_5785828 : Nat := 4983230072969 + 3 ^ 40 * 5785828 * 2
def baseEnd_5785828 : Nat := 110033731416366450186721

theorem tailTrace_5785828 : CollatzResearch.WordTrace tailWord_5785828 prefixEnd_5785828 110033731416366450186721 := by
  unfold tailWord_5785828
  simp only [CollatzResearch.WordTrace]
  refine ⟨105513241841470385798803069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140684322455293847731737425 105513241841470385798803069)
  ·
    refine ⟨39567465690551394674551151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105513241841470385798803069 39567465690551394674551151)
    ·
      refine ⟨59351198535827092011826727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39567465690551394674551151 59351198535827092011826727)
      ·
        refine ⟨89026797803740638017740091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59351198535827092011826727 89026797803740638017740091)
        ·
          refine ⟨133540196705610957026610137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89026797803740638017740091 133540196705610957026610137)
          ·
            refine ⟨100155147529208217769957603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133540196705610957026610137 100155147529208217769957603)
            ·
              refine ⟨150232721293812326654936405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100155147529208217769957603 150232721293812326654936405)
              ·
                refine ⟨110033731416366450186721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 150232721293812326654936405 110033731416366450186721)
                ·
                  rfl

theorem cell23_5785828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 12].length) (baseStart_5785828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785828 prefixEnd_5785828 := by exact prefixLift 5785828
  have htrace : WordTrace (prefixWord ++ tailWord_5785828) baseStart_5785828 baseEnd_5785828 := by
    simpa [prefixWord, tailWord_5785828, baseEnd_5785828] using wordTrace_append hprefix tailTrace_5785828
  have hstable : (prefixWord ++ tailWord_5785828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785828).length < 2 ^ (prefixWord ++ tailWord_5785828).sum := by decide
  have hdescent : baseEnd_5785828 < baseStart_5785828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785832 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5785832 : Nat := 118140960795 + 5785832 * 2 ^ 59
def prefixEnd_5785832 : Nat := 4983230072969 + 3 ^ 40 * 5785832 * 2
def baseEnd_5785832 : Nat := 990304267388170713130483

theorem tailTrace_5785832 : CollatzResearch.WordTrace tailWord_5785832 prefixEnd_5785832 990304267388170713130483 := by
  unfold tailWord_5785832
  simp only [CollatzResearch.WordTrace]
  refine ⟨105513314787463140140375875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140684419716617520187167833 105513314787463140140375875)
  ·
    refine ⟨158269972181194710210563813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105513314787463140140375875 158269972181194710210563813)
    ·
      refine ⟨29675619783974008164480715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158269972181194710210563813 29675619783974008164480715)
      ·
        refine ⟨44513429675961012246721073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29675619783974008164480715 44513429675961012246721073)
        ·
          refine ⟨33385072256970759185040805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44513429675961012246721073 33385072256970759185040805)
          ·
            refine ⟨6259701048182017347195151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33385072256970759185040805 6259701048182017347195151)
            ·
              refine ⟨9389551572273026020792727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259701048182017347195151 9389551572273026020792727)
              ·
                refine ⟨14084327358409539031189091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9389551572273026020792727 14084327358409539031189091)
                ·
                  refine ⟨21126491037614308546783637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14084327358409539031189091 21126491037614308546783637)
                  ·
                    refine ⟨990304267388170713130483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21126491037614308546783637 990304267388170713130483)
                    ·
                      rfl

theorem cell23_5785832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5785832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785832 prefixEnd_5785832 := by exact prefixLift 5785832
  have htrace : WordTrace (prefixWord ++ tailWord_5785832) baseStart_5785832 baseEnd_5785832 := by
    simpa [prefixWord, tailWord_5785832, baseEnd_5785832] using wordTrace_append hprefix tailTrace_5785832
  have hstable : (prefixWord ++ tailWord_5785832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785832).length < 2 ^ (prefixWord ++ tailWord_5785832).sum := by decide
  have hdescent : baseEnd_5785832 < baseStart_5785832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785839 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 3, 2, 2]
def baseStart_5785839 : Nat := 118140960795 + 5785839 * 2 ^ 59
def prefixEnd_5785839 : Nat := 4983230072969 + 3 ^ 40 * 5785839 * 2
def baseEnd_5785839 : Nat := 2970916396529093612003917

theorem tailTrace_5785839 : CollatzResearch.WordTrace tailWord_5785839 prefixEnd_5785839 2970916396529093612003917 := by
  unfold tailWord_5785839
  simp only [CollatzResearch.WordTrace]
  refine ⟨211026884885900920476256571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140684589923933946984171047 211026884885900920476256571)
  ·
    refine ⟨316540327328851380714384857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211026884885900920476256571 316540327328851380714384857)
    ·
      refine ⟨237405245496638535535788643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316540327328851380714384857 237405245496638535535788643)
      ·
        refine ⟨356107868244957803303682965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237405245496638535535788643 356107868244957803303682965)
        ·
          refine ⟨16692556323982397029860139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 356107868244957803303682965 16692556323982397029860139)
          ·
            refine ⟨25038834485973595544790209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16692556323982397029860139 25038834485973595544790209)
            ·
              refine ⟨18779125864480196658592657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25038834485973595544790209 18779125864480196658592657)
              ·
                refine ⟨14084344398360147493944493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18779125864480196658592657 14084344398360147493944493)
                ·
                  refine ⟨5281629149385055310229185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14084344398360147493944493 5281629149385055310229185)
                  ·
                    refine ⟨3961221862038791482671889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5281629149385055310229185 3961221862038791482671889)
                    ·
                      refine ⟨2970916396529093612003917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961221862038791482671889 2970916396529093612003917)
                      ·
                        rfl

theorem cell23_5785839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2, 2].length) (baseStart_5785839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785839 prefixEnd_5785839 := by exact prefixLift 5785839
  have htrace : WordTrace (prefixWord ++ tailWord_5785839) baseStart_5785839 baseEnd_5785839 := by
    simpa [prefixWord, tailWord_5785839, baseEnd_5785839] using wordTrace_append hprefix tailTrace_5785839
  have hstable : (prefixWord ++ tailWord_5785839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785839).length < 2 ^ (prefixWord ++ tailWord_5785839).sum := by decide
  have hdescent : baseEnd_5785839 < baseStart_5785839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785848 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_5785848 : Nat := 118140960795 + 5785848 * 2 ^ 59
def prefixEnd_5785848 : Nat := 4983230072969 + 3 ^ 40 * 5785848 * 2
def baseEnd_5785848 : Nat := 2970921017854984076791375

theorem tailTrace_5785848 : CollatzResearch.WordTrace tailWord_5785848 prefixEnd_5785848 2970921017854984076791375 := by
  unfold tailWord_5785848
  simp only [CollatzResearch.WordTrace]
  refine ⟨105513606571434157506667099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140684808761912210008889465 105513606571434157506667099)
  ·
    refine ⟨158270409857151236260000649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105513606571434157506667099 158270409857151236260000649)
    ·
      refine ⟨118702807392863427195000487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158270409857151236260000649 118702807392863427195000487)
      ·
        refine ⟨178054211089295140792500731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118702807392863427195000487 178054211089295140792500731)
        ·
          refine ⟨267081316633942711188751097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178054211089295140792500731 267081316633942711188751097)
          ·
            refine ⟨200310987475457033391563323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267081316633942711188751097 200310987475457033391563323)
            ·
              refine ⟨300466481213185550087344985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200310987475457033391563323 300466481213185550087344985)
              ·
                refine ⟨225349860909889162565508739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300466481213185550087344985 225349860909889162565508739)
                ·
                  refine ⟨338024791364833743848263109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225349860909889162565508739 338024791364833743848263109)
                  ·
                    refine ⟨63379648380906326971549333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338024791364833743848263109 63379648380906326971549333)
                    ·
                      refine ⟨2970921017854984076791375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63379648380906326971549333 2970921017854984076791375)
                      ·
                        rfl

theorem cell23_5785848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_5785848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785848 prefixEnd_5785848 := by exact prefixLift 5785848
  have htrace : WordTrace (prefixWord ++ tailWord_5785848) baseStart_5785848 baseEnd_5785848 := by
    simpa [prefixWord, tailWord_5785848, baseEnd_5785848] using wordTrace_append hprefix tailTrace_5785848
  have hstable : (prefixWord ++ tailWord_5785848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785848).length < 2 ^ (prefixWord ++ tailWord_5785848).sum := by decide
  have hdescent : baseEnd_5785848 < baseStart_5785848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785855 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_5785855 : Nat := 118140960795 + 5785855 * 2 ^ 59
def prefixEnd_5785855 : Nat := 4983230072969 + 3 ^ 40 * 5785855 * 2
def baseEnd_5785855 : Nat := 2970924612219565549403843

theorem tailTrace_5785855 : CollatzResearch.WordTrace tailWord_5785855 prefixEnd_5785855 2970924612219565549403843 := by
  unfold tailWord_5785855
  simp only [CollatzResearch.WordTrace]
  refine ⟨211027468453842955208839019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140684978969228636805892679 211027468453842955208839019)
  ·
    refine ⟨316541202680764432813258529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211027468453842955208839019 316541202680764432813258529)
    ·
      refine ⟨237405902010573324609943897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316541202680764432813258529 237405902010573324609943897)
      ·
        refine ⟨178054426507929993457457923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237405902010573324609943897 178054426507929993457457923)
        ·
          refine ⟨267081639761894990186186885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178054426507929993457457923 267081639761894990186186885)
          ·
            refine ⟨50077807455355310659910041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267081639761894990186186885 50077807455355310659910041)
            ·
              refine ⟨37558355591516482994932531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50077807455355310659910041 37558355591516482994932531)
              ·
                refine ⟨56337533387274724492398797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37558355591516482994932531 56337533387274724492398797)
                ·
                  refine ⟨21126575020228021684649549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56337533387274724492398797 21126575020228021684649549)
                  ·
                    refine ⟨7922465632585508131743581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21126575020228021684649549 7922465632585508131743581)
                    ·
                      refine ⟨2970924612219565549403843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7922465632585508131743581 2970924612219565549403843)
                      ·
                        rfl

theorem cell23_5785855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_5785855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785855 prefixEnd_5785855 := by exact prefixLift 5785855
  have htrace : WordTrace (prefixWord ++ tailWord_5785855) baseStart_5785855 baseEnd_5785855 := by
    simpa [prefixWord, tailWord_5785855, baseEnd_5785855] using wordTrace_append hprefix tailTrace_5785855
  have hstable : (prefixWord ++ tailWord_5785855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785855).length < 2 ^ (prefixWord ++ tailWord_5785855).sum := by decide
  have hdescent : baseEnd_5785855 < baseStart_5785855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785856 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 1, 2, 2]
def baseStart_5785856 : Nat := 118140960795 + 5785856 * 2 ^ 59
def prefixEnd_5785856 : Nat := 4983230072969 + 3 ^ 40 * 5785856 * 2
def baseEnd_5785856 : Nat := 2970925125700220045491339

theorem tailTrace_5785856 : CollatzResearch.WordTrace tailWord_5785856 prefixEnd_5785856 2970925125700220045491339 := by
  unfold tailWord_5785856
  simp only [CollatzResearch.WordTrace]
  refine ⟨105513752463419666189812711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140685003284559554919750281 105513752463419666189812711)
  ·
    refine ⟨158270628695129499284719067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105513752463419666189812711 158270628695129499284719067)
    ·
      refine ⟨237405943042694248927078601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158270628695129499284719067 237405943042694248927078601)
      ·
        refine ⟨178054457282020686695308951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237405943042694248927078601 178054457282020686695308951)
        ·
          refine ⟨267081685923031030042963427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178054457282020686695308951 267081685923031030042963427)
          ·
            refine ⟨400622528884546545064445141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267081685923031030042963427 400622528884546545064445141)
            ·
              refine ⟨9389590520731559649947933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 400622528884546545064445141 9389590520731559649947933)
              ·
                refine ⟨3521096445274334868730475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9389590520731559649947933 3521096445274334868730475)
                ·
                  refine ⟨5281644667911502303095713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521096445274334868730475 5281644667911502303095713)
                  ·
                    refine ⟨3961233500933626727321785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5281644667911502303095713 3961233500933626727321785)
                    ·
                      refine ⟨2970925125700220045491339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961233500933626727321785 2970925125700220045491339)
                      ·
                        rfl

theorem cell23_5785856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_5785856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785856 prefixEnd_5785856 := by exact prefixLift 5785856
  have htrace : WordTrace (prefixWord ++ tailWord_5785856) baseStart_5785856 baseEnd_5785856 := by
    simpa [prefixWord, tailWord_5785856, baseEnd_5785856] using wordTrace_append hprefix tailTrace_5785856
  have hstable : (prefixWord ++ tailWord_5785856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785856).length < 2 ^ (prefixWord ++ tailWord_5785856).sum := by decide
  have hdescent : baseEnd_5785856 < baseStart_5785856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785873 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 1, 2, 2]
def baseStart_5785873 : Nat := 118140960795 + 5785873 * 2 ^ 59
def prefixEnd_5785873 : Nat := 4983230072969 + 3 ^ 40 * 5785873 * 2
def baseEnd_5785873 : Nat := 2970933854871346478978761

theorem tailTrace_5785873 : CollatzResearch.WordTrace tailWord_5785873 prefixEnd_5785873 2970933854871346478978761 := by
  unfold tailWord_5785873
  simp only [CollatzResearch.WordTrace]
  refine ⟨211028124967777744282994273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140685416645185162855329515 211028124967777744282994273)
  ·
    refine ⟨158271093725833308212245705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211028124967777744282994273 158271093725833308212245705)
    ·
      refine ⟨118703320294374981159184279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158271093725833308212245705 118703320294374981159184279)
      ·
        refine ⟨178054980441562471738776419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118703320294374981159184279 178054980441562471738776419)
        ·
          refine ⟨267082470662343707608164629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178054980441562471738776419 267082470662343707608164629)
          ·
            refine ⟨12519490812297361294132717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 267082470662343707608164629 12519490812297361294132717)
            ·
              refine ⟨4694809054611510485299769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12519490812297361294132717 4694809054611510485299769)
              ·
                refine ⟨3521106790958632863974827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4694809054611510485299769 3521106790958632863974827)
                ·
                  refine ⟨5281660186437949295962241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521106790958632863974827 5281660186437949295962241)
                  ·
                    refine ⟨3961245139828461971971681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5281660186437949295962241 3961245139828461971971681)
                    ·
                      refine ⟨2970933854871346478978761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961245139828461971971681 2970933854871346478978761)
                      ·
                        rfl

theorem cell23_5785873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_5785873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785873 prefixEnd_5785873 := by exact prefixLift 5785873
  have htrace : WordTrace (prefixWord ++ tailWord_5785873) baseStart_5785873 baseEnd_5785873 := by
    simpa [prefixWord, tailWord_5785873, baseEnd_5785873] using wordTrace_append hprefix tailTrace_5785873
  have hstable : (prefixWord ++ tailWord_5785873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785873).length < 2 ^ (prefixWord ++ tailWord_5785873).sum := by decide
  have hdescent : baseEnd_5785873 < baseStart_5785873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785912 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_5785912 : Nat := 118140960795 + 5785912 * 2 ^ 59
def prefixEnd_5785912 : Nat := 4983230072969 + 3 ^ 40 * 5785912 * 2
def baseEnd_5785912 : Nat := 2970953880616871826391081

theorem tailTrace_5785912 : CollatzResearch.WordTrace tailWord_5785912 prefixEnd_5785912 2970953880616871826391081 := by
  unfold tailWord_5785912
  simp only [CollatzResearch.WordTrace]
  refine ⟨105514773707318226971831995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140686364943090969295775993 105514773707318226971831995)
  ·
    refine ⟨158272160560977340457747993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105514773707318226971831995 158272160560977340457747993)
    ·
      refine ⟨118704120420733005343310995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158272160560977340457747993 118704120420733005343310995)
      ·
        refine ⟨178056180631099508014966493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118704120420733005343310995 178056180631099508014966493)
        ·
          refine ⟨66771067736662315505612435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178056180631099508014966493 66771067736662315505612435)
          ·
            refine ⟨100156601604993473258418653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66771067736662315505612435 100156601604993473258418653)
            ·
              refine ⟨37558725601872552471906995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100156601604993473258418653 37558725601872552471906995)
              ·
                refine ⟨56338088402808828707860493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37558725601872552471906995 56338088402808828707860493)
                ·
                  refine ⟨21126783151053310765447685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56338088402808828707860493 21126783151053310765447685)
                  ·
                    refine ⟨3961271840822495768521441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21126783151053310765447685 3961271840822495768521441)
                    ·
                      refine ⟨2970953880616871826391081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961271840822495768521441 2970953880616871826391081)
                      ·
                        rfl

theorem cell23_5785912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_5785912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785912 prefixEnd_5785912 := by exact prefixLift 5785912
  have htrace : WordTrace (prefixWord ++ tailWord_5785912) baseStart_5785912 baseEnd_5785912 := by
    simpa [prefixWord, tailWord_5785912, baseEnd_5785912] using wordTrace_append hprefix tailTrace_5785912
  have hstable : (prefixWord ++ tailWord_5785912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785912).length < 2 ^ (prefixWord ++ tailWord_5785912).sum := by decide
  have hdescent : baseEnd_5785912 < baseStart_5785912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785916 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_5785916 : Nat := 118140960795 + 5785916 * 2 ^ 59
def prefixEnd_5785916 : Nat := 4983230072969 + 3 ^ 40 * 5785916 * 2
def baseEnd_5785916 : Nat := 2970955934539489810741063

theorem tailTrace_5785916 : CollatzResearch.WordTrace tailWord_5785916 prefixEnd_5785916 2970955934539489810741063 := by
  unfold tailWord_5785916
  simp only [CollatzResearch.WordTrace]
  refine ⟨105514846653310981313404801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140686462204414641751206401 105514846653310981313404801)
  ·
    refine ⟨79136134989983235985053601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105514846653310981313404801 79136134989983235985053601)
    ·
      refine ⟨59352101242487426988790201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79136134989983235985053601 59352101242487426988790201)
      ·
        refine ⟨44514075931865570241592651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59352101242487426988790201 44514075931865570241592651)
        ·
          refine ⟨66771113897798355362388977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44514075931865570241592651 66771113897798355362388977)
          ·
            refine ⟨50078335423348766521791733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66771113897798355362388977 50078335423348766521791733)
            ·
              refine ⟨4694843945938946861417975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50078335423348766521791733 4694843945938946861417975)
              ·
                refine ⟨7042265918908420292126963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694843945938946861417975 7042265918908420292126963)
                ·
                  refine ⟨10563398878362630438190445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042265918908420292126963 10563398878362630438190445)
                  ·
                    refine ⟨3961274579385986414321417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10563398878362630438190445 3961274579385986414321417)
                    ·
                      refine ⟨2970955934539489810741063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961274579385986414321417 2970955934539489810741063)
                      ·
                        rfl

theorem cell23_5785916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_5785916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785916 prefixEnd_5785916 := by exact prefixLift 5785916
  have htrace : WordTrace (prefixWord ++ tailWord_5785916) baseStart_5785916 baseEnd_5785916 := by
    simpa [prefixWord, tailWord_5785916, baseEnd_5785916] using wordTrace_append hprefix tailTrace_5785916
  have hstable : (prefixWord ++ tailWord_5785916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785916).length < 2 ^ (prefixWord ++ tailWord_5785916).sum := by decide
  have hdescent : baseEnd_5785916 < baseStart_5785916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785924 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5785924 : Nat := 118140960795 + 5785924 * 2 ^ 59
def prefixEnd_5785924 : Nat := 4983230072969 + 3 ^ 40 * 5785924 * 2
def baseEnd_5785924 : Nat := 2970960042384725779441027

theorem tailTrace_5785924 : CollatzResearch.WordTrace tailWord_5785924 prefixEnd_5785924 2970960042384725779441027 := by
  unfold tailWord_5785924
  simp only [CollatzResearch.WordTrace]
  refine ⟨105514992545296489996550413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140686656727061986662067217 105514992545296489996550413)
  ·
    refine ⟨39568122204486183748706405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105514992545296489996550413 39568122204486183748706405)
    ·
      refine ⟨7419022913341159452882451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39568122204486183748706405 7419022913341159452882451)
      ·
        refine ⟨11128534370011739179323677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419022913341159452882451 11128534370011739179323677)
        ·
          refine ⟨4173200388754402192246379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11128534370011739179323677 4173200388754402192246379)
          ·
            refine ⟨6259800583131603288369569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173200388754402192246379 6259800583131603288369569)
            ·
              refine ⟨4694850437348702466277177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6259800583131603288369569 4694850437348702466277177)
              ·
                refine ⟨3521137828011526849707883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4694850437348702466277177 3521137828011526849707883)
                ·
                  refine ⟨5281706742017290274561825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521137828011526849707883 5281706742017290274561825)
                  ·
                    refine ⟨3961280056512967705921369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5281706742017290274561825 3961280056512967705921369)
                    ·
                      refine ⟨2970960042384725779441027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961280056512967705921369 2970960042384725779441027)
                      ·
                        rfl

theorem cell23_5785924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5785924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785924 prefixEnd_5785924 := by exact prefixLift 5785924
  have htrace : WordTrace (prefixWord ++ tailWord_5785924) baseStart_5785924 baseEnd_5785924 := by
    simpa [prefixWord, tailWord_5785924, baseEnd_5785924] using wordTrace_append hprefix tailTrace_5785924
  have hstable : (prefixWord ++ tailWord_5785924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785924).length < 2 ^ (prefixWord ++ tailWord_5785924).sum := by decide
  have hdescent : baseEnd_5785924 < baseStart_5785924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785952 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 7]
def baseStart_5785952 : Nat := 118140960795 + 5785952 * 2 ^ 59
def prefixEnd_5785952 : Nat := 4983230072969 + 3 ^ 40 * 5785952 * 2
def baseEnd_5785952 : Nat := 330108268871450185543433

theorem tailTrace_5785952 : CollatzResearch.WordTrace tailWord_5785952 prefixEnd_5785952 330108268871450185543433 := by
  unfold tailWord_5785952
  simp only [CollatzResearch.WordTrace]
  refine ⟨105515503167245770387560055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140687337556327693850080073 105515503167245770387560055)
  ·
    refine ⟨158273254750868655581340083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105515503167245770387560055 158273254750868655581340083)
    ·
      refine ⟨237409882126302983372010125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158273254750868655581340083 237409882126302983372010125)
      ·
        refine ⟨89028705797363618764503797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237409882126302983372010125 89028705797363618764503797)
        ·
          refine ⟨8346441168502839259172231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89028705797363618764503797 8346441168502839259172231)
          ·
            refine ⟨12519661752754258888758347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346441168502839259172231 12519661752754258888758347)
            ·
              refine ⟨18779492629131388333137521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519661752754258888758347 18779492629131388333137521)
              ·
                refine ⟨14084619471848541249853141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18779492629131388333137521 14084619471848541249853141)
                ·
                  refine ⟨330108268871450185543433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14084619471848541249853141 330108268871450185543433)
                  ·
                    rfl

theorem cell23_5785952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_5785952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785952 prefixEnd_5785952 := by exact prefixLift 5785952
  have htrace : WordTrace (prefixWord ++ tailWord_5785952) baseStart_5785952 baseEnd_5785952 := by
    simpa [prefixWord, tailWord_5785952, baseEnd_5785952] using wordTrace_append hprefix tailTrace_5785952
  have hstable : (prefixWord ++ tailWord_5785952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785952).length < 2 ^ (prefixWord ++ tailWord_5785952).sum := by decide
  have hdescent : baseEnd_5785952 < baseStart_5785952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785975 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_5785975 : Nat := 118140960795 + 5785975 * 2 ^ 59
def prefixEnd_5785975 : Nat := 4983230072969 + 3 ^ 40 * 5785975 * 2
def baseEnd_5785975 : Nat := 2970986229898105079903291

theorem tailTrace_5785975 : CollatzResearch.WordTrace tailWord_5785975 prefixEnd_5785975 2970986229898105079903291 := by
  unfold tailWord_5785975
  simp only [CollatzResearch.WordTrace]
  refine ⟨211031845213408215703207379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140687896808938810468804919 211031845213408215703207379)
  ·
    refine ⟨316547767820112323554811069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211031845213408215703207379 316547767820112323554811069)
    ·
      refine ⟨118705412932542121333054151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316547767820112323554811069 118705412932542121333054151)
      ·
        refine ⟨178058119398813181999581227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118705412932542121333054151 178058119398813181999581227)
        ·
          refine ⟨267087179098219772999371841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178058119398813181999581227 267087179098219772999371841)
          ·
            refine ⟨200315384323664829749528881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267087179098219772999371841 200315384323664829749528881)
            ·
              refine ⟨150236538242748622312146661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200315384323664829749528881 150236538242748622312146661)
              ·
                refine ⟨28169350920515366683527499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150236538242748622312146661 28169350920515366683527499)
                ·
                  refine ⟨42254026380773050025291249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28169350920515366683527499 42254026380773050025291249)
                  ·
                    refine ⟨31690519785579787518968437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42254026380773050025291249 31690519785579787518968437)
                    ·
                      refine ⟨2970986229898105079903291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31690519785579787518968437 2970986229898105079903291)
                      ·
                        rfl

theorem cell23_5785975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_5785975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785975 prefixEnd_5785975 := by exact prefixLift 5785975
  have htrace : WordTrace (prefixWord ++ tailWord_5785975) baseStart_5785975 baseEnd_5785975 := by
    simpa [prefixWord, tailWord_5785975, baseEnd_5785975] using wordTrace_append hprefix tailTrace_5785975
  have hstable : (prefixWord ++ tailWord_5785975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785975).length < 2 ^ (prefixWord ++ tailWord_5785975).sum := by decide
  have hdescent : baseEnd_5785975 < baseStart_5785975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5785986 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_5785986 : Nat := 118140960795 + 5785986 * 2 ^ 59
def prefixEnd_5785986 : Nat := 4983230072969 + 3 ^ 40 * 5785986 * 2
def baseEnd_5785986 : Nat := 330110208687256059651749

theorem tailTrace_5785986 : CollatzResearch.WordTrace tailWord_5785986 prefixEnd_5785986 330110208687256059651749 := by
  unfold tailWord_5785986
  simp only [CollatzResearch.WordTrace]
  refine ⟨52758061604092091145464453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140688164277578909721238541 52758061604092091145464453)
  ·
    refine ⟨9892136550767267089774585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52758061604092091145464453 9892136550767267089774585)
    ·
      refine ⟨7419102413075450317330939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9892136550767267089774585 7419102413075450317330939)
      ·
        refine ⟨11128653619613175475996409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419102413075450317330939 11128653619613175475996409)
        ·
          refine ⟨8346490214709881606997307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11128653619613175475996409 8346490214709881606997307)
          ·
            refine ⟨12519735322064822410495961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346490214709881606997307 12519735322064822410495961)
            ·
              refine ⟨9389801491548616807871971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12519735322064822410495961 9389801491548616807871971)
              ·
                refine ⟨14084702237322925211807957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9389801491548616807871971 14084702237322925211807957)
                ·
                  refine ⟨330110208687256059651749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14084702237322925211807957 330110208687256059651749)
                  ·
                    rfl

theorem cell23_5785986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_5785986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5785986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5785986 prefixEnd_5785986 := by exact prefixLift 5785986
  have htrace : WordTrace (prefixWord ++ tailWord_5785986) baseStart_5785986 baseEnd_5785986 := by
    simpa [prefixWord, tailWord_5785986, baseEnd_5785986] using wordTrace_append hprefix tailTrace_5785986
  have hstable : (prefixWord ++ tailWord_5785986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5785986).length < 2 ^ (prefixWord ++ tailWord_5785986).sum := by decide
  have hdescent : baseEnd_5785986 < baseStart_5785986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5785986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786039 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_5786039 : Nat := 118140960795 + 5786039 * 2 ^ 59
def prefixEnd_5786039 : Nat := 4983230072969 + 3 ^ 40 * 5786039 * 2
def baseEnd_5786039 : Nat := 2971019092659992829502997

theorem tailTrace_5786039 : CollatzResearch.WordTrace tailWord_5786039 prefixEnd_5786039 2971019092659992829502997 := by
  unfold tailWord_5786039
  simp only [CollatzResearch.WordTrace]
  refine ⟨211034179485176354633537171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140689452990117569755691447 211034179485176354633537171)
  ·
    refine ⟨316551269227764531950305757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211034179485176354633537171 316551269227764531950305757)
    ·
      refine ⟨118706725960411699481364659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316551269227764531950305757 118706725960411699481364659)
      ·
        refine ⟨178060088940617549222046989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118706725960411699481364659 178060088940617549222046989)
        ·
          refine ⟨66772533352731580958267621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178060088940617549222046989 66772533352731580958267621)
          ·
            refine ⟨12519850003637171429675179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66772533352731580958267621 12519850003637171429675179)
            ·
              refine ⟨18779775005455757144512769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519850003637171429675179 18779775005455757144512769)
              ·
                refine ⟨14084831254091817858384577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18779775005455757144512769 14084831254091817858384577)
                ·
                  refine ⟨10563623440568863393788433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14084831254091817858384577 10563623440568863393788433)
                  ·
                    refine ⟨7922717580426647545341325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10563623440568863393788433 7922717580426647545341325)
                    ·
                      refine ⟨2971019092659992829502997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7922717580426647545341325 2971019092659992829502997)
                      ·
                        rfl

theorem cell23_5786039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_5786039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786039 prefixEnd_5786039 := by exact prefixLift 5786039
  have htrace : WordTrace (prefixWord ++ tailWord_5786039) baseStart_5786039 baseEnd_5786039 := by
    simpa [prefixWord, tailWord_5786039, baseEnd_5786039] using wordTrace_append hprefix tailTrace_5786039
  have hstable : (prefixWord ++ tailWord_5786039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786039).length < 2 ^ (prefixWord ++ tailWord_5786039).sum := by decide
  have hdescent : baseEnd_5786039 < baseStart_5786039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786046 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5786046 : Nat := 118140960795 + 5786046 * 2 ^ 59
def prefixEnd_5786046 : Nat := 4983230072969 + 3 ^ 40 * 5786046 * 2
def baseEnd_5786046 : Nat := 990340895674858100705155

theorem tailTrace_5786046 : CollatzResearch.WordTrace tailWord_5786046 prefixEnd_5786046 990340895674858100705155 := by
  unfold tailWord_5786046
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379304349518874353630249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140689623197433996552694661 26379304349518874353630249)
  ·
    refine ⟨19784478262139155765222687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26379304349518874353630249 19784478262139155765222687)
    ·
      refine ⟨29676717393208733647834031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19784478262139155765222687 29676717393208733647834031)
      ·
        refine ⟨44515076089813100471751047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29676717393208733647834031 44515076089813100471751047)
        ·
          refine ⟨66772614134719650707626571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44515076089813100471751047 66772614134719650707626571)
          ·
            refine ⟨100158921202079476061439857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66772614134719650707626571 100158921202079476061439857)
            ·
              refine ⟨75119190901559607046079893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100158921202079476061439857 75119190901559607046079893)
              ·
                refine ⟨3521212073510606580284995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75119190901559607046079893 3521212073510606580284995)
                ·
                  refine ⟨5281818110265909870427493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521212073510606580284995 5281818110265909870427493)
                  ·
                    refine ⟨990340895674858100705155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5281818110265909870427493 990340895674858100705155)
                    ·
                      rfl

theorem cell23_5786046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5786046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786046 prefixEnd_5786046 := by exact prefixLift 5786046
  have htrace : WordTrace (prefixWord ++ tailWord_5786046) baseStart_5786046 baseEnd_5786046 := by
    simpa [prefixWord, tailWord_5786046, baseEnd_5786046] using wordTrace_append hprefix tailTrace_5786046
  have hstable : (prefixWord ++ tailWord_5786046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786046).length < 2 ^ (prefixWord ++ tailWord_5786046).sum := by decide
  have hdescent : baseEnd_5786046 < baseStart_5786046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786075 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_5786075 : Nat := 118140960795 + 5786075 * 2 ^ 59
def prefixEnd_5786075 : Nat := 4983230072969 + 3 ^ 40 * 5786075 * 2
def baseEnd_5786075 : Nat := 2971037577963554688652831

theorem tailTrace_5786075 : CollatzResearch.WordTrace tailWord_5786075 prefixEnd_5786075 2971037577963554688652831 := by
  unfold tailWord_5786075
  simp only [CollatzResearch.WordTrace]
  refine ⟨211035492513045932781847679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140690328342030621854565119 211035492513045932781847679)
  ·
    refine ⟨316553238769568899172771519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211035492513045932781847679 316553238769568899172771519)
    ·
      refine ⟨474829858154353348759157279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316553238769568899172771519 474829858154353348759157279)
      ·
        refine ⟨712244787231530023138735919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474829858154353348759157279 712244787231530023138735919)
        ·
          refine ⟨1068367180847295034708103879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712244787231530023138735919 1068367180847295034708103879)
          ·
            refine ⟨1602550771270942552062155819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068367180847295034708103879 1602550771270942552062155819)
            ·
              refine ⟨2403826156906413828093233729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602550771270942552062155819 2403826156906413828093233729)
              ·
                refine ⟨1802869617679810371069925297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403826156906413828093233729 1802869617679810371069925297)
                ·
                  refine ⟨1352152213259857778302443973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1802869617679810371069925297 1352152213259857778302443973)
                  ·
                    refine ⟨253528539986223333431708245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352152213259857778302443973 253528539986223333431708245)
                    ·
                      refine ⟨2971037577963554688652831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 253528539986223333431708245 2971037577963554688652831)
                      ·
                        rfl

theorem cell23_5786075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_5786075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786075 prefixEnd_5786075 := by exact prefixLift 5786075
  have htrace : WordTrace (prefixWord ++ tailWord_5786075) baseStart_5786075 baseEnd_5786075 := by
    simpa [prefixWord, tailWord_5786075, baseEnd_5786075] using wordTrace_append hprefix tailTrace_5786075
  have hstable : (prefixWord ++ tailWord_5786075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786075).length < 2 ^ (prefixWord ++ tailWord_5786075).sum := by decide
  have hdescent : baseEnd_5786075 < baseStart_5786075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786162 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_5786162 : Nat := 118140960795 + 5786162 * 2 ^ 59
def prefixEnd_5786162 : Nat := 4983230072969 + 3 ^ 40 * 5786162 * 2
def baseEnd_5786162 : Nat := 990360750260165282754977

theorem tailTrace_5786162 : CollatzResearch.WordTrace tailWord_5786162 prefixEnd_5786162 990360750260165282754977 := by
  unfold tailWord_5786162
  simp only [CollatzResearch.WordTrace]
  refine ⟨52759666415932686660066185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140692443775820497760176493 52759666415932686660066185)
  ·
    refine ⟨39569749811949514995049639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52759666415932686660066185 39569749811949514995049639)
    ·
      refine ⟨59354624717924272492574459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39569749811949514995049639 59354624717924272492574459)
      ·
        refine ⟨89031937076886408738861689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59354624717924272492574459 89031937076886408738861689)
        ·
          refine ⟨66773952807664806554146267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89031937076886408738861689 66773952807664806554146267)
          ·
            refine ⟨100160929211497209831219401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66773952807664806554146267 100160929211497209831219401)
            ·
              refine ⟨75120696908622907373414551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100160929211497209831219401 75120696908622907373414551)
              ·
                refine ⟨112681045362934361060121827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75120696908622907373414551 112681045362934361060121827)
                ·
                  refine ⟨169021568044401541590182741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112681045362934361060121827 169021568044401541590182741)
                  ·
                    refine ⟨990360750260165282754977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169021568044401541590182741 990360750260165282754977)
                    ·
                      rfl

theorem cell23_5786162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_5786162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786162 prefixEnd_5786162 := by exact prefixLift 5786162
  have htrace : WordTrace (prefixWord ++ tailWord_5786162) baseStart_5786162 baseEnd_5786162 := by
    simpa [prefixWord, tailWord_5786162, baseEnd_5786162] using wordTrace_append hprefix tailTrace_5786162
  have hstable : (prefixWord ++ tailWord_5786162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786162).length < 2 ^ (prefixWord ++ tailWord_5786162).sum := by decide
  have hdescent : baseEnd_5786162 < baseStart_5786162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786176 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3]
def baseStart_5786176 : Nat := 118140960795 + 5786176 * 2 ^ 59
def prefixEnd_5786176 : Nat := 4983230072969 + 3 ^ 40 * 5786176 * 2
def baseEnd_5786176 : Nat := 2971089439509658793489867

theorem tailTrace_5786176 : CollatzResearch.WordTrace tailWord_5786176 prefixEnd_5786176 2971089439509658793489867 := by
  unfold tailWord_5786176
  simp only [CollatzResearch.WordTrace]
  refine ⟨105519588142840013515637191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140692784190453351354182921 105519588142840013515637191)
  ·
    refine ⟨158279382214260020273455787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105519588142840013515637191 158279382214260020273455787)
    ·
      refine ⟨237419073321390030410183681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158279382214260020273455787 237419073321390030410183681)
      ·
        refine ⟨178064304991042522807637761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237419073321390030410183681 178064304991042522807637761)
        ·
          refine ⟨133548228743281892105728321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178064304991042522807637761 133548228743281892105728321)
          ·
            refine ⟨100161171557461419079296241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133548228743281892105728321 100161171557461419079296241)
            ·
              refine ⟨75120878668096064309472181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100161171557461419079296241 75120878668096064309472181)
              ·
                refine ⟨7042582375134006029013017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75120878668096064309472181 7042582375134006029013017)
                ·
                  refine ⟨5281936781350504521759763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7042582375134006029013017 5281936781350504521759763)
                  ·
                    refine ⟨7922905172025756782639645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5281936781350504521759763 7922905172025756782639645)
                    ·
                      refine ⟨2971089439509658793489867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7922905172025756782639645 2971089439509658793489867)
                      ·
                        rfl

theorem cell23_5786176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_5786176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786176 prefixEnd_5786176 := by exact prefixLift 5786176
  have htrace : WordTrace (prefixWord ++ tailWord_5786176) baseStart_5786176 baseEnd_5786176 := by
    simpa [prefixWord, tailWord_5786176, baseEnd_5786176] using wordTrace_append hprefix tailTrace_5786176
  have hstable : (prefixWord ++ tailWord_5786176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786176).length < 2 ^ (prefixWord ++ tailWord_5786176).sum := by decide
  have hdescent : baseEnd_5786176 < baseStart_5786176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786192 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_5786192 : Nat := 118140960795 + 5786192 * 2 ^ 59
def prefixEnd_5786192 : Nat := 4983230072969 + 3 ^ 40 * 5786192 * 2
def baseEnd_5786192 : Nat := 990365885066710243629931

theorem tailTrace_5786192 : CollatzResearch.WordTrace tailWord_5786192 prefixEnd_5786192 990365885066710243629931 := by
  unfold tailWord_5786192
  simp only [CollatzResearch.WordTrace]
  refine ⟨105519879926811030881928415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140693173235748041175904553 105519879926811030881928415)
  ·
    refine ⟨158279819890216546322892623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105519879926811030881928415 158279819890216546322892623)
    ·
      refine ⟨237419729835324819484338935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158279819890216546322892623 237419729835324819484338935)
      ·
        refine ⟨356129594752987229226508403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237419729835324819484338935 356129594752987229226508403)
        ·
          refine ⟨534194392129480843839762605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356129594752987229226508403 534194392129480843839762605)
          ·
            refine ⟨200322897048555316439910977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534194392129480843839762605 200322897048555316439910977)
            ·
              refine ⟨150242172786416487329933233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200322897048555316439910977 150242172786416487329933233)
              ·
                refine ⟨112681629589812365497449925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150242172786416487329933233 112681629589812365497449925)
                ·
                  refine ⟨21127805548089818530771861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112681629589812365497449925 21127805548089818530771861)
                  ·
                    refine ⟨990365885066710243629931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21127805548089818530771861 990365885066710243629931)
                    ·
                      rfl

theorem cell23_5786192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_5786192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786192 prefixEnd_5786192 := by exact prefixLift 5786192
  have htrace : WordTrace (prefixWord ++ tailWord_5786192) baseStart_5786192 baseEnd_5786192 := by
    simpa [prefixWord, tailWord_5786192, baseEnd_5786192] using wordTrace_append hprefix tailTrace_5786192
  have hstable : (prefixWord ++ tailWord_5786192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786192).length < 2 ^ (prefixWord ++ tailWord_5786192).sum := by decide
  have hdescent : baseEnd_5786192 < baseStart_5786192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786232 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_5786232 : Nat := 118140960795 + 5786232 * 2 ^ 59
def prefixEnd_5786232 : Nat := 4983230072969 + 3 ^ 40 * 5786232 * 2
def baseEnd_5786232 : Nat := 2971118194426310574389609

theorem tailTrace_5786232 : CollatzResearch.WordTrace tailWord_5786232 prefixEnd_5786232 2971118194426310574389609 := by
  unfold tailWord_5786232
  simp only [CollatzResearch.WordTrace]
  refine ⟨105520609386738574297656475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140694145848984765730208633 105520609386738574297656475)
  ·
    refine ⟨158280914080107861446484713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105520609386738574297656475 158280914080107861446484713)
    ·
      refine ⟨118710685560080896084863535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158280914080107861446484713 118710685560080896084863535)
      ·
        refine ⟨178066028340121344127295303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118710685560080896084863535 178066028340121344127295303)
        ·
          refine ⟨267099042510182016190942955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178066028340121344127295303 267099042510182016190942955)
          ·
            refine ⟨400648563765273024286414433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267099042510182016190942955 400648563765273024286414433)
            ·
              refine ⟨300486422823954768214810825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400648563765273024286414433 300486422823954768214810825)
              ·
                refine ⟨225364817117966076161108119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300486422823954768214810825 225364817117966076161108119)
                ·
                  refine ⟨338047225676949114241662179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225364817117966076161108119 338047225676949114241662179)
                  ·
                    refine ⟨507070838515423671362493269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338047225676949114241662179 507070838515423671362493269)
                    ·
                      refine ⟨2971118194426310574389609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 507070838515423671362493269 2971118194426310574389609)
                      ·
                        rfl

theorem cell23_5786232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_5786232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786232 prefixEnd_5786232 := by exact prefixLift 5786232
  have htrace : WordTrace (prefixWord ++ tailWord_5786232) baseStart_5786232 baseEnd_5786232 := by
    simpa [prefixWord, tailWord_5786232, baseEnd_5786232] using wordTrace_append hprefix tailTrace_5786232
  have hstable : (prefixWord ++ tailWord_5786232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786232).length < 2 ^ (prefixWord ++ tailWord_5786232).sum := by decide
  have hdescent : baseEnd_5786232 < baseStart_5786232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786237 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_5786237 : Nat := 118140960795 + 5786237 * 2 ^ 59
def prefixEnd_5786237 : Nat := 4983230072969 + 3 ^ 40 * 5786237 * 2
def baseEnd_5786237 : Nat := 2971120761829583054827087

theorem tailTrace_5786237 : CollatzResearch.WordTrace tailWord_5786237 prefixEnd_5786237 2971120761829583054827087 := by
  unfold tailWord_5786237
  simp only [CollatzResearch.WordTrace]
  refine ⟨211041401138459034449244965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140694267425639356299496643 211041401138459034449244965)
  ·
    refine ⟨39570262713461068959233431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211041401138459034449244965 39570262713461068959233431)
    ·
      refine ⟨59355394070191603438850147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39570262713461068959233431 59355394070191603438850147)
      ·
        refine ⟨89033091105287405158275221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59355394070191603438850147 89033091105287405158275221)
        ·
          refine ⟨4173426145560347116794151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89033091105287405158275221 4173426145560347116794151)
          ·
            refine ⟨6260139218340520675191227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173426145560347116794151 6260139218340520675191227)
            ·
              refine ⟨9390208827510781012786841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260139218340520675191227 9390208827510781012786841)
              ·
                refine ⟨7042656620633085759590131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9390208827510781012786841 7042656620633085759590131)
                ·
                  refine ⟨10563984930949628639385197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042656620633085759590131 10563984930949628639385197)
                  ·
                    refine ⟨3961494349106110739769449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10563984930949628639385197 3961494349106110739769449)
                    ·
                      refine ⟨2971120761829583054827087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961494349106110739769449 2971120761829583054827087)
                      ·
                        rfl

theorem cell23_5786237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_5786237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786237 prefixEnd_5786237 := by exact prefixLift 5786237
  have htrace : WordTrace (prefixWord ++ tailWord_5786237) baseStart_5786237 baseEnd_5786237 := by
    simpa [prefixWord, tailWord_5786237, baseEnd_5786237] using wordTrace_append hprefix tailTrace_5786237
  have hstable : (prefixWord ++ tailWord_5786237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786237).length < 2 ^ (prefixWord ++ tailWord_5786237).sum := by decide
  have hdescent : baseEnd_5786237 < baseStart_5786237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786249 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_5786249 : Nat := 118140960795 + 5786249 * 2 ^ 59
def prefixEnd_5786249 : Nat := 4983230072969 + 3 ^ 40 * 5786249 * 2
def baseEnd_5786249 : Nat := 2971126923597437007877031

theorem tailTrace_5786249 : CollatzResearch.WordTrace tailWord_5786249 prefixEnd_5786249 2971126923597437007877031 := by
  unfold tailWord_5786249
  simp only [CollatzResearch.WordTrace]
  refine ⟨211041838814415560498681801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140694559209610373665787867 211041838814415560498681801)
  ·
    refine ⟨158281379110811670374011351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211041838814415560498681801 158281379110811670374011351)
    ·
      refine ⟨237422068666217505561017027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158281379110811670374011351 237422068666217505561017027)
      ·
        refine ⟨356133102999326258341525541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237422068666217505561017027 356133102999326258341525541)
        ·
          refine ⟨66774956812373673439036039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356133102999326258341525541 66774956812373673439036039)
          ·
            refine ⟨100162435218560510158554059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66774956812373673439036039 100162435218560510158554059)
            ·
              refine ⟨150243652827840765237831089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100162435218560510158554059 150243652827840765237831089)
              ·
                refine ⟨112682739620880573928373317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150243652827840765237831089 112682739620880573928373317)
                ·
                  refine ⟨21128013678915107611569997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112682739620880573928373317 21128013678915107611569997)
                  ·
                    refine ⟨7923005129593165354338749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21128013678915107611569997 7923005129593165354338749)
                    ·
                      refine ⟨2971126923597437007877031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923005129593165354338749 2971126923597437007877031)
                      ·
                        rfl

theorem cell23_5786249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_5786249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786249 prefixEnd_5786249 := by exact prefixLift 5786249
  have htrace : WordTrace (prefixWord ++ tailWord_5786249) baseStart_5786249 baseEnd_5786249 := by
    simpa [prefixWord, tailWord_5786249, baseEnd_5786249] using wordTrace_append hprefix tailTrace_5786249
  have hstable : (prefixWord ++ tailWord_5786249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786249).length < 2 ^ (prefixWord ++ tailWord_5786249).sum := by decide
  have hdescent : baseEnd_5786249 < baseStart_5786249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786273 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 5]
def baseStart_5786273 : Nat := 118140960795 + 5786273 * 2 ^ 59
def prefixEnd_5786273 : Nat := 4983230072969 + 3 ^ 40 * 5786273 * 2
def baseEnd_5786273 : Nat := 330126583014793879330769

theorem tailTrace_5786273 : CollatzResearch.WordTrace tailWord_5786273 prefixEnd_5786273 330126583014793879330769 := by
  unfold tailWord_5786273
  simp only [CollatzResearch.WordTrace]
  refine ⟨211042714166328612597555473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140695142777552408398370315 211042714166328612597555473)
  ·
    refine ⟨158282035624746459448166605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211042714166328612597555473 158282035624746459448166605)
    ·
      refine ⟨59355763359279922293062477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158282035624746459448166605 59355763359279922293062477)
      ·
        refine ⟨22258411259729970859898429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59355763359279922293062477 22258411259729970859898429)
        ·
          refine ⟨8346904222398739072461911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22258411259729970859898429 8346904222398739072461911)
          ·
            refine ⟨12520356333598108608692867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346904222398739072461911 12520356333598108608692867)
            ·
              refine ⟨18780534500397162913039301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12520356333598108608692867 18780534500397162913039301)
              ·
                refine ⟨3521350218824468046194869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18780534500397162913039301 3521350218824468046194869)
                ·
                  refine ⟨330126583014793879330769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521350218824468046194869 330126583014793879330769)
                  ·
                    rfl

theorem cell23_5786273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 5].length) (baseStart_5786273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786273 prefixEnd_5786273 := by exact prefixLift 5786273
  have htrace : WordTrace (prefixWord ++ tailWord_5786273) baseStart_5786273 baseEnd_5786273 := by
    simpa [prefixWord, tailWord_5786273, baseEnd_5786273] using wordTrace_append hprefix tailTrace_5786273
  have hstable : (prefixWord ++ tailWord_5786273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786273).length < 2 ^ (prefixWord ++ tailWord_5786273).sum := by decide
  have hdescent : baseEnd_5786273 < baseStart_5786273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786276 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_5786276 : Nat := 118140960795 + 5786276 * 2 ^ 59
def prefixEnd_5786276 : Nat := 4983230072969 + 3 ^ 40 * 5786276 * 2
def baseEnd_5786276 : Nat := 2971140787575108402239407

theorem tailTrace_5786276 : CollatzResearch.WordTrace tailWord_5786276 prefixEnd_5786276 2971140787575108402239407 := by
  unfold tailWord_5786276
  simp only [CollatzResearch.WordTrace]
  refine ⟨105521411792658872054957341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140695215723545162739943121 105521411792658872054957341)
  ·
    refine ⟨39570529422247077020609003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105521411792658872054957341 39570529422247077020609003)
    ·
      refine ⟨59355794133370615530913505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39570529422247077020609003 59355794133370615530913505)
      ·
        refine ⟨44516845600027961648185129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59355794133370615530913505 44516845600027961648185129)
        ·
          refine ⟨33387634200020971236138847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44516845600027961648185129 33387634200020971236138847)
          ·
            refine ⟨50081451300031456854208271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33387634200020971236138847 50081451300031456854208271)
            ·
              refine ⟨75122176950047185281312407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50081451300031456854208271 75122176950047185281312407)
              ·
                refine ⟨112683265425070777921968611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75122176950047185281312407 112683265425070777921968611)
                ·
                  refine ⟨169024898137606166882952917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112683265425070777921968611 169024898137606166882952917)
                  ·
                    refine ⟨3961521050100144536319209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169024898137606166882952917 3961521050100144536319209)
                    ·
                      refine ⟨2971140787575108402239407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961521050100144536319209 2971140787575108402239407)
                      ·
                        rfl

theorem cell23_5786276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_5786276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786276 prefixEnd_5786276 := by exact prefixLift 5786276
  have htrace : WordTrace (prefixWord ++ tailWord_5786276) baseStart_5786276 baseEnd_5786276 := by
    simpa [prefixWord, tailWord_5786276, baseEnd_5786276] using wordTrace_append hprefix tailTrace_5786276
  have hstable : (prefixWord ++ tailWord_5786276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786276).length < 2 ^ (prefixWord ++ tailWord_5786276).sum := by decide
  have hdescent : baseEnd_5786276 < baseStart_5786276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786329 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 8]
def baseStart_5786329 : Nat := 118140960795 + 5786329 * 2 ^ 59
def prefixEnd_5786329 : Nat := 4983230072969 + 3 ^ 40 * 5786329 * 2
def baseEnd_5786329 : Nat := 330129778005532966097407

theorem tailTrace_5786329 : CollatzResearch.WordTrace tailWord_5786329 prefixEnd_5786329 330129778005532966097407 := by
  unfold tailWord_5786329
  simp only [CollatzResearch.WordTrace]
  refine ⟨211044756654125734161594041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140696504436083822774396027 211044756654125734161594041)
  ·
    refine ⟨158283567490594300621195531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211044756654125734161594041 158283567490594300621195531)
    ·
      refine ⟨237425351235891450931793297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158283567490594300621195531 237425351235891450931793297)
      ·
        refine ⟨178069013426918588198844973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237425351235891450931793297 178069013426918588198844973)
        ·
          refine ⟨66775880035094470574566865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178069013426918588198844973 66775880035094470574566865)
          ·
            refine ⟨50081910026320852930925149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66775880035094470574566865 50081910026320852930925149)
            ·
              refine ⟨18780716259870319849096931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50081910026320852930925149 18780716259870319849096931)
              ·
                refine ⟨28171074389805479773645397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18780716259870319849096931 28171074389805479773645397)
                ·
                  refine ⟨330129778005532966097407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28171074389805479773645397 330129778005532966097407)
                  ·
                    rfl

theorem cell23_5786329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_5786329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786329 prefixEnd_5786329 := by exact prefixLift 5786329
  have htrace : WordTrace (prefixWord ++ tailWord_5786329) baseStart_5786329 baseEnd_5786329 := by
    simpa [prefixWord, tailWord_5786329, baseEnd_5786329] using wordTrace_append hprefix tailTrace_5786329
  have hstable : (prefixWord ++ tailWord_5786329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786329).length < 2 ^ (prefixWord ++ tailWord_5786329).sum := by decide
  have hdescent : baseEnd_5786329 < baseStart_5786329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786383 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 2, 3, 2]
def baseStart_5786383 : Nat := 118140960795 + 5786383 * 2 ^ 59
def prefixEnd_5786383 : Nat := 4983230072969 + 3 ^ 40 * 5786383 * 2
def baseEnd_5786383 : Nat := 2971195730005139483601415

theorem tailTrace_5786383 : CollatzResearch.WordTrace tailWord_5786383 prefixEnd_5786383 2971195730005139483601415 := by
  unfold tailWord_5786383
  simp only [CollatzResearch.WordTrace]
  refine ⟨211046726195930101384059803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140697817463953400922706535 211046726195930101384059803)
  ·
    refine ⟨316570089293895152076089705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211046726195930101384059803 316570089293895152076089705)
    ·
      refine ⟨237427566970421364057067279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316570089293895152076089705 237427566970421364057067279)
      ·
        refine ⟨356141350455632046085600919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237427566970421364057067279 356141350455632046085600919)
        ·
          refine ⟨534212025683448069128401379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356141350455632046085600919 534212025683448069128401379)
          ·
            refine ⟨801318038525172103692602069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534212025683448069128401379 801318038525172103692602069)
            ·
              refine ⟨18780891527933721180295361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 801318038525172103692602069 18780891527933721180295361)
              ·
                refine ⟨14085668645950290885221521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18780891527933721180295361 14085668645950290885221521)
                ·
                  refine ⟨10564251484462718163916141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14085668645950290885221521 10564251484462718163916141)
                  ·
                    refine ⟨3961594306673519311468553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10564251484462718163916141 3961594306673519311468553)
                    ·
                      refine ⟨2971195730005139483601415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961594306673519311468553 2971195730005139483601415)
                      ·
                        rfl

theorem cell23_5786383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3, 2].length) (baseStart_5786383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786383 prefixEnd_5786383 := by exact prefixLift 5786383
  have htrace : WordTrace (prefixWord ++ tailWord_5786383) baseStart_5786383 baseEnd_5786383 := by
    simpa [prefixWord, tailWord_5786383, baseEnd_5786383] using wordTrace_append hprefix tailTrace_5786383
  have hstable : (prefixWord ++ tailWord_5786383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786383).length < 2 ^ (prefixWord ++ tailWord_5786383).sum := by decide
  have hdescent : baseEnd_5786383 < baseStart_5786383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786397 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 6]
def baseStart_5786397 : Nat := 118140960795 + 5786397 * 2 ^ 59
def prefixEnd_5786397 : Nat := 4983230072969 + 3 ^ 40 * 5786397 * 2
def baseEnd_5786397 : Nat := 330133657637144714314039

theorem tailTrace_5786397 : CollatzResearch.WordTrace tailWord_5786397 prefixEnd_5786397 330133657637144714314039 := by
  unfold tailWord_5786397
  simp only [CollatzResearch.WordTrace]
  refine ⟨211047236817879381775069445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140698157878586254516712963 211047236817879381775069445)
  ·
    refine ⟨39571356903352384082825521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211047236817879381775069445 39571356903352384082825521)
    ·
      refine ⟨29678517677514288062119141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39571356903352384082825521 29678517677514288062119141)
      ·
        refine ⟨5564722064533929011647339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29678517677514288062119141 5564722064533929011647339)
        ·
          refine ⟨8347083096800893517471009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564722064533929011647339 8347083096800893517471009)
          ·
            refine ⟨6260312322600670138103257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8347083096800893517471009 6260312322600670138103257)
            ·
              refine ⟨4695234241950502603577443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6260312322600670138103257 4695234241950502603577443)
              ·
                refine ⟨7042851362925753905366165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695234241950502603577443 7042851362925753905366165)
                ·
                  refine ⟨330133657637144714314039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7042851362925753905366165 330133657637144714314039)
                  ·
                    rfl

theorem cell23_5786397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_5786397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786397 prefixEnd_5786397 := by exact prefixLift 5786397
  have htrace : WordTrace (prefixWord ++ tailWord_5786397) baseStart_5786397 baseEnd_5786397 := by
    simpa [prefixWord, tailWord_5786397, baseEnd_5786397] using wordTrace_append hprefix tailTrace_5786397
  have hstable : (prefixWord ++ tailWord_5786397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786397).length < 2 ^ (prefixWord ++ tailWord_5786397).sum := by decide
  have hdescent : baseEnd_5786397 < baseStart_5786397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786410 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5786410 : Nat := 118140960795 + 5786410 * 2 ^ 59
def prefixEnd_5786410 : Nat := 4983230072969 + 3 ^ 40 * 5786410 * 2
def baseEnd_5786410 : Nat := 990403197994270292654597

theorem tailTrace_5786410 : CollatzResearch.WordTrace tailWord_5786410 prefixEnd_5786410 990403197994270292654597 := by
  unfold tailWord_5786410
  simp only [CollatzResearch.WordTrace]
  refine ⟨52761927741708071248823171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140698473977888189996861789 52761927741708071248823171)
  ·
    refine ⟨79142891612562106873234757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52761927741708071248823171 79142891612562106873234757)
    ·
      refine ⟨14839292177355395038731517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79142891612562106873234757 14839292177355395038731517)
      ·
        refine ⟨5564734566508273139524319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14839292177355395038731517 5564734566508273139524319)
        ·
          refine ⟨8347101849762409709286479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564734566508273139524319 8347101849762409709286479)
          ·
            refine ⟨12520652774643614563929719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347101849762409709286479 12520652774643614563929719)
            ·
              refine ⟨18780979161965421845894579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12520652774643614563929719 18780979161965421845894579)
              ·
                refine ⟨28171468742948132768841869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18780979161965421845894579 28171468742948132768841869)
                ·
                  refine ⟨10564300778605549788315701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28171468742948132768841869 10564300778605549788315701)
                  ·
                    refine ⟨990403197994270292654597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10564300778605549788315701 990403197994270292654597)
                    ·
                      rfl

theorem cell23_5786410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5786410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786410 prefixEnd_5786410 := by exact prefixLift 5786410
  have htrace : WordTrace (prefixWord ++ tailWord_5786410) baseStart_5786410 baseEnd_5786410 := by
    simpa [prefixWord, tailWord_5786410, baseEnd_5786410] using wordTrace_append hprefix tailTrace_5786410
  have hstable : (prefixWord ++ tailWord_5786410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786410).length < 2 ^ (prefixWord ++ tailWord_5786410).sum := by decide
  have hdescent : baseEnd_5786410 < baseStart_5786410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786460 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5786460 : Nat := 118140960795 + 5786460 * 2 ^ 59
def prefixEnd_5786460 : Nat := 4983230072969 + 3 ^ 40 * 5786460 * 2
def baseEnd_5786460 : Nat := 2971235268015535682338561

theorem tailTrace_5786460 : CollatzResearch.WordTrace tailWord_5786460 prefixEnd_5786460 2971235268015535682338561 := by
  unfold tailWord_5786460
  simp only [CollatzResearch.WordTrace]
  refine ⟨105524767308325571767306417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140699689744434095689741889 105524767308325571767306417)
  ·
    refine ⟨79143575481244178825479813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105524767308325571767306417 79143575481244178825479813)
    ·
      refine ⟨14839420402733283529777465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79143575481244178825479813 14839420402733283529777465)
      ·
        refine ⟨11129565302049962647333099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14839420402733283529777465 11129565302049962647333099)
        ·
          refine ⟨16694347953074943970999649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11129565302049962647333099 16694347953074943970999649)
          ·
            refine ⟨12520760964806207978249737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16694347953074943970999649 12520760964806207978249737)
            ·
              refine ⟨9390570723604655983687303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12520760964806207978249737 9390570723604655983687303)
              ·
                refine ⟨14085856085406983975530955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390570723604655983687303 14085856085406983975530955)
                ·
                  refine ⟨21128784128110475963296433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14085856085406983975530955 21128784128110475963296433)
                  ·
                    refine ⟨15846588096082856972472325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21128784128110475963296433 15846588096082856972472325)
                    ·
                      refine ⟨2971235268015535682338561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15846588096082856972472325 2971235268015535682338561)
                      ·
                        rfl

theorem cell23_5786460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5786460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786460 prefixEnd_5786460 := by exact prefixLift 5786460
  have htrace : WordTrace (prefixWord ++ tailWord_5786460) baseStart_5786460 baseEnd_5786460 := by
    simpa [prefixWord, tailWord_5786460, baseEnd_5786460] using wordTrace_append hprefix tailTrace_5786460
  have hstable : (prefixWord ++ tailWord_5786460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786460).length < 2 ^ (prefixWord ++ tailWord_5786460).sum := by decide
  have hdescent : baseEnd_5786460 < baseStart_5786460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786463 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_5786463 : Nat := 118140960795 + 5786463 * 2 ^ 59
def prefixEnd_5786463 : Nat := 4983230072969 + 3 ^ 40 * 5786463 * 2
def baseEnd_5786463 : Nat := 2971236808457499170601047

theorem tailTrace_5786463 : CollatzResearch.WordTrace tailWord_5786463 prefixEnd_5786463 2971236808457499170601047 := by
  unfold tailWord_5786463
  simp only [CollatzResearch.WordTrace]
  refine ⟨211049644035640275046972043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140699762690426850031314695 211049644035640275046972043)
  ·
    refine ⟨316574466053460412570458065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211049644035640275046972043 316574466053460412570458065)
    ·
      refine ⟨237430849540095309427843549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316574466053460412570458065 237430849540095309427843549)
      ·
        refine ⟨89036568577535741035441331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237430849540095309427843549 89036568577535741035441331)
        ·
          refine ⟨133554852866303611553161997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89036568577535741035441331 133554852866303611553161997)
          ·
            refine ⟨50083069824863854332435749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133554852866303611553161997 50083069824863854332435749)
            ·
              refine ⟨9390575592161972687331703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50083069824863854332435749 9390575592161972687331703)
              ·
                refine ⟨14085863388242959030997555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390575592161972687331703 14085863388242959030997555)
                ·
                  refine ⟨21128795082364438546496333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14085863388242959030997555 21128795082364438546496333)
                  ·
                    refine ⟨7923298155886664454936125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21128795082364438546496333 7923298155886664454936125)
                    ·
                      refine ⟨2971236808457499170601047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923298155886664454936125 2971236808457499170601047)
                      ·
                        rfl

theorem cell23_5786463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_5786463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786463 prefixEnd_5786463 := by exact prefixLift 5786463
  have htrace : WordTrace (prefixWord ++ tailWord_5786463) baseStart_5786463 baseEnd_5786463 := by
    simpa [prefixWord, tailWord_5786463, baseEnd_5786463] using wordTrace_append hprefix tailTrace_5786463
  have hstable : (prefixWord ++ tailWord_5786463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786463).length < 2 ^ (prefixWord ++ tailWord_5786463).sum := by decide
  have hdescent : baseEnd_5786463 < baseStart_5786463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786476 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_5786476 : Nat := 118140960795 + 5786476 * 2 ^ 59
def prefixEnd_5786476 : Nat := 4983230072969 + 3 ^ 40 * 5786476 * 2
def baseEnd_5786476 : Nat := 2971243483706007619738487

theorem tailTrace_5786476 : CollatzResearch.WordTrace tailWord_5786476 prefixEnd_5786476 2971243483706007619738487 := by
  unfold tailWord_5786476
  simp only [CollatzResearch.WordTrace]
  refine ⟨105525059092296589133597641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140700078789728785511463521 105525059092296589133597641)
  ·
    refine ⟨79143794319222441850198231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105525059092296589133597641 79143794319222441850198231)
    ·
      refine ⟨118715691478833662775297347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79143794319222441850198231 118715691478833662775297347)
      ·
        refine ⟨178073537218250494162946021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118715691478833662775297347 178073537218250494162946021)
        ·
          refine ⟨33388788228421967655552379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178073537218250494162946021 33388788228421967655552379)
          ·
            refine ⟨50083182342632951483328569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33388788228421967655552379 50083182342632951483328569)
            ·
              refine ⟨37562386756974713612496427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50083182342632951483328569 37562386756974713612496427)
              ·
                refine ⟨56343580135462070418744641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37562386756974713612496427 56343580135462070418744641)
                ·
                  refine ⟨42257685101596552814058481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56343580135462070418744641 42257685101596552814058481)
                  ·
                    refine ⟨31693263826197414610543861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42257685101596552814058481 31693263826197414610543861)
                    ·
                      refine ⟨2971243483706007619738487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31693263826197414610543861 2971243483706007619738487)
                      ·
                        rfl

theorem cell23_5786476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_5786476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786476 prefixEnd_5786476 := by exact prefixLift 5786476
  have htrace : WordTrace (prefixWord ++ tailWord_5786476) baseStart_5786476 baseEnd_5786476 := by
    simpa [prefixWord, tailWord_5786476, baseEnd_5786476] using wordTrace_append hprefix tailTrace_5786476
  have hstable : (prefixWord ++ tailWord_5786476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786476).length < 2 ^ (prefixWord ++ tailWord_5786476).sum := by decide
  have hdescent : baseEnd_5786476 < baseStart_5786476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786514 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5786514 : Nat := 118140960795 + 5786514 * 2 ^ 59
def prefixEnd_5786514 : Nat := 4983230072969 + 3 ^ 40 * 5786514 * 2
def baseEnd_5786514 : Nat := 2971262995970878471063313

theorem tailTrace_5786514 : CollatzResearch.WordTrace tailWord_5786514 prefixEnd_5786514 2971262995970878471063313 := by
  unfold tailWord_5786514
  simp only [CollatzResearch.WordTrace]
  refine ⟨52762876039613877689269649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140701002772303673838052397 52762876039613877689269649)
  ·
    refine ⟨39572157029710408266952237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52762876039613877689269649 39572157029710408266952237)
    ·
      refine ⟨14839558886141403100107089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39572157029710408266952237 14839558886141403100107089)
      ·
        refine ⟨11129669164606052325080317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14839558886141403100107089 11129669164606052325080317)
        ·
          refine ⟨4173625936727269621905119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11129669164606052325080317 4173625936727269621905119)
          ·
            refine ⟨6260438905090904432857679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173625936727269621905119 6260438905090904432857679)
            ·
              refine ⟨9390658357636356649286519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260438905090904432857679 9390658357636356649286519)
              ·
                refine ⟨14085987536454534973929779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390658357636356649286519 14085987536454534973929779)
                ·
                  refine ⟨21128981304681802460894669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14085987536454534973929779 21128981304681802460894669)
                  ·
                    refine ⟨7923367989255675922835501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21128981304681802460894669 7923367989255675922835501)
                    ·
                      refine ⟨2971262995970878471063313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923367989255675922835501 2971262995970878471063313)
                      ·
                        rfl

theorem cell23_5786514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5786514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786514 prefixEnd_5786514 := by exact prefixLift 5786514
  have htrace : WordTrace (prefixWord ++ tailWord_5786514) baseStart_5786514 baseEnd_5786514 := by
    simpa [prefixWord, tailWord_5786514, baseEnd_5786514] using wordTrace_append hprefix tailTrace_5786514
  have hstable : (prefixWord ++ tailWord_5786514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786514).length < 2 ^ (prefixWord ++ tailWord_5786514).sum := by decide
  have hdescent : baseEnd_5786514 < baseStart_5786514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786524 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5786524 : Nat := 118140960795 + 5786524 * 2 ^ 59
def prefixEnd_5786524 : Nat := 4983230072969 + 3 ^ 40 * 5786524 * 2
def baseEnd_5786524 : Nat := 2971268130777423431938267

theorem tailTrace_5786524 : CollatzResearch.WordTrace tailWord_5786524 prefixEnd_5786524 2971268130777423431938267 := by
  unfold tailWord_5786524
  simp only [CollatzResearch.WordTrace]
  refine ⟨105525934444209641232471313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140701245925612854976628417 105525934444209641232471313)
  ·
    refine ⟨79144450833157230924353485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105525934444209641232471313 79144450833157230924353485)
    ·
      refine ⟨29679169062433961596632557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79144450833157230924353485 29679169062433961596632557)
      ·
        refine ⟨11129688398412735598737209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29679169062433961596632557 11129688398412735598737209)
        ·
          refine ⟨8347266298809551699052907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11129688398412735598737209 8347266298809551699052907)
          ·
            refine ⟨12520899448214327548579361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347266298809551699052907 12520899448214327548579361)
            ·
              refine ⟨9390674586160745661434521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12520899448214327548579361 9390674586160745661434521)
              ·
                refine ⟨7043005939620559246075891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9390674586160745661434521 7043005939620559246075891)
                ·
                  refine ⟨10564508909430838869113837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043005939620559246075891 10564508909430838869113837)
                  ·
                    refine ⟨3961690841036564575917689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10564508909430838869113837 3961690841036564575917689)
                    ·
                      refine ⟨2971268130777423431938267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961690841036564575917689 2971268130777423431938267)
                      ·
                        rfl

theorem cell23_5786524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5786524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786524 prefixEnd_5786524 := by exact prefixLift 5786524
  have htrace : WordTrace (prefixWord ++ tailWord_5786524) baseStart_5786524 baseEnd_5786524 := by
    simpa [prefixWord, tailWord_5786524, baseEnd_5786524] using wordTrace_append hprefix tailTrace_5786524
  have hstable : (prefixWord ++ tailWord_5786524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786524).length < 2 ^ (prefixWord ++ tailWord_5786524).sum := by decide
  have hdescent : baseEnd_5786524 < baseStart_5786524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786543 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 5]
def baseStart_5786543 : Nat := 118140960795 + 5786543 * 2 ^ 59
def prefixEnd_5786543 : Nat := 4983230072969 + 3 ^ 40 * 5786543 * 2
def baseEnd_5786543 : Nat := 330141987434428761955631

theorem tailTrace_5786543 : CollatzResearch.WordTrace tailWord_5786543 prefixEnd_5786543 330141987434428761955631 := by
  unfold tailWord_5786543
  simp only [CollatzResearch.WordTrace]
  refine ⟨211052561875350448709884283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140701707916900299139922855 211052561875350448709884283)
  ·
    refine ⟨316578842813025673064826425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211052561875350448709884283 316578842813025673064826425)
    ·
      refine ⟨237434132109769254798619819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316578842813025673064826425 237434132109769254798619819)
      ·
        refine ⟨356151198164653882197929729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237434132109769254798619819 356151198164653882197929729)
        ·
          refine ⟨267113398623490411648447297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356151198164653882197929729 267113398623490411648447297)
          ·
            refine ⟨200335048967617808736335473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267113398623490411648447297 200335048967617808736335473)
            ·
              refine ⟨150251286725713356552251605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200335048967617808736335473 150251286725713356552251605)
              ·
                refine ⟨3521514532633906794193397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150251286725713356552251605 3521514532633906794193397)
                ·
                  refine ⟨330141987434428761955631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521514532633906794193397 330141987434428761955631)
                  ·
                    rfl

theorem cell23_5786543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 5].length) (baseStart_5786543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786543 prefixEnd_5786543 := by exact prefixLift 5786543
  have htrace : WordTrace (prefixWord ++ tailWord_5786543) baseStart_5786543 baseEnd_5786543 := by
    simpa [prefixWord, tailWord_5786543, baseEnd_5786543] using wordTrace_append hprefix tailTrace_5786543
  have hstable : (prefixWord ++ tailWord_5786543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786543).length < 2 ^ (prefixWord ++ tailWord_5786543).sum := by decide
  have hdescent : baseEnd_5786543 < baseStart_5786543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786546 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_5786546 : Nat := 118140960795 + 5786546 * 2 ^ 59
def prefixEnd_5786546 : Nat := 4983230072969 + 3 ^ 40 * 5786546 * 2
def baseEnd_5786546 : Nat := 2971279427351822345863165

theorem tailTrace_5786546 : CollatzResearch.WordTrace tailWord_5786546 prefixEnd_5786546 2971279427351822345863165 := by
  unfold tailWord_5786546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52763167823584895055560873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140701780862893053481495661 52763167823584895055560873)
  ·
    refine ⟨39572375867688671291670655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52763167823584895055560873 39572375867688671291670655)
    ·
      refine ⟨59358563801533006937505983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39572375867688671291670655 59358563801533006937505983)
      ·
        refine ⟨89037845702299510406258975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59358563801533006937505983 89037845702299510406258975)
        ·
          refine ⟨133556768553449265609388463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89037845702299510406258975 133556768553449265609388463)
          ·
            refine ⟨200335152830173898414082695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133556768553449265609388463 200335152830173898414082695)
            ·
              refine ⟨300502729245260847621124043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200335152830173898414082695 300502729245260847621124043)
              ·
                refine ⟨450754093867891271431686065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300502729245260847621124043 450754093867891271431686065)
                ·
                  refine ⟨338065570400918453573764549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450754093867891271431686065 338065570400918453573764549)
                  ·
                    refine ⟨63387294450172210045080853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338065570400918453573764549 63387294450172210045080853)
                    ·
                      refine ⟨2971279427351822345863165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63387294450172210045080853 2971279427351822345863165)
                      ·
                        rfl

theorem cell23_5786546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_5786546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786546 prefixEnd_5786546 := by exact prefixLift 5786546
  have htrace : WordTrace (prefixWord ++ tailWord_5786546) baseStart_5786546 baseEnd_5786546 := by
    simpa [prefixWord, tailWord_5786546, baseEnd_5786546] using wordTrace_append hprefix tailTrace_5786546
  have hstable : (prefixWord ++ tailWord_5786546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786546).length < 2 ^ (prefixWord ++ tailWord_5786546).sum := by decide
  have hdescent : baseEnd_5786546 < baseStart_5786546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786563 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 7, 2]
def baseStart_5786563 : Nat := 118140960795 + 5786563 * 2 ^ 59
def prefixEnd_5786563 : Nat := 4983230072969 + 3 ^ 40 * 5786563 * 2
def baseEnd_5786563 : Nat := 2971288156522948779350587

theorem tailTrace_5786563 : CollatzResearch.WordTrace tailWord_5786563 prefixEnd_5786563 2971288156522948779350587 := by
  unfold tailWord_5786563
  simp only [CollatzResearch.WordTrace]
  refine ⟨211053291335277992125612343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140702194223518661417074895 211053291335277992125612343)
  ·
    refine ⟨316579937002916988188418515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211053291335277992125612343 316579937002916988188418515)
    ·
      refine ⟨474869905504375482282627773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316579937002916988188418515 474869905504375482282627773)
      ·
        refine ⟨178076214564140805855985415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474869905504375482282627773 178076214564140805855985415)
        ·
          refine ⟨267114321846211208783978123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178076214564140805855985415 267114321846211208783978123)
          ·
            refine ⟨400671482769316813175967185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267114321846211208783978123 400671482769316813175967185)
            ·
              refine ⟨300503612076987609881975389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400671482769316813175967185 300503612076987609881975389)
              ·
                refine ⟨112688854528870353705740771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300503612076987609881975389 112688854528870353705740771)
                ·
                  refine ⟨169033281793305530558611157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112688854528870353705740771 169033281793305530558611157)
                  ·
                    refine ⟨3961717542030598372467449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169033281793305530558611157 3961717542030598372467449)
                    ·
                      refine ⟨2971288156522948779350587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961717542030598372467449 2971288156522948779350587)
                      ·
                        rfl

theorem cell23_5786563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_5786563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786563 prefixEnd_5786563 := by exact prefixLift 5786563
  have htrace : WordTrace (prefixWord ++ tailWord_5786563) baseStart_5786563 baseEnd_5786563 := by
    simpa [prefixWord, tailWord_5786563, baseEnd_5786563] using wordTrace_append hprefix tailTrace_5786563
  have hstable : (prefixWord ++ tailWord_5786563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786563).length < 2 ^ (prefixWord ++ tailWord_5786563).sum := by decide
  have hdescent : baseEnd_5786563 < baseStart_5786563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786647 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5786647 : Nat := 118140960795 + 5786647 * 2 ^ 59
def prefixEnd_5786647 : Nat := 4983230072969 + 3 ^ 40 * 5786647 * 2
def baseEnd_5786647 : Nat := 2971331288897926450700201

theorem tailTrace_5786647 : CollatzResearch.WordTrace tailWord_5786647 prefixEnd_5786647 2971331288897926450700201 := by
  unfold tailWord_5786647
  simp only [CollatzResearch.WordTrace]
  refine ⟨211056355066973674471670195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140704236711315782981113463 211056355066973674471670195)
  ·
    refine ⟨316584532600460511707505293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211056355066973674471670195 316584532600460511707505293)
    ·
      refine ⟨118719199725172691890314485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316584532600460511707505293 118719199725172691890314485)
      ·
        refine ⟨11129924974234939864716983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118719199725172691890314485 11129924974234939864716983)
        ·
          refine ⟨16694887461352409797075475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11129924974234939864716983 16694887461352409797075475)
          ·
            refine ⟨25042331192028614695613213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16694887461352409797075475 25042331192028614695613213)
            ·
              refine ⟨9390874197010730510854955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25042331192028614695613213 9390874197010730510854955)
              ·
                refine ⟨14086311295516095766282433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390874197010730510854955 14086311295516095766282433)
                ·
                  refine ⟨10564733471637071824711825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14086311295516095766282433 10564733471637071824711825)
                  ·
                    refine ⟨7923550103727803868533869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10564733471637071824711825 7923550103727803868533869)
                    ·
                      refine ⟨2971331288897926450700201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923550103727803868533869 2971331288897926450700201)
                      ·
                        rfl

theorem cell23_5786647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5786647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786647 prefixEnd_5786647 := by exact prefixLift 5786647
  have htrace : WordTrace (prefixWord ++ tailWord_5786647) baseStart_5786647 baseEnd_5786647 := by
    simpa [prefixWord, tailWord_5786647, baseEnd_5786647] using wordTrace_append hprefix tailTrace_5786647
  have hstable : (prefixWord ++ tailWord_5786647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786647).length < 2 ^ (prefixWord ++ tailWord_5786647).sum := by decide
  have hdescent : baseEnd_5786647 < baseStart_5786647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786700 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_5786700 : Nat := 118140960795 + 5786700 * 2 ^ 59
def prefixEnd_5786700 : Nat := 4983230072969 + 3 ^ 40 * 5786700 * 2
def baseEnd_5786700 : Nat := 2971358503372614743337457

theorem tailTrace_5786700 : CollatzResearch.WordTrace tailWord_5786700 prefixEnd_5786700 2971358503372614743337457 := by
  unfold tailWord_5786700
  simp only [CollatzResearch.WordTrace]
  refine ⟨105529144067890832261674777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140705525423854443015566369 105529144067890832261674777)
  ·
    refine ⟨79146858050918124196256083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105529144067890832261674777 79146858050918124196256083)
    ·
      refine ⟨118720287076377186294384125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79146858050918124196256083 118720287076377186294384125)
      ·
        refine ⟨44520107653641444860394047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118720287076377186294384125 44520107653641444860394047)
        ·
          refine ⟨66780161480462167290591071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44520107653641444860394047 66780161480462167290591071)
          ·
            refine ⟨100170242220693250935886607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66780161480462167290591071 100170242220693250935886607)
            ·
              refine ⟨150255363331039876403829911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100170242220693250935886607 150255363331039876403829911)
              ·
                refine ⟨225383044996559814605744867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150255363331039876403829911 225383044996559814605744867)
                ·
                  refine ⟨338074567494839721908617301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225383044996559814605744867 338074567494839721908617301)
                  ·
                    refine ⟨3961811337830152991116609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 338074567494839721908617301 3961811337830152991116609)
                    ·
                      refine ⟨2971358503372614743337457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961811337830152991116609 2971358503372614743337457)
                      ·
                        rfl

theorem cell23_5786700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_5786700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786700 prefixEnd_5786700 := by exact prefixLift 5786700
  have htrace : WordTrace (prefixWord ++ tailWord_5786700) baseStart_5786700 baseEnd_5786700 := by
    simpa [prefixWord, tailWord_5786700, baseEnd_5786700] using wordTrace_append hprefix tailTrace_5786700
  have hstable : (prefixWord ++ tailWord_5786700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786700).length < 2 ^ (prefixWord ++ tailWord_5786700).sum := by decide
  have hdescent : baseEnd_5786700 < baseStart_5786700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786720 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_5786720 : Nat := 118140960795 + 5786720 * 2 ^ 59
def prefixEnd_5786720 : Nat := 4983230072969 + 3 ^ 40 * 5786720 * 2
def baseEnd_5786720 : Nat := 2971368772985704665087365

theorem tailTrace_5786720 : CollatzResearch.WordTrace tailWord_5786720 prefixEnd_5786720 2971368772985704665087365 := by
  unfold tailWord_5786720
  simp only [CollatzResearch.WordTrace]
  refine ⟨105529508797854603969538807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140706011730472805292718409 105529508797854603969538807)
  ·
    refine ⟨158294263196781905954308211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105529508797854603969538807 158294263196781905954308211)
    ·
      refine ⟨237441394795172858931462317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158294263196781905954308211 237441394795172858931462317)
      ·
        refine ⟨89040523048189822099298369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237441394795172858931462317 89040523048189822099298369)
        ·
          refine ⟨66780392286142366574473777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89040523048189822099298369 66780392286142366574473777)
          ·
            refine ⟨50085294214606774930855333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66780392286142366574473777 50085294214606774930855333)
            ·
              refine ⟨9390992665238770299535375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50085294214606774930855333 9390992665238770299535375)
              ·
                refine ⟨14086488997858155449303063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390992665238770299535375 14086488997858155449303063)
                ·
                  refine ⟨21129733496787233173954595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14086488997858155449303063 21129733496787233173954595)
                  ·
                    refine ⟨31694600245180849760931893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21129733496787233173954595 31694600245180849760931893)
                    ·
                      refine ⟨2971368772985704665087365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31694600245180849760931893 2971368772985704665087365)
                      ·
                        rfl

theorem cell23_5786720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_5786720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786720 prefixEnd_5786720 := by exact prefixLift 5786720
  have htrace : WordTrace (prefixWord ++ tailWord_5786720) baseStart_5786720 baseEnd_5786720 := by
    simpa [prefixWord, tailWord_5786720, baseEnd_5786720] using wordTrace_append hprefix tailTrace_5786720
  have hstable : (prefixWord ++ tailWord_5786720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786720).length < 2 ^ (prefixWord ++ tailWord_5786720).sum := by decide
  have hdescent : baseEnd_5786720 < baseStart_5786720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786728 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5786728 : Nat := 118140960795 + 5786728 * 2 ^ 59
def prefixEnd_5786728 : Nat := 4983230072969 + 3 ^ 40 * 5786728 * 2
def baseEnd_5786728 : Nat := 2971372880830940633787329

theorem tailTrace_5786728 : CollatzResearch.WordTrace tailWord_5786728 prefixEnd_5786728 2971372880830940633787329 := by
  unfold tailWord_5786728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105529654689840112652684419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140706206253120150203579225 105529654689840112652684419)
  ·
    refine ⟨158294482034760168979026629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105529654689840112652684419 158294482034760168979026629)
    ·
      refine ⟨29680215381517531683567493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158294482034760168979026629 29680215381517531683567493)
      ·
        refine ⟨5565040384034537190668905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29680215381517531683567493 5565040384034537190668905)
        ·
          refine ⟨4173780288025902893001679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5565040384034537190668905 4173780288025902893001679)
          ·
            refine ⟨6260670432038854339502519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173780288025902893001679 6260670432038854339502519)
            ·
              refine ⟨9391005648058281509253779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260670432038854339502519 9391005648058281509253779)
              ·
                refine ⟨14086508472087422263880669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391005648058281509253779 14086508472087422263880669)
                ·
                  refine ⟨5282440677032783348955251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14086508472087422263880669 5282440677032783348955251)
                  ·
                    refine ⟨7923661015549175023432877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5282440677032783348955251 7923661015549175023432877)
                    ·
                      refine ⟨2971372880830940633787329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923661015549175023432877 2971372880830940633787329)
                      ·
                        rfl

theorem cell23_5786728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5786728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786728 prefixEnd_5786728 := by exact prefixLift 5786728
  have htrace : WordTrace (prefixWord ++ tailWord_5786728) baseStart_5786728 baseEnd_5786728 := by
    simpa [prefixWord, tailWord_5786728, baseEnd_5786728] using wordTrace_append hprefix tailTrace_5786728
  have hstable : (prefixWord ++ tailWord_5786728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786728).length < 2 ^ (prefixWord ++ tailWord_5786728).sum := by decide
  have hdescent : baseEnd_5786728 < baseStart_5786728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786730 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5786730 : Nat := 118140960795 + 5786730 * 2 ^ 59
def prefixEnd_5786730 : Nat := 4983230072969 + 3 ^ 40 * 5786730 * 2
def baseEnd_5786730 : Nat := 2971373907792249625962319

theorem tailTrace_5786730 : CollatzResearch.WordTrace tailWord_5786730 prefixEnd_5786730 2971373907792249625962319 := by
  unfold tailWord_5786730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52764845581418244911735411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140706254883781986431294429 52764845581418244911735411)
  ·
    refine ⟨79147268372127367367603117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52764845581418244911735411 79147268372127367367603117)
    ·
      refine ⟨29680225639547762762851169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79147268372127367367603117 29680225639547762762851169)
      ·
        refine ⟨22260169229660822072138377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29680225639547762762851169 22260169229660822072138377)
        ·
          refine ⟨16695126922245616554103783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22260169229660822072138377 16695126922245616554103783)
          ·
            refine ⟨25042690383368424831155675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16695126922245616554103783 25042690383368424831155675)
            ·
              refine ⟨37564035575052637246733513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25042690383368424831155675 37564035575052637246733513)
              ·
                refine ⟨28173026681289477935050135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37564035575052637246733513 28173026681289477935050135)
                ·
                  refine ⟨42259540021934216902575203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28173026681289477935050135 42259540021934216902575203)
                  ·
                    refine ⟨63389310032901325353862805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42259540021934216902575203 63389310032901325353862805)
                    ·
                      refine ⟨2971373907792249625962319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63389310032901325353862805 2971373907792249625962319)
                      ·
                        rfl

theorem cell23_5786730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5786730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786730 prefixEnd_5786730 := by exact prefixLift 5786730
  have htrace : WordTrace (prefixWord ++ tailWord_5786730) baseStart_5786730 baseEnd_5786730 := by
    simpa [prefixWord, tailWord_5786730, baseEnd_5786730] using wordTrace_append hprefix tailTrace_5786730
  have hstable : (prefixWord ++ tailWord_5786730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786730).length < 2 ^ (prefixWord ++ tailWord_5786730).sum := by decide
  have hdescent : baseEnd_5786730 < baseStart_5786730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786743 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_5786743 : Nat := 118140960795 + 5786743 * 2 ^ 59
def prefixEnd_5786743 : Nat := 4983230072969 + 3 ^ 40 * 5786743 * 2
def baseEnd_5786743 : Nat := 2971380583040758075099759

theorem tailTrace_5786743 : CollatzResearch.WordTrace tailWord_5786743 prefixEnd_5786743 2971380583040758075099759 := by
  unfold tailWord_5786743
  simp only [CollatzResearch.WordTrace]
  refine ⟨211059856474625882867164883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140706570983083921911443255 211059856474625882867164883)
  ·
    refine ⟨316589784711938824300747325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211059856474625882867164883 316589784711938824300747325)
    ·
      refine ⟨118721169266977059112780247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316589784711938824300747325 118721169266977059112780247)
      ·
        refine ⟨178081753900465588669170371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118721169266977059112780247 178081753900465588669170371)
        ·
          refine ⟨267122630850698383003755557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178081753900465588669170371 267122630850698383003755557)
          ·
            refine ⟨50085493284505946813204167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267122630850698383003755557 50085493284505946813204167)
            ·
              refine ⟨75128239926758920219806251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50085493284505946813204167 75128239926758920219806251)
              ·
                refine ⟨112692359890138380329709377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75128239926758920219806251 112692359890138380329709377)
                ·
                  refine ⟨84519269917603785247282033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112692359890138380329709377 84519269917603785247282033)
                  ·
                    refine ⟨63389452438202838935461525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84519269917603785247282033 63389452438202838935461525)
                    ·
                      refine ⟨2971380583040758075099759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63389452438202838935461525 2971380583040758075099759)
                      ·
                        rfl

theorem cell23_5786743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_5786743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786743 prefixEnd_5786743 := by exact prefixLift 5786743
  have htrace : WordTrace (prefixWord ++ tailWord_5786743) baseStart_5786743 baseEnd_5786743 := by
    simpa [prefixWord, tailWord_5786743, baseEnd_5786743] using wordTrace_append hprefix tailTrace_5786743
  have hstable : (prefixWord ++ tailWord_5786743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786743).length < 2 ^ (prefixWord ++ tailWord_5786743).sum := by decide
  have hdescent : baseEnd_5786743 < baseStart_5786743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786763 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_5786763 : Nat := 118140960795 + 5786763 * 2 ^ 59
def prefixEnd_5786763 : Nat := 4983230072969 + 3 ^ 40 * 5786763 * 2
def baseEnd_5786763 : Nat := 2971390852653847996849667

theorem tailTrace_5786763 : CollatzResearch.WordTrace tailWord_5786763 prefixEnd_5786763 2971390852653847996849667 := by
  unfold tailWord_5786763
  simp only [CollatzResearch.WordTrace]
  refine ⟨211060585934553426282892943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140707057289702284188595295 211060585934553426282892943)
  ·
    refine ⟨316590878901830139424339415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211060585934553426282892943 316590878901830139424339415)
    ·
      refine ⟨474886318352745209136509123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316590878901830139424339415 474886318352745209136509123)
      ·
        refine ⟨712329477529117813704763685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474886318352745209136509123 712329477529117813704763685)
        ·
          refine ⟨133561777036709590069643191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 712329477529117813704763685 133561777036709590069643191)
          ·
            refine ⟨200342665555064385104464787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133561777036709590069643191 200342665555064385104464787)
            ·
              refine ⟨300513998332596577656697181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200342665555064385104464787 300513998332596577656697181)
              ·
                refine ⟨112692749374723716621261443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300513998332596577656697181 112692749374723716621261443)
                ·
                  refine ⟨169039124062085574931892165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112692749374723716621261443 169039124062085574931892165)
                  ·
                    refine ⟨31694835761641045299729781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169039124062085574931892165 31694835761641045299729781)
                    ·
                      refine ⟨2971390852653847996849667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31694835761641045299729781 2971390852653847996849667)
                      ·
                        rfl

theorem cell23_5786763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_5786763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786763 prefixEnd_5786763 := by exact prefixLift 5786763
  have htrace : WordTrace (prefixWord ++ tailWord_5786763) baseStart_5786763 baseEnd_5786763 := by
    simpa [prefixWord, tailWord_5786763, baseEnd_5786763] using wordTrace_append hprefix tailTrace_5786763
  have hstable : (prefixWord ++ tailWord_5786763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786763).length < 2 ^ (prefixWord ++ tailWord_5786763).sum := by decide
  have hdescent : baseEnd_5786763 < baseStart_5786763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786784 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3]
def baseStart_5786784 : Nat := 118140960795 + 5786784 * 2 ^ 59
def prefixEnd_5786784 : Nat := 4983230072969 + 3 ^ 40 * 5786784 * 2
def baseEnd_5786784 : Nat := 2971401635747592414687071

theorem tailTrace_5786784 : CollatzResearch.WordTrace tailWord_5786784 prefixEnd_5786784 2971401635747592414687071 := by
  unfold tailWord_5786784
  simp only [CollatzResearch.WordTrace]
  refine ⟨105530675933738673434703703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140707567911651564579604937 105530675933738673434703703)
  ·
    refine ⟨158296013900608010152055555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105530675933738673434703703 158296013900608010152055555)
    ·
      refine ⟨237444020850912015228083333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158296013900608010152055555 237444020850912015228083333)
      ·
        refine ⟨44520753909546002855265625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237444020850912015228083333 44520753909546002855265625)
        ·
          refine ⟨33390565432159502141449219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44520753909546002855265625 33390565432159502141449219)
          ·
            refine ⟨50085848148239253212173829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33390565432159502141449219 50085848148239253212173829)
            ·
              refine ⟨9391096527794859977282593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50085848148239253212173829 9391096527794859977282593)
              ·
                refine ⟨7043322395846144982961945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9391096527794859977282593 7043322395846144982961945)
                ·
                  refine ⟨5282491796884608737221459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043322395846144982961945 5282491796884608737221459)
                  ·
                    refine ⟨7923737695326913105832189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5282491796884608737221459 7923737695326913105832189)
                    ·
                      refine ⟨2971401635747592414687071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923737695326913105832189 2971401635747592414687071)
                      ·
                        rfl

theorem cell23_5786784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_5786784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786784 prefixEnd_5786784 := by exact prefixLift 5786784
  have htrace : WordTrace (prefixWord ++ tailWord_5786784) baseStart_5786784 baseEnd_5786784 := by
    simpa [prefixWord, tailWord_5786784, baseEnd_5786784] using wordTrace_append hprefix tailTrace_5786784
  have hstable : (prefixWord ++ tailWord_5786784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786784).length < 2 ^ (prefixWord ++ tailWord_5786784).sum := by decide
  have hdescent : baseEnd_5786784 < baseStart_5786784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786810 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_5786810 : Nat := 118140960795 + 5786810 * 2 ^ 59
def prefixEnd_5786810 : Nat := 4983230072969 + 3 ^ 40 * 5786810 * 2
def baseEnd_5786810 : Nat := 2971414986244609312961951

theorem tailTrace_5786810 : CollatzResearch.WordTrace tailWord_5786810 prefixEnd_5786810 2971414986244609312961951 := by
  unfold tailWord_5786810
  simp only [CollatzResearch.WordTrace]
  refine ⟨52765575041345788327463471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140708200110255435539902589 52765575041345788327463471)
  ·
    refine ⟨79148362562018682491195207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52765575041345788327463471 79148362562018682491195207)
    ·
      refine ⟨118722543843028023736792811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79148362562018682491195207 118722543843028023736792811)
      ·
        refine ⟨178083815764542035605189217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118722543843028023736792811 178083815764542035605189217)
        ·
          refine ⟨133562861823406526703891913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178083815764542035605189217 133562861823406526703891913)
          ·
            refine ⟨100172146367554895027918935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133562861823406526703891913 100172146367554895027918935)
            ·
              refine ⟨150258219551332342541878403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100172146367554895027918935 150258219551332342541878403)
              ·
                refine ⟨225387329326998513812817605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150258219551332342541878403 225387329326998513812817605)
                ·
                  refine ⟨42260124248812221339903301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225387329326998513812817605 42260124248812221339903301)
                  ·
                    refine ⟨7923773296652291501231869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42260124248812221339903301 7923773296652291501231869)
                    ·
                      refine ⟨2971414986244609312961951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923773296652291501231869 2971414986244609312961951)
                      ·
                        rfl

theorem cell23_5786810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_5786810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786810 prefixEnd_5786810 := by exact prefixLift 5786810
  have htrace : WordTrace (prefixWord ++ tailWord_5786810) baseStart_5786810 baseEnd_5786810 := by
    simpa [prefixWord, tailWord_5786810, baseEnd_5786810] using wordTrace_append hprefix tailTrace_5786810
  have hstable : (prefixWord ++ tailWord_5786810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786810).length < 2 ^ (prefixWord ++ tailWord_5786810).sum := by decide
  have hdescent : baseEnd_5786810 < baseStart_5786810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786822 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5786822 : Nat := 118140960795 + 5786822 * 2 ^ 59
def prefixEnd_5786822 : Nat := 4983230072969 + 3 ^ 40 * 5786822 * 2
def baseEnd_5786822 : Nat := 2971421148012463266011897

theorem tailTrace_5786822 : CollatzResearch.WordTrace tailWord_5786822 prefixEnd_5786822 2971421148012463266011897 := by
  unfold tailWord_5786822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595710557541864979977835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140708491894226452906193813 6595710557541864979977835)
  ·
    refine ⟨9893565836312797469966753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6595710557541864979977835 9893565836312797469966753)
    ·
      refine ⟨7420174377234598102475065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9893565836312797469966753 7420174377234598102475065)
      ·
        refine ⟨5565130782925948576856299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7420174377234598102475065 5565130782925948576856299)
        ·
          refine ⟨8347696174388922865284449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565130782925948576856299 8347696174388922865284449)
          ·
            refine ⟨6260772130791692148963337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8347696174388922865284449 6260772130791692148963337)
            ·
              refine ⟨4695579098093769111722503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6260772130791692148963337 4695579098093769111722503)
              ·
                refine ⟨7043368647140653667583755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695579098093769111722503 7043368647140653667583755)
                ·
                  refine ⟨10565052970710980501375633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043368647140653667583755 10565052970710980501375633)
                  ·
                    refine ⟨7923789728033235376031725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10565052970710980501375633 7923789728033235376031725)
                    ·
                      refine ⟨2971421148012463266011897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7923789728033235376031725 2971421148012463266011897)
                      ·
                        rfl

theorem cell23_5786822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5786822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786822 prefixEnd_5786822 := by exact prefixLift 5786822
  have htrace : WordTrace (prefixWord ++ tailWord_5786822) baseStart_5786822 baseEnd_5786822 := by
    simpa [prefixWord, tailWord_5786822, baseEnd_5786822] using wordTrace_append hprefix tailTrace_5786822
  have hstable : (prefixWord ++ tailWord_5786822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786822).length < 2 ^ (prefixWord ++ tailWord_5786822).sum := by decide
  have hdescent : baseEnd_5786822 < baseStart_5786822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786837 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5786837 : Nat := 118140960795 + 5786837 * 2 ^ 59
def prefixEnd_5786837 : Nat := 4983230072969 + 3 ^ 40 * 5786837 * 2
def baseEnd_5786837 : Nat := 2971428850222280707324327

theorem tailTrace_5786837 : CollatzResearch.WordTrace tailWord_5786837 prefixEnd_5786837 2971428850222280707324327 := by
  unfold tailWord_5786837
  simp only [CollatzResearch.WordTrace]
  refine ⟨211063284936285336921086765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140708856624190224614057843 211063284936285336921086765)
  ·
    refine ⟨79148731851107001345407537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211063284936285336921086765 79148731851107001345407537)
    ·
      refine ⟨59361548888330251009055653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79148731851107001345407537 59361548888330251009055653)
      ·
        refine ⟨11130290416561922064197935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59361548888330251009055653 11130290416561922064197935)
        ·
          refine ⟨16695435624842883096296903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11130290416561922064197935 16695435624842883096296903)
          ·
            refine ⟨25043153437264324644445355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16695435624842883096296903 25043153437264324644445355)
            ·
              refine ⟨37564730155896486966668033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25043153437264324644445355 37564730155896486966668033)
              ·
                refine ⟨28173547616922365225001025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37564730155896486966668033 28173547616922365225001025)
                ·
                  refine ⟨21130160712691773918750769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28173547616922365225001025 21130160712691773918750769)
                  ·
                    refine ⟨15847620534518830439063077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21130160712691773918750769 15847620534518830439063077)
                    ·
                      refine ⟨2971428850222280707324327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15847620534518830439063077 2971428850222280707324327)
                      ·
                        rfl

theorem cell23_5786837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5786837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786837 prefixEnd_5786837 := by exact prefixLift 5786837
  have htrace : WordTrace (prefixWord ++ tailWord_5786837) baseStart_5786837 baseEnd_5786837 := by
    simpa [prefixWord, tailWord_5786837, baseEnd_5786837] using wordTrace_append hprefix tailTrace_5786837
  have hstable : (prefixWord ++ tailWord_5786837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786837).length < 2 ^ (prefixWord ++ tailWord_5786837).sum := by decide
  have hdescent : baseEnd_5786837 < baseStart_5786837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786847 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 5]
def baseStart_5786847 : Nat := 118140960795 + 5786847 * 2 ^ 59
def prefixEnd_5786847 : Nat := 4983230072969 + 3 ^ 40 * 5786847 * 2
def baseEnd_5786847 : Nat := 330159331669869518688809

theorem tailTrace_5786847 : CollatzResearch.WordTrace tailWord_5786847 prefixEnd_5786847 330159331669869518688809 := by
  unfold tailWord_5786847
  simp only [CollatzResearch.WordTrace]
  refine ⟨211063649666249108628950795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140709099777499405752633863 211063649666249108628950795)
  ·
    refine ⟨316595474499373662943426193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211063649666249108628950795 316595474499373662943426193)
    ·
      refine ⟨237446605874530247207569645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316595474499373662943426193 237446605874530247207569645)
      ·
        refine ⟨89042477202948842702838617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237446605874530247207569645 89042477202948842702838617)
        ·
          refine ⟨66781857902211632027128963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89042477202948842702838617 66781857902211632027128963)
          ·
            refine ⟨100172786853317448040693445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66781857902211632027128963 100172786853317448040693445)
            ·
              refine ⟨18782397534997021507630021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100172786853317448040693445 18782397534997021507630021)
              ·
                refine ⟨3521699537811941532680629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18782397534997021507630021 3521699537811941532680629)
                ·
                  refine ⟨330159331669869518688809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521699537811941532680629 330159331669869518688809)
                  ·
                    rfl

theorem cell23_5786847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 5].length) (baseStart_5786847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786847 prefixEnd_5786847 := by exact prefixLift 5786847
  have htrace : WordTrace (prefixWord ++ tailWord_5786847) baseStart_5786847 baseEnd_5786847 := by
    simpa [prefixWord, tailWord_5786847, baseEnd_5786847] using wordTrace_append hprefix tailTrace_5786847
  have hstable : (prefixWord ++ tailWord_5786847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786847).length < 2 ^ (prefixWord ++ tailWord_5786847).sum := by decide
  have hdescent : baseEnd_5786847 < baseStart_5786847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786858 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_5786858 : Nat := 118140960795 + 5786858 * 2 ^ 59
def prefixEnd_5786858 : Nat := 4983230072969 + 3 ^ 40 * 5786858 * 2
def baseEnd_5786858 : Nat := 2971439633316025125161731

theorem tailTrace_5786858 : CollatzResearch.WordTrace tailWord_5786858 prefixEnd_5786858 2971439633316025125161731 := by
  unfold tailWord_5786858
  simp only [CollatzResearch.WordTrace]
  refine ⟨52766012717302314376900307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140709367246139505005067485 52766012717302314376900307)
  ·
    refine ⟨79149019075953471565350461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52766012717302314376900307 79149019075953471565350461)
    ·
      refine ⟨29680882153482551837006423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79149019075953471565350461 29680882153482551837006423)
      ·
        refine ⟨44521323230223827755509635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29680882153482551837006423 44521323230223827755509635)
        ·
          refine ⟨66781984845335741633264453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44521323230223827755509635 66781984845335741633264453)
          ·
            refine ⟨12521622158500451556237085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66781984845335741633264453 12521622158500451556237085)
            ·
              refine ⟨4695608309437669333588907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12521622158500451556237085 4695608309437669333588907)
              ·
                refine ⟨7043412464156504000383361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695608309437669333588907 7043412464156504000383361)
                ·
                  refine ⟨5282559348117378000287521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043412464156504000383361 5282559348117378000287521)
                  ·
                    refine ⟨3961919511088033500215641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282559348117378000287521 3961919511088033500215641)
                    ·
                      refine ⟨2971439633316025125161731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3961919511088033500215641 2971439633316025125161731)
                      ·
                        rfl

theorem cell23_5786858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_5786858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786858 prefixEnd_5786858 := by exact prefixLift 5786858
  have htrace : WordTrace (prefixWord ++ tailWord_5786858) baseStart_5786858 baseEnd_5786858 := by
    simpa [prefixWord, tailWord_5786858, baseEnd_5786858] using wordTrace_append hprefix tailTrace_5786858
  have hstable : (prefixWord ++ tailWord_5786858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786858).length < 2 ^ (prefixWord ++ tailWord_5786858).sum := by decide
  have hdescent : baseEnd_5786858 < baseStart_5786858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786860 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_5786860 : Nat := 118140960795 + 5786860 * 2 ^ 59
def prefixEnd_5786860 : Nat := 4983230072969 + 3 ^ 40 * 5786860 * 2
def baseEnd_5786860 : Nat := 990480220092444705778907

theorem tailTrace_5786860 : CollatzResearch.WordTrace tailWord_5786860 prefixEnd_5786860 990480220092444705778907 := by
  unfold tailWord_5786860
  simp only [CollatzResearch.WordTrace]
  refine ⟨105532061907601005924587017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140709415876801341232782689 105532061907601005924587017)
  ·
    refine ⟨79149046430700754443440263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105532061907601005924587017 79149046430700754443440263)
    ·
      refine ⟨118723569646051131665160395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79149046430700754443440263 118723569646051131665160395)
      ·
        refine ⟨178085354469076697497740593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118723569646051131665160395 178085354469076697497740593)
        ·
          refine ⟨133564015851807523123305445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178085354469076697497740593 133564015851807523123305445)
          ·
            refine ⟨25043252972213910585619771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133564015851807523123305445 25043252972213910585619771)
            ·
              refine ⟨37564879458320865878429657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25043252972213910585619771 37564879458320865878429657)
              ·
                refine ⟨28173659593740649408822243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37564879458320865878429657 28173659593740649408822243)
                ·
                  refine ⟨42260489390610974113233365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28173659593740649408822243 42260489390610974113233365)
                  ·
                    refine ⟨990480220092444705778907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42260489390610974113233365 990480220092444705778907)
                    ·
                      rfl

theorem cell23_5786860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_5786860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786860 prefixEnd_5786860 := by exact prefixLift 5786860
  have htrace : WordTrace (prefixWord ++ tailWord_5786860) baseStart_5786860 baseEnd_5786860 := by
    simpa [prefixWord, tailWord_5786860, baseEnd_5786860] using wordTrace_append hprefix tailTrace_5786860
  have hstable : (prefixWord ++ tailWord_5786860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786860).length < 2 ^ (prefixWord ++ tailWord_5786860).sum := by decide
  have hdescent : baseEnd_5786860 < baseStart_5786860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786897 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_5786897 : Nat := 118140960795 + 5786897 * 2 ^ 59
def prefixEnd_5786897 : Nat := 4983230072969 + 3 ^ 40 * 5786897 * 2
def baseEnd_5786897 : Nat := 2971459659061550472574051

theorem tailTrace_5786897 : CollatzResearch.WordTrace tailWord_5786897 prefixEnd_5786897 2971459659061550472574051 := by
  unfold tailWord_5786897
  simp only [CollatzResearch.WordTrace]
  refine ⟨211065473316067967168270945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140710315544045311445513963 211065473316067967168270945)
  ·
    refine ⟨158299104987050975376203209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211065473316067967168270945 158299104987050975376203209)
    ·
      refine ⟨118724328740288231532152407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158299104987050975376203209 118724328740288231532152407)
      ·
        refine ⟨178086493110432347298228611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118724328740288231532152407 178086493110432347298228611)
        ·
          refine ⟨267129739665648520947342917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178086493110432347298228611 267129739665648520947342917)
          ·
            refine ⟨50086826187309097677626797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267129739665648520947342917 50086826187309097677626797)
            ·
              refine ⟨18782559820240911629110049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50086826187309097677626797 18782559820240911629110049)
              ·
                refine ⟨14086919865180683721832537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18782559820240911629110049 14086919865180683721832537)
                ·
                  refine ⟨10565189898885512791374403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14086919865180683721832537 10565189898885512791374403)
                  ·
                    refine ⟨15847784848328269187061605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10565189898885512791374403 15847784848328269187061605)
                    ·
                      refine ⟨2971459659061550472574051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15847784848328269187061605 2971459659061550472574051)
                      ·
                        rfl

theorem cell23_5786897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_5786897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786897 prefixEnd_5786897 := by exact prefixLift 5786897
  have htrace : WordTrace (prefixWord ++ tailWord_5786897) baseStart_5786897 baseEnd_5786897 := by
    simpa [prefixWord, tailWord_5786897, baseEnd_5786897] using wordTrace_append hprefix tailTrace_5786897
  have hstable : (prefixWord ++ tailWord_5786897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786897).length < 2 ^ (prefixWord ++ tailWord_5786897).sum := by decide
  have hdescent : baseEnd_5786897 < baseStart_5786897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786898 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_5786898 : Nat := 118140960795 + 5786898 * 2 ^ 59
def prefixEnd_5786898 : Nat := 4983230072969 + 3 ^ 40 * 5786898 * 2
def baseEnd_5786898 : Nat := 330162241393578329851283

theorem tailTrace_5786898 : CollatzResearch.WordTrace tailWord_5786898 prefixEnd_5786898 330162241393578329851283 := by
  unfold tailWord_5786898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52766377447266086084764337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140710339859376229559371565 52766377447266086084764337)
  ·
    refine ⟨39574783085449564563573253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52766377447266086084764337 39574783085449564563573253)
    ·
      refine ⟨7420271828521793355669985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39574783085449564563573253 7420271828521793355669985)
      ·
        refine ⟨5565203871391345016752489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7420271828521793355669985 5565203871391345016752489)
        ·
          refine ⟨4173902903543508762564367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5565203871391345016752489 4173902903543508762564367)
          ·
            refine ⟨6260854355315263143846551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173902903543508762564367 6260854355315263143846551)
            ·
              refine ⟨9391281532972894715769827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260854355315263143846551 9391281532972894715769827)
              ·
                refine ⟨14086922299459342073654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391281532972894715769827 14086922299459342073654741)
                ·
                  refine ⟨330162241393578329851283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14086922299459342073654741 330162241393578329851283)
                  ·
                    rfl

theorem cell23_5786898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_5786898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786898 prefixEnd_5786898 := by exact prefixLift 5786898
  have htrace : WordTrace (prefixWord ++ tailWord_5786898) baseStart_5786898 baseEnd_5786898 := by
    simpa [prefixWord, tailWord_5786898, baseEnd_5786898] using wordTrace_append hprefix tailTrace_5786898
  have hstable : (prefixWord ++ tailWord_5786898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786898).length < 2 ^ (prefixWord ++ tailWord_5786898).sum := by decide
  have hdescent : baseEnd_5786898 < baseStart_5786898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5786967 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 3, 5]
def baseStart_5786967 : Nat := 118140960795 + 5786967 * 2 ^ 59
def prefixEnd_5786967 : Nat := 4983230072969 + 3 ^ 40 * 5786967 * 2
def baseEnd_5786967 : Nat := 990498534235788399566243

theorem tailTrace_5786967 : CollatzResearch.WordTrace tailWord_5786967 prefixEnd_5786967 990498534235788399566243 := by
  unfold tailWord_5786967
  simp only [CollatzResearch.WordTrace]
  refine ⟨211068026425814369123319155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140712017617209579415546103 211068026425814369123319155)
  ·
    refine ⟨316602039638721553684978733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211068026425814369123319155 316602039638721553684978733)
    ·
      refine ⟨118725764864520582631867025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316602039638721553684978733 118725764864520582631867025)
      ·
        refine ⟨89044323648390436973900269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118725764864520582631867025 89044323648390436973900269)
        ·
          refine ⟨33391621368146413865212601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89044323648390436973900269 33391621368146413865212601)
          ·
            refine ⟨25043716026109810398909451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33391621368146413865212601 25043716026109810398909451)
            ·
              refine ⟨37565574039164715598364177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25043716026109810398909451 37565574039164715598364177)
              ·
                refine ⟨28174180529373536698773133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37565574039164715598364177 28174180529373536698773133)
                ·
                  refine ⟨10565317698515076262039925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28174180529373536698773133 10565317698515076262039925)
                  ·
                    refine ⟨990498534235788399566243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10565317698515076262039925 990498534235788399566243)
                    ·
                      rfl

theorem cell23_5786967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_5786967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5786967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5786967 prefixEnd_5786967 := by exact prefixLift 5786967
  have htrace : WordTrace (prefixWord ++ tailWord_5786967) baseStart_5786967 baseEnd_5786967 := by
    simpa [prefixWord, tailWord_5786967, baseEnd_5786967] using wordTrace_append hprefix tailTrace_5786967
  have hstable : (prefixWord ++ tailWord_5786967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5786967).length < 2 ^ (prefixWord ++ tailWord_5786967).sum := by decide
  have hdescent : baseEnd_5786967 < baseStart_5786967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5786967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787004 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_5787004 : Nat := 118140960795 + 5787004 * 2 ^ 59
def prefixEnd_5787004 : Nat := 4983230072969 + 3 ^ 40 * 5787004 * 2
def baseEnd_5787004 : Nat := 2971514601491581553936059

theorem tailTrace_5787004 : CollatzResearch.WordTrace tailWord_5787004 prefixEnd_5787004 2971514601491581553936059 := by
  unfold tailWord_5787004
  simp only [CollatzResearch.WordTrace]
  refine ⟨105534687963340162221208033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140712917284453549628277377 105534687963340162221208033)
  ·
    refine ⟨79151015972505121665906025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105534687963340162221208033 79151015972505121665906025)
    ·
      refine ⟨59363261979378841249429519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79151015972505121665906025 59363261979378841249429519)
      ·
        refine ⟨89044892969068261874144279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59363261979378841249429519 89044892969068261874144279)
        ·
          refine ⟨133567339453602392811216419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89044892969068261874144279 133567339453602392811216419)
          ·
            refine ⟨200351009180403589216824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133567339453602392811216419 200351009180403589216824629)
            ·
              refine ⟨18782907110662836489077309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200351009180403589216824629 18782907110662836489077309)
              ·
                refine ⟨7043590166498563683403991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18782907110662836489077309 7043590166498563683403991)
                ·
                  refine ⟨10565385249747845525105987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043590166498563683403991 10565385249747845525105987)
                  ·
                    refine ⟨15848077874621768287658981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10565385249747845525105987 15848077874621768287658981)
                    ·
                      refine ⟨2971514601491581553936059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15848077874621768287658981 2971514601491581553936059)
                      ·
                        rfl

theorem cell23_5787004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_5787004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787004 prefixEnd_5787004 := by exact prefixLift 5787004
  have htrace : WordTrace (prefixWord ++ tailWord_5787004) baseStart_5787004 baseEnd_5787004 := by
    simpa [prefixWord, tailWord_5787004, baseEnd_5787004] using wordTrace_append hprefix tailTrace_5787004
  have hstable : (prefixWord ++ tailWord_5787004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787004).length < 2 ^ (prefixWord ++ tailWord_5787004).sum := by decide
  have hdescent : baseEnd_5787004 < baseStart_5787004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787087 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 2, 6]
def baseStart_5787087 : Nat := 118140960795 + 5787087 * 2 ^ 59
def prefixEnd_5787087 : Nat := 4983230072969 + 3 ^ 40 * 5787087 * 2
def baseEnd_5787087 : Nat := 990519073461968243066059

theorem tailTrace_5787087 : CollatzResearch.WordTrace tailWord_5787087 prefixEnd_5787087 990519073461968243066059 := by
  unfold tailWord_5787087
  simp only [CollatzResearch.WordTrace]
  refine ⟨211072403185379629617687515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140714935456919753078458343 211072403185379629617687515)
  ·
    refine ⟨316608604778069444426531273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211072403185379629617687515 316608604778069444426531273)
    ·
      refine ⟨237456453583552083319898455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316608604778069444426531273 237456453583552083319898455)
      ·
        refine ⟨356184680375328124979847683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237456453583552083319898455 356184680375328124979847683)
        ·
          refine ⟨534277020562992187469771525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356184680375328124979847683 534277020562992187469771525)
          ·
            refine ⟨100176941355561035150582161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 534277020562992187469771525 100176941355561035150582161)
            ·
              refine ⟨75132706016670776362936621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100176941355561035150582161 75132706016670776362936621)
              ·
                refine ⟨28174764756251541136101233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75132706016670776362936621 28174764756251541136101233)
                ·
                  refine ⟨21131073567188655852075925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28174764756251541136101233 21131073567188655852075925)
                  ·
                    refine ⟨990519073461968243066059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21131073567188655852075925 990519073461968243066059)
                    ·
                      rfl

theorem cell23_5787087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_5787087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787087 prefixEnd_5787087 := by exact prefixLift 5787087
  have htrace : WordTrace (prefixWord ++ tailWord_5787087) baseStart_5787087 baseEnd_5787087 := by
    simpa [prefixWord, tailWord_5787087, baseEnd_5787087] using wordTrace_append hprefix tailTrace_5787087
  have hstable : (prefixWord ++ tailWord_5787087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787087).length < 2 ^ (prefixWord ++ tailWord_5787087).sum := by decide
  have hdescent : baseEnd_5787087 < baseStart_5787087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787098 : List Nat := [3, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_5787098 : Nat := 118140960795 + 5787098 * 2 ^ 59
def prefixEnd_5787098 : Nat := 4983230072969 + 3 ^ 40 * 5787098 * 2
def baseEnd_5787098 : Nat := 2971562868673104186160627

theorem tailTrace_5787098 : CollatzResearch.WordTrace tailWord_5787098 prefixEnd_5787098 2971562868673104186160627 := by
  unfold tailWord_5787098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52768201097084944624084487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140715202925559852330891965 52768201097084944624084487)
  ·
    refine ⟨79152301645627416936126731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52768201097084944624084487 79152301645627416936126731)
    ·
      refine ⟨118728452468441125404190097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79152301645627416936126731 118728452468441125404190097)
      ·
        refine ⟨89046339351330844053142573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118728452468441125404190097 89046339351330844053142573)
        ·
          refine ⟨33392377256749066519928465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89046339351330844053142573 33392377256749066519928465)
          ·
            refine ⟨25044282942561799889946349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33392377256749066519928465 25044282942561799889946349)
            ·
              refine ⟨9391606103460674958729881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25044282942561799889946349 9391606103460674958729881)
              ·
                refine ⟨7043704577595506219047411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9391606103460674958729881 7043704577595506219047411)
                ·
                  refine ⟨10565556866393259328571117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043704577595506219047411 10565556866393259328571117)
                  ·
                    refine ⟨3962083824897472248214169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10565556866393259328571117 3962083824897472248214169)
                    ·
                      refine ⟨2971562868673104186160627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962083824897472248214169 2971562868673104186160627)
                      ·
                        rfl

theorem cell23_5787098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_5787098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787098 prefixEnd_5787098 := by exact prefixLift 5787098
  have htrace : WordTrace (prefixWord ++ tailWord_5787098) baseStart_5787098 baseEnd_5787098 := by
    simpa [prefixWord, tailWord_5787098, baseEnd_5787098] using wordTrace_append hprefix tailTrace_5787098
  have hstable : (prefixWord ++ tailWord_5787098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787098).length < 2 ^ (prefixWord ++ tailWord_5787098).sum := by decide
  have hdescent : baseEnd_5787098 < baseStart_5787098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787111 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5787111 : Nat := 118140960795 + 5787111 * 2 ^ 59
def prefixEnd_5787111 : Nat := 4983230072969 + 3 ^ 40 * 5787111 * 2
def baseEnd_5787111 : Nat := 2971569543921612635298067

theorem tailTrace_5787111 : CollatzResearch.WordTrace tailWord_5787111 prefixEnd_5787111 2971569543921612635298067 := by
  unfold tailWord_5787111
  simp only [CollatzResearch.WordTrace]
  refine ⟨211073278537292681716561187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140715519024861787811040791 211073278537292681716561187)
  ·
    refine ⟨316609917805939022574841781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211073278537292681716561187 316609917805939022574841781)
    ·
      refine ⟨29682179794306783366391417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316609917805939022574841781 29682179794306783366391417)
      ·
        refine ⟨22261634845730087524793563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29682179794306783366391417 22261634845730087524793563)
        ·
          refine ⟨33392452268595131287190345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22261634845730087524793563 33392452268595131287190345)
          ·
            refine ⟨25044339201446348465392759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33392452268595131287190345 25044339201446348465392759)
            ·
              refine ⟨37566508802169522698089139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25044339201446348465392759 37566508802169522698089139)
              ·
                refine ⟨56349763203254284047133709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37566508802169522698089139 56349763203254284047133709)
                ·
                  refine ⟨21131161201220356517675141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56349763203254284047133709 21131161201220356517675141)
                  ·
                    refine ⟨3962092725228816847064089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21131161201220356517675141 3962092725228816847064089)
                    ·
                      refine ⟨2971569543921612635298067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962092725228816847064089 2971569543921612635298067)
                      ·
                        rfl

theorem cell23_5787111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5787111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787111 prefixEnd_5787111 := by exact prefixLift 5787111
  have htrace : WordTrace (prefixWord ++ tailWord_5787111) baseStart_5787111 baseEnd_5787111 := by
    simpa [prefixWord, tailWord_5787111, baseEnd_5787111] using wordTrace_append hprefix tailTrace_5787111
  have hstable : (prefixWord ++ tailWord_5787111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787111).length < 2 ^ (prefixWord ++ tailWord_5787111).sum := by decide
  have hdescent : baseEnd_5787111 < baseStart_5787111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787128 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_5787128 : Nat := 118140960795 + 5787128 * 2 ^ 59
def prefixEnd_5787128 : Nat := 4983230072969 + 3 ^ 40 * 5787128 * 2
def baseEnd_5787128 : Nat := 2971578273092739068785489

theorem tailTrace_5787128 : CollatzResearch.WordTrace tailWord_5787128 prefixEnd_5787128 2971578273092739068785489 := by
  unfold tailWord_5787128
  simp only [CollatzResearch.WordTrace]
  refine ⟨105536949289115546809965019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140715932385487395746620025 105536949289115546809965019)
  ·
    refine ⟨158305423933673320214947529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105536949289115546809965019 158305423933673320214947529)
    ·
      refine ⟨118729067950254990161210647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158305423933673320214947529 118729067950254990161210647)
      ·
        refine ⟨178093601925382485241815971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118729067950254990161210647 178093601925382485241815971)
        ·
          refine ⟨267140402888073727862723957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178093601925382485241815971 267140402888073727862723957)
          ·
            refine ⟨25044412770756911987130371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267140402888073727862723957 25044412770756911987130371)
            ·
              refine ⟨37566619156135367980695557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25044412770756911987130371 37566619156135367980695557)
              ·
                refine ⟨7043741091775381496380417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37566619156135367980695557 7043741091775381496380417)
                ·
                  refine ⟨5282805818831536122285313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043741091775381496380417 5282805818831536122285313)
                  ·
                    refine ⟨3962104364123652091713985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282805818831536122285313 3962104364123652091713985)
                    ·
                      refine ⟨2971578273092739068785489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962104364123652091713985 2971578273092739068785489)
                      ·
                        rfl

theorem cell23_5787128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_5787128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787128 prefixEnd_5787128 := by exact prefixLift 5787128
  have htrace : WordTrace (prefixWord ++ tailWord_5787128) baseStart_5787128 baseEnd_5787128 := by
    simpa [prefixWord, tailWord_5787128, baseEnd_5787128] using wordTrace_append hprefix tailTrace_5787128
  have hstable : (prefixWord ++ tailWord_5787128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787128).length < 2 ^ (prefixWord ++ tailWord_5787128).sum := by decide
  have hdescent : baseEnd_5787128 < baseStart_5787128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787144 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_5787144 : Nat := 118140960795 + 5787144 * 2 ^ 59
def prefixEnd_5787144 : Nat := 4983230072969 + 3 ^ 40 * 5787144 * 2
def baseEnd_5787144 : Nat := 2971586488783211006185415

theorem tailTrace_5787144 : CollatzResearch.WordTrace tailWord_5787144 prefixEnd_5787144 2971586488783211006185415 := by
  unfold tailWord_5787144
  simp only [CollatzResearch.WordTrace]
  refine ⟨105537241073086564176256243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140716321430782085568341657 105537241073086564176256243)
  ·
    refine ⟨158305861609629846264384365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105537241073086564176256243 158305861609629846264384365)
    ·
      refine ⟨59364698103611192349144137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158305861609629846264384365 59364698103611192349144137)
      ·
        refine ⟨44523523577708394261858103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59364698103611192349144137 44523523577708394261858103)
        ·
          refine ⟨66785285366562591392787155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44523523577708394261858103 66785285366562591392787155)
          ·
            refine ⟨100177928049843887089180733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66785285366562591392787155 100177928049843887089180733)
            ·
              refine ⟨37566723018691457658442775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100177928049843887089180733 37566723018691457658442775)
              ·
                refine ⟨56350084528037186487664163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37566723018691457658442775 56350084528037186487664163)
                ·
                  refine ⟨84525126792055779731496245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56350084528037186487664163 84525126792055779731496245)
                  ·
                    refine ⟨7924230636755229349827773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84525126792055779731496245 7924230636755229349827773)
                    ·
                      refine ⟨2971586488783211006185415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924230636755229349827773 2971586488783211006185415)
                      ·
                        rfl

theorem cell23_5787144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_5787144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787144 prefixEnd_5787144 := by exact prefixLift 5787144
  have htrace : WordTrace (prefixWord ++ tailWord_5787144) baseStart_5787144 baseEnd_5787144 := by
    simpa [prefixWord, tailWord_5787144, baseEnd_5787144] using wordTrace_append hprefix tailTrace_5787144
  have hstable : (prefixWord ++ tailWord_5787144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787144).length < 2 ^ (prefixWord ++ tailWord_5787144).sum := by decide
  have hdescent : baseEnd_5787144 < baseStart_5787144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787164 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_5787164 : Nat := 118140960795 + 5787164 * 2 ^ 59
def prefixEnd_5787164 : Nat := 4983230072969 + 3 ^ 40 * 5787164 * 2
def baseEnd_5787164 : Nat := 990532252798766975978441

theorem tailTrace_5787164 : CollatzResearch.WordTrace tailWord_5787164 prefixEnd_5787164 990532252798766975978441 := by
  unfold tailWord_5787164
  simp only [CollatzResearch.WordTrace]
  refine ⟨105537605803050335884120273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140716807737400447845493697 105537605803050335884120273)
  ·
    refine ⟨79153204352287751913090205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105537605803050335884120273 79153204352287751913090205)
    ·
      refine ⟨29682451632107906967408827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79153204352287751913090205 29682451632107906967408827)
      ·
        refine ⟨44523677448161860451113241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29682451632107906967408827 44523677448161860451113241)
        ·
          refine ⟨33392758086121395338334931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44523677448161860451113241 33392758086121395338334931)
          ·
            refine ⟨50089137129182093007502397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33392758086121395338334931 50089137129182093007502397)
            ·
              refine ⟨18783426423443284877813399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50089137129182093007502397 18783426423443284877813399)
              ·
                refine ⟨28175139635164927316720099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18783426423443284877813399 28175139635164927316720099)
                ·
                  refine ⟨42262709452747390975080149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28175139635164927316720099 42262709452747390975080149)
                  ·
                    refine ⟨990532252798766975978441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42262709452747390975080149 990532252798766975978441)
                    ·
                      rfl

theorem cell23_5787164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_5787164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787164 prefixEnd_5787164 := by exact prefixLift 5787164
  have htrace : WordTrace (prefixWord ++ tailWord_5787164) baseStart_5787164 baseEnd_5787164 := by
    simpa [prefixWord, tailWord_5787164, baseEnd_5787164] using wordTrace_append hprefix tailTrace_5787164
  have hstable : (prefixWord ++ tailWord_5787164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787164).length < 2 ^ (prefixWord ++ tailWord_5787164).sum := by decide
  have hdescent : baseEnd_5787164 < baseStart_5787164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787168 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 5]
def baseStart_5787168 : Nat := 118140960795 + 5787168 * 2 ^ 59
def prefixEnd_5787168 : Nat := 4983230072969 + 3 ^ 40 * 5787168 * 2
def baseEnd_5787168 : Nat := 330177645813213212476145

theorem tailTrace_5787168 : CollatzResearch.WordTrace tailWord_5787168 prefixEnd_5787168 330177645813213212476145 := by
  unfold tailWord_5787168
  simp only [CollatzResearch.WordTrace]
  refine ⟨105537678749043090225693079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140716904998724120300924105 105537678749043090225693079)
  ·
    refine ⟨158306518123564635338539619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105537678749043090225693079 158306518123564635338539619)
    ·
      refine ⟨237459777185346953007809429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158306518123564635338539619 237459777185346953007809429)
      ·
        refine ⟨11130927055563138422241067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 237459777185346953007809429 11130927055563138422241067)
        ·
          refine ⟨16696390583344707633361601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11130927055563138422241067 16696390583344707633361601)
          ·
            refine ⟨12522292937508530725021201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16696390583344707633361601 12522292937508530725021201)
            ·
              refine ⟨9391719703131398043765901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12522292937508530725021201 9391719703131398043765901)
              ·
                refine ⟨3521894888674274266412213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9391719703131398043765901 3521894888674274266412213)
                ·
                  refine ⟨330177645813213212476145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521894888674274266412213 330177645813213212476145)
                  ·
                    rfl

theorem cell23_5787168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 5].length) (baseStart_5787168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787168 prefixEnd_5787168 := by exact prefixLift 5787168
  have htrace : WordTrace (prefixWord ++ tailWord_5787168) baseStart_5787168 baseEnd_5787168 := by
    simpa [prefixWord, tailWord_5787168, baseEnd_5787168] using wordTrace_append hprefix tailTrace_5787168
  have hstable : (prefixWord ++ tailWord_5787168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787168).length < 2 ^ (prefixWord ++ tailWord_5787168).sum := by decide
  have hdescent : baseEnd_5787168 < baseStart_5787168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787184 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_5787184 : Nat := 118140960795 + 5787184 * 2 ^ 59
def prefixEnd_5787184 : Nat := 4983230072969 + 3 ^ 40 * 5787184 * 2
def baseEnd_5787184 : Nat := 2971607028009390849685231

theorem tailTrace_5787184 : CollatzResearch.WordTrace tailWord_5787184 prefixEnd_5787184 2971607028009390849685231 := by
  unfold tailWord_5787184
  simp only [CollatzResearch.WordTrace]
  refine ⟨105537970533014107591984303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140717294044018810122645737 105537970533014107591984303)
  ·
    refine ⟨158306955799521161387976455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105537970533014107591984303 158306955799521161387976455)
    ·
      refine ⟨237460433699281742081964683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158306955799521161387976455 237460433699281742081964683)
      ·
        refine ⟨356190650548922613122947025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237460433699281742081964683 356190650548922613122947025)
        ·
          refine ⟨267142987911691959842210269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356190650548922613122947025 267142987911691959842210269)
          ·
            refine ⟨100178620466884484940828851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267142987911691959842210269 100178620466884484940828851)
            ·
              refine ⟨150267930700326727411243277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100178620466884484940828851 150267930700326727411243277)
              ·
                refine ⟨56350474012622522779216229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150267930700326727411243277 56350474012622522779216229)
                ·
                  refine ⟨10565713877366723021103043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56350474012622522779216229 10565713877366723021103043)
                  ·
                    refine ⟨15848570816050084531654565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10565713877366723021103043 15848570816050084531654565)
                    ·
                      refine ⟨2971607028009390849685231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15848570816050084531654565 2971607028009390849685231)
                      ·
                        rfl

theorem cell23_5787184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_5787184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787184 prefixEnd_5787184 := by exact prefixLift 5787184
  have htrace : WordTrace (prefixWord ++ tailWord_5787184) baseStart_5787184 baseEnd_5787184 := by
    simpa [prefixWord, tailWord_5787184, baseEnd_5787184] using wordTrace_append hprefix tailTrace_5787184
  have hstable : (prefixWord ++ tailWord_5787184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787184).length < 2 ^ (prefixWord ++ tailWord_5787184).sum := by decide
  have hdescent : baseEnd_5787184 < baseStart_5787184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787214 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_5787214 : Nat := 118140960795 + 5787214 * 2 ^ 59
def prefixEnd_5787214 : Nat := 4983230072969 + 3 ^ 40 * 5787214 * 2
def baseEnd_5787214 : Nat := 2971622432429025732310093

theorem tailTrace_5787214 : CollatzResearch.WordTrace tailWord_5787214 prefixEnd_5787214 2971622432429025732310093 := by
  unfold tailWord_5787214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26384629406989941288445087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140718023503946353538373797 26384629406989941288445087)
  ·
    refine ⟨39576944110484911932667631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26384629406989941288445087 39576944110484911932667631)
    ·
      refine ⟨59365416165727367899001447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39576944110484911932667631 59365416165727367899001447)
      ·
        refine ⟨89048124248591051848502171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59365416165727367899001447 89048124248591051848502171)
        ·
          refine ⟨133572186372886577772753257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89048124248591051848502171 133572186372886577772753257)
          ·
            refine ⟨100179139779664933329564943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133572186372886577772753257 100179139779664933329564943)
            ·
              refine ⟨150268709669497399994347415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100179139779664933329564943 150268709669497399994347415)
              ·
                refine ⟨225403064504246099991521123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150268709669497399994347415 225403064504246099991521123)
                ·
                  refine ⟨338104596756369149987281685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225403064504246099991521123 338104596756369149987281685)
                  ·
                    refine ⟨15848652972954803905653829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 338104596756369149987281685 15848652972954803905653829)
                    ·
                      refine ⟨2971622432429025732310093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15848652972954803905653829 2971622432429025732310093)
                      ·
                        rfl

theorem cell23_5787214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_5787214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787214 prefixEnd_5787214 := by exact prefixLift 5787214
  have htrace : WordTrace (prefixWord ++ tailWord_5787214) baseStart_5787214 baseEnd_5787214 := by
    simpa [prefixWord, tailWord_5787214, baseEnd_5787214] using wordTrace_append hprefix tailTrace_5787214
  have hstable : (prefixWord ++ tailWord_5787214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787214).length < 2 ^ (prefixWord ++ tailWord_5787214).sum := by decide
  have hdescent : baseEnd_5787214 < baseStart_5787214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787221 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5787221 : Nat := 118140960795 + 5787221 * 2 ^ 59
def prefixEnd_5787221 : Nat := 4983230072969 + 3 ^ 40 * 5787221 * 2
def baseEnd_5787221 : Nat := 2971626026793607204922561

theorem tailTrace_5787221 : CollatzResearch.WordTrace tailWord_5787221 prefixEnd_5787221 2971626026793607204922561 := by
  unfold tailWord_5787221
  simp only [CollatzResearch.WordTrace]
  refine ⟨211077290566894170503065517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140718193711262780335377011 211077290566894170503065517)
  ·
    refine ⟨79153983962585313938649569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211077290566894170503065517 79153983962585313938649569)
    ·
      refine ⟨59365487971938985453987177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79153983962585313938649569 59365487971938985453987177)
      ·
        refine ⟨44524115978954239090490383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59365487971938985453987177 44524115978954239090490383)
        ·
          refine ⟨66786173968431358635735575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44524115978954239090490383 66786173968431358635735575)
          ·
            refine ⟨100179260952647037953603363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66786173968431358635735575 100179260952647037953603363)
            ·
              refine ⟨150268891428970556930405045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100179260952647037953603363 150268891428970556930405045)
              ·
                refine ⟨14087708571465989712225473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150268891428970556930405045 14087708571465989712225473)
                ·
                  refine ⟨10565781428599492284169105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14087708571465989712225473 10565781428599492284169105)
                  ·
                    refine ⟨7924336071449619213126829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10565781428599492284169105 7924336071449619213126829)
                    ·
                      refine ⟨2971626026793607204922561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924336071449619213126829 2971626026793607204922561)
                      ·
                        rfl

theorem cell23_5787221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5787221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787221 prefixEnd_5787221 := by exact prefixLift 5787221
  have htrace : WordTrace (prefixWord ++ tailWord_5787221) baseStart_5787221 baseEnd_5787221 := by
    simpa [prefixWord, tailWord_5787221, baseEnd_5787221] using wordTrace_append hprefix tailTrace_5787221
  have hstable : (prefixWord ++ tailWord_5787221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787221).length < 2 ^ (prefixWord ++ tailWord_5787221).sum := by decide
  have hdescent : baseEnd_5787221 < baseStart_5787221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787245 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_5787245 : Nat := 118140960795 + 5787245 * 2 ^ 59
def prefixEnd_5787245 : Nat := 4983230072969 + 3 ^ 40 * 5787245 * 2
def baseEnd_5787245 : Nat := 990546116776438370340817

theorem tailTrace_5787245 : CollatzResearch.WordTrace tailWord_5787245 prefixEnd_5787245 990546116776438370340817 := by
  unfold tailWord_5787245
  simp only [CollatzResearch.WordTrace]
  refine ⟨211078165918807222601939189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140718777279204815067959459 211078165918807222601939189)
  ·
    refine ⟨19788578054888177118931799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211078165918807222601939189 19788578054888177118931799)
    ·
      refine ⟨29682867082332265678397699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19788578054888177118931799 29682867082332265678397699)
      ·
        refine ⟨44524300623498398517596549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29682867082332265678397699 44524300623498398517596549)
        ·
          refine ⟨8348306366905949722049353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44524300623498398517596549 8348306366905949722049353)
          ·
            refine ⟨6261229775179462291537015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8348306366905949722049353 6261229775179462291537015)
            ·
              refine ⟨9391844662769193437305523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261229775179462291537015 9391844662769193437305523)
              ·
                refine ⟨14087766994153790155958285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391844662769193437305523 14087766994153790155958285)
                ·
                  refine ⟨5282912622807671308484357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14087766994153790155958285 5282912622807671308484357)
                  ·
                    refine ⟨990546116776438370340817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5282912622807671308484357 990546116776438370340817)
                    ·
                      rfl

theorem cell23_5787245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_5787245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787245 prefixEnd_5787245 := by exact prefixLift 5787245
  have htrace : WordTrace (prefixWord ++ tailWord_5787245) baseStart_5787245 baseEnd_5787245 := by
    simpa [prefixWord, tailWord_5787245, baseEnd_5787245] using wordTrace_append hprefix tailTrace_5787245
  have hstable : (prefixWord ++ tailWord_5787245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787245).length < 2 ^ (prefixWord ++ tailWord_5787245).sum := by decide
  have hdescent : baseEnd_5787245 < baseStart_5787245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787271 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 3, 5]
def baseStart_5787271 : Nat := 118140960795 + 5787271 * 2 ^ 59
def prefixEnd_5787271 : Nat := 4983230072969 + 3 ^ 40 * 5787271 * 2
def baseEnd_5787271 : Nat := 990550566942110669765777

theorem tailTrace_5787271 : CollatzResearch.WordTrace tailWord_5787271 prefixEnd_5787271 990550566942110669765777 := by
  unfold tailWord_5787271
  simp only [CollatzResearch.WordTrace]
  refine ⟨211079114216713029042385667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140719409477808686028257111 211079114216713029042385667)
  ·
    refine ⟨316618671325069543563578501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211079114216713029042385667 316618671325069543563578501)
    ·
      refine ⟨59366000873450539418170969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316618671325069543563578501 59366000873450539418170969)
      ·
        refine ⟨44524500655087904563628227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59366000873450539418170969 44524500655087904563628227)
        ·
          refine ⟨66786750982631856845442341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44524500655087904563628227 66786750982631856845442341)
          ·
            refine ⟨12522515809243473158520439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66786750982631856845442341 12522515809243473158520439)
            ·
              refine ⟨18783773713865209737780659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12522515809243473158520439 18783773713865209737780659)
              ·
                refine ⟨28175660570797814606670989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18783773713865209737780659 28175660570797814606670989)
                ·
                  refine ⟨10565872714049180477501621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28175660570797814606670989 10565872714049180477501621)
                  ·
                    refine ⟨990550566942110669765777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10565872714049180477501621 990550566942110669765777)
                    ·
                      rfl

theorem cell23_5787271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_5787271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787271 prefixEnd_5787271 := by exact prefixLift 5787271
  have htrace : WordTrace (prefixWord ++ tailWord_5787271) baseStart_5787271 baseEnd_5787271 := by
    simpa [prefixWord, tailWord_5787271, baseEnd_5787271] using wordTrace_append hprefix tailTrace_5787271
  have hstable : (prefixWord ++ tailWord_5787271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787271).length < 2 ^ (prefixWord ++ tailWord_5787271).sum := by decide
  have hdescent : baseEnd_5787271 < baseStart_5787271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787301 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_5787301 : Nat := 118140960795 + 5787301 * 2 ^ 59
def prefixEnd_5787301 : Nat := 4983230072969 + 3 ^ 40 * 5787301 * 2
def baseEnd_5787301 : Nat := 990555701748655630640731

theorem tailTrace_5787301 : CollatzResearch.WordTrace tailWord_5787301 prefixEnd_5787301 990555701748655630640731 := by
  unfold tailWord_5787301
  simp only [CollatzResearch.WordTrace]
  refine ⟨211080208406604344165977757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140720138937736229443985171 211080208406604344165977757)
  ·
    refine ⟨79155078152476629062241659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211080208406604344165977757 79155078152476629062241659)
    ·
      refine ⟨118732617228714943593362489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79155078152476629062241659 118732617228714943593362489)
      ·
        refine ⟨89049462921536207695021867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118732617228714943593362489 89049462921536207695021867)
        ·
          refine ⟨133574194382304311542532801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89049462921536207695021867 133574194382304311542532801)
          ·
            refine ⟨100180645786728233656899601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133574194382304311542532801 100180645786728233656899601)
            ·
              refine ⟨75135484340046175242674701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100180645786728233656899601 75135484340046175242674701)
              ·
                refine ⟨28175806627517315716003013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75135484340046175242674701 28175806627517315716003013)
                ·
                  refine ⟨5282963742659496696750565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28175806627517315716003013 5282963742659496696750565)
                  ·
                    refine ⟨990555701748655630640731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5282963742659496696750565 990555701748655630640731)
                    ·
                      rfl

theorem cell23_5787301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_5787301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787301 prefixEnd_5787301 := by exact prefixLift 5787301
  have htrace : WordTrace (prefixWord ++ tailWord_5787301) baseStart_5787301 baseEnd_5787301 := by
    simpa [prefixWord, tailWord_5787301, baseEnd_5787301] using wordTrace_append hprefix tailTrace_5787301
  have hstable : (prefixWord ++ tailWord_5787301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787301).length < 2 ^ (prefixWord ++ tailWord_5787301).sum := by decide
  have hdescent : baseEnd_5787301 < baseStart_5787301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787308 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_5787308 : Nat := 118140960795 + 5787308 * 2 ^ 59
def prefixEnd_5787308 : Nat := 4983230072969 + 3 ^ 40 * 5787308 * 2
def baseEnd_5787308 : Nat := 2971670699610548364534661

theorem tailTrace_5787308 : CollatzResearch.WordTrace tailWord_5787308 prefixEnd_5787308 2971670699610548364534661 := by
  unfold tailWord_5787308
  simp only [CollatzResearch.WordTrace]
  refine ⟨105540231858789492180741289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140720309145052656240988385 105540231858789492180741289)
  ·
    refine ⟨79155173894092119135555967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105540231858789492180741289 79155173894092119135555967)
    ·
      refine ⟨118732760841138178703333951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79155173894092119135555967 118732760841138178703333951)
      ·
        refine ⟨178099141261707268055000927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118732760841138178703333951 178099141261707268055000927)
        ·
          refine ⟨267148711892560902082501391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178099141261707268055000927 267148711892560902082501391)
          ·
            refine ⟨400723067838841353123752087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267148711892560902082501391 400723067838841353123752087)
            ·
              refine ⟨601084601758262029685628131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400723067838841353123752087 601084601758262029685628131)
              ·
                refine ⟨901626902637393044528442197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601084601758262029685628131 901626902637393044528442197)
                ·
                  refine ⟨5282970132640974870283841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 901626902637393044528442197 5282970132640974870283841)
                  ·
                    refine ⟨3962227599480731152712881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282970132640974870283841 3962227599480731152712881)
                    ·
                      refine ⟨2971670699610548364534661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962227599480731152712881 2971670699610548364534661)
                      ·
                        rfl

theorem cell23_5787308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_5787308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787308 prefixEnd_5787308 := by exact prefixLift 5787308
  have htrace : WordTrace (prefixWord ++ tailWord_5787308) baseStart_5787308 baseEnd_5787308 := by
    simpa [prefixWord, tailWord_5787308, baseEnd_5787308] using wordTrace_append hprefix tailTrace_5787308
  have hstable : (prefixWord ++ tailWord_5787308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787308).length < 2 ^ (prefixWord ++ tailWord_5787308).sum := by decide
  have hdescent : baseEnd_5787308 < baseStart_5787308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787311 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_5787311 : Nat := 118140960795 + 5787311 * 2 ^ 59
def prefixEnd_5787311 : Nat := 4983230072969 + 3 ^ 40 * 5787311 * 2
def baseEnd_5787311 : Nat := 2971672240052511852797147

theorem tailTrace_5787311 : CollatzResearch.WordTrace tailWord_5787311 prefixEnd_5787311 2971672240052511852797147 := by
  unfold tailWord_5787311
  simp only [CollatzResearch.WordTrace]
  refine ⟨211080573136568115873841787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140720382091045410582561191 211080573136568115873841787)
  ·
    refine ⟨316620859704852173810762681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211080573136568115873841787 316620859704852173810762681)
    ·
      refine ⟨237465644778639130358072011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316620859704852173810762681 237465644778639130358072011)
      ·
        refine ⟨356198467167958695537108017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237465644778639130358072011 356198467167958695537108017)
        ·
          refine ⟨267148850375969021652831013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356198467167958695537108017 267148850375969021652831013)
          ·
            refine ⟨50090409445494191559905815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267148850375969021652831013 50090409445494191559905815)
            ·
              refine ⟨75135614168241287339858723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50090409445494191559905815 75135614168241287339858723)
              ·
                refine ⟨112703421252361931009788085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75135614168241287339858723 112703421252361931009788085)
                ·
                  refine ⟨10565945742408931032167633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112703421252361931009788085 10565945742408931032167633)
                  ·
                    refine ⟨7924459306806698274125725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10565945742408931032167633 7924459306806698274125725)
                    ·
                      refine ⟨2971672240052511852797147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924459306806698274125725 2971672240052511852797147)
                      ·
                        rfl

theorem cell23_5787311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_5787311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787311 prefixEnd_5787311 := by exact prefixLift 5787311
  have htrace : WordTrace (prefixWord ++ tailWord_5787311) baseStart_5787311 baseEnd_5787311 := by
    simpa [prefixWord, tailWord_5787311, baseEnd_5787311] using wordTrace_append hprefix tailTrace_5787311
  have hstable : (prefixWord ++ tailWord_5787311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787311).length < 2 ^ (prefixWord ++ tailWord_5787311).sum := by decide
  have hdescent : baseEnd_5787311 < baseStart_5787311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787321 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5787321 : Nat := 118140960795 + 5787321 * 2 ^ 59
def prefixEnd_5787321 : Nat := 4983230072969 + 3 ^ 40 * 5787321 * 2
def baseEnd_5787321 : Nat := 2971677374859056813672101

theorem tailTrace_5787321 : CollatzResearch.WordTrace tailWord_5787321 prefixEnd_5787321 2971677374859056813672101 := by
  unfold tailWord_5787321
  simp only [CollatzResearch.WordTrace]
  refine ⟨211080937866531887581705817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140720625244354591721137211 211080937866531887581705817)
  ·
    refine ⟨158310703399898915686279363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211080937866531887581705817 158310703399898915686279363)
    ·
      refine ⟨237466055099848373529419045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158310703399898915686279363 237466055099848373529419045)
      ·
        refine ⟨44524885331221570036766071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237466055099848373529419045 44524885331221570036766071)
        ·
          refine ⟨66787327996832355055149107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44524885331221570036766071 66787327996832355055149107)
          ·
            refine ⟨100180991995248532582723661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66787327996832355055149107 100180991995248532582723661)
            ·
              refine ⟨37567871998218199718521373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100180991995248532582723661 37567871998218199718521373)
              ·
                refine ⟨14087951999331824894445515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37567871998218199718521373 14087951999331824894445515)
                ·
                  refine ⟨21131927998997737341668273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14087951999331824894445515 21131927998997737341668273)
                  ·
                    refine ⟨15848945999248303006251205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21131927998997737341668273 15848945999248303006251205)
                    ·
                      refine ⟨2971677374859056813672101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15848945999248303006251205 2971677374859056813672101)
                      ·
                        rfl

theorem cell23_5787321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5787321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787321 prefixEnd_5787321 := by exact prefixLift 5787321
  have htrace : WordTrace (prefixWord ++ tailWord_5787321) baseStart_5787321 baseEnd_5787321 := by
    simpa [prefixWord, tailWord_5787321, baseEnd_5787321] using wordTrace_append hprefix tailTrace_5787321
  have hstable : (prefixWord ++ tailWord_5787321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787321).length < 2 ^ (prefixWord ++ tailWord_5787321).sum := by decide
  have hdescent : baseEnd_5787321 < baseStart_5787321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787325 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5787325 : Nat := 118140960795 + 5787325 * 2 ^ 59
def prefixEnd_5787325 : Nat := 4983230072969 + 3 ^ 40 * 5787325 * 2
def baseEnd_5787325 : Nat := 2971679428781674798022083

theorem tailTrace_5787325 : CollatzResearch.WordTrace tailWord_5787325 prefixEnd_5787325 2971679428781674798022083 := by
  unfold tailWord_5787325
  simp only [CollatzResearch.WordTrace]
  refine ⟨211081083758517396264851429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140720722505678264176567619 211081083758517396264851429)
  ·
    refine ⟨39577703204722011799659643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211081083758517396264851429 39577703204722011799659643)
    ·
      refine ⟨59366554807083017699489465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39577703204722011799659643 59366554807083017699489465)
      ·
        refine ⟨44524916105312263274617099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59366554807083017699489465 44524916105312263274617099)
        ·
          refine ⟨66787374157968394911925649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44524916105312263274617099 66787374157968394911925649)
          ·
            refine ⟨50090530618476296183944237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66787374157968394911925649 50090530618476296183944237)
            ·
              refine ⟨18783948981928611068979089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50090530618476296183944237 18783948981928611068979089)
              ·
                refine ⟨14087961736446458301734317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18783948981928611068979089 14087961736446458301734317)
                ·
                  refine ⟨5282985651167421863150369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14087961736446458301734317 5282985651167421863150369)
                  ·
                    refine ⟨3962239238375566397362777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282985651167421863150369 3962239238375566397362777)
                    ·
                      refine ⟨2971679428781674798022083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962239238375566397362777 2971679428781674798022083)
                      ·
                        rfl

theorem cell23_5787325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5787325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787325 prefixEnd_5787325 := by exact prefixLift 5787325
  have htrace : WordTrace (prefixWord ++ tailWord_5787325) baseStart_5787325 baseEnd_5787325 := by
    simpa [prefixWord, tailWord_5787325, baseEnd_5787325] using wordTrace_append hprefix tailTrace_5787325
  have hstable : (prefixWord ++ tailWord_5787325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787325).length < 2 ^ (prefixWord ++ tailWord_5787325).sum := by decide
  have hdescent : baseEnd_5787325 < baseStart_5787325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787328 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_5787328 : Nat := 118140960795 + 5787328 * 2 ^ 59
def prefixEnd_5787328 : Nat := 4983230072969 + 3 ^ 40 * 5787328 * 2
def baseEnd_5787328 : Nat := 2971680969223638286284569

theorem tailTrace_5787328 : CollatzResearch.WordTrace tailWord_5787328 prefixEnd_5787328 2971680969223638286284569 := by
  unfold tailWord_5787328
  simp only [CollatzResearch.WordTrace]
  refine ⟨105540596588753263888605319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140720795451671018518140425 105540596588753263888605319)
  ·
    refine ⟨158310894883129895832907979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105540596588753263888605319 158310894883129895832907979)
    ·
      refine ⟨237466342324694843749361969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158310894883129895832907979 237466342324694843749361969)
      ·
        refine ⟨178099756743521132812021477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237466342324694843749361969 178099756743521132812021477)
        ·
          refine ⟨33393704389410212402254027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178099756743521132812021477 33393704389410212402254027)
          ·
            refine ⟨50090556584115318603381041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33393704389410212402254027 50090556584115318603381041)
            ·
              refine ⟨37567917438086488952535781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50090556584115318603381041 37567917438086488952535781)
              ·
                refine ⟨7043984519641216678600459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37567917438086488952535781 7043984519641216678600459)
                ·
                  refine ⟨10565976779461825017900689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043984519641216678600459 10565976779461825017900689)
                  ·
                    refine ⟨7924482584596368763425517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10565976779461825017900689 7924482584596368763425517)
                    ·
                      refine ⟨2971680969223638286284569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924482584596368763425517 2971680969223638286284569)
                      ·
                        rfl

theorem cell23_5787328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_5787328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787328 prefixEnd_5787328 := by exact prefixLift 5787328
  have htrace : WordTrace (prefixWord ++ tailWord_5787328) baseStart_5787328 baseEnd_5787328 := by
    simpa [prefixWord, tailWord_5787328, baseEnd_5787328] using wordTrace_append hprefix tailTrace_5787328
  have hstable : (prefixWord ++ tailWord_5787328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787328).length < 2 ^ (prefixWord ++ tailWord_5787328).sum := by decide
  have hdescent : baseEnd_5787328 < baseStart_5787328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787344 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_5787344 : Nat := 118140960795 + 5787344 * 2 ^ 59
def prefixEnd_5787344 : Nat := 4983230072969 + 3 ^ 40 * 5787344 * 2
def baseEnd_5787344 : Nat := 990563061638036741228165

theorem tailTrace_5787344 : CollatzResearch.WordTrace tailWord_5787344 prefixEnd_5787344 990563061638036741228165 := by
  unfold tailWord_5787344
  simp only [CollatzResearch.WordTrace]
  refine ⟨105540888372724281254896543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140721184496965708339862057 105540888372724281254896543)
  ·
    refine ⟨158311332559086421882344815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105540888372724281254896543 158311332559086421882344815)
    ·
      refine ⟨237466998838629632823517223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158311332559086421882344815 237466998838629632823517223)
      ·
        refine ⟨356200498257944449235275835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237466998838629632823517223 356200498257944449235275835)
        ·
          refine ⟨534300747386916673852913753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356200498257944449235275835 534300747386916673852913753)
          ·
            refine ⟨400725560540187505389685315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534300747386916673852913753 400725560540187505389685315)
            ·
              refine ⟨601088340810281258084527973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400725560540187505389685315 601088340810281258084527973)
              ·
                refine ⟨112704063901927735890848995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601088340810281258084527973 112704063901927735890848995)
                ·
                  refine ⟨169056095852891603836273493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112704063901927735890848995 169056095852891603836273493)
                  ·
                    refine ⟨990563061638036741228165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169056095852891603836273493 990563061638036741228165)
                    ·
                      rfl

theorem cell23_5787344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_5787344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787344 prefixEnd_5787344 := by exact prefixLift 5787344
  have htrace : WordTrace (prefixWord ++ tailWord_5787344) baseStart_5787344 baseEnd_5787344 := by
    simpa [prefixWord, tailWord_5787344, baseEnd_5787344] using wordTrace_append hprefix tailTrace_5787344
  have hstable : (prefixWord ++ tailWord_5787344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787344).length < 2 ^ (prefixWord ++ tailWord_5787344).sum := by decide
  have hdescent : baseEnd_5787344 < baseStart_5787344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787345 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_5787345 : Nat := 118140960795 + 5787345 * 2 ^ 59
def prefixEnd_5787345 : Nat := 4983230072969 + 3 ^ 40 * 5787345 * 2
def baseEnd_5787345 : Nat := 2971689698394764719771991

theorem tailTrace_5787345 : CollatzResearch.WordTrace tailWord_5787345 prefixEnd_5787345 2971689698394764719771991 := by
  unfold tailWord_5787345
  simp only [CollatzResearch.WordTrace]
  refine ⟨211081813218444939680579489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140721208812296626453719659 211081813218444939680579489)
  ·
    refine ⟨158311359913833704760434617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211081813218444939680579489 158311359913833704760434617)
    ·
      refine ⟨118733519935375278570325963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158311359913833704760434617 118733519935375278570325963)
      ·
        refine ⟨178100279903062917855488945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118733519935375278570325963 178100279903062917855488945)
        ·
          refine ⟨133575209927297188391616709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178100279903062917855488945 133575209927297188391616709)
          ·
            refine ⟨25045351861368222823428133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133575209927297188391616709 25045351861368222823428133)
            ·
              refine ⟨4696003474006541779392775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25045351861368222823428133 4696003474006541779392775)
              ·
                refine ⟨7044005211009812669089163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696003474006541779392775 7044005211009812669089163)
                ·
                  refine ⟨10566007816514719003633745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044005211009812669089163 10566007816514719003633745)
                  ·
                    refine ⟨7924505862386039252725309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10566007816514719003633745 7924505862386039252725309)
                    ·
                      refine ⟨2971689698394764719771991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924505862386039252725309 2971689698394764719771991)
                      ·
                        rfl

theorem cell23_5787345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_5787345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787345 prefixEnd_5787345 := by exact prefixLift 5787345
  have htrace : WordTrace (prefixWord ++ tailWord_5787345) baseStart_5787345 baseEnd_5787345 := by
    simpa [prefixWord, tailWord_5787345, baseEnd_5787345] using wordTrace_append hprefix tailTrace_5787345
  have hstable : (prefixWord ++ tailWord_5787345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787345).length < 2 ^ (prefixWord ++ tailWord_5787345).sum := by decide
  have hdescent : baseEnd_5787345 < baseStart_5787345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787401 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_5787401 : Nat := 118140960795 + 5787401 * 2 ^ 59
def prefixEnd_5787401 : Nat := 4983230072969 + 3 ^ 40 * 5787401 * 2
def baseEnd_5787401 : Nat := 2971718453311416500671733

theorem tailTrace_5787401 : CollatzResearch.WordTrace tailWord_5787401 prefixEnd_5787401 2971718453311416500671733 := by
  unfold tailWord_5787401
  simp only [CollatzResearch.WordTrace]
  refine ⟨211083855706242061244618057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140722570470828040829745371 211083855706242061244618057)
  ·
    refine ⟨158312891779681545933463543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211083855706242061244618057 158312891779681545933463543)
    ·
      refine ⟨237469337669522318900195315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158312891779681545933463543 237469337669522318900195315)
      ·
        refine ⟨356204006504283478350292973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237469337669522318900195315 356204006504283478350292973)
        ·
          refine ⟨133576502439106304381359865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356204006504283478350292973 133576502439106304381359865)
          ·
            refine ⟨100182376829329728286019899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133576502439106304381359865 100182376829329728286019899)
            ·
              refine ⟨150273565243994592429029849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100182376829329728286019899 150273565243994592429029849)
              ·
                refine ⟨112705173932995944321772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150273565243994592429029849 112705173932995944321772387)
                ·
                  refine ⟨169057760899493916482658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112705173932995944321772387 169057760899493916482658581)
                  ·
                    refine ⟨7924582542163777335124621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169057760899493916482658581 7924582542163777335124621)
                    ·
                      refine ⟨2971718453311416500671733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924582542163777335124621 2971718453311416500671733)
                      ·
                        rfl

theorem cell23_5787401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_5787401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787401 prefixEnd_5787401 := by exact prefixLift 5787401
  have htrace : WordTrace (prefixWord ++ tailWord_5787401) baseStart_5787401 baseEnd_5787401 := by
    simpa [prefixWord, tailWord_5787401, baseEnd_5787401] using wordTrace_append hprefix tailTrace_5787401
  have hstable : (prefixWord ++ tailWord_5787401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787401).length < 2 ^ (prefixWord ++ tailWord_5787401).sum := by decide
  have hdescent : baseEnd_5787401 < baseStart_5787401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787411 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_5787411 : Nat := 118140960795 + 5787411 * 2 ^ 59
def prefixEnd_5787411 : Nat := 4983230072969 + 3 ^ 40 * 5787411 * 2
def baseEnd_5787411 : Nat := 2971723588117961461546687

theorem tailTrace_5787411 : CollatzResearch.WordTrace tailWord_5787411 prefixEnd_5787411 2971723588117961461546687 := by
  unfold tailWord_5787411
  simp only [CollatzResearch.WordTrace]
  refine ⟨211084220436205832952482087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140722813624137221968321391 211084220436205832952482087)
  ·
    refine ⟨316626330654308749428723131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211084220436205832952482087 316626330654308749428723131)
    ·
      refine ⟨474939495981463124143084697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316626330654308749428723131 474939495981463124143084697)
      ·
        refine ⟨356204621986097343107313523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474939495981463124143084697 356204621986097343107313523)
        ·
          refine ⟨534306932979146014660970285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356204621986097343107313523 534306932979146014660970285)
          ·
            refine ⟨200365099867179755497863857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534306932979146014660970285 200365099867179755497863857)
            ·
              refine ⟨150273824900384816623397893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200365099867179755497863857 150273824900384816623397893)
              ·
                refine ⟨28176342168822153116887105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150273824900384816623397893 28176342168822153116887105)
                ·
                  refine ⟨21132256626616614837665329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28176342168822153116887105 21132256626616614837665329)
                  ·
                    refine ⟨15849192469962461128248997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21132256626616614837665329 15849192469962461128248997)
                    ·
                      refine ⟨2971723588117961461546687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15849192469962461128248997 2971723588117961461546687)
                      ·
                        rfl

theorem cell23_5787411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_5787411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787411 prefixEnd_5787411 := by exact prefixLift 5787411
  have htrace : WordTrace (prefixWord ++ tailWord_5787411) baseStart_5787411 baseEnd_5787411 := by
    simpa [prefixWord, tailWord_5787411, baseEnd_5787411] using wordTrace_append hprefix tailTrace_5787411
  have hstable : (prefixWord ++ tailWord_5787411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787411).length < 2 ^ (prefixWord ++ tailWord_5787411).sum := by decide
  have hdescent : baseEnd_5787411 < baseStart_5787411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787461 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_5787461 : Nat := 118140960795 + 5787461 * 2 ^ 59
def prefixEnd_5787461 : Nat := 4983230072969 + 3 ^ 40 * 5787461 * 2
def baseEnd_5787461 : Nat := 2971749262150686265921457

theorem tailTrace_5787461 : CollatzResearch.WordTrace tailWord_5787461 prefixEnd_5787461 2971749262150686265921457 := by
  unfold tailWord_5787461
  simp only [CollatzResearch.WordTrace]
  refine ⟨211086044086024691491802237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140724029390683127661201491 211086044086024691491802237)
  ·
    refine ⟨79157266532259259309425839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211086044086024691491802237 79157266532259259309425839)
    ·
      refine ⟨118735899798388888964138759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79157266532259259309425839 118735899798388888964138759)
      ·
        refine ⟨178103849697583333446208139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118735899798388888964138759 178103849697583333446208139)
        ·
          refine ⟨267155774546375000169312209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178103849697583333446208139 267155774546375000169312209)
          ·
            refine ⟨200366830909781250126984157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267155774546375000169312209 200366830909781250126984157)
            ·
              refine ⟨75137561591167968797619059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200366830909781250126984157 75137561591167968797619059)
              ·
                refine ⟨112706342386751953196428589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75137561591167968797619059 112706342386751953196428589)
                ·
                  refine ⟨42264878395031982448660721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112706342386751953196428589 42264878395031982448660721)
                  ·
                    refine ⟨31698658796273986836495541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42264878395031982448660721 31698658796273986836495541)
                    ·
                      refine ⟨2971749262150686265921457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31698658796273986836495541 2971749262150686265921457)
                      ·
                        rfl

theorem cell23_5787461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_5787461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787461 prefixEnd_5787461 := by exact prefixLift 5787461
  have htrace : WordTrace (prefixWord ++ tailWord_5787461) baseStart_5787461 baseEnd_5787461 := by
    simpa [prefixWord, tailWord_5787461, baseEnd_5787461] using wordTrace_append hprefix tailTrace_5787461
  have hstable : (prefixWord ++ tailWord_5787461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787461).length < 2 ^ (prefixWord ++ tailWord_5787461).sum := by decide
  have hdescent : baseEnd_5787461 < baseStart_5787461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787502 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_5787502 : Nat := 118140960795 + 5787502 * 2 ^ 59
def prefixEnd_5787502 : Nat := 4983230072969 + 3 ^ 40 * 5787502 * 2
def baseEnd_5787502 : Nat := 990590104952506868502923

theorem tailTrace_5787502 : CollatzResearch.WordTrace tailWord_5787502 prefixEnd_5787502 990590104952506868502923 := by
  unfold tailWord_5787502
  simp only [CollatzResearch.WordTrace]
  refine ⟨26385942434859519436755595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140725026319250770329363173 26385942434859519436755595)
  ·
    refine ⟨39578913652289279155133393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26385942434859519436755595 39578913652289279155133393)
    ·
      refine ⟨29684185239216959366350045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39578913652289279155133393 29684185239216959366350045)
      ·
        refine ⟨11131569464706359762381267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29684185239216959366350045 11131569464706359762381267)
        ·
          refine ⟨16697354197059539643571901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11131569464706359762381267 16697354197059539643571901)
          ·
            refine ⟨6261507823897327366339463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16697354197059539643571901 6261507823897327366339463)
            ·
              refine ⟨9392261735845991049509195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261507823897327366339463 9392261735845991049509195)
              ·
                refine ⟨14088392603768986574263793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9392261735845991049509195 14088392603768986574263793)
                ·
                  refine ⟨10566294452826739930697845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14088392603768986574263793 10566294452826739930697845)
                  ·
                    refine ⟨990590104952506868502923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10566294452826739930697845 990590104952506868502923)
                    ·
                      rfl

theorem cell23_5787502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_5787502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787502 prefixEnd_5787502 := by exact prefixLift 5787502
  have htrace : WordTrace (prefixWord ++ tailWord_5787502) baseStart_5787502 baseEnd_5787502 := by
    simpa [prefixWord, tailWord_5787502, baseEnd_5787502] using wordTrace_append hprefix tailTrace_5787502
  have hstable : (prefixWord ++ tailWord_5787502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787502).length < 2 ^ (prefixWord ++ tailWord_5787502).sum := by decide
  have hdescent : baseEnd_5787502 < baseStart_5787502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787582 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_5787582 : Nat := 118140960795 + 5787582 * 2 ^ 59
def prefixEnd_5787582 : Nat := 4983230072969 + 3 ^ 40 * 5787582 * 2
def baseEnd_5787582 : Nat := 2971811393309880292508401

theorem tailTrace_5787582 : CollatzResearch.WordTrace tailWord_5787582 prefixEnd_5787582 2971811393309880292508401 := by
  unfold tailWord_5787582
  simp only [CollatzResearch.WordTrace]
  refine ⟨26386307164823291144619625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140726971545724219437971333 26386307164823291144619625)
  ·
    refine ⟨19789730373617468358464719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26386307164823291144619625 19789730373617468358464719)
    ·
      refine ⟨29684595560426202537697079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19789730373617468358464719 29684595560426202537697079)
      ·
        refine ⟨44526893340639303806545619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29684595560426202537697079 44526893340639303806545619)
        ·
          refine ⟨66790340010958955709818429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44526893340639303806545619 66790340010958955709818429)
          ·
            refine ⟨25046377504109608391181911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66790340010958955709818429 25046377504109608391181911)
            ·
              refine ⟨37569566256164412586772867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25046377504109608391181911 37569566256164412586772867)
              ·
                refine ⟨56354349384246618880159301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37569566256164412586772867 56354349384246618880159301)
                ·
                  refine ⟨10566440509546241040029869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56354349384246618880159301 10566440509546241040029869)
                  ·
                    refine ⟨3962415191079840390011201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10566440509546241040029869 3962415191079840390011201)
                    ·
                      refine ⟨2971811393309880292508401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962415191079840390011201 2971811393309880292508401)
                      ·
                        rfl

theorem cell23_5787582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_5787582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787582 prefixEnd_5787582 := by exact prefixLift 5787582
  have htrace : WordTrace (prefixWord ++ tailWord_5787582) baseStart_5787582 baseEnd_5787582 := by
    simpa [prefixWord, tailWord_5787582, baseEnd_5787582] using wordTrace_append hprefix tailTrace_5787582
  have hstable : (prefixWord ++ tailWord_5787582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787582).length < 2 ^ (prefixWord ++ tailWord_5787582).sum := by decide
  have hdescent : baseEnd_5787582 < baseStart_5787582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787608 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_5787608 : Nat := 118140960795 + 5787608 * 2 ^ 59
def prefixEnd_5787608 : Nat := 4983230072969 + 3 ^ 40 * 5787608 * 2
def baseEnd_5787608 : Nat := 2971824743806897190783281

theorem tailTrace_5787608 : CollatzResearch.WordTrace tailWord_5787608 prefixEnd_5787608 2971824743806897190783281 := by
  unfold tailWord_5787608
  simp only [CollatzResearch.WordTrace]
  refine ⟨105545702808246067798701739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140727603744328090398268985 105545702808246067798701739)
  ·
    refine ⟨158318554212369101698052609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105545702808246067798701739 158318554212369101698052609)
    ·
      refine ⟨118738915659276826273539457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158318554212369101698052609 118738915659276826273539457)
      ·
        refine ⟨89054186744457619705154593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118738915659276826273539457 89054186744457619705154593)
        ·
          refine ⟨66790640058343214778865945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89054186744457619705154593 66790640058343214778865945)
          ·
            refine ⟨50092980043757411084149459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66790640058343214778865945 50092980043757411084149459)
            ·
              refine ⟨75139470065636116626224189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50092980043757411084149459 75139470065636116626224189)
              ·
                refine ⟨28177301274613543734834071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75139470065636116626224189 28177301274613543734834071)
                ·
                  refine ⟨42265951911920315602251107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28177301274613543734834071 42265951911920315602251107)
                  ·
                    refine ⟨63398927867880473403376661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42265951911920315602251107 63398927867880473403376661)
                    ·
                      refine ⟨2971824743806897190783281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63398927867880473403376661 2971824743806897190783281)
                      ·
                        rfl

theorem cell23_5787608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_5787608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787608 prefixEnd_5787608 := by exact prefixLift 5787608
  have htrace : WordTrace (prefixWord ++ tailWord_5787608) baseStart_5787608 baseEnd_5787608 := by
    simpa [prefixWord, tailWord_5787608, baseEnd_5787608] using wordTrace_append hprefix tailTrace_5787608
  have hstable : (prefixWord ++ tailWord_5787608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787608).length < 2 ^ (prefixWord ++ tailWord_5787608).sum := by decide
  have hdescent : baseEnd_5787608 < baseStart_5787608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787609 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 1, 5]
def baseStart_5787609 : Nat := 118140960795 + 5787609 * 2 ^ 59
def prefixEnd_5787609 : Nat := 4983230072969 + 3 ^ 40 * 5787609 * 2
def baseEnd_5787609 : Nat := 990608419095850562290259

theorem tailTrace_5787609 : CollatzResearch.WordTrace tailWord_5787609 prefixEnd_5787609 990608419095850562290259 := by
  unfold tailWord_5787609
  simp only [CollatzResearch.WordTrace]
  refine ⟨211091442089488512768189881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140727628059659008512126587 211091442089488512768189881)
  ·
    refine ⟨158318581567116384576142411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211091442089488512768189881 158318581567116384576142411)
    ·
      refine ⟨237477872350674576864213617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158318581567116384576142411 237477872350674576864213617)
      ·
        refine ⟨178108404263005932648160213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237477872350674576864213617 178108404263005932648160213)
        ·
          refine ⟨4174415724914201546441255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 178108404263005932648160213 4174415724914201546441255)
          ·
            refine ⟨6261623587371302319661883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174415724914201546441255 6261623587371302319661883)
            ·
              refine ⟨9392435381056953479492825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261623587371302319661883 9392435381056953479492825)
              ·
                refine ⟨7044326535792715109619619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9392435381056953479492825 7044326535792715109619619)
                ·
                  refine ⟨10566489803689072664429429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044326535792715109619619 10566489803689072664429429)
                  ·
                    refine ⟨990608419095850562290259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10566489803689072664429429 990608419095850562290259)
                    ·
                      rfl

theorem cell23_5787609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_5787609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787609 prefixEnd_5787609 := by exact prefixLift 5787609
  have htrace : WordTrace (prefixWord ++ tailWord_5787609) baseStart_5787609 baseEnd_5787609 := by
    simpa [prefixWord, tailWord_5787609, baseEnd_5787609] using wordTrace_append hprefix tailTrace_5787609
  have hstable : (prefixWord ++ tailWord_5787609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787609).length < 2 ^ (prefixWord ++ tailWord_5787609).sum := by decide
  have hdescent : baseEnd_5787609 < baseStart_5787609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787662 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5787662 : Nat := 118140960795 + 5787662 * 2 ^ 59
def prefixEnd_5787662 : Nat := 4983230072969 + 3 ^ 40 * 5787662 * 2
def baseEnd_5787662 : Nat := 2971852471762239979508033

theorem tailTrace_5787662 : CollatzResearch.WordTrace tailWord_5787662 prefixEnd_5787662 2971852471762239979508033 := by
  unfold tailWord_5787662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26386671894787062852483655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140728916772197668546579493 26386671894787062852483655)
  ·
    refine ⟨39580007842180594278725483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26386671894787062852483655 39580007842180594278725483)
    ·
      refine ⟨59370011763270891418088225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39580007842180594278725483 59370011763270891418088225)
      ·
        refine ⟨44527508822453168563566169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59370011763270891418088225 44527508822453168563566169)
        ·
          refine ⟨33395631616839876422674627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44527508822453168563566169 33395631616839876422674627)
          ·
            refine ⟨50093447425259814634011941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33395631616839876422674627 50093447425259814634011941)
            ·
              refine ⟨9392521392236215243877239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50093447425259814634011941 9392521392236215243877239)
              ·
                refine ⟨14088782088354322865815859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9392521392236215243877239 14088782088354322865815859)
                ·
                  refine ⟨21133173132531484298723789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14088782088354322865815859 21133173132531484298723789)
                  ·
                    refine ⟨7924939924699306612021421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21133173132531484298723789 7924939924699306612021421)
                    ·
                      refine ⟨2971852471762239979508033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7924939924699306612021421 2971852471762239979508033)
                      ·
                        rfl

theorem cell23_5787662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5787662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787662 prefixEnd_5787662 := by exact prefixLift 5787662
  have htrace : WordTrace (prefixWord ++ tailWord_5787662) baseStart_5787662 baseEnd_5787662 := by
    simpa [prefixWord, tailWord_5787662, baseEnd_5787662] using wordTrace_append hprefix tailTrace_5787662
  have hstable : (prefixWord ++ tailWord_5787662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787662).length < 2 ^ (prefixWord ++ tailWord_5787662).sum := by decide
  have hdescent : baseEnd_5787662 < baseStart_5787662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787672 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_5787672 : Nat := 118140960795 + 5787672 * 2 ^ 59
def prefixEnd_5787672 : Nat := 4983230072969 + 3 ^ 40 * 5787672 * 2
def baseEnd_5787672 : Nat := 2971857606568784940382987

theorem tailTrace_5787672 : CollatzResearch.WordTrace tailWord_5787672 prefixEnd_5787672 2971857606568784940382987 := by
  unfold tailWord_5787672
  simp only [CollatzResearch.WordTrace]
  refine ⟨105546869944130137263866635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140729159925506849685155513 105546869944130137263866635)
  ·
    refine ⟨158320304916195205895799953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105546869944130137263866635 158320304916195205895799953)
    ·
      refine ⟨118740228687146404421849965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158320304916195205895799953 118740228687146404421849965)
      ·
        refine ⟨44527585757679901658193737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118740228687146404421849965 44527585757679901658193737)
        ·
          refine ⟨33395689318259926243645303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44527585757679901658193737 33395689318259926243645303)
          ·
            refine ⟨50093533977389889365467955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33395689318259926243645303 50093533977389889365467955)
            ·
              refine ⟨75140300966084834048201933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50093533977389889365467955 75140300966084834048201933)
              ·
                refine ⟨28177612862281812768075725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75140300966084834048201933 28177612862281812768075725)
                ·
                  refine ⟨10566604823355679788028397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28177612862281812768075725 10566604823355679788028397)
                  ·
                    refine ⟨3962476808758379920510649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10566604823355679788028397 3962476808758379920510649)
                    ·
                      refine ⟨2971857606568784940382987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962476808758379920510649 2971857606568784940382987)
                      ·
                        rfl

theorem cell23_5787672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_5787672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787672 prefixEnd_5787672 := by exact prefixLift 5787672
  have htrace : WordTrace (prefixWord ++ tailWord_5787672) baseStart_5787672 baseEnd_5787672 := by
    simpa [prefixWord, tailWord_5787672, baseEnd_5787672] using wordTrace_append hprefix tailTrace_5787672
  have hstable : (prefixWord ++ tailWord_5787672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787672).length < 2 ^ (prefixWord ++ tailWord_5787672).sum := by decide
  have hdescent : baseEnd_5787672 < baseStart_5787672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787735 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_5787735 : Nat := 118140960795 + 5787735 * 2 ^ 59
def prefixEnd_5787735 : Nat := 4983230072969 + 3 ^ 40 * 5787735 * 2
def baseEnd_5787735 : Nat := 2971889955850018193895197

theorem tailTrace_5787735 : CollatzResearch.WordTrace tailWord_5787735 prefixEnd_5787735 2971889955850018193895197 := by
  unfold tailWord_5787735
  simp only [CollatzResearch.WordTrace]
  refine ⟨211096037687032036287276659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140730691791354690858184439 211096037687032036287276659)
  ·
    refine ⟨316644056530548054430914989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211096037687032036287276659 316644056530548054430914989)
    ·
      refine ⟨118741521198955520411593121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316644056530548054430914989 118741521198955520411593121)
      ·
        refine ⟨89056140899216640308694841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118741521198955520411593121 89056140899216640308694841)
        ·
          refine ⟨66792105674412480231521131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89056140899216640308694841 66792105674412480231521131)
          ·
            refine ⟨100188158511618720347281697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66792105674412480231521131 100188158511618720347281697)
            ·
              refine ⟨75141118883714040260461273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100188158511618720347281697 75141118883714040260461273)
              ·
                refine ⟨56355839162785530195345955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75141118883714040260461273 56355839162785530195345955)
                ·
                  refine ⟨84533758744178295293018933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56355839162785530195345955 84533758744178295293018933)
                  ·
                    refine ⟨7925039882266715183720525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84533758744178295293018933 7925039882266715183720525)
                    ·
                      refine ⟨2971889955850018193895197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925039882266715183720525 2971889955850018193895197)
                      ·
                        rfl

theorem cell23_5787735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_5787735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787735 prefixEnd_5787735 := by exact prefixLift 5787735
  have htrace : WordTrace (prefixWord ++ tailWord_5787735) baseStart_5787735 baseEnd_5787735 := by
    simpa [prefixWord, tailWord_5787735, baseEnd_5787735] using wordTrace_append hprefix tailTrace_5787735
  have hstable : (prefixWord ++ tailWord_5787735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787735).length < 2 ^ (prefixWord ++ tailWord_5787735).sum := by decide
  have hdescent : baseEnd_5787735 < baseStart_5787735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787759 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 5]
def baseStart_5787759 : Nat := 118140960795 + 5787759 * 2 ^ 59
def prefixEnd_5787759 : Nat := 4983230072969 + 3 ^ 40 * 5787759 * 2
def baseEnd_5787759 : Nat := 330211364376191788888343

theorem tailTrace_5787759 : CollatzResearch.WordTrace tailWord_5787759 prefixEnd_5787759 330211364376191788888343 := by
  unfold tailWord_5787759
  simp only [CollatzResearch.WordTrace]
  refine ⟨211096913038945088386150331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140731275359296725590766887 211096913038945088386150331)
  ·
    refine ⟨316645369558417632579225497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211096913038945088386150331 316645369558417632579225497)
    ·
      refine ⟨237484027168813224434419123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316645369558417632579225497 237484027168813224434419123)
      ·
        refine ⟨356226040753219836651628685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237484027168813224434419123 356226040753219836651628685)
        ·
          refine ⟨133584765282457438744360757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356226040753219836651628685 133584765282457438744360757)
          ·
            refine ⟨12523571745230384882283821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133584765282457438744360757 12523571745230384882283821)
            ·
              refine ⟨4696339404461394330856433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12523571745230384882283821 4696339404461394330856433)
              ·
                refine ⟨3522254553346045748142325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696339404461394330856433 3522254553346045748142325)
                ·
                  refine ⟨330211364376191788888343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3522254553346045748142325 330211364376191788888343)
                  ·
                    rfl

theorem cell23_5787759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 5].length) (baseStart_5787759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787759 prefixEnd_5787759 := by exact prefixLift 5787759
  have htrace : WordTrace (prefixWord ++ tailWord_5787759) baseStart_5787759 baseEnd_5787759 := by
    simpa [prefixWord, tailWord_5787759, baseEnd_5787759] using wordTrace_append hprefix tailTrace_5787759
  have hstable : (prefixWord ++ tailWord_5787759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787759).length < 2 ^ (prefixWord ++ tailWord_5787759).sum := by decide
  have hdescent : baseEnd_5787759 < baseStart_5787759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787792 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_5787792 : Nat := 118140960795 + 5787792 * 2 ^ 59
def prefixEnd_5787792 : Nat := 4983230072969 + 3 ^ 40 * 5787792 * 2
def baseEnd_5787792 : Nat := 2971919224247324470882435

theorem tailTrace_5787792 : CollatzResearch.WordTrace tailWord_5787792 prefixEnd_5787792 2971919224247324470882435 := by
  unfold tailWord_5787792
  simp only [CollatzResearch.WordTrace]
  refine ⟨105549058323912767511050815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140732077765217023348067753 105549058323912767511050815)
  ·
    refine ⟨158323587485869151266576223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105549058323912767511050815 158323587485869151266576223)
    ·
      refine ⟨237485381228803726899864335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158323587485869151266576223 237485381228803726899864335)
      ·
        refine ⟨356228071843205590349796503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237485381228803726899864335 356228071843205590349796503)
        ·
          refine ⟨534342107764808385524694755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356228071843205590349796503 534342107764808385524694755)
          ·
            refine ⟨801513161647212578287042133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534342107764808385524694755 801513161647212578287042133)
            ·
              refine ⟨9392732363053272401801275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 801513161647212578287042133 9392732363053272401801275)
              ·
                refine ⟨14089098544579908602701913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9392732363053272401801275 14089098544579908602701913)
                ·
                  refine ⟨10566823908434931452026435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14089098544579908602701913 10566823908434931452026435)
                  ·
                    refine ⟨15850235862652397178039653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10566823908434931452026435 15850235862652397178039653)
                    ·
                      refine ⟨2971919224247324470882435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15850235862652397178039653 2971919224247324470882435)
                      ·
                        rfl

theorem cell23_5787792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_5787792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787792 prefixEnd_5787792 := by exact prefixLift 5787792
  have htrace : WordTrace (prefixWord ++ tailWord_5787792) baseStart_5787792 baseEnd_5787792 := by
    simpa [prefixWord, tailWord_5787792, baseEnd_5787792] using wordTrace_append hprefix tailTrace_5787792
  have hstable : (prefixWord ++ tailWord_5787792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787792).length < 2 ^ (prefixWord ++ tailWord_5787792).sum := by decide
  have hdescent : baseEnd_5787792 < baseStart_5787792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787950 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5787950 : Nat := 118140960795 + 5787950 * 2 ^ 59
def prefixEnd_5787950 : Nat := 4983230072969 + 3 ^ 40 * 5787950 * 2
def baseEnd_5787950 : Nat := 2972000354190734852706709

theorem tailTrace_5787950 : CollatzResearch.WordTrace tailWord_5787950 prefixEnd_5787950 2972000354190734852706709 := by
  unfold tailWord_5787950
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387984922656641000794163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140735919587502085337568869 26387984922656641000794163)
  ·
    refine ⟨39581977383984961501191245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26387984922656641000794163 39581977383984961501191245)
    ·
      refine ⟨14843241518994360562946717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39581977383984961501191245 14843241518994360562946717)
      ·
        refine ⟨5566215569622885211105019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14843241518994360562946717 5566215569622885211105019)
        ·
          refine ⟨8349323354434327816657529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566215569622885211105019 8349323354434327816657529)
          ·
            refine ⟨6261992515825745862493147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8349323354434327816657529 6261992515825745862493147)
            ·
              refine ⟨9392988773738618793739721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261992515825745862493147 9392988773738618793739721)
              ·
                refine ⟨7044741580303964095304791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9392988773738618793739721 7044741580303964095304791)
                ·
                  refine ⟨10567112370455946142957187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044741580303964095304791 10567112370455946142957187)
                  ·
                    refine ⟨15850668555683919214435781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10567112370455946142957187 15850668555683919214435781)
                    ·
                      refine ⟨2972000354190734852706709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15850668555683919214435781 2972000354190734852706709)
                      ·
                        rfl

theorem cell23_5787950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5787950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787950 prefixEnd_5787950 := by exact prefixLift 5787950
  have htrace : WordTrace (prefixWord ++ tailWord_5787950) baseStart_5787950 baseEnd_5787950 := by
    simpa [prefixWord, tailWord_5787950, baseEnd_5787950] using wordTrace_append hprefix tailTrace_5787950
  have hstable : (prefixWord ++ tailWord_5787950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787950).length < 2 ^ (prefixWord ++ tailWord_5787950).sum := by decide
  have hdescent : baseEnd_5787950 < baseStart_5787950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787953 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_5787953 : Nat := 118140960795 + 5787953 * 2 ^ 59
def prefixEnd_5787953 : Nat := 4983230072969 + 3 ^ 40 * 5787953 * 2
def baseEnd_5787953 : Nat := 2972001894632698340969195

theorem tailTrace_5787953 : CollatzResearch.WordTrace tailWord_5787953 prefixEnd_5787953 2972001894632698340969195 := by
  unfold tailWord_5787953
  simp only [CollatzResearch.WordTrace]
  refine ⟨211103988800242259518712513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140735992533494839679141675 211103988800242259518712513)
  ·
    refine ⟨158327991600181694639034385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211103988800242259518712513 158327991600181694639034385)
    ·
      refine ⟨118745993700136270979275789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158327991600181694639034385 118745993700136270979275789)
      ·
        refine ⟨44529747637551101617228421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118745993700136270979275789 44529747637551101617228421)
        ·
          refine ⟨8349327682040831553230329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44529747637551101617228421 8349327682040831553230329)
          ·
            refine ⟨6261995761530623664922747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8349327682040831553230329 6261995761530623664922747)
            ·
              refine ⟨9392993642295935497384121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261995761530623664922747 9392993642295935497384121)
              ·
                refine ⟨7044745231721951623038091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9392993642295935497384121 7044745231721951623038091)
                ·
                  refine ⟨10567117847582927434557137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044745231721951623038091 10567117847582927434557137)
                  ·
                    refine ⟨7925338385687195575917853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10567117847582927434557137 7925338385687195575917853)
                    ·
                      refine ⟨2972001894632698340969195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925338385687195575917853 2972001894632698340969195)
                      ·
                        rfl

theorem cell23_5787953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_5787953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787953 prefixEnd_5787953 := by exact prefixLift 5787953
  have htrace : WordTrace (prefixWord ++ tailWord_5787953) baseStart_5787953 baseEnd_5787953 := by
    simpa [prefixWord, tailWord_5787953, baseEnd_5787953] using wordTrace_append hprefix tailTrace_5787953
  have hstable : (prefixWord ++ tailWord_5787953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787953).length < 2 ^ (prefixWord ++ tailWord_5787953).sum := by decide
  have hdescent : baseEnd_5787953 < baseStart_5787953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787966 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_5787966 : Nat := 118140960795 + 5787966 * 2 ^ 59
def prefixEnd_5787966 : Nat := 4983230072969 + 3 ^ 40 * 5787966 * 2
def baseEnd_5787966 : Nat := 2972008569881206790106635

theorem tailTrace_5787966 : CollatzResearch.WordTrace tailWord_5787966 prefixEnd_5787966 2972008569881206790106635 := by
  unfold tailWord_5787966
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388057868649395342366969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140736308632796775159290501 26388057868649395342366969)
  ·
    refine ⟨19791043401487046506775227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26388057868649395342366969 19791043401487046506775227)
    ·
      refine ⟨29686565102230569760162841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19791043401487046506775227 29686565102230569760162841)
      ·
        refine ⟨22264923826672927320122131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29686565102230569760162841 22264923826672927320122131)
        ·
          refine ⟨33397385740009390980183197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22264923826672927320122131 33397385740009390980183197)
          ·
            refine ⟨12524019652503521617568699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33397385740009390980183197 12524019652503521617568699)
            ·
              refine ⟨18786029478755282426353049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12524019652503521617568699 18786029478755282426353049)
              ·
                refine ⟨14089522109066461819764787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18786029478755282426353049 14089522109066461819764787)
                ·
                  refine ⟨21134283163599692729647181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14089522109066461819764787 21134283163599692729647181)
                  ·
                    refine ⟨7925356186349884773617693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21134283163599692729647181 7925356186349884773617693)
                    ·
                      refine ⟨2972008569881206790106635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925356186349884773617693 2972008569881206790106635)
                      ·
                        rfl

theorem cell23_5787966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_5787966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787966 prefixEnd_5787966 := by exact prefixLift 5787966
  have htrace : WordTrace (prefixWord ++ tailWord_5787966) baseStart_5787966 baseEnd_5787966 := by
    simpa [prefixWord, tailWord_5787966, baseEnd_5787966] using wordTrace_append hprefix tailTrace_5787966
  have hstable : (prefixWord ++ tailWord_5787966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787966).length < 2 ^ (prefixWord ++ tailWord_5787966).sum := by decide
  have hdescent : baseEnd_5787966 < baseStart_5787966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787976 : List Nat := [2, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_5787976 : Nat := 118140960795 + 5787976 * 2 ^ 59
def prefixEnd_5787976 : Nat := 4983230072969 + 3 ^ 40 * 5787976 * 2
def baseEnd_5787976 : Nat := 2972013704687751750981589

theorem tailTrace_5787976 : CollatzResearch.WordTrace tailWord_5787976 prefixEnd_5787976 2972013704687751750981589 := by
  unfold tailWord_5787976
  simp only [CollatzResearch.WordTrace]
  refine ⟨105552413839579467223399891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140736551786105956297866521 105552413839579467223399891)
  ·
    refine ⟨158328620759369200835099837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105552413839579467223399891 158328620759369200835099837)
    ·
      refine ⟨59373232784763450313162439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158328620759369200835099837 59373232784763450313162439)
      ·
        refine ⟨89059849177145175469743659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59373232784763450313162439 89059849177145175469743659)
        ·
          refine ⟨133589773765717763204615489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89059849177145175469743659 133589773765717763204615489)
          ·
            refine ⟨100192330324288322403461617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133589773765717763204615489 100192330324288322403461617)
            ·
              refine ⟨75144247743216241802596213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100192330324288322403461617 75144247743216241802596213)
              ·
                refine ⟨7044773225926522668993395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75144247743216241802596213 7044773225926522668993395)
                ·
                  refine ⟨10567159838889784003490093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044773225926522668993395 10567159838889784003490093)
                  ·
                    refine ⟨3962684939583669001308785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10567159838889784003490093 3962684939583669001308785)
                    ·
                      refine ⟨2972013704687751750981589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962684939583669001308785 2972013704687751750981589)
                      ·
                        rfl

theorem cell23_5787976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_5787976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787976 prefixEnd_5787976 := by exact prefixLift 5787976
  have htrace : WordTrace (prefixWord ++ tailWord_5787976) baseStart_5787976 baseEnd_5787976 := by
    simpa [prefixWord, tailWord_5787976, baseEnd_5787976] using wordTrace_append hprefix tailTrace_5787976
  have hstable : (prefixWord ++ tailWord_5787976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787976).length < 2 ^ (prefixWord ++ tailWord_5787976).sum := by decide
  have hdescent : baseEnd_5787976 < baseStart_5787976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5787992 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_5787992 : Nat := 118140960795 + 5787992 * 2 ^ 59
def prefixEnd_5787992 : Nat := 4983230072969 + 3 ^ 40 * 5787992 * 2
def baseEnd_5787992 : Nat := 2972021920378223688381515

theorem tailTrace_5787992 : CollatzResearch.WordTrace tailWord_5787992 prefixEnd_5787992 2972021920378223688381515 := by
  unfold tailWord_5787992
  simp only [CollatzResearch.WordTrace]
  refine ⟨105552705623550484589691115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140736940831400646119588153 105552705623550484589691115)
  ·
    refine ⟨158329058435325726884536673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105552705623550484589691115 158329058435325726884536673)
    ·
      refine ⟨118746793826494295163402505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158329058435325726884536673 118746793826494295163402505)
      ·
        refine ⟨89060095369870721372551879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118746793826494295163402505 89060095369870721372551879)
        ·
          refine ⟨133590143054806082058827819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89060095369870721372551879 133590143054806082058827819)
          ·
            refine ⟨200385214582209123088241729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133590143054806082058827819 200385214582209123088241729)
            ·
              refine ⟨150288910936656842316181297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200385214582209123088241729 150288910936656842316181297)
              ·
                refine ⟨112716683202492631737135973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150288910936656842316181297 112716683202492631737135973)
                ·
                  refine ⟨21134378100467368450712995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112716683202492631737135973 21134378100467368450712995)
                  ·
                    refine ⟨31701567150701052676069493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21134378100467368450712995 31701567150701052676069493)
                    ·
                      refine ⟨2972021920378223688381515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31701567150701052676069493 2972021920378223688381515)
                      ·
                        rfl

theorem cell23_5787992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_5787992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5787992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5787992 prefixEnd_5787992 := by exact prefixLift 5787992
  have htrace : WordTrace (prefixWord ++ tailWord_5787992) baseStart_5787992 baseEnd_5787992 := by
    simpa [prefixWord, tailWord_5787992, baseEnd_5787992] using wordTrace_append hprefix tailTrace_5787992
  have hstable : (prefixWord ++ tailWord_5787992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5787992).length < 2 ^ (prefixWord ++ tailWord_5787992).sum := by decide
  have hdescent : baseEnd_5787992 < baseStart_5787992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5787992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788034 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5788034 : Nat := 118140960795 + 5788034 * 2 ^ 59
def prefixEnd_5788034 : Nat := 4983230072969 + 3 ^ 40 * 5788034 * 2
def baseEnd_5788034 : Nat := 2972043486565712524056323

theorem tailTrace_5788034 : CollatzResearch.WordTrace tailWord_5788034 prefixEnd_5788034 2972043486565712524056323 := by
  unfold tailWord_5788034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52776735778237202588102789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140737962075299206901607437 52776735778237202588102789)
  ·
    refine ⟨9895637958419475485269273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52776735778237202588102789 9895637958419475485269273)
    ·
      refine ⟨7421728468814606613951955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9895637958419475485269273 7421728468814606613951955)
      ·
        refine ⟨11132592703221909920927933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421728468814606613951955 11132592703221909920927933)
        ·
          refine ⟨4174722263708216220347975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11132592703221909920927933 4174722263708216220347975)
          ·
            refine ⟨6262083395562324330521963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174722263708216220347975 6262083395562324330521963)
            ·
              refine ⟨9393125093343486495782945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262083395562324330521963 9393125093343486495782945)
              ·
                refine ⟨7044843820007614871837209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9393125093343486495782945 7044843820007614871837209)
                ·
                  refine ⟨5283632865005711153877907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7044843820007614871837209 5283632865005711153877907)
                  ·
                    refine ⟨7925449297508566730816861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5283632865005711153877907 7925449297508566730816861)
                    ·
                      refine ⟨2972043486565712524056323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925449297508566730816861 2972043486565712524056323)
                      ·
                        rfl

theorem cell23_5788034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5788034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788034 prefixEnd_5788034 := by exact prefixLift 5788034
  have htrace : WordTrace (prefixWord ++ tailWord_5788034) baseStart_5788034 baseEnd_5788034 := by
    simpa [prefixWord, tailWord_5788034, baseEnd_5788034] using wordTrace_append hprefix tailTrace_5788034
  have hstable : (prefixWord ++ tailWord_5788034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788034).length < 2 ^ (prefixWord ++ tailWord_5788034).sum := by decide
  have hdescent : baseEnd_5788034 < baseStart_5788034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788039 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_5788039 : Nat := 118140960795 + 5788039 * 2 ^ 59
def prefixEnd_5788039 : Nat := 4983230072969 + 3 ^ 40 * 5788039 * 2
def baseEnd_5788039 : Nat := 2972046053968985004493799

theorem tailTrace_5788039 : CollatzResearch.WordTrace tailWord_5788039 prefixEnd_5788039 2972046053968985004493799 := by
  unfold tailWord_5788039
  simp only [CollatzResearch.WordTrace]
  refine ⟨211107125477930696206343171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140738083651953797470895447 211107125477930696206343171)
  ·
    refine ⟨316660688216896044309514757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211107125477930696206343171 316660688216896044309514757)
    ·
      refine ⟨59373879040668008308034017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316660688216896044309514757 59373879040668008308034017)
      ·
        refine ⟨44530409280501006231025513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59373879040668008308034017 44530409280501006231025513)
        ·
          refine ⟨33397806960375754673269135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44530409280501006231025513 33397806960375754673269135)
          ·
            refine ⟨50096710440563632009903703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33397806960375754673269135 50096710440563632009903703)
            ·
              refine ⟨75145065660845448014855555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50096710440563632009903703 75145065660845448014855555)
              ·
                refine ⟨112717598491268172022283333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75145065660845448014855555 112717598491268172022283333)
                ·
                  refine ⟨21134549717112782254178125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112717598491268172022283333 21134549717112782254178125)
                  ·
                    refine ⟨7925456143917293345316797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21134549717112782254178125 7925456143917293345316797)
                    ·
                      refine ⟨2972046053968985004493799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925456143917293345316797 2972046053968985004493799)
                      ·
                        rfl

theorem cell23_5788039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_5788039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788039 prefixEnd_5788039 := by exact prefixLift 5788039
  have htrace : WordTrace (prefixWord ++ tailWord_5788039) baseStart_5788039 baseEnd_5788039 := by
    simpa [prefixWord, tailWord_5788039, baseEnd_5788039] using wordTrace_append hprefix tailTrace_5788039
  have hstable : (prefixWord ++ tailWord_5788039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788039).length < 2 ^ (prefixWord ++ tailWord_5788039).sum := by decide
  have hdescent : baseEnd_5788039 < baseStart_5788039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788046 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_5788046 : Nat := 118140960795 + 5788046 * 2 ^ 59
def prefixEnd_5788046 : Nat := 4983230072969 + 3 ^ 40 * 5788046 * 2
def baseEnd_5788046 : Nat := 330227738703729608567363

theorem tailTrace_5788046 : CollatzResearch.WordTrace tailWord_5788046 prefixEnd_5788046 330227738703729608567363 := by
  unfold tailWord_5788046
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388422598613167050230999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140738253859270224267898661 26388422598613167050230999)
  ·
    refine ⟨39582633897919750575346499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26388422598613167050230999 39582633897919750575346499)
    ·
      refine ⟨59373950846879625863019749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39582633897919750575346499 59373950846879625863019749)
      ·
        refine ⟨11132615783789929849316203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59373950846879625863019749 11132615783789929849316203)
        ·
          refine ⟨16698923675684894773974305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132615783789929849316203 16698923675684894773974305)
          ·
            refine ⟨12524192756763671080480729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16698923675684894773974305 12524192756763671080480729)
            ·
              refine ⟨9393144567572753310360547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12524192756763671080480729 9393144567572753310360547)
              ·
                refine ⟨14089716851359129965540821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9393144567572753310360547 14089716851359129965540821)
                ·
                  refine ⟨330227738703729608567363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14089716851359129965540821 330227738703729608567363)
                  ·
                    rfl

theorem cell23_5788046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_5788046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788046 prefixEnd_5788046 := by exact prefixLift 5788046
  have htrace : WordTrace (prefixWord ++ tailWord_5788046) baseStart_5788046 baseEnd_5788046 := by
    simpa [prefixWord, tailWord_5788046, baseEnd_5788046] using wordTrace_append hprefix tailTrace_5788046
  have hstable : (prefixWord ++ tailWord_5788046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788046).length < 2 ^ (prefixWord ++ tailWord_5788046).sum := by decide
  have hdescent : baseEnd_5788046 < baseStart_5788046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788056 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5788056 : Nat := 118140960795 + 5788056 * 2 ^ 59
def prefixEnd_5788056 : Nat := 4983230072969 + 3 ^ 40 * 5788056 * 2
def baseEnd_5788056 : Nat := 2972054783140111437981221

theorem tailTrace_5788056 : CollatzResearch.WordTrace tailWord_5788056 prefixEnd_5788056 2972054783140111437981221 := by
  unfold tailWord_5788056
  simp only [CollatzResearch.WordTrace]
  refine ⟨105553872759434554054856011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140738497012579405406474681 105553872759434554054856011)
  ·
    refine ⟨158330809139151831082284017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105553872759434554054856011 158330809139151831082284017)
    ·
      refine ⟨118748106854363873311713013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158330809139151831082284017 118748106854363873311713013)
      ·
        refine ⟨11132635017596613122973095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118748106854363873311713013 11132635017596613122973095)
        ·
          refine ⟨16698952526394919684459643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132635017596613122973095 16698952526394919684459643)
          ·
            refine ⟨25048428789592379526689465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16698952526394919684459643 25048428789592379526689465)
            ·
              refine ⟨18786321592194284645017099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25048428789592379526689465 18786321592194284645017099)
              ·
                refine ⟨28179482388291426967525649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18786321592194284645017099 28179482388291426967525649)
                ·
                  refine ⟨21134611791218570225644237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28179482388291426967525649 21134611791218570225644237)
                  ·
                    refine ⟨7925479421706963834616589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21134611791218570225644237 7925479421706963834616589)
                    ·
                      refine ⟨2972054783140111437981221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925479421706963834616589 2972054783140111437981221)
                      ·
                        rfl

theorem cell23_5788056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5788056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788056 prefixEnd_5788056 := by exact prefixLift 5788056
  have htrace : WordTrace (prefixWord ++ tailWord_5788056) baseStart_5788056 baseEnd_5788056 := by
    simpa [prefixWord, tailWord_5788056, baseEnd_5788056] using wordTrace_append hprefix tailTrace_5788056
  have hstable : (prefixWord ++ tailWord_5788056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788056).length < 2 ^ (prefixWord ++ tailWord_5788056).sum := by decide
  have hdescent : baseEnd_5788056 < baseStart_5788056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788097 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 7]
def baseStart_5788097 : Nat := 118140960795 + 5788097 * 2 ^ 59
def prefixEnd_5788097 : Nat := 4983230072969 + 3 ^ 40 * 5788097 * 2
def baseEnd_5788097 : Nat := 330230648427438419729837

theorem tailTrace_5788097 : CollatzResearch.WordTrace tailWord_5788097 prefixEnd_5788097 330230648427438419729837 := by
  unfold tailWord_5788097
  simp only [CollatzResearch.WordTrace]
  refine ⟨211109240911720572111954545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140739493941147048074636363 211109240911720572111954545)
  ·
    refine ⟨158331930683790429083965909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211109240911720572111954545 158331930683790429083965909)
    ·
      refine ⟨3710904625401338181655451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158331930683790429083965909 3710904625401338181655451)
      ·
        refine ⟨5566356938102007272483177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710904625401338181655451 5566356938102007272483177)
        ·
          refine ⟨4174767703576505454362383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5566356938102007272483177 4174767703576505454362383)
          ·
            refine ⟨6262151555364758181543575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174767703576505454362383 6262151555364758181543575)
            ·
              refine ⟨9393227333047137272315363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262151555364758181543575 9393227333047137272315363)
              ·
                refine ⟨14089840999570705908473045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9393227333047137272315363 14089840999570705908473045)
                ·
                  refine ⟨330230648427438419729837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14089840999570705908473045 330230648427438419729837)
                  ·
                    rfl

theorem cell23_5788097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 7].length) (baseStart_5788097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788097 prefixEnd_5788097 := by exact prefixLift 5788097
  have htrace : WordTrace (prefixWord ++ tailWord_5788097) baseStart_5788097 baseEnd_5788097 := by
    simpa [prefixWord, tailWord_5788097, baseEnd_5788097] using wordTrace_append hprefix tailTrace_5788097
  have hstable : (prefixWord ++ tailWord_5788097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788097).length < 2 ^ (prefixWord ++ tailWord_5788097).sum := by decide
  have hdescent : baseEnd_5788097 < baseStart_5788097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788156 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_5788156 : Nat := 118140960795 + 5788156 * 2 ^ 59
def prefixEnd_5788156 : Nat := 4983230072969 + 3 ^ 40 * 5788156 * 2
def baseEnd_5788156 : Nat := 2972106131205561046730761

theorem tailTrace_5788156 : CollatzResearch.WordTrace tailWord_5788156 prefixEnd_5788156 2972106131205561046730761 := by
  unfold tailWord_5788156
  simp only [CollatzResearch.WordTrace]
  refine ⟨105555696409253412594176161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140740928545671216792234881 105555696409253412594176161)
  ·
    refine ⟨79166772306940059445632121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105555696409253412594176161 79166772306940059445632121)
    ·
      refine ⟨59375079230205044584224091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79166772306940059445632121 59375079230205044584224091)
      ·
        refine ⟨89062618845307566876336137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59375079230205044584224091 89062618845307566876336137)
        ·
          refine ⟨66796964133980675157252103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89062618845307566876336137 66796964133980675157252103)
          ·
            refine ⟨100195446200971012735878155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66796964133980675157252103 100195446200971012735878155)
            ·
              refine ⟨150293169301456519103817233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100195446200971012735878155 150293169301456519103817233)
              ·
                refine ⟨112719876976092389327862925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150293169301456519103817233 112719876976092389327862925)
                ·
                  refine ⟨42269953866034645997948597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112719876976092389327862925 42269953866034645997948597)
                  ·
                    refine ⟨3962808174940748062307681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42269953866034645997948597 3962808174940748062307681)
                    ·
                      refine ⟨2972106131205561046730761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962808174940748062307681 2972106131205561046730761)
                      ·
                        rfl

theorem cell23_5788156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_5788156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788156 prefixEnd_5788156 := by exact prefixLift 5788156
  have htrace : WordTrace (prefixWord ++ tailWord_5788156) baseStart_5788156 baseEnd_5788156 := by
    simpa [prefixWord, tailWord_5788156, baseEnd_5788156] using wordTrace_append hprefix tailTrace_5788156
  have hstable : (prefixWord ++ tailWord_5788156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788156).length < 2 ^ (prefixWord ++ tailWord_5788156).sum := by decide
  have hdescent : baseEnd_5788156 < baseStart_5788156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788180 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5788180 : Nat := 118140960795 + 5788180 * 2 ^ 59
def prefixEnd_5788180 : Nat := 4983230072969 + 3 ^ 40 * 5788180 * 2
def baseEnd_5788180 : Nat := 2972118454741268952830651

theorem tailTrace_5788180 : CollatzResearch.WordTrace tailWord_5788180 prefixEnd_5788180 2972118454741268952830651 := by
  unfold tailWord_5788180
  simp only [CollatzResearch.WordTrace]
  refine ⟨105556134085209938643612997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140741512113613251524817329 105556134085209938643612997)
  ·
    refine ⟨19791775140976863495677437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105556134085209938643612997 19791775140976863495677437)
    ·
      refine ⟨7421915677866323810879039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19791775140976863495677437 7421915677866323810879039)
      ·
        refine ⟨11132873516799485716318559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421915677866323810879039 11132873516799485716318559)
        ·
          refine ⟨16699310275199228574477839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132873516799485716318559 16699310275199228574477839)
          ·
            refine ⟨25048965412798842861716759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699310275199228574477839 25048965412798842861716759)
            ·
              refine ⟨37573448119198264292575139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25048965412798842861716759 37573448119198264292575139)
              ·
                refine ⟨56360172178797396438862709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37573448119198264292575139 56360172178797396438862709)
                ·
                  refine ⟨5283766141762255916143379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56360172178797396438862709 5283766141762255916143379)
                  ·
                    refine ⟨7925649212643383874215069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5283766141762255916143379 7925649212643383874215069)
                    ·
                      refine ⟨2972118454741268952830651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925649212643383874215069 2972118454741268952830651)
                      ·
                        rfl

theorem cell23_5788180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5788180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788180 prefixEnd_5788180 := by exact prefixLift 5788180
  have htrace : WordTrace (prefixWord ++ tailWord_5788180) baseStart_5788180 baseEnd_5788180 := by
    simpa [prefixWord, tailWord_5788180, baseEnd_5788180] using wordTrace_append hprefix tailTrace_5788180
  have hstable : (prefixWord ++ tailWord_5788180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788180).length < 2 ^ (prefixWord ++ tailWord_5788180).sum := by decide
  have hdescent : baseEnd_5788180 < baseStart_5788180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788186 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_5788186 : Nat := 118140960795 + 5788186 * 2 ^ 59
def prefixEnd_5788186 : Nat := 4983230072969 + 3 ^ 40 * 5788186 * 2
def baseEnd_5788186 : Nat := 2972121535625195929355623

theorem tailTrace_5788186 : CollatzResearch.WordTrace tailWord_5788186 prefixEnd_5788186 2972121535625195929355623 := by
  unfold tailWord_5788186
  simp only [CollatzResearch.WordTrace]
  refine ⟨52778121752099535077986103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140741658005598760207962941 52778121752099535077986103)
  ·
    refine ⟨79167182628149302616979155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52778121752099535077986103 79167182628149302616979155)
    ·
      refine ⟨118750773942223953925468733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79167182628149302616979155 118750773942223953925468733)
      ·
        refine ⟨44531540228333982722050775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118750773942223953925468733 44531540228333982722050775)
        ·
          refine ⟨66797310342500974083076163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44531540228333982722050775 66797310342500974083076163)
          ·
            refine ⟨100195965513751461124614245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66797310342500974083076163 100195965513751461124614245)
            ·
              refine ⟨18786743533828398960865171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100195965513751461124614245 18786743533828398960865171)
              ·
                refine ⟨28180115300742598441297757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18786743533828398960865171 28180115300742598441297757)
                ·
                  refine ⟨10567543237778474415486659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28180115300742598441297757 10567543237778474415486659)
                  ·
                    refine ⟨15851314856667711623229989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10567543237778474415486659 15851314856667711623229989)
                    ·
                      refine ⟨2972121535625195929355623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15851314856667711623229989 2972121535625195929355623)
                      ·
                        rfl

theorem cell23_5788186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_5788186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788186 prefixEnd_5788186 := by exact prefixLift 5788186
  have htrace : WordTrace (prefixWord ++ tailWord_5788186) baseStart_5788186 baseEnd_5788186 := by
    simpa [prefixWord, tailWord_5788186, baseEnd_5788186] using wordTrace_append hprefix tailTrace_5788186
  have hstable : (prefixWord ++ tailWord_5788186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788186).length < 2 ^ (prefixWord ++ tailWord_5788186).sum := by decide
  have hdescent : baseEnd_5788186 < baseStart_5788186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788200 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 1, 5]
def baseStart_5788200 : Nat := 118140960795 + 5788200 * 2 ^ 59
def prefixEnd_5788200 : Nat := 4983230072969 + 3 ^ 40 * 5788200 * 2
def baseEnd_5788200 : Nat := 990709574784786291526853

theorem tailTrace_5788200 : CollatzResearch.WordTrace tailWord_5788200 prefixEnd_5788200 990709574784786291526853 := by
  unfold tailWord_5788200
  simp only [CollatzResearch.WordTrace]
  refine ⟨105556498815173710351477027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140741998420231613801969369 105556498815173710351477027)
  ·
    refine ⟨158334748222760565527215541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105556498815173710351477027 158334748222760565527215541)
    ·
      refine ⟨14843882645883803018176457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158334748222760565527215541 14843882645883803018176457)
      ·
        refine ⟨11132911984412852263632343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14843882645883803018176457 11132911984412852263632343)
        ·
          refine ⟨16699367976619278395448515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132911984412852263632343 16699367976619278395448515)
          ·
            refine ⟨25049051964928917593172773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699367976619278395448515 25049051964928917593172773)
            ·
              refine ⟨4696697243424172048719895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25049051964928917593172773 4696697243424172048719895)
              ·
                refine ⟨7045045865136258073079843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696697243424172048719895 7045045865136258073079843)
                ·
                  refine ⟨10567568797704387109619765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7045045865136258073079843 10567568797704387109619765)
                  ·
                    refine ⟨990709574784786291526853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10567568797704387109619765 990709574784786291526853)
                    ·
                      rfl

theorem cell23_5788200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_5788200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788200 prefixEnd_5788200 := by exact prefixLift 5788200
  have htrace : WordTrace (prefixWord ++ tailWord_5788200) baseStart_5788200 baseEnd_5788200 := by
    simpa [prefixWord, tailWord_5788200, baseEnd_5788200] using wordTrace_append hprefix tailTrace_5788200
  have hstable : (prefixWord ++ tailWord_5788200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788200).length < 2 ^ (prefixWord ++ tailWord_5788200).sum := by decide
  have hdescent : baseEnd_5788200 < baseStart_5788200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788220 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_5788220 : Nat := 118140960795 + 5788220 * 2 ^ 59
def prefixEnd_5788220 : Nat := 4983230072969 + 3 ^ 40 * 5788220 * 2
def baseEnd_5788220 : Nat := 2972138993967448796330467

theorem tailTrace_5788220 : CollatzResearch.WordTrace tailWord_5788220 prefixEnd_5788220 2972138993967448796330467 := by
  unfold tailWord_5788220
  simp only [CollatzResearch.WordTrace]
  refine ⟨105556863545137482059341057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140742484726849976079121409 105556863545137482059341057)
  ·
    refine ⟨79167647658853111544505793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105556863545137482059341057 79167647658853111544505793)
    ·
      refine ⟨59375735744139833658379345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79167647658853111544505793 59375735744139833658379345)
      ·
        refine ⟨44531801808104875243784509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59375735744139833658379345 44531801808104875243784509)
        ·
          refine ⟨16699425678039328216419191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44531801808104875243784509 16699425678039328216419191)
          ·
            refine ⟨25049138517058992324628787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699425678039328216419191 25049138517058992324628787)
            ·
              refine ⟨37573707775588488486943181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25049138517058992324628787 37573707775588488486943181)
              ·
                refine ⟨14090140415845683182603693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37573707775588488486943181 14090140415845683182603693)
                ·
                  refine ⟨5283802655942131193476385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14090140415845683182603693 5283802655942131193476385)
                  ·
                    refine ⟨3962851991956598395107289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5283802655942131193476385 3962851991956598395107289)
                    ·
                      refine ⟨2972138993967448796330467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962851991956598395107289 2972138993967448796330467)
                      ·
                        rfl

theorem cell23_5788220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_5788220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788220 prefixEnd_5788220 := by exact prefixLift 5788220
  have htrace : WordTrace (prefixWord ++ tailWord_5788220) baseStart_5788220 baseEnd_5788220 := by
    simpa [prefixWord, tailWord_5788220, baseEnd_5788220] using wordTrace_append hprefix tailTrace_5788220
  have hstable : (prefixWord ++ tailWord_5788220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788220).length < 2 ^ (prefixWord ++ tailWord_5788220).sum := by decide
  have hdescent : baseEnd_5788220 < baseStart_5788220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788230 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_5788230 : Nat := 118140960795 + 5788230 * 2 ^ 59
def prefixEnd_5788230 : Nat := 4983230072969 + 3 ^ 40 * 5788230 * 2
def baseEnd_5788230 : Nat := 990714709591331252401807

theorem tailTrace_5788230 : CollatzResearch.WordTrace tailWord_5788230 prefixEnd_5788230 990714709591331252401807 := by
  unfold tailWord_5788230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597315369382460494579567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140742727880159157217697429 6597315369382460494579567)
  ·
    refine ⟨9895973054073690741869351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6597315369382460494579567 9895973054073690741869351)
    ·
      refine ⟨14843959581110536112804027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9895973054073690741869351 14843959581110536112804027)
      ·
        refine ⟨22265939371665804169206041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14843959581110536112804027 22265939371665804169206041)
        ·
          refine ⟨16699454528749353126904531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22265939371665804169206041 16699454528749353126904531)
          ·
            refine ⟨25049181793124029690356797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699454528749353126904531 25049181793124029690356797)
            ·
              refine ⟨9393443172421511133883799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25049181793124029690356797 9393443172421511133883799)
              ·
                refine ⟨14090164758632266700825699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9393443172421511133883799 14090164758632266700825699)
                ·
                  refine ⟨21135247137948400051238549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14090164758632266700825699 21135247137948400051238549)
                  ·
                    refine ⟨990714709591331252401807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21135247137948400051238549 990714709591331252401807)
                    ·
                      rfl

theorem cell23_5788230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_5788230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788230 prefixEnd_5788230 := by exact prefixLift 5788230
  have htrace : WordTrace (prefixWord ++ tailWord_5788230) baseStart_5788230 baseEnd_5788230 := by
    simpa [prefixWord, tailWord_5788230, baseEnd_5788230] using wordTrace_append hprefix tailTrace_5788230
  have hstable : (prefixWord ++ tailWord_5788230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788230).length < 2 ^ (prefixWord ++ tailWord_5788230).sum := by decide
  have hdescent : baseEnd_5788230 < baseStart_5788230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788237 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_5788237 : Nat := 118140960795 + 5788237 * 2 ^ 59
def prefixEnd_5788237 : Nat := 4983230072969 + 3 ^ 40 * 5788237 * 2
def baseEnd_5788237 : Nat := 2972147723138575229817889

theorem tailTrace_5788237 : CollatzResearch.WordTrace tailWord_5788237 prefixEnd_5788237 2972147723138575229817889 := by
  unfold tailWord_5788237
  simp only [CollatzResearch.WordTrace]
  refine ⟨211114347131213376022050965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140742898087475584014700643 211114347131213376022050965)
  ·
    refine ⟨9895985021775627001033639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211114347131213376022050965 9895985021775627001033639)
    ·
      refine ⟨14843977532663440501550459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9895985021775627001033639 14843977532663440501550459)
      ·
        refine ⟨22265966298995160752325689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14843977532663440501550459 22265966298995160752325689)
        ·
          refine ⟨16699474724246370564244267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22265966298995160752325689 16699474724246370564244267)
          ·
            refine ⟨25049212086369555846366401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699474724246370564244267 25049212086369555846366401)
            ·
              refine ⟨18786909064777166884774801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25049212086369555846366401 18786909064777166884774801)
              ·
                refine ⟨14090181798582875163581101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18786909064777166884774801 14090181798582875163581101)
                ·
                  refine ⟨5283818174468578186342913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14090181798582875163581101 5283818174468578186342913)
                  ·
                    refine ⟨3962863630851433639757185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5283818174468578186342913 3962863630851433639757185)
                    ·
                      refine ⟨2972147723138575229817889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962863630851433639757185 2972147723138575229817889)
                      ·
                        rfl

theorem cell23_5788237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_5788237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788237 prefixEnd_5788237 := by exact prefixLift 5788237
  have htrace : WordTrace (prefixWord ++ tailWord_5788237) baseStart_5788237 baseEnd_5788237 := by
    simpa [prefixWord, tailWord_5788237, baseEnd_5788237] using wordTrace_append hprefix tailTrace_5788237
  have hstable : (prefixWord ++ tailWord_5788237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788237).length < 2 ^ (prefixWord ++ tailWord_5788237).sum := by decide
  have hdescent : baseEnd_5788237 < baseStart_5788237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788239 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 7]
def baseStart_5788239 : Nat := 118140960795 + 5788239 * 2 ^ 59
def prefixEnd_5788239 : Nat := 4983230072969 + 3 ^ 40 * 5788239 * 2
def baseEnd_5788239 : Nat := 990716250033294740664293

theorem tailTrace_5788239 : CollatzResearch.WordTrace tailWord_5788239 prefixEnd_5788239 990716250033294740664293 := by
  unfold tailWord_5788239
  simp only [CollatzResearch.WordTrace]
  refine ⟨211114420077206130363623771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140742946718137420242415847 211114420077206130363623771)
  ·
    refine ⟨316671630115809195545435657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211114420077206130363623771 316671630115809195545435657)
    ·
      refine ⟨237503722586856896659076743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316671630115809195545435657 237503722586856896659076743)
      ·
        refine ⟨356255583880285344988615115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237503722586856896659076743 356255583880285344988615115)
        ·
          refine ⟨534383375820428017482922673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356255583880285344988615115 534383375820428017482922673)
          ·
            refine ⟨400787531865321013112192005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534383375820428017482922673 400787531865321013112192005)
            ·
              refine ⟨75147662224747689958536001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 400787531865321013112192005 75147662224747689958536001)
              ·
                refine ⟨56360746668560767468902001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75147662224747689958536001 56360746668560767468902001)
                ·
                  refine ⟨42270560001420575601676501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56360746668560767468902001 42270560001420575601676501)
                  ·
                    refine ⟨990716250033294740664293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42270560001420575601676501 990716250033294740664293)
                    ·
                      rfl

theorem cell23_5788239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_5788239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788239 prefixEnd_5788239 := by exact prefixLift 5788239
  have htrace : WordTrace (prefixWord ++ tailWord_5788239) baseStart_5788239 baseEnd_5788239 := by
    simpa [prefixWord, tailWord_5788239, baseEnd_5788239] using wordTrace_append hprefix tailTrace_5788239
  have hstable : (prefixWord ++ tailWord_5788239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788239).length < 2 ^ (prefixWord ++ tailWord_5788239).sum := by decide
  have hdescent : baseEnd_5788239 < baseStart_5788239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788263 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_5788263 : Nat := 118140960795 + 5788263 * 2 ^ 59
def prefixEnd_5788263 : Nat := 4983230072969 + 3 ^ 40 * 5788263 * 2
def baseEnd_5788263 : Nat := 2972161073635592128092769

theorem tailTrace_5788263 : CollatzResearch.WordTrace tailWord_5788263 prefixEnd_5788263 2972161073635592128092769 := by
  unfold tailWord_5788263
  simp only [CollatzResearch.WordTrace]
  refine ⟨211115295429119182462497443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140743530286079454974998295 211115295429119182462497443)
  ·
    refine ⟨316672943143678773693746165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211115295429119182462497443 316672943143678773693746165)
    ·
      refine ⟨29688088419719885033788703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316672943143678773693746165 29688088419719885033788703)
      ·
        refine ⟨44532132629579827550683055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29688088419719885033788703 44532132629579827550683055)
        ·
          refine ⟨66798198944369741326024583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44532132629579827550683055 66798198944369741326024583)
          ·
            refine ⟨100197298416554611989036875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66798198944369741326024583 100197298416554611989036875)
            ·
              refine ⟨150295947624831917983555313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100197298416554611989036875 150295947624831917983555313)
              ·
                refine ⟨112721960718623938487666485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150295947624831917983555313 112721960718623938487666485)
                ·
                  refine ⟨10567683817370994233218733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112721960718623938487666485 10567683817370994233218733)
                  ·
                    refine ⟨3962881431514122837457025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10567683817370994233218733 3962881431514122837457025)
                    ·
                      refine ⟨2972161073635592128092769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3962881431514122837457025 2972161073635592128092769)
                      ·
                        rfl

theorem cell23_5788263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_5788263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788263 prefixEnd_5788263 := by exact prefixLift 5788263
  have htrace : WordTrace (prefixWord ++ tailWord_5788263) baseStart_5788263 baseEnd_5788263 := by
    simpa [prefixWord, tailWord_5788263, baseEnd_5788263] using wordTrace_append hprefix tailTrace_5788263
  have hstable : (prefixWord ++ tailWord_5788263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788263).length < 2 ^ (prefixWord ++ tailWord_5788263).sum := by decide
  have hdescent : baseEnd_5788263 < baseStart_5788263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788266 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5788266 : Nat := 118140960795 + 5788266 * 2 ^ 59
def prefixEnd_5788266 : Nat := 4983230072969 + 3 ^ 40 * 5788266 * 2
def baseEnd_5788266 : Nat := 2972162614077555616355255

theorem tailTrace_5788266 : CollatzResearch.WordTrace tailWord_5788266 prefixEnd_5788266 2972162614077555616355255 := by
  unfold tailWord_5788266
  simp only [CollatzResearch.WordTrace]
  refine ⟨52778851212027078493714163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140743603232072209316571101 52778851212027078493714163)
  ·
    refine ⟨79168276818040617740571245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52778851212027078493714163 79168276818040617740571245)
    ·
      refine ⟨29688103806765231652714217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79168276818040617740571245 29688103806765231652714217)
      ·
        refine ⟨22266077855073923739535663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29688103806765231652714217 22266077855073923739535663)
        ·
          refine ⟨33399116782610885609303495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22266077855073923739535663 33399116782610885609303495)
          ·
            refine ⟨50098675173916328413955243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33399116782610885609303495 50098675173916328413955243)
            ·
              refine ⟨75148012760874492620932865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50098675173916328413955243 75148012760874492620932865)
              ·
                refine ⟨56361009570655869465699649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75148012760874492620932865 56361009570655869465699649)
                ·
                  refine ⟨42270757177991902099274737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56361009570655869465699649 42270757177991902099274737)
                  ·
                    refine ⟨31703067883493926574456053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42270757177991902099274737 31703067883493926574456053)
                    ·
                      refine ⟨2972162614077555616355255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31703067883493926574456053 2972162614077555616355255)
                      ·
                        rfl

theorem cell23_5788266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5788266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788266 prefixEnd_5788266 := by exact prefixLift 5788266
  have htrace : WordTrace (prefixWord ++ tailWord_5788266) baseStart_5788266 baseEnd_5788266 := by
    simpa [prefixWord, tailWord_5788266, baseEnd_5788266] using wordTrace_append hprefix tailTrace_5788266
  have hstable : (prefixWord ++ tailWord_5788266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788266).length < 2 ^ (prefixWord ++ tailWord_5788266).sum := by decide
  have hdescent : baseEnd_5788266 < baseStart_5788266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788270 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5788270 : Nat := 118140960795 + 5788270 * 2 ^ 59
def prefixEnd_5788270 : Nat := 4983230072969 + 3 ^ 40 * 5788270 * 2
def baseEnd_5788270 : Nat := 2972164668000173600705237

theorem tailTrace_5788270 : CollatzResearch.WordTrace tailWord_5788270 prefixEnd_5788270 2972164668000173600705237 := by
  unfold tailWord_5788270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26389443842511727832250283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140743700493395881772001509 26389443842511727832250283)
  ·
    refine ⟨39584165763767591748375425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26389443842511727832250283 39584165763767591748375425)
    ·
      refine ⟨29688124322825693811281569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39584165763767591748375425 29688124322825693811281569)
      ·
        refine ⟨22266093242119270358461177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29688124322825693811281569 22266093242119270358461177)
        ·
          refine ⟨16699569931589452768845883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22266093242119270358461177 16699569931589452768845883)
          ·
            refine ⟨25049354897384179153268825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16699569931589452768845883 25049354897384179153268825)
            ·
              refine ⟨18787016173038134364951619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25049354897384179153268825 18787016173038134364951619)
              ·
                refine ⟨28180524259557201547427429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18787016173038134364951619 28180524259557201547427429)
                ·
                  refine ⟨5283848298666975290142643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28180524259557201547427429 5283848298666975290142643)
                  ·
                    refine ⟨7925772448000462935213965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5283848298666975290142643 7925772448000462935213965)
                    ·
                      refine ⟨2972164668000173600705237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925772448000462935213965 2972164668000173600705237)
                      ·
                        rfl

theorem cell23_5788270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5788270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788270 prefixEnd_5788270 := by exact prefixLift 5788270
  have htrace : WordTrace (prefixWord ++ tailWord_5788270) baseStart_5788270 baseEnd_5788270 := by
    simpa [prefixWord, tailWord_5788270, baseEnd_5788270] using wordTrace_append hprefix tailTrace_5788270
  have hstable : (prefixWord ++ tailWord_5788270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788270).length < 2 ^ (prefixWord ++ tailWord_5788270).sum := by decide
  have hdescent : baseEnd_5788270 < baseStart_5788270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788346 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_5788346 : Nat := 118140960795 + 5788346 * 2 ^ 59
def prefixEnd_5788346 : Nat := 4983230072969 + 3 ^ 40 * 5788346 * 2
def baseEnd_5788346 : Nat := 990734564176638434451629

theorem tailTrace_5788346 : CollatzResearch.WordTrace tailWord_5788346 prefixEnd_5788346 990734564176638434451629 := by
  unfold tailWord_5788346
  simp only [CollatzResearch.WordTrace]
  refine ⟨52779580671954621909442223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140745548458545658425179261 52779580671954621909442223)
  ·
    refine ⟨79169371007931932864163335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52779580671954621909442223 79169371007931932864163335)
    ·
      refine ⟨118754056511897899296245003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79169371007931932864163335 118754056511897899296245003)
      ·
        refine ⟨178131084767846848944367505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118754056511897899296245003 178131084767846848944367505)
        ·
          refine ⟨133598313575885136708275629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178131084767846848944367505 133598313575885136708275629)
          ·
            refine ⟨50099367590956926265603361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133598313575885136708275629 50099367590956926265603361)
            ·
              refine ⟨37574525693217694699202521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50099367590956926265603361 37574525693217694699202521)
              ·
                refine ⟨28180894269913271024401891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37574525693217694699202521 28180894269913271024401891)
                ·
                  refine ⟨42271341404869906536602837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28180894269913271024401891 42271341404869906536602837)
                  ·
                    refine ⟨990734564176638434451629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42271341404869906536602837 990734564176638434451629)
                    ·
                      rfl

theorem cell23_5788346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_5788346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788346 prefixEnd_5788346 := by exact prefixLift 5788346
  have htrace : WordTrace (prefixWord ++ tailWord_5788346) baseStart_5788346 baseEnd_5788346 := by
    simpa [prefixWord, tailWord_5788346, baseEnd_5788346] using wordTrace_append hprefix tailTrace_5788346
  have hstable : (prefixWord ++ tailWord_5788346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788346).length < 2 ^ (prefixWord ++ tailWord_5788346).sum := by decide
  have hdescent : baseEnd_5788346 < baseStart_5788346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788393 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_5788393 : Nat := 118140960795 + 5788393 * 2 ^ 59
def prefixEnd_5788393 : Nat := 4983230072969 + 3 ^ 40 * 5788393 * 2
def baseEnd_5788393 : Nat := 990742608706892206489057

theorem tailTrace_5788393 : CollatzResearch.WordTrace tailWord_5788393 prefixEnd_5788393 990742608706892206489057 := by
  unfold tailWord_5788393
  simp only [CollatzResearch.WordTrace]
  refine ⟨211120036918648214664729833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140746691279098809776486555 211120036918648214664729833)
  ·
    refine ⟨158340027688986160998547375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211120036918648214664729833 158340027688986160998547375)
    ·
      refine ⟨237510041533479241497821063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158340027688986160998547375 237510041533479241497821063)
      ·
        refine ⟨356265062300218862246731595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237510041533479241497821063 356265062300218862246731595)
        ·
          refine ⟨534397593450328293370097393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356265062300218862246731595 534397593450328293370097393)
          ·
            refine ⟨400798195087746220027573045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534397593450328293370097393 400798195087746220027573045)
            ·
              refine ⟨37574830789476208127584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400798195087746220027573045 37574830789476208127584973)
              ·
                refine ⟨14090561546053578047844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37574830789476208127584973 14090561546053578047844365)
                ·
                  refine ⟨5283960579770091767941637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14090561546053578047844365 5283960579770091767941637)
                  ·
                    refine ⟨990742608706892206489057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5283960579770091767941637 990742608706892206489057)
                    ·
                      rfl

theorem cell23_5788393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_5788393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788393 prefixEnd_5788393 := by exact prefixLift 5788393
  have htrace : WordTrace (prefixWord ++ tailWord_5788393) baseStart_5788393 baseEnd_5788393 := by
    simpa [prefixWord, tailWord_5788393, baseEnd_5788393] using wordTrace_append hprefix tailTrace_5788393
  have hstable : (prefixWord ++ tailWord_5788393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788393).length < 2 ^ (prefixWord ++ tailWord_5788393).sum := by decide
  have hdescent : baseEnd_5788393 < baseStart_5788393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788396 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_5788396 : Nat := 118140960795 + 5788396 * 2 ^ 59
def prefixEnd_5788396 : Nat := 4983230072969 + 3 ^ 40 * 5788396 * 2
def baseEnd_5788396 : Nat := 2972229366562640107729657

theorem tailTrace_5788396 : CollatzResearch.WordTrace tailWord_5788396 prefixEnd_5788396 2972229366562640107729657 := by
  unfold tailWord_5788396
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560073168818673088544521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140746764225091564118059361 105560073168818673088544521)
  ·
    refine ⟨79170054876614004816408391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105560073168818673088544521 79170054876614004816408391)
    ·
      refine ⟨118755082314921007224612587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79170054876614004816408391 118755082314921007224612587)
      ·
        refine ⟨178132623472381510836918881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118755082314921007224612587 178132623472381510836918881)
        ·
          refine ⟨133599467604286133127689161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178132623472381510836918881 133599467604286133127689161)
          ·
            refine ⟨100199600703214599845766871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133599467604286133127689161 100199600703214599845766871)
            ·
              refine ⟨150299401054821899768650307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100199600703214599845766871 150299401054821899768650307)
              ·
                refine ⟨225449101582232849652975461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150299401054821899768650307 225449101582232849652975461)
                ·
                  refine ⟨42271706546668659309932899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225449101582232849652975461 42271706546668659309932899)
                  ·
                    refine ⟨63407559820002988964899349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42271706546668659309932899 63407559820002988964899349)
                    ·
                      refine ⟨2972229366562640107729657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63407559820002988964899349 2972229366562640107729657)
                      ·
                        rfl

theorem cell23_5788396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_5788396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788396 prefixEnd_5788396 := by exact prefixLift 5788396
  have htrace : WordTrace (prefixWord ++ tailWord_5788396) baseStart_5788396 baseEnd_5788396 := by
    simpa [prefixWord, tailWord_5788396, baseEnd_5788396] using wordTrace_append hprefix tailTrace_5788396
  have hstable : (prefixWord ++ tailWord_5788396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788396).length < 2 ^ (prefixWord ++ tailWord_5788396).sum := by decide
  have hdescent : baseEnd_5788396 < baseStart_5788396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788420 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5788420 : Nat := 118140960795 + 5788420 * 2 ^ 59
def prefixEnd_5788420 : Nat := 4983230072969 + 3 ^ 40 * 5788420 * 2
def baseEnd_5788420 : Nat := 2972241690098348013829547

theorem tailTrace_5788420 : CollatzResearch.WordTrace tailWord_5788420 prefixEnd_5788420 2972241690098348013829547 := by
  unfold tailWord_5788420
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560510844775199137981357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140747347793033598850641809 105560510844775199137981357)
  ·
    refine ⟨39585191566790699676743009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105560510844775199137981357 39585191566790699676743009)
    ·
      refine ⟨29688893675093024757557257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39585191566790699676743009 29688893675093024757557257)
      ·
        refine ⟨22266670256319768568167943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29688893675093024757557257 22266670256319768568167943)
        ·
          refine ⟨33400005384479652852251915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22266670256319768568167943 33400005384479652852251915)
          ·
            refine ⟨50100008076719479278377873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33400005384479652852251915 50100008076719479278377873)
            ·
              refine ⟨37575006057539609458783405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50100008076719479278377873 37575006057539609458783405)
              ·
                refine ⟨14090627271577353547043777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37575006057539609458783405 14090627271577353547043777)
                ·
                  refine ⟨10567970453683015160282833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14090627271577353547043777 10567970453683015160282833)
                  ·
                    refine ⟨7925977840262261370212125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10567970453683015160282833 7925977840262261370212125)
                    ·
                      refine ⟨2972241690098348013829547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7925977840262261370212125 2972241690098348013829547)
                      ·
                        rfl

theorem cell23_5788420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5788420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788420 prefixEnd_5788420 := by exact prefixLift 5788420
  have htrace : WordTrace (prefixWord ++ tailWord_5788420) baseStart_5788420 baseEnd_5788420 := by
    simpa [prefixWord, tailWord_5788420, baseEnd_5788420] using wordTrace_append hprefix tailTrace_5788420
  have hstable : (prefixWord ++ tailWord_5788420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788420).length < 2 ^ (prefixWord ++ tailWord_5788420).sum := by decide
  have hdescent : baseEnd_5788420 < baseStart_5788420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788423 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 8]
def baseStart_5788423 : Nat := 118140960795 + 5788423 * 2 ^ 59
def prefixEnd_5788423 : Nat := 4983230072969 + 3 ^ 40 * 5788423 * 2
def baseEnd_5788423 : Nat := 330249247837812389121337

theorem tailTrace_5788423 : CollatzResearch.WordTrace tailWord_5788423 prefixEnd_5788423 330249247837812389121337 := by
  unfold tailWord_5788423
  simp only [CollatzResearch.WordTrace]
  refine ⟨211121131108539529788321923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140747420739026353192214615 211121131108539529788321923)
  ·
    refine ⟨316681696662809294682482885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211121131108539529788321923 316681696662809294682482885)
    ·
      refine ⟨59377818124276742752965541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316681696662809294682482885 59377818124276742752965541)
      ·
        refine ⟨11133340898301889266181039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59377818124276742752965541 11133340898301889266181039)
        ·
          refine ⟨16700011347452833899271559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11133340898301889266181039 16700011347452833899271559)
          ·
            refine ⟨25050017021179250848907339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16700011347452833899271559 25050017021179250848907339)
            ·
              refine ⟨37575025531768876273361009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25050017021179250848907339 37575025531768876273361009)
              ·
                refine ⟨28181269148826657205020757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37575025531768876273361009 28181269148826657205020757)
                ·
                  refine ⟨330249247837812389121337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28181269148826657205020757 330249247837812389121337)
                  ·
                    rfl

theorem cell23_5788423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 8].length) (baseStart_5788423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788423 prefixEnd_5788423 := by exact prefixLift 5788423
  have htrace : WordTrace (prefixWord ++ tailWord_5788423) baseStart_5788423 baseEnd_5788423 := by
    simpa [prefixWord, tailWord_5788423, baseEnd_5788423] using wordTrace_append hprefix tailTrace_5788423
  have hstable : (prefixWord ++ tailWord_5788423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788423).length < 2 ^ (prefixWord ++ tailWord_5788423).sum := by decide
  have hdescent : baseEnd_5788423 < baseStart_5788423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788444 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_5788444 : Nat := 118140960795 + 5788444 * 2 ^ 59
def prefixEnd_5788444 : Nat := 4983230072969 + 3 ^ 40 * 5788444 * 2
def baseEnd_5788444 : Nat := 990751337878018639976479

theorem tailTrace_5788444 : CollatzResearch.WordTrace tailWord_5788444 prefixEnd_5788444 990751337878018639976479 := by
  unfold tailWord_5788444
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560948520731725187418193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140747931360975633583224257 105560948520731725187418193)
  ·
    refine ⟨79170711390548793890563645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105560948520731725187418193 79170711390548793890563645)
    ·
      refine ⟨29689016771455797708961367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79170711390548793890563645 29689016771455797708961367)
      ·
        refine ⟨44533525157183696563442051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29689016771455797708961367 44533525157183696563442051)
        ·
          refine ⟨66800287735775544845163077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44533525157183696563442051 66800287735775544845163077)
          ·
            refine ⟨12525053950457914658468077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66800287735775544845163077 12525053950457914658468077)
            ·
              refine ⟨4696895231421717996925529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12525053950457914658468077 4696895231421717996925529)
              ·
                refine ⟨3522671423566288497694147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696895231421717996925529 3522671423566288497694147)
                ·
                  refine ⟨5284007135349432746541221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522671423566288497694147 5284007135349432746541221)
                  ·
                    refine ⟨990751337878018639976479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5284007135349432746541221 990751337878018639976479)
                    ·
                      rfl

theorem cell23_5788444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_5788444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788444 prefixEnd_5788444 := by exact prefixLift 5788444
  have htrace : WordTrace (prefixWord ++ tailWord_5788444) baseStart_5788444 baseEnd_5788444 := by
    simpa [prefixWord, tailWord_5788444, baseEnd_5788444] using wordTrace_append hprefix tailTrace_5788444
  have hstable : (prefixWord ++ tailWord_5788444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788444).length < 2 ^ (prefixWord ++ tailWord_5788444).sum := by decide
  have hdescent : baseEnd_5788444 < baseStart_5788444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788453 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_5788453 : Nat := 118140960795 + 5788453 * 2 ^ 59
def prefixEnd_5788453 : Nat := 4983230072969 + 3 ^ 40 * 5788453 * 2
def baseEnd_5788453 : Nat := 990752878319982128238965

theorem tailTrace_5788453 : CollatzResearch.WordTrace tailWord_5788453 prefixEnd_5788453 990752878319982128238965 := by
  unfold tailWord_5788453
  simp only [CollatzResearch.WordTrace]
  refine ⟨211122225298430844911914013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140748150198953896607942675 211122225298430844911914013)
  ·
    refine ⟨79170834486911566841967755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211122225298430844911914013 79170834486911566841967755)
    ·
      refine ⟨118756251730367350262951633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79170834486911566841967755 118756251730367350262951633)
      ·
        refine ⟨89067188797775512697213725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118756251730367350262951633 89067188797775512697213725)
        ·
          refine ⟨33400195799165817261455147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89067188797775512697213725 33400195799165817261455147)
          ·
            refine ⟨50100293698748725892182721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33400195799165817261455147 50100293698748725892182721)
            ·
              refine ⟨37575220274061544419137041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50100293698748725892182721 37575220274061544419137041)
              ·
                refine ⟨28181415205546158314352781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37575220274061544419137041 28181415205546158314352781)
                ·
                  refine ⟨10568030702079809367882293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28181415205546158314352781 10568030702079809367882293)
                  ·
                    refine ⟨990752878319982128238965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10568030702079809367882293 990752878319982128238965)
                    ·
                      rfl

theorem cell23_5788453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_5788453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788453 prefixEnd_5788453 := by exact prefixLift 5788453
  have htrace : WordTrace (prefixWord ++ tailWord_5788453) baseStart_5788453 baseEnd_5788453 := by
    simpa [prefixWord, tailWord_5788453, baseEnd_5788453] using wordTrace_append hprefix tailTrace_5788453
  have hstable : (prefixWord ++ tailWord_5788453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788453).length < 2 ^ (prefixWord ++ tailWord_5788453).sum := by decide
  have hdescent : baseEnd_5788453 < baseStart_5788453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788460 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_5788460 : Nat := 118140960795 + 5788460 * 2 ^ 59
def prefixEnd_5788460 : Nat := 4983230072969 + 3 ^ 40 * 5788460 * 2
def baseEnd_5788460 : Nat := 2972262229324527857329363

theorem tailTrace_5788460 : CollatzResearch.WordTrace tailWord_5788460 prefixEnd_5788460 2972262229324527857329363 := by
  unfold tailWord_5788460
  simp only [CollatzResearch.WordTrace]
  refine ⟨105561240304702742553709417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140748320406270323404945889 105561240304702742553709417)
  ·
    refine ⟨79170930228527056915282063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105561240304702742553709417 79170930228527056915282063)
    ·
      refine ⟨118756395342790585372923095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79170930228527056915282063 118756395342790585372923095)
      ·
        refine ⟨178134593014185878059384643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118756395342790585372923095 178134593014185878059384643)
        ·
          refine ⟨267201889521278817089076965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178134593014185878059384643 267201889521278817089076965)
          ·
            refine ⟨50100354285239778204201931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267201889521278817089076965 50100354285239778204201931)
            ·
              refine ⟨75150531427859667306302897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50100354285239778204201931 75150531427859667306302897)
              ·
                refine ⟨56362898570894750479727173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75150531427859667306302897 56362898570894750479727173)
                ·
                  refine ⟨10568043482042765714948845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56362898570894750479727173 10568043482042765714948845)
                  ·
                    refine ⟨3963016305766037143105817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10568043482042765714948845 3963016305766037143105817)
                    ·
                      refine ⟨2972262229324527857329363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963016305766037143105817 2972262229324527857329363)
                      ·
                        rfl

theorem cell23_5788460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_5788460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788460 prefixEnd_5788460 := by exact prefixLift 5788460
  have htrace : WordTrace (prefixWord ++ tailWord_5788460) baseStart_5788460 baseEnd_5788460 := by
    simpa [prefixWord, tailWord_5788460, baseEnd_5788460] using wordTrace_append hprefix tailTrace_5788460
  have hstable : (prefixWord ++ tailWord_5788460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788460).length < 2 ^ (prefixWord ++ tailWord_5788460).sum := by decide
  have hdescent : baseEnd_5788460 < baseStart_5788460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788483 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 1, 6]
def baseStart_5788483 : Nat := 118140960795 + 5788483 * 2 ^ 59
def prefixEnd_5788483 : Nat := 4983230072969 + 3 ^ 40 * 5788483 * 2
def baseEnd_5788483 : Nat := 990758013126527089113919

theorem tailTrace_5788483 : CollatzResearch.WordTrace tailWord_5788483 prefixEnd_5788483 990758013126527089113919 := by
  unfold tailWord_5788483
  simp only [CollatzResearch.WordTrace]
  refine ⟨211123319488322160035506103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140748879658881440023670735 211123319488322160035506103)
  ·
    refine ⟨316684979232483240053259155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211123319488322160035506103 316684979232483240053259155)
    ·
      refine ⟨475027468848724860079888733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316684979232483240053259155 475027468848724860079888733)
      ·
        refine ⟨178135300818271822529958275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475027468848724860079888733 178135300818271822529958275)
        ·
          refine ⟨267202951227407733794937413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178135300818271822529958275 267202951227407733794937413)
          ·
            refine ⟨50100553355138950086550765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267202951227407733794937413 50100553355138950086550765)
            ·
              refine ⟨18787707508177106282456537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50100553355138950086550765 18787707508177106282456537)
              ·
                refine ⟨14090780631132829711842403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18787707508177106282456537 14090780631132829711842403)
                ·
                  refine ⟨21136170946699244567763605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14090780631132829711842403 21136170946699244567763605)
                  ·
                    refine ⟨990758013126527089113919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21136170946699244567763605 990758013126527089113919)
                    ·
                      rfl

theorem cell23_5788483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 6].length) (baseStart_5788483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788483 prefixEnd_5788483 := by exact prefixLift 5788483
  have htrace : WordTrace (prefixWord ++ tailWord_5788483) baseStart_5788483 baseEnd_5788483 := by
    simpa [prefixWord, tailWord_5788483, baseEnd_5788483] using wordTrace_append hprefix tailTrace_5788483
  have hstable : (prefixWord ++ tailWord_5788483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788483).length < 2 ^ (prefixWord ++ tailWord_5788483).sum := by decide
  have hdescent : baseEnd_5788483 < baseStart_5788483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788520 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5788520 : Nat := 118140960795 + 5788520 * 2 ^ 59
def prefixEnd_5788520 : Nat := 4983230072969 + 3 ^ 40 * 5788520 * 2
def baseEnd_5788520 : Nat := 2972293038163797622579087

theorem tailTrace_5788520 : CollatzResearch.WordTrace tailWord_5788520 prefixEnd_5788520 2972293038163797622579087 := by
  unfold tailWord_5788520
  simp only [CollatzResearch.WordTrace]
  refine ⟨105562334494594057677301507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140749779326125410236402009 105562334494594057677301507)
  ·
    refine ⟨158343501741891086515952261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105562334494594057677301507 158343501741891086515952261)
    ·
      refine ⟨29689406576604578721741049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158343501741891086515952261 29689406576604578721741049)
      ·
        refine ⟨22267054932453434041305787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29689406576604578721741049 22267054932453434041305787)
        ·
          refine ⟨33400582398680151061958681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22267054932453434041305787 33400582398680151061958681)
          ·
            refine ⟨25050436799010113296469011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33400582398680151061958681 25050436799010113296469011)
            ·
              refine ⟨37575655198515169944703517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25050436799010113296469011 37575655198515169944703517)
              ·
                refine ⟨14090870699443188729263819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37575655198515169944703517 14090870699443188729263819)
                ·
                  refine ⟨21136306049164783093895729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14090870699443188729263819 21136306049164783093895729)
                  ·
                    refine ⟨15852229536873587320421797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21136306049164783093895729 15852229536873587320421797)
                    ·
                      refine ⟨2972293038163797622579087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15852229536873587320421797 2972293038163797622579087)
                      ·
                        rfl

theorem cell23_5788520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5788520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788520 prefixEnd_5788520 := by exact prefixLift 5788520
  have htrace : WordTrace (prefixWord ++ tailWord_5788520) baseStart_5788520 baseEnd_5788520 := by
    simpa [prefixWord, tailWord_5788520, baseEnd_5788520] using wordTrace_append hprefix tailTrace_5788520
  have hstable : (prefixWord ++ tailWord_5788520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788520).length < 2 ^ (prefixWord ++ tailWord_5788520).sum := by decide
  have hdescent : baseEnd_5788520 < baseStart_5788520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788563 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_5788563 : Nat := 118140960795 + 5788563 * 2 ^ 59
def prefixEnd_5788563 : Nat := 4983230072969 + 3 ^ 40 * 5788563 * 2
def baseEnd_5788563 : Nat := 2972315117831940954341389

theorem tailTrace_5788563 : CollatzResearch.WordTrace tailWord_5788563 prefixEnd_5788563 2972315117831940954341389 := by
  unfold tailWord_5788563
  simp only [CollatzResearch.WordTrace]
  refine ⟨211126237328032333698418343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140750824885354889132278895 211126237328032333698418343)
  ·
    refine ⟨316689355992048500547627515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211126237328032333698418343 316689355992048500547627515)
    ·
      refine ⟨475034033988072750821441273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316689355992048500547627515 475034033988072750821441273)
      ·
        refine ⟨356275525491054563116080955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475034033988072750821441273 356275525491054563116080955)
        ·
          refine ⟨534413288236581844674121433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356275525491054563116080955 534413288236581844674121433)
          ·
            refine ⟨400809966177436383505591075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534413288236581844674121433 400809966177436383505591075)
            ·
              refine ⟨601214949266154575258386613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400809966177436383505591075 601214949266154575258386613)
              ·
                refine ⟨56363901493701991430473745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 601214949266154575258386613 56363901493701991430473745)
                ·
                  refine ⟨42272926120276493572855309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56363901493701991430473745 42272926120276493572855309)
                  ·
                    refine ⟨15852347295103685089820741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42272926120276493572855309 15852347295103685089820741)
                    ·
                      refine ⟨2972315117831940954341389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15852347295103685089820741 2972315117831940954341389)
                      ·
                        rfl

theorem cell23_5788563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_5788563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788563 prefixEnd_5788563 := by exact prefixLift 5788563
  have htrace : WordTrace (prefixWord ++ tailWord_5788563) baseStart_5788563 baseEnd_5788563 := by
    simpa [prefixWord, tailWord_5788563, baseEnd_5788563] using wordTrace_append hprefix tailTrace_5788563
  have hstable : (prefixWord ++ tailWord_5788563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788563).length < 2 ^ (prefixWord ++ tailWord_5788563).sum := by decide
  have hdescent : baseEnd_5788563 < baseStart_5788563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788597 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_5788597 : Nat := 118140960795 + 5788597 * 2 ^ 59
def prefixEnd_5788597 : Nat := 4983230072969 + 3 ^ 40 * 5788597 * 2
def baseEnd_5788597 : Nat := 2972332576174193821316233

theorem tailTrace_5788597 : CollatzResearch.WordTrace tailWord_5788597 prefixEnd_5788597 2972332576174193821316233 := by
  unfold tailWord_5788597
  simp only [CollatzResearch.WordTrace]
  refine ⟨211127477409909157505156045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140751651606606105003437363 211127477409909157505156045)
  ·
    refine ⟨79172804028715934064433517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211127477409909157505156045 79172804028715934064433517)
    ·
      refine ⟨29689801510768475274162569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79172804028715934064433517 29689801510768475274162569)
      ·
        refine ⟨22267351133076356455621927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29689801510768475274162569 22267351133076356455621927)
        ·
          refine ⟨33401026699614534683432891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22267351133076356455621927 33401026699614534683432891)
          ·
            refine ⟨50101540049421802025149337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33401026699614534683432891 50101540049421802025149337)
            ·
              refine ⟨37576155037066351518862003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50101540049421802025149337 37576155037066351518862003)
              ·
                refine ⟨56364232555599527278293005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37576155037066351518862003 56364232555599527278293005)
                ·
                  refine ⟨21136587208349822729359877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56364232555599527278293005 21136587208349822729359877)
                  ·
                    refine ⟨3963110101565591761754977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21136587208349822729359877 3963110101565591761754977)
                    ·
                      refine ⟨2972332576174193821316233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963110101565591761754977 2972332576174193821316233)
                      ·
                        rfl

theorem cell23_5788597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_5788597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788597 prefixEnd_5788597 := by exact prefixLift 5788597
  have htrace : WordTrace (prefixWord ++ tailWord_5788597) baseStart_5788597 baseEnd_5788597 := by
    simpa [prefixWord, tailWord_5788597, baseEnd_5788597] using wordTrace_append hprefix tailTrace_5788597
  have hstable : (prefixWord ++ tailWord_5788597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788597).length < 2 ^ (prefixWord ++ tailWord_5788597).sum := by decide
  have hdescent : baseEnd_5788597 < baseStart_5788597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788600 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_5788600 : Nat := 118140960795 + 5788600 * 2 ^ 59
def prefixEnd_5788600 : Nat := 4983230072969 + 3 ^ 40 * 5788600 * 2
def baseEnd_5788600 : Nat := 2972334116616157309578719

theorem tailTrace_5788600 : CollatzResearch.WordTrace tailWord_5788600 prefixEnd_5788600 2972334116616157309578719 := by
  unfold tailWord_5788600
  simp only [CollatzResearch.WordTrace]
  refine ⟨105563793414449144508757627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140751724552598859345010169 105563793414449144508757627)
  ·
    refine ⟨158345690121673716763136441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105563793414449144508757627 158345690121673716763136441)
    ·
      refine ⟨118759267591255287572352331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158345690121673716763136441 118759267591255287572352331)
      ·
        refine ⟨178138901386882931358528497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118759267591255287572352331 178138901386882931358528497)
        ·
          refine ⟨133604176040162198518896373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178138901386882931358528497 133604176040162198518896373)
          ·
            refine ⟨12525391503765206111146535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133604176040162198518896373 12525391503765206111146535)
            ·
              refine ⟨18788087255647809166719803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525391503765206111146535 18788087255647809166719803)
              ·
                refine ⟨28182130883471713750079705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18788087255647809166719803 28182130883471713750079705)
                ·
                  refine ⟨21136598162603785312559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28182130883471713750079705 21136598162603785312559779)
                  ·
                    refine ⟨31704897243905677968839669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21136598162603785312559779 31704897243905677968839669)
                    ·
                      refine ⟨2972334116616157309578719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31704897243905677968839669 2972334116616157309578719)
                      ·
                        rfl

theorem cell23_5788600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_5788600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788600 prefixEnd_5788600 := by exact prefixLift 5788600
  have htrace : WordTrace (prefixWord ++ tailWord_5788600) baseStart_5788600 baseEnd_5788600 := by
    simpa [prefixWord, tailWord_5788600, baseEnd_5788600] using wordTrace_append hprefix tailTrace_5788600
  have hstable : (prefixWord ++ tailWord_5788600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788600).length < 2 ^ (prefixWord ++ tailWord_5788600).sum := by decide
  have hdescent : baseEnd_5788600 < baseStart_5788600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788701 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_5788701 : Nat := 118140960795 + 5788701 * 2 ^ 59
def prefixEnd_5788701 : Nat := 4983230072969 + 3 ^ 40 * 5788701 * 2
def baseEnd_5788701 : Nat := 990795326054087138138585

theorem tailTrace_5788701 : CollatzResearch.WordTrace tailWord_5788701 prefixEnd_5788701 990795326054087138138585 := by
  unfold tailWord_5788701
  simp only [CollatzResearch.WordTrace]
  refine ⟨211131270601532383266941957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140754180401021588844627971 211131270601532383266941957)
  ·
    refine ⟨39587113237787321862551617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211131270601532383266941957 39587113237787321862551617)
    ·
      refine ⟨29690334928340491396913713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39587113237787321862551617 29690334928340491396913713)
      ·
        refine ⟨22267751196255368547685285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29690334928340491396913713 22267751196255368547685285)
        ·
          refine ⟨4175203349297881602690991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22267751196255368547685285 4175203349297881602690991)
          ·
            refine ⟨6262805023946822404036487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175203349297881602690991 6262805023946822404036487)
            ·
              refine ⟨9394207535920233606054731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262805023946822404036487 9394207535920233606054731)
              ·
                refine ⟨14091311303880350409082097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394207535920233606054731 14091311303880350409082097)
                ·
                  refine ⟨10568483477910262806811573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14091311303880350409082097 10568483477910262806811573)
                  ·
                    refine ⟨990795326054087138138585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10568483477910262806811573 990795326054087138138585)
                    ·
                      rfl

theorem cell23_5788701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_5788701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788701 prefixEnd_5788701 := by exact prefixLift 5788701
  have htrace : WordTrace (prefixWord ++ tailWord_5788701) baseStart_5788701 baseEnd_5788701 := by
    simpa [prefixWord, tailWord_5788701, baseEnd_5788701] using wordTrace_append hprefix tailTrace_5788701
  have hstable : (prefixWord ++ tailWord_5788701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788701).length < 2 ^ (prefixWord ++ tailWord_5788701).sum := by decide
  have hdescent : baseEnd_5788701 < baseStart_5788701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788704 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5788704 : Nat := 118140960795 + 5788704 * 2 ^ 59
def prefixEnd_5788704 : Nat := 4983230072969 + 3 ^ 40 * 5788704 * 2
def baseEnd_5788704 : Nat := 2972387518604224902678241

theorem tailTrace_5788704 : CollatzResearch.WordTrace tailWord_5788704 prefixEnd_5788704 2972387518604224902678241 := by
  unfold tailWord_5788704
  simp only [CollatzResearch.WordTrace]
  refine ⟨105565690010260757389650583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140754253347014343186200777 105565690010260757389650583)
  ·
    refine ⟨158348535015391136084475875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105565690010260757389650583 158348535015391136084475875)
    ·
      refine ⟨237522802523086704126713813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158348535015391136084475875 237522802523086704126713813)
      ·
        refine ⟨5566940684134844627969855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 237522802523086704126713813 5566940684134844627969855)
        ·
          refine ⟨8350411026202266941954783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566940684134844627969855 8350411026202266941954783)
          ·
            refine ⟨12525616539303400412932175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8350411026202266941954783 12525616539303400412932175)
            ·
              refine ⟨18788424808955100619398263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525616539303400412932175 18788424808955100619398263)
              ·
                refine ⟨28182637213432650929097395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18788424808955100619398263 28182637213432650929097395)
                ·
                  refine ⟨42273955820148976393646093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28182637213432650929097395 42273955820148976393646093)
                  ·
                    refine ⟨15852733432555866147617285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42273955820148976393646093 15852733432555866147617285)
                    ·
                      refine ⟨2972387518604224902678241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15852733432555866147617285 2972387518604224902678241)
                      ·
                        rfl

theorem cell23_5788704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5788704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788704 prefixEnd_5788704 := by exact prefixLift 5788704
  have htrace : WordTrace (prefixWord ++ tailWord_5788704) baseStart_5788704 baseEnd_5788704 := by
    simpa [prefixWord, tailWord_5788704, baseEnd_5788704] using wordTrace_append hprefix tailTrace_5788704
  have hstable : (prefixWord ++ tailWord_5788704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788704).length < 2 ^ (prefixWord ++ tailWord_5788704).sum := by decide
  have hdescent : baseEnd_5788704 < baseStart_5788704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788707 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3]
def baseStart_5788707 : Nat := 118140960795 + 5788707 * 2 ^ 59
def prefixEnd_5788707 : Nat := 4983230072969 + 3 ^ 40 * 5788707 * 2
def baseEnd_5788707 : Nat := 2972389059046188390940727

theorem tailTrace_5788707 : CollatzResearch.WordTrace tailWord_5788707 prefixEnd_5788707 2972389059046188390940727 := by
  unfold tailWord_5788707
  simp only [CollatzResearch.WordTrace]
  refine ⟨211131489439510646291660375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140754326293007097527773583 211131489439510646291660375)
  ·
    refine ⟨316697234159265969437490563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211131489439510646291660375 316697234159265969437490563)
    ·
      refine ⟨475045851238898954156235845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316697234159265969437490563 475045851238898954156235845)
      ·
        refine ⟨89071097107293553904294221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 475045851238898954156235845 89071097107293553904294221)
        ·
          refine ⟨33401661415235082714110333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89071097107293553904294221 33401661415235082714110333)
          ·
            refine ⟨12525623030713156017791375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33401661415235082714110333 12525623030713156017791375)
            ·
              refine ⟨18788434546069734026687063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525623030713156017791375 18788434546069734026687063)
              ·
                refine ⟨28182651819104601040030595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18788434546069734026687063 28182651819104601040030595)
                ·
                  refine ⟨42273977728656901560045893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28182651819104601040030595 42273977728656901560045893)
                  ·
                    refine ⟨7926370824123169042508605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42273977728656901560045893 7926370824123169042508605)
                    ·
                      refine ⟨2972389059046188390940727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7926370824123169042508605 2972389059046188390940727)
                      ·
                        rfl

theorem cell23_5788707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_5788707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788707 prefixEnd_5788707 := by exact prefixLift 5788707
  have htrace : WordTrace (prefixWord ++ tailWord_5788707) baseStart_5788707 baseEnd_5788707 := by
    simpa [prefixWord, tailWord_5788707, baseEnd_5788707] using wordTrace_append hprefix tailTrace_5788707
  have hstable : (prefixWord ++ tailWord_5788707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788707).length < 2 ^ (prefixWord ++ tailWord_5788707).sum := by decide
  have hdescent : baseEnd_5788707 < baseStart_5788707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788730 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_5788730 : Nat := 118140960795 + 5788730 * 2 ^ 59
def prefixEnd_5788730 : Nat := 4983230072969 + 3 ^ 40 * 5788730 * 2
def baseEnd_5788730 : Nat := 2972400869101241800953121

theorem tailTrace_5788730 : CollatzResearch.WordTrace tailWord_5788730 prefixEnd_5788730 2972400869101241800953121 := by
  unfold tailWord_5788730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52783082079606830304936911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140754885545618214146498429 52783082079606830304936911)
  ·
    refine ⟨79174623119410245457405367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52783082079606830304936911 79174623119410245457405367)
    ·
      refine ⟨118761934679115368186108051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79174623119410245457405367 118761934679115368186108051)
      ·
        refine ⟨178142902018673052279162077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118761934679115368186108051 178142902018673052279162077)
        ·
          refine ⟨66803588257002394604685779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178142902018673052279162077 66803588257002394604685779)
          ·
            refine ⟨100205382385503591907028669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66803588257002394604685779 100205382385503591907028669)
            ·
              refine ⟨37577018394563846965135751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100205382385503591907028669 37577018394563846965135751)
              ·
                refine ⟨56365527591845770447703627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37577018394563846965135751 56365527591845770447703627)
                ·
                  refine ⟨84548291387768655671555441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56365527591845770447703627 84548291387768655671555441)
                  ·
                    refine ⟨63411218540826491753666581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84548291387768655671555441 63411218540826491753666581)
                    ·
                      refine ⟨2972400869101241800953121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63411218540826491753666581 2972400869101241800953121)
                      ·
                        rfl

theorem cell23_5788730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_5788730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788730 prefixEnd_5788730 := by exact prefixLift 5788730
  have htrace : WordTrace (prefixWord ++ tailWord_5788730) baseStart_5788730 baseEnd_5788730 := by
    simpa [prefixWord, tailWord_5788730, baseEnd_5788730] using wordTrace_append hprefix tailTrace_5788730
  have hstable : (prefixWord ++ tailWord_5788730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788730).length < 2 ^ (prefixWord ++ tailWord_5788730).sum := by decide
  have hdescent : baseEnd_5788730 < baseStart_5788730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788764 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5788764 : Nat := 118140960795 + 5788764 * 2 ^ 59
def prefixEnd_5788764 : Nat := 4983230072969 + 3 ^ 40 * 5788764 * 2
def baseEnd_5788764 : Nat := 2972418327443494667927965

theorem tailTrace_5788764 : CollatzResearch.WordTrace tailWord_5788764 prefixEnd_5788764 2972418327443494667927965 := by
  unfold tailWord_5788764
  simp only [CollatzResearch.WordTrace]
  refine ⟨105566784200152072513242673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140755712266869430017656897 105566784200152072513242673)
  ·
    refine ⟨79175088150114054384932005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105566784200152072513242673 79175088150114054384932005)
    ·
      refine ⟨14845329028146385197174751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79175088150114054384932005 14845329028146385197174751)
      ·
        refine ⟨22267993542219577795762127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14845329028146385197174751 22267993542219577795762127)
        ·
          refine ⟨33401990313329366693643191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22267993542219577795762127 33401990313329366693643191)
          ·
            refine ⟨50102985469994050040464787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33401990313329366693643191 50102985469994050040464787)
            ·
              refine ⟨75154478204991075060697181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50102985469994050040464787 75154478204991075060697181)
              ·
                refine ⟨28182929326871653147761443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75154478204991075060697181 28182929326871653147761443)
                ·
                  refine ⟨42274393990307479721642165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28182929326871653147761443 42274393990307479721642165)
                  ·
                    refine ⟨3963224436591326223903953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42274393990307479721642165 3963224436591326223903953)
                    ·
                      refine ⟨2972418327443494667927965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963224436591326223903953 2972418327443494667927965)
                      ·
                        rfl

theorem cell23_5788764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5788764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788764 prefixEnd_5788764 := by exact prefixLift 5788764
  have htrace : WordTrace (prefixWord ++ tailWord_5788764) baseStart_5788764 baseEnd_5788764 := by
    simpa [prefixWord, tailWord_5788764, baseEnd_5788764] using wordTrace_append hprefix tailTrace_5788764
  have hstable : (prefixWord ++ tailWord_5788764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788764).length < 2 ^ (prefixWord ++ tailWord_5788764).sum := by decide
  have hdescent : baseEnd_5788764 < baseStart_5788764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788765 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5788765 : Nat := 118140960795 + 5788765 * 2 ^ 59
def prefixEnd_5788765 : Nat := 4983230072969 + 3 ^ 40 * 5788765 * 2
def baseEnd_5788765 : Nat := 990806280308049721338487

theorem tailTrace_5788765 : CollatzResearch.WordTrace tailWord_5788765 prefixEnd_5788765 990806280308049721338487 := by
  unfold tailWord_5788765
  simp only [CollatzResearch.WordTrace]
  refine ⟨211133604873300522197271749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140755736582200348131514499 211133604873300522197271749)
  ·
    refine ⟨39587550913743847911988453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211133604873300522197271749 39587550913743847911988453)
    ·
      refine ⟨7422665796326971483497835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39587550913743847911988453 7422665796326971483497835)
      ·
        refine ⟨11133998694490457225246753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7422665796326971483497835 11133998694490457225246753)
        ·
          refine ⟨8350499020867842918935065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11133998694490457225246753 8350499020867842918935065)
          ·
            refine ⟨6262874265650882189201299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350499020867842918935065 6262874265650882189201299)
            ·
              refine ⟨9394311398476323283801949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262874265650882189201299 9394311398476323283801949)
              ·
                refine ⟨3522866774428621231425731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9394311398476323283801949 3522866774428621231425731)
                ·
                  refine ⟨5284300161642931847138597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522866774428621231425731 5284300161642931847138597)
                  ·
                    refine ⟨990806280308049721338487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5284300161642931847138597 990806280308049721338487)
                    ·
                      rfl

theorem cell23_5788765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5788765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788765 prefixEnd_5788765 := by exact prefixLift 5788765
  have htrace : WordTrace (prefixWord ++ tailWord_5788765) baseStart_5788765 baseEnd_5788765 := by
    simpa [prefixWord, tailWord_5788765, baseEnd_5788765] using wordTrace_append hprefix tailTrace_5788765
  have hstable : (prefixWord ++ tailWord_5788765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788765).length < 2 ^ (prefixWord ++ tailWord_5788765).sum := by decide
  have hdescent : baseEnd_5788765 < baseStart_5788765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788781 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_5788781 : Nat := 118140960795 + 5788781 * 2 ^ 59
def prefixEnd_5788781 : Nat := 4983230072969 + 3 ^ 40 * 5788781 * 2
def baseEnd_5788781 : Nat := 2972427056614621101415387

theorem tailTrace_5788781 : CollatzResearch.WordTrace tailWord_5788781 prefixEnd_5788781 2972427056614621101415387 := by
  unfold tailWord_5788781
  simp only [CollatzResearch.WordTrace]
  refine ⟨211134188441242556929854197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140756125627495037953236131 211134188441242556929854197)
  ·
    refine ⟨19793830166366489712173831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211134188441242556929854197 19793830166366489712173831)
    ·
      refine ⟨29690745249549734568260747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19793830166366489712173831 29690745249549734568260747)
      ·
        refine ⟨44536117874324601852391121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29690745249549734568260747 44536117874324601852391121)
        ·
          refine ⟨33402088405743451389293341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44536117874324601852391121 33402088405743451389293341)
          ·
            refine ⟨12525783152153794270985003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33402088405743451389293341 12525783152153794270985003)
            ·
              refine ⟨18788674728230691406477505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525783152153794270985003 18788674728230691406477505)
              ·
                refine ⟨14091506046173018554858129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18788674728230691406477505 14091506046173018554858129)
                ·
                  refine ⟨10568629534629763916143597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14091506046173018554858129 10568629534629763916143597)
                  ·
                    refine ⟨3963236075486161468553849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10568629534629763916143597 3963236075486161468553849)
                    ·
                      refine ⟨2972427056614621101415387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963236075486161468553849 2972427056614621101415387)
                      ·
                        rfl

theorem cell23_5788781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_5788781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788781 prefixEnd_5788781 := by exact prefixLift 5788781
  have htrace : WordTrace (prefixWord ++ tailWord_5788781) baseStart_5788781 baseEnd_5788781 := by
    simpa [prefixWord, tailWord_5788781, baseEnd_5788781] using wordTrace_append hprefix tailTrace_5788781
  have hstable : (prefixWord ++ tailWord_5788781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788781).length < 2 ^ (prefixWord ++ tailWord_5788781).sum := by decide
  have hdescent : baseEnd_5788781 < baseStart_5788781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788797 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_5788797 : Nat := 118140960795 + 5788797 * 2 ^ 59
def prefixEnd_5788797 : Nat := 4983230072969 + 3 ^ 40 * 5788797 * 2
def baseEnd_5788797 : Nat := 2972435272305093038815313

theorem tailTrace_5788797 : CollatzResearch.WordTrace tailWord_5788797 prefixEnd_5788797 2972435272305093038815313 := by
  unfold tailWord_5788797
  simp only [CollatzResearch.WordTrace]
  refine ⟨211134772009184591662436645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140756514672789727774957763 211134772009184591662436645)
  ·
    refine ⟨39587769751722110936706871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211134772009184591662436645 39587769751722110936706871)
    ·
      refine ⟨59381654627583166405060307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39587769751722110936706871 59381654627583166405060307)
      ·
        refine ⟨89072481941374749607590461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59381654627583166405060307 89072481941374749607590461)
        ·
          refine ⟨33402180728015531102846423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89072481941374749607590461 33402180728015531102846423)
          ·
            refine ⟨50103271092023296654269635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33402180728015531102846423 50103271092023296654269635)
            ·
              refine ⟨75154906638034944981404453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50103271092023296654269635 75154906638034944981404453)
              ·
                refine ⟨14091544994631552184013335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75154906638034944981404453 14091544994631552184013335)
                ·
                  refine ⟨21137317491947328276020003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14091544994631552184013335 21137317491947328276020003)
                  ·
                    refine ⟨31705976237920992414030005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21137317491947328276020003 31705976237920992414030005)
                    ·
                      refine ⟨2972435272305093038815313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31705976237920992414030005 2972435272305093038815313)
                      ·
                        rfl

theorem cell23_5788797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_5788797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788797 prefixEnd_5788797 := by exact prefixLift 5788797
  have htrace : WordTrace (prefixWord ++ tailWord_5788797) baseStart_5788797 baseEnd_5788797 := by
    simpa [prefixWord, tailWord_5788797, baseEnd_5788797] using wordTrace_append hprefix tailTrace_5788797
  have hstable : (prefixWord ++ tailWord_5788797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788797).length < 2 ^ (prefixWord ++ tailWord_5788797).sum := by decide
  have hdescent : baseEnd_5788797 < baseStart_5788797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788800 : List Nat := [2, 1, 1, 2, 1, 3, 3, 10]
def baseStart_5788800 : Nat := 118140960795 + 5788800 * 2 ^ 59
def prefixEnd_5788800 : Nat := 4983230072969 + 3 ^ 40 * 5788800 * 2
def baseEnd_5788800 : Nat := 110090252323965056558437

theorem tailTrace_5788800 : CollatzResearch.WordTrace tailWord_5788800 prefixEnd_5788800 110090252323965056558437 := by
  unfold tailWord_5788800
  simp only [CollatzResearch.WordTrace]
  refine ⟨105567440714086861587397927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140756587618782482116530569 105567440714086861587397927)
  ·
    refine ⟨158351161071130292381096891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105567440714086861587397927 158351161071130292381096891)
    ·
      refine ⟨237526741606695438571645337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158351161071130292381096891 237526741606695438571645337)
      ·
        refine ⟨178145056205021578928734003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237526741606695438571645337 178145056205021578928734003)
        ·
          refine ⟨267217584307532368393101005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178145056205021578928734003 267217584307532368393101005)
          ·
            refine ⟨100206594115324638147412877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267217584307532368393101005 100206594115324638147412877)
            ·
              refine ⟨37577472793246739305279829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100206594115324638147412877 37577472793246739305279829)
              ·
                refine ⟨110090252323965056558437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37577472793246739305279829 110090252323965056558437)
                ·
                  rfl

theorem cell23_5788800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 10].length) (baseStart_5788800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788800 prefixEnd_5788800 := by exact prefixLift 5788800
  have htrace : WordTrace (prefixWord ++ tailWord_5788800) baseStart_5788800 baseEnd_5788800 := by
    simpa [prefixWord, tailWord_5788800, baseEnd_5788800] using wordTrace_append hprefix tailTrace_5788800
  have hstable : (prefixWord ++ tailWord_5788800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788800).length < 2 ^ (prefixWord ++ tailWord_5788800).sum := by decide
  have hdescent : baseEnd_5788800 < baseStart_5788800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788807 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_5788807 : Nat := 118140960795 + 5788807 * 2 ^ 59
def prefixEnd_5788807 : Nat := 4983230072969 + 3 ^ 40 * 5788807 * 2
def baseEnd_5788807 : Nat := 2972440407111637999690267

theorem tailTrace_5788807 : CollatzResearch.WordTrace tailWord_5788807 prefixEnd_5788807 2972440407111637999690267 := by
  unfold tailWord_5788807
  simp only [CollatzResearch.WordTrace]
  refine ⟨211135136739148363370300675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140756757826098908913533783 211135136739148363370300675)
  ·
    refine ⟨316702705108722545055451013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211135136739148363370300675 316702705108722545055451013)
    ·
      refine ⟨59381757207885477197897065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316702705108722545055451013 59381757207885477197897065)
      ·
        refine ⟨44536317905914107898422799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59381757207885477197897065 44536317905914107898422799)
        ·
          refine ⟨66804476858871161847634199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44536317905914107898422799 66804476858871161847634199)
          ·
            refine ⟨100206715288306742771451299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66804476858871161847634199 100206715288306742771451299)
            ·
              refine ⟨150310072932460114157176949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100206715288306742771451299 150310072932460114157176949)
              ·
                refine ⟨14091569337418135702235339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150310072932460114157176949 14091569337418135702235339)
                ·
                  refine ⟨21137354006127203553353009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14091569337418135702235339 21137354006127203553353009)
                  ·
                    refine ⟨15853015504595402665014757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21137354006127203553353009 15853015504595402665014757)
                    ·
                      refine ⟨2972440407111637999690267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15853015504595402665014757 2972440407111637999690267)
                      ·
                        rfl

theorem cell23_5788807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_5788807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788807 prefixEnd_5788807 := by exact prefixLift 5788807
  have htrace : WordTrace (prefixWord ++ tailWord_5788807) baseStart_5788807 baseEnd_5788807 := by
    simpa [prefixWord, tailWord_5788807, baseEnd_5788807] using wordTrace_append hprefix tailTrace_5788807
  have hstable : (prefixWord ++ tailWord_5788807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788807).length < 2 ^ (prefixWord ++ tailWord_5788807).sum := by decide
  have hdescent : baseEnd_5788807 < baseStart_5788807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788808 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 1, 5]
def baseStart_5788808 : Nat := 118140960795 + 5788808 * 2 ^ 59
def prefixEnd_5788808 : Nat := 4983230072969 + 3 ^ 40 * 5788808 * 2
def baseEnd_5788808 : Nat := 990813640197430831925921

theorem tailTrace_5788808 : CollatzResearch.WordTrace tailWord_5788808 prefixEnd_5788808 990813640197430831925921 := by
  unfold tailWord_5788808
  simp only [CollatzResearch.WordTrace]
  refine ⟨105567586606072370270543539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140756782141429827027391385 105567586606072370270543539)
  ·
    refine ⟨158351379909108555405815309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105567586606072370270543539 158351379909108555405815309)
    ·
      refine ⟨59381767465915708277180741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158351379909108555405815309 59381767465915708277180741)
      ·
        refine ⟨11134081399859195301971389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59381767465915708277180741 11134081399859195301971389)
        ·
          refine ⟨4175280524947198238239271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11134081399859195301971389 4175280524947198238239271)
          ·
            refine ⟨6262920787420797357358907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175280524947198238239271 6262920787420797357358907)
            ·
              refine ⟨9394381181131196036038361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262920787420797357358907 9394381181131196036038361)
              ·
                refine ⟨7045785885848397027028771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9394381181131196036038361 7045785885848397027028771)
                ·
                  refine ⟨10568678828772595540543157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7045785885848397027028771 10568678828772595540543157)
                  ·
                    refine ⟨990813640197430831925921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10568678828772595540543157 990813640197430831925921)
                    ·
                      rfl

theorem cell23_5788808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_5788808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788808 prefixEnd_5788808 := by exact prefixLift 5788808
  have htrace : WordTrace (prefixWord ++ tailWord_5788808) baseStart_5788808 baseEnd_5788808 := by
    simpa [prefixWord, tailWord_5788808, baseEnd_5788808] using wordTrace_append hprefix tailTrace_5788808
  have hstable : (prefixWord ++ tailWord_5788808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788808).length < 2 ^ (prefixWord ++ tailWord_5788808).sum := by decide
  have hdescent : baseEnd_5788808 < baseStart_5788808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788824 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5788824 : Nat := 118140960795 + 5788824 * 2 ^ 59
def prefixEnd_5788824 : Nat := 4983230072969 + 3 ^ 40 * 5788824 * 2
def baseEnd_5788824 : Nat := 2972449136282764433177689

theorem tailTrace_5788824 : CollatzResearch.WordTrace tailWord_5788824 prefixEnd_5788824 2972449136282764433177689 := by
  unfold tailWord_5788824
  simp only [CollatzResearch.WordTrace]
  refine ⟨105567878390043387636834763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140757171186724516849113017 105567878390043387636834763)
  ·
    refine ⟨158351817585065081455252145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105567878390043387636834763 158351817585065081455252145)
    ·
      refine ⟨118763863188798811091439109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158351817585065081455252145 118763863188798811091439109)
      ·
        refine ⟨22268224347899777079644833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118763863188798811091439109 22268224347899777079644833)
        ·
          refine ⟨16701168260924832809733625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22268224347899777079644833 16701168260924832809733625)
          ·
            refine ⟨12525876195693624607300219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16701168260924832809733625 12525876195693624607300219)
            ·
              refine ⟨18788814293540436910950329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525876195693624607300219 18788814293540436910950329)
              ·
                refine ⟨14091610720155327683212747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18788814293540436910950329 14091610720155327683212747)
                ·
                  refine ⟨21137416080232991524819121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14091610720155327683212747 21137416080232991524819121)
                  ·
                    refine ⟨15853062060174743643614341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21137416080232991524819121 15853062060174743643614341)
                    ·
                      refine ⟨2972449136282764433177689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15853062060174743643614341 2972449136282764433177689)
                      ·
                        rfl

theorem cell23_5788824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5788824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788824 prefixEnd_5788824 := by exact prefixLift 5788824
  have htrace : WordTrace (prefixWord ++ tailWord_5788824) baseStart_5788824 baseEnd_5788824 := by
    simpa [prefixWord, tailWord_5788824, baseEnd_5788824] using wordTrace_append hprefix tailTrace_5788824
  have hstable : (prefixWord ++ tailWord_5788824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788824).length < 2 ^ (prefixWord ++ tailWord_5788824).sum := by decide
  have hdescent : baseEnd_5788824 < baseStart_5788824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788831 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_5788831 : Nat := 118140960795 + 5788831 * 2 ^ 59
def prefixEnd_5788831 : Nat := 4983230072969 + 3 ^ 40 * 5788831 * 2
def baseEnd_5788831 : Nat := 2972452730647345905790157

theorem tailTrace_5788831 : CollatzResearch.WordTrace tailWord_5788831 prefixEnd_5788831 2972452730647345905790157 := by
  unfold tailWord_5788831
  simp only [CollatzResearch.WordTrace]
  refine ⟨211136012091061415469174347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140757341394040943646116231 211136012091061415469174347)
  ·
    refine ⟨316704018136592123203761521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211136012091061415469174347 316704018136592123203761521)
    ·
      refine ⟨237528013602444092402821141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316704018136592123203761521 237528013602444092402821141)
      ·
        refine ⟨11134125637614566831382241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 237528013602444092402821141 11134125637614566831382241)
        ·
          refine ⟨8350594228210925123536681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11134125637614566831382241 8350594228210925123536681)
          ·
            refine ⟨6262945671158193842652511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350594228210925123536681 6262945671158193842652511)
            ·
              refine ⟨9394418506737290763978767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262945671158193842652511 9394418506737290763978767)
              ·
                refine ⟨14091627760105936145968151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394418506737290763978767 14091627760105936145968151)
                ·
                  refine ⟨21137441640158904218952227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14091627760105936145968151 21137441640158904218952227)
                  ·
                    refine ⟨31706162460238356328428341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21137441640158904218952227 31706162460238356328428341)
                    ·
                      refine ⟨2972452730647345905790157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31706162460238356328428341 2972452730647345905790157)
                      ·
                        rfl

theorem cell23_5788831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_5788831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788831 prefixEnd_5788831 := by exact prefixLift 5788831
  have htrace : WordTrace (prefixWord ++ tailWord_5788831) baseStart_5788831 baseEnd_5788831 := by
    simpa [prefixWord, tailWord_5788831, baseEnd_5788831] using wordTrace_append hprefix tailTrace_5788831
  have hstable : (prefixWord ++ tailWord_5788831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788831).length < 2 ^ (prefixWord ++ tailWord_5788831).sum := by decide
  have hdescent : baseEnd_5788831 < baseStart_5788831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788834 : List Nat := [3, 3, 1, 3, 3, 10]
def baseStart_5788834 : Nat := 118140960795 + 5788834 * 2 ^ 59
def prefixEnd_5788834 : Nat := 4983230072969 + 3 ^ 40 * 5788834 * 2
def baseEnd_5788834 : Nat := 12232322103248186806801

theorem tailTrace_5788834 : CollatzResearch.WordTrace tailWord_5788834 prefixEnd_5788834 12232322103248186806801 := by
  unfold tailWord_5788834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52784030377512636745383389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140757414340033697987689037 52784030377512636745383389)
  ·
    refine ⟨19794011391567238779518771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52784030377512636745383389 19794011391567238779518771)
    ·
      refine ⟨29691017087350858169278157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19794011391567238779518771 29691017087350858169278157)
      ·
        refine ⟨11134131407756571813479309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29691017087350858169278157 11134131407756571813479309)
        ·
          refine ⟨4175299277908714430054741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11134131407756571813479309 4175299277908714430054741)
          ·
            refine ⟨12232322103248186806801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4175299277908714430054741 12232322103248186806801)
            ·
              rfl

theorem cell23_5788834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 10].length) (baseStart_5788834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788834 prefixEnd_5788834 := by exact prefixLift 5788834
  have htrace : WordTrace (prefixWord ++ tailWord_5788834) baseStart_5788834 baseEnd_5788834 := by
    simpa [prefixWord, tailWord_5788834, baseEnd_5788834] using wordTrace_append hprefix tailTrace_5788834
  have hstable : (prefixWord ++ tailWord_5788834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788834).length < 2 ^ (prefixWord ++ tailWord_5788834).sum := by decide
  have hdescent : baseEnd_5788834 < baseStart_5788834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788861 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5788861 : Nat := 118140960795 + 5788861 * 2 ^ 59
def prefixEnd_5788861 : Nat := 4983230072969 + 3 ^ 40 * 5788861 * 2
def baseEnd_5788861 : Nat := 2972468135066980788415019

theorem tailTrace_5788861 : CollatzResearch.WordTrace tailWord_5788861 prefixEnd_5788861 2972468135066980788415019 := by
  unfold tailWord_5788861
  simp only [CollatzResearch.WordTrace]
  refine ⟨211137106280952730592766437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140758070853968487061844291 211137106280952730592766437)
  ·
    refine ⟨39588207427678636986143707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211137106280952730592766437 39588207427678636986143707)
    ·
      refine ⟨59382311141517955479215561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39588207427678636986143707 59382311141517955479215561)
      ·
        refine ⟨44536733356138466609411671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59382311141517955479215561 44536733356138466609411671)
        ·
          refine ⟨66805100034207699914117507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44536733356138466609411671 66805100034207699914117507)
          ·
            refine ⟨100207650051311549871176261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66805100034207699914117507 100207650051311549871176261)
            ·
              refine ⟨18788934384620915600845549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100207650051311549871176261 18788934384620915600845549)
              ·
                refine ⟨7045850394232843350317081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18788934384620915600845549 7045850394232843350317081)
                ·
                  refine ⟨5284387795674632512737811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7045850394232843350317081 5284387795674632512737811)
                  ·
                    refine ⟨7926581693511948769106717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5284387795674632512737811 7926581693511948769106717)
                    ·
                      refine ⟨2972468135066980788415019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7926581693511948769106717 2972468135066980788415019)
                      ·
                        rfl

theorem cell23_5788861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5788861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788861 prefixEnd_5788861 := by exact prefixLift 5788861
  have htrace : WordTrace (prefixWord ++ tailWord_5788861) baseStart_5788861 baseEnd_5788861 := by
    simpa [prefixWord, tailWord_5788861, baseEnd_5788861] using wordTrace_append hprefix tailTrace_5788861
  have hstable : (prefixWord ++ tailWord_5788861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788861).length < 2 ^ (prefixWord ++ tailWord_5788861).sum := by decide
  have hdescent : baseEnd_5788861 < baseStart_5788861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788887 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_5788887 : Nat := 118140960795 + 5788887 * 2 ^ 59
def prefixEnd_5788887 : Nat := 4983230072969 + 3 ^ 40 * 5788887 * 2
def baseEnd_5788887 : Nat := 2972481485563997686689899

theorem tailTrace_5788887 : CollatzResearch.WordTrace tailWord_5788887 prefixEnd_5788887 2972481485563997686689899 := by
  unfold tailWord_5788887
  simp only [CollatzResearch.WordTrace]
  refine ⟨211138054578858537033212915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140758703052572358022141943 211138054578858537033212915)
  ·
    refine ⟨316707081868287805549819373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211138054578858537033212915 316707081868287805549819373)
    ·
      refine ⟨118765155700607927081182265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316707081868287805549819373 118765155700607927081182265)
      ·
        refine ⟨89073866775455945310886699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118765155700607927081182265 89073866775455945310886699)
        ·
          refine ⟨133610800163183917966330049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89073866775455945310886699 133610800163183917966330049)
          ·
            refine ⟨100208100122387938474747537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133610800163183917966330049 100208100122387938474747537)
            ·
              refine ⟨75156075091790953856060653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100208100122387938474747537 75156075091790953856060653)
              ·
                refine ⟨28183528159421607696022745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75156075091790953856060653 28183528159421607696022745)
                ·
                  refine ⟨21137646119566205772017059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28183528159421607696022745 21137646119566205772017059)
                  ·
                    refine ⟨31706469179349308658025589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21137646119566205772017059 31706469179349308658025589)
                    ·
                      refine ⟨2972481485563997686689899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31706469179349308658025589 2972481485563997686689899)
                      ·
                        rfl

theorem cell23_5788887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_5788887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788887 prefixEnd_5788887 := by exact prefixLift 5788887
  have htrace : WordTrace (prefixWord ++ tailWord_5788887) baseStart_5788887 baseEnd_5788887 := by
    simpa [prefixWord, tailWord_5788887, baseEnd_5788887] using wordTrace_append hprefix tailTrace_5788887
  have hstable : (prefixWord ++ tailWord_5788887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788887).length < 2 ^ (prefixWord ++ tailWord_5788887).sum := by decide
  have hdescent : baseEnd_5788887 < baseStart_5788887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788888 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_5788888 : Nat := 118140960795 + 5788888 * 2 ^ 59
def prefixEnd_5788888 : Nat := 4983230072969 + 3 ^ 40 * 5788888 * 2
def baseEnd_5788888 : Nat := 2972481999044652182777395

theorem tailTrace_5788888 : CollatzResearch.WordTrace tailWord_5788888 prefixEnd_5788888 2972481999044652182777395 := by
  unfold tailWord_5788888
  simp only [CollatzResearch.WordTrace]
  refine ⟨105569045525927457101999659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140758727367903276135999545 105569045525927457101999659)
  ·
    refine ⟨158353568288891185652999489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105569045525927457101999659 158353568288891185652999489)
    ·
      refine ⟨118765176216668389239749617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158353568288891185652999489 118765176216668389239749617)
      ·
        refine ⟨89073882162501291929812213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118765176216668389239749617 89073882162501291929812213)
        ·
          refine ⟨8350676452734496118419895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89073882162501291929812213 8350676452734496118419895)
          ·
            refine ⟨12526014679101744177629843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8350676452734496118419895 12526014679101744177629843)
            ·
              refine ⟨18789022018652616266444765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12526014679101744177629843 18789022018652616266444765)
              ·
                refine ⟨7045883256994731099916787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18789022018652616266444765 7045883256994731099916787)
                ·
                  refine ⟨10568824885492096649875181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7045883256994731099916787 10568824885492096649875181)
                  ·
                    refine ⟨3963309332059536243703193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10568824885492096649875181 3963309332059536243703193)
                    ·
                      refine ⟨2972481999044652182777395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963309332059536243703193 2972481999044652182777395)
                      ·
                        rfl

theorem cell23_5788888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_5788888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788888 prefixEnd_5788888 := by exact prefixLift 5788888
  have htrace : WordTrace (prefixWord ++ tailWord_5788888) baseStart_5788888 baseEnd_5788888 := by
    simpa [prefixWord, tailWord_5788888, baseEnd_5788888] using wordTrace_append hprefix tailTrace_5788888
  have hstable : (prefixWord ++ tailWord_5788888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788888).length < 2 ^ (prefixWord ++ tailWord_5788888).sum := by decide
  have hdescent : baseEnd_5788888 < baseStart_5788888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788907 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 7]
def baseStart_5788907 : Nat := 118140960795 + 5788907 * 2 ^ 59
def prefixEnd_5788907 : Nat := 4983230072969 + 3 ^ 40 * 5788907 * 2
def baseEnd_5788907 : Nat := 330276861686343067604423

theorem tailTrace_5788907 : CollatzResearch.WordTrace tailWord_5788907 prefixEnd_5788907 330276861686343067604423 := by
  unfold tailWord_5788907
  simp only [CollatzResearch.WordTrace]
  refine ⟨211138784038786080448940975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140759189359190720299293983 211138784038786080448940975)
  ·
    refine ⟨316708176058179120673411463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211138784038786080448940975 316708176058179120673411463)
    ·
      refine ⟨475062264087268681010117195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316708176058179120673411463 475062264087268681010117195)
      ·
        refine ⟨712593396130903021515175793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475062264087268681010117195 712593396130903021515175793)
        ·
          refine ⟨534445047098177266136381845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712593396130903021515175793 534445047098177266136381845)
          ·
            refine ⟨25052111582727059350142899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 534445047098177266136381845 25052111582727059350142899)
            ·
              refine ⟨37578167374090589025214349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25052111582727059350142899 37578167374090589025214349)
              ·
                refine ⟨14091812765283970884455381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37578167374090589025214349 14091812765283970884455381)
                ·
                  refine ⟨330276861686343067604423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14091812765283970884455381 330276861686343067604423)
                  ·
                    rfl

theorem cell23_5788907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 7].length) (baseStart_5788907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788907 prefixEnd_5788907 := by exact prefixLift 5788907
  have htrace : WordTrace (prefixWord ++ tailWord_5788907) baseStart_5788907 baseEnd_5788907 := by
    simpa [prefixWord, tailWord_5788907, baseEnd_5788907] using wordTrace_append hprefix tailTrace_5788907
  have hstable : (prefixWord ++ tailWord_5788907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788907).length < 2 ^ (prefixWord ++ tailWord_5788907).sum := by decide
  have hdescent : baseEnd_5788907 < baseStart_5788907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788937 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_5788937 : Nat := 118140960795 + 5788937 * 2 ^ 59
def prefixEnd_5788937 : Nat := 4983230072969 + 3 ^ 40 * 5788937 * 2
def baseEnd_5788937 : Nat := 990835719865574163688223

theorem tailTrace_5788937 : CollatzResearch.WordTrace tailWord_5788937 prefixEnd_5788937 990835719865574163688223 := by
  unfold tailWord_5788937
  simp only [CollatzResearch.WordTrace]
  refine ⟨211139878228677395572533065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140759918819118263715022043 211139878228677395572533065)
  ·
    refine ⟨158354908671508046679399799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211139878228677395572533065 158354908671508046679399799)
    ·
      refine ⟨237532363007262070019099699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158354908671508046679399799 237532363007262070019099699)
      ·
        refine ⟨356298544510893105028649549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237532363007262070019099699 356298544510893105028649549)
        ·
          refine ⟨133611954191584914385743581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356298544510893105028649549 133611954191584914385743581)
          ·
            refine ⟨50104482821844342894653843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133611954191584914385743581 50104482821844342894653843)
            ·
              refine ⟨75156724232766514341980765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50104482821844342894653843 75156724232766514341980765)
              ·
                refine ⟨28183771587287442878242787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75156724232766514341980765 28183771587287442878242787)
                ·
                  refine ⟨42275657380931164317364181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28183771587287442878242787 42275657380931164317364181)
                  ·
                    refine ⟨990835719865574163688223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42275657380931164317364181 990835719865574163688223)
                    ·
                      rfl

theorem cell23_5788937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_5788937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788937 prefixEnd_5788937 := by exact prefixLift 5788937
  have htrace : WordTrace (prefixWord ++ tailWord_5788937) baseStart_5788937 baseEnd_5788937 := by
    simpa [prefixWord, tailWord_5788937, baseEnd_5788937] using wordTrace_append hprefix tailTrace_5788937
  have hstable : (prefixWord ++ tailWord_5788937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788937).length < 2 ^ (prefixWord ++ tailWord_5788937).sum := by decide
  have hdescent : baseEnd_5788937 < baseStart_5788937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788954 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_5788954 : Nat := 118140960795 + 5788954 * 2 ^ 59
def prefixEnd_5788954 : Nat := 4983230072969 + 3 ^ 40 * 5788954 * 2
def baseEnd_5788954 : Nat := 990838629589282974850697

theorem tailTrace_5788954 : CollatzResearch.WordTrace tailWord_5788954 prefixEnd_5788954 990838629589282974850697 := by
  unfold tailWord_5788954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52785124567403951868975479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140760332179743871650601277 52785124567403951868975479)
  ·
    refine ⟨79177686851105927803463219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52785124567403951868975479 79177686851105927803463219)
    ·
      refine ⟨118766530276658891705194829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79177686851105927803463219 118766530276658891705194829)
      ·
        refine ⟨44537448853747084389448061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118766530276658891705194829 44537448853747084389448061)
        ·
          refine ⟨16701543320155156646043023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44537448853747084389448061 16701543320155156646043023)
          ·
            refine ⟨25052314980232734969064535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16701543320155156646043023 25052314980232734969064535)
            ·
              refine ⟨37578472470349102453596803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25052314980232734969064535 37578472470349102453596803)
              ·
                refine ⟨56367708705523653680395205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37578472470349102453596803 56367708705523653680395205)
                ·
                  refine ⟨10568945382285685065074101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56367708705523653680395205 10568945382285685065074101)
                  ·
                    refine ⟨990838629589282974850697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10568945382285685065074101 990838629589282974850697)
                    ·
                      rfl

theorem cell23_5788954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_5788954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788954 prefixEnd_5788954 := by exact prefixLift 5788954
  have htrace : WordTrace (prefixWord ++ tailWord_5788954) baseStart_5788954 baseEnd_5788954 := by
    simpa [prefixWord, tailWord_5788954, baseEnd_5788954] using wordTrace_append hprefix tailTrace_5788954
  have hstable : (prefixWord ++ tailWord_5788954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788954).length < 2 ^ (prefixWord ++ tailWord_5788954).sum := by decide
  have hdescent : baseEnd_5788954 < baseStart_5788954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788964 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_5788964 : Nat := 118140960795 + 5788964 * 2 ^ 59
def prefixEnd_5788964 : Nat := 4983230072969 + 3 ^ 40 * 5788964 * 2
def baseEnd_5788964 : Nat := 2972521023574393885427045

theorem tailTrace_5788964 : CollatzResearch.WordTrace tailWord_5788964 prefixEnd_5788964 2972521023574393885427045 := by
  unfold tailWord_5788964
  simp only [CollatzResearch.WordTrace]
  refine ⟨105570431499789789591882973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140760575333053052789177297 105570431499789789591882973)
  ·
    refine ⟨39588911812421171096956115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105570431499789789591882973 39588911812421171096956115)
    ·
      refine ⟨59383367718631756645434173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39588911812421171096956115 59383367718631756645434173)
      ·
        refine ⟨22268762894486908742037815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59383367718631756645434173 22268762894486908742037815)
        ·
          refine ⟨33403144341730363113056723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22268762894486908742037815 33403144341730363113056723)
          ·
            refine ⟨50104716512595544669585085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33403144341730363113056723 50104716512595544669585085)
            ·
              refine ⟨18789268692223329251094407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50104716512595544669585085 18789268692223329251094407)
              ·
                refine ⟨28183903038334993876641611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18789268692223329251094407 28183903038334993876641611)
                ·
                  refine ⟨42275854557502490814962417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28183903038334993876641611 42275854557502490814962417)
                  ·
                    refine ⟨31706890918126868111221813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42275854557502490814962417 31706890918126868111221813)
                    ·
                      refine ⟨2972521023574393885427045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31706890918126868111221813 2972521023574393885427045)
                      ·
                        rfl

theorem cell23_5788964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_5788964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788964 prefixEnd_5788964 := by exact prefixLift 5788964
  have htrace : WordTrace (prefixWord ++ tailWord_5788964) baseStart_5788964 baseEnd_5788964 := by
    simpa [prefixWord, tailWord_5788964, baseEnd_5788964] using wordTrace_append hprefix tailTrace_5788964
  have hstable : (prefixWord ++ tailWord_5788964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788964).length < 2 ^ (prefixWord ++ tailWord_5788964).sum := by decide
  have hdescent : baseEnd_5788964 < baseStart_5788964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788984 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_5788984 : Nat := 118140960795 + 5788984 * 2 ^ 59
def prefixEnd_5788984 : Nat := 4983230072969 + 3 ^ 40 * 5788984 * 2
def baseEnd_5788984 : Nat := 990843764395827935725651

theorem tailTrace_5788984 : CollatzResearch.WordTrace tailWord_5788984 prefixEnd_5788984 990843764395827935725651 := by
  unfold tailWord_5788984
  simp only [CollatzResearch.WordTrace]
  refine ⟨105570796229753561299747003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140761061639671415066329337 105570796229753561299747003)
  ·
    refine ⟨158356194344630341949620505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105570796229753561299747003 158356194344630341949620505)
    ·
      refine ⟨118767145758472756462215379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158356194344630341949620505 118767145758472756462215379)
      ·
        refine ⟨178150718637709134693323069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118767145758472756462215379 178150718637709134693323069)
        ·
          refine ⟨66806519489140925509996151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178150718637709134693323069 66806519489140925509996151)
          ·
            refine ⟨100209779233711388264994227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66806519489140925509996151 100209779233711388264994227)
            ·
              refine ⟨150314668850567082397491341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100209779233711388264994227 150314668850567082397491341)
              ·
                refine ⟨56368000818962655899059253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150314668850567082397491341 56368000818962655899059253)
                ·
                  refine ⟨5284500076777748990536805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56368000818962655899059253 5284500076777748990536805)
                  ·
                    refine ⟨990843764395827935725651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5284500076777748990536805 990843764395827935725651)
                    ·
                      rfl

theorem cell23_5788984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_5788984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788984 prefixEnd_5788984 := by exact prefixLift 5788984
  have htrace : WordTrace (prefixWord ++ tailWord_5788984) baseStart_5788984 baseEnd_5788984 := by
    simpa [prefixWord, tailWord_5788984, baseEnd_5788984] using wordTrace_append hprefix tailTrace_5788984
  have hstable : (prefixWord ++ tailWord_5788984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788984).length < 2 ^ (prefixWord ++ tailWord_5788984).sum := by decide
  have hdescent : baseEnd_5788984 < baseStart_5788984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788991 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_5788991 : Nat := 118140960795 + 5788991 * 2 ^ 59
def prefixEnd_5788991 : Nat := 4983230072969 + 3 ^ 40 * 5788991 * 2
def baseEnd_5788991 : Nat := 2972534887552065279789421

theorem tailTrace_5788991 : CollatzResearch.WordTrace tailWord_5788991 prefixEnd_5788991 2972534887552065279789421 := by
  unfold tailWord_5788991
  simp only [CollatzResearch.WordTrace]
  refine ⟨211141847770481762794998827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140761231846987841863332551 211141847770481762794998827)
  ·
    refine ⟨316712771655722644192498241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211141847770481762794998827 316712771655722644192498241)
    ·
      refine ⟨237534578741791983144373681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316712771655722644192498241 237534578741791983144373681)
      ·
        refine ⟨178150934056343987358280261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237534578741791983144373681 178150934056343987358280261)
        ·
          refine ⟨33403300135564497629677549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178150934056343987358280261 33403300135564497629677549)
          ·
            refine ⟨12526237550836686611129081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33403300135564497629677549 12526237550836686611129081)
            ·
              refine ⟨9394678163127514958346811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12526237550836686611129081 9394678163127514958346811)
              ·
                refine ⟨14092017244691272437520217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394678163127514958346811 14092017244691272437520217)
                ·
                  refine ⟨10569012933518454328140163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14092017244691272437520217 10569012933518454328140163)
                  ·
                    refine ⟨15853519400277681492210245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10569012933518454328140163 15853519400277681492210245)
                    ·
                      refine ⟨2972534887552065279789421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15853519400277681492210245 2972534887552065279789421)
                      ·
                        rfl

theorem cell23_5788991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_5788991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788991 prefixEnd_5788991 := by exact prefixLift 5788991
  have htrace : WordTrace (prefixWord ++ tailWord_5788991) baseStart_5788991 baseEnd_5788991 := by
    simpa [prefixWord, tailWord_5788991, baseEnd_5788991] using wordTrace_append hprefix tailTrace_5788991
  have hstable : (prefixWord ++ tailWord_5788991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788991).length < 2 ^ (prefixWord ++ tailWord_5788991).sum := by decide
  have hdescent : baseEnd_5788991 < baseStart_5788991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5788997 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 10]
def baseStart_5788997 : Nat := 118140960795 + 5788997 * 2 ^ 59
def prefixEnd_5788997 : Nat := 4983230072969 + 3 ^ 40 * 5788997 * 2
def baseEnd_5788997 : Nat := 330281996492888028479377

theorem tailTrace_5788997 : CollatzResearch.WordTrace tailWord_5788997 prefixEnd_5788997 330281996492888028479377 := by
  unfold tailWord_5788997
  simp only [CollatzResearch.WordTrace]
  refine ⟨211142066608460025819717245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140761377738973350546478163 211142066608460025819717245)
  ·
    refine ⟨79178274978172509682393967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211142066608460025819717245 79178274978172509682393967)
    ·
      refine ⟨118767412467258764523590951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79178274978172509682393967 118767412467258764523590951)
      ·
        refine ⟨178151118700888146785386427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118767412467258764523590951 178151118700888146785386427)
        ·
          refine ⟨267226678051332220178079641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178151118700888146785386427 267226678051332220178079641)
          ·
            refine ⟨200420008538499165133559731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267226678051332220178079641 200420008538499165133559731)
            ·
              refine ⟨300630012807748747700339597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200420008538499165133559731 300630012807748747700339597)
              ·
                refine ⟨112736254802905780387627349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300630012807748747700339597 112736254802905780387627349)
                ·
                  refine ⟨330281996492888028479377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112736254802905780387627349 330281996492888028479377)
                  ·
                    rfl

theorem cell23_5788997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_5788997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5788997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5788997 prefixEnd_5788997 := by exact prefixLift 5788997
  have htrace : WordTrace (prefixWord ++ tailWord_5788997) baseStart_5788997 baseEnd_5788997 := by
    simpa [prefixWord, tailWord_5788997, baseEnd_5788997] using wordTrace_append hprefix tailTrace_5788997
  have hstable : (prefixWord ++ tailWord_5788997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5788997).length < 2 ^ (prefixWord ++ tailWord_5788997).sum := by decide
  have hdescent : baseEnd_5788997 < baseStart_5788997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5788997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789041 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_5789041 : Nat := 118140960795 + 5789041 * 2 ^ 59
def prefixEnd_5789041 : Nat := 4983230072969 + 3 ^ 40 * 5789041 * 2
def baseEnd_5789041 : Nat := 2972560561584790084164191

theorem tailTrace_5789041 : CollatzResearch.WordTrace tailWord_5789041 prefixEnd_5789041 2972560561584790084164191 := by
  unfold tailWord_5789041
  simp only [CollatzResearch.WordTrace]
  refine ⟨211143671420300621334318977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140762447613533747556212651 211143671420300621334318977)
  ·
    refine ⟨158357753565225466000739233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211143671420300621334318977 158357753565225466000739233)
    ·
      refine ⟨118768315173919099500554425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158357753565225466000739233 118768315173919099500554425)
      ·
        refine ⟨89076236380439324625415819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118768315173919099500554425 89076236380439324625415819)
        ·
          refine ⟨133614354570658986938123729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89076236380439324625415819 133614354570658986938123729)
          ·
            refine ⟨100210765927994240203592797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133614354570658986938123729 100210765927994240203592797)
            ·
              refine ⟨37579037222997840076347299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100210765927994240203592797 37579037222997840076347299)
              ·
                refine ⟨56368555834496760114520949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37579037222997840076347299 56368555834496760114520949)
                ·
                  refine ⟨5284552109484071260736339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56368555834496760114520949 5284552109484071260736339)
                  ·
                    refine ⟨7926828164226106891104509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5284552109484071260736339 7926828164226106891104509)
                    ·
                      refine ⟨2972560561584790084164191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7926828164226106891104509 2972560561584790084164191)
                      ·
                        rfl

theorem cell23_5789041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_5789041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789041 prefixEnd_5789041 := by exact prefixLift 5789041
  have htrace : WordTrace (prefixWord ++ tailWord_5789041) baseStart_5789041 baseEnd_5789041 := by
    simpa [prefixWord, tailWord_5789041, baseEnd_5789041] using wordTrace_append hprefix tailTrace_5789041
  have hstable : (prefixWord ++ tailWord_5789041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789041).length < 2 ^ (prefixWord ++ tailWord_5789041).sum := by decide
  have hdescent : baseEnd_5789041 < baseStart_5789041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789045 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5789045 : Nat := 118140960795 + 5789045 * 2 ^ 59
def prefixEnd_5789045 : Nat := 4983230072969 + 3 ^ 40 * 5789045 * 2
def baseEnd_5789045 : Nat := 2972562615507408068514173

theorem tailTrace_5789045 : CollatzResearch.WordTrace tailWord_5789045 prefixEnd_5789045 2972562615507408068514173 := by
  unfold tailWord_5789045
  simp only [CollatzResearch.WordTrace]
  refine ⟨211143817312286130017464589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140762544874857420011643059 211143817312286130017464589)
  ·
    refine ⟨79178931492107298756549221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211143817312286130017464589 79178931492107298756549221)
    ·
      refine ⟨14846049654770118516852979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79178931492107298756549221 14846049654770118516852979)
      ·
        refine ⟨22269074482155177775279469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14846049654770118516852979 22269074482155177775279469)
        ·
          refine ⟨8350902930808191665729801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22269074482155177775279469 8350902930808191665729801)
          ·
            refine ⟨6263177198106143749297351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350902930808191665729801 6263177198106143749297351)
            ·
              refine ⟨9394765797159215623946027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263177198106143749297351 9394765797159215623946027)
              ·
                refine ⟨14092148695738823435919041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394765797159215623946027 14092148695738823435919041)
                ·
                  refine ⟨10569111521804117576939281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14092148695738823435919041 10569111521804117576939281)
                  ·
                    refine ⟨7926833641353088182704461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10569111521804117576939281 7926833641353088182704461)
                    ·
                      refine ⟨2972562615507408068514173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7926833641353088182704461 2972562615507408068514173)
                      ·
                        rfl

theorem cell23_5789045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5789045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789045 prefixEnd_5789045 := by exact prefixLift 5789045
  have htrace : WordTrace (prefixWord ++ tailWord_5789045) baseStart_5789045 baseEnd_5789045 := by
    simpa [prefixWord, tailWord_5789045, baseEnd_5789045] using wordTrace_append hprefix tailTrace_5789045
  have hstable : (prefixWord ++ tailWord_5789045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789045).length < 2 ^ (prefixWord ++ tailWord_5789045).sum := by decide
  have hdescent : baseEnd_5789045 < baseStart_5789045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789051 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 5, 2]
def baseStart_5789051 : Nat := 118140960795 + 5789051 * 2 ^ 59
def prefixEnd_5789051 : Nat := 4983230072969 + 3 ^ 40 * 5789051 * 2
def baseEnd_5789051 : Nat := 2972565696391335045039145

theorem tailTrace_5789051 : CollatzResearch.WordTrace tailWord_5789051 prefixEnd_5789051 2972565696391335045039145 := by
  unfold tailWord_5789051
  simp only [CollatzResearch.WordTrace]
  refine ⟨211144036150264393042183007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140762690766842928694788671 211144036150264393042183007)
  ·
    refine ⟨316716054225396589563274511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211144036150264393042183007 316716054225396589563274511)
    ·
      refine ⟨475074081338094884344911767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316716054225396589563274511 475074081338094884344911767)
      ·
        refine ⟨712611122007142326517367651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475074081338094884344911767 712611122007142326517367651)
        ·
          refine ⟨1068916683010713489776051477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712611122007142326517367651 1068916683010713489776051477)
          ·
            refine ⟨50105469516127194833252413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1068916683010713489776051477 50105469516127194833252413)
            ·
              refine ⟨18789551068547698062469655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50105469516127194833252413 18789551068547698062469655)
              ·
                refine ⟨28184326602821547093704483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18789551068547698062469655 28184326602821547093704483)
                ·
                  refine ⟨42276489904232320640556725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28184326602821547093704483 42276489904232320640556725)
                  ·
                    refine ⟨3963420928521780060052193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42276489904232320640556725 3963420928521780060052193)
                    ·
                      refine ⟨2972565696391335045039145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963420928521780060052193 2972565696391335045039145)
                      ·
                        rfl

theorem cell23_5789051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5, 2].length) (baseStart_5789051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789051 prefixEnd_5789051 := by exact prefixLift 5789051
  have htrace : WordTrace (prefixWord ++ tailWord_5789051) baseStart_5789051 baseEnd_5789051 := by
    simpa [prefixWord, tailWord_5789051, baseEnd_5789051] using wordTrace_append hprefix tailTrace_5789051
  have hstable : (prefixWord ++ tailWord_5789051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789051).length < 2 ^ (prefixWord ++ tailWord_5789051).sum := by decide
  have hdescent : baseEnd_5789051 < baseStart_5789051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789132 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5789132 : Nat := 118140960795 + 5789132 * 2 ^ 59
def prefixEnd_5789132 : Nat := 4983230072969 + 3 ^ 40 * 5789132 * 2
def baseEnd_5789132 : Nat := 2972607288324349228126273

theorem tailTrace_5789132 : CollatzResearch.WordTrace tailWord_5789132 prefixEnd_5789132 2972607288324349228126273 := by
  unfold tailWord_5789132
  simp only [CollatzResearch.WordTrace]
  refine ⟨105573495231485471937940825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140764660308647295917254433 105573495231485471937940825)
  ·
    refine ⟨79180121423614103953455619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105573495231485471937940825 79180121423614103953455619)
    ·
      refine ⟨118770182135421155930183429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79180121423614103953455619 118770182135421155930183429)
      ·
        refine ⟨22269409150391466736909393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118770182135421155930183429 22269409150391466736909393)
        ·
          refine ⟨16702056862793600052682045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22269409150391466736909393 16702056862793600052682045)
          ·
            refine ⟨6263271323547600019755767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16702056862793600052682045 6263271323547600019755767)
            ·
              refine ⟨9394906985321400029633651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263271323547600019755767 9394906985321400029633651)
              ·
                refine ⟨14092360477982100044450477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394906985321400029633651 14092360477982100044450477)
                ·
                  refine ⟨5284635179243287516668929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14092360477982100044450477 5284635179243287516668929)
                  ·
                    refine ⟨3963476384432465637501697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5284635179243287516668929 3963476384432465637501697)
                    ·
                      refine ⟨2972607288324349228126273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963476384432465637501697 2972607288324349228126273)
                      ·
                        rfl

theorem cell23_5789132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5789132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789132 prefixEnd_5789132 := by exact prefixLift 5789132
  have htrace : WordTrace (prefixWord ++ tailWord_5789132) baseStart_5789132 baseEnd_5789132 := by
    simpa [prefixWord, tailWord_5789132, baseEnd_5789132] using wordTrace_append hprefix tailTrace_5789132
  have hstable : (prefixWord ++ tailWord_5789132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789132).length < 2 ^ (prefixWord ++ tailWord_5789132).sum := by decide
  have hdescent : baseEnd_5789132 < baseStart_5789132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789142 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5789142 : Nat := 118140960795 + 5789142 * 2 ^ 59
def prefixEnd_5789142 : Nat := 4983230072969 + 3 ^ 40 * 5789142 * 2
def baseEnd_5789142 : Nat := 990870807710298063000409

theorem tailTrace_5789142 : CollatzResearch.WordTrace tailWord_5789142 prefixEnd_5789142 990870807710298063000409 := by
  unfold tailWord_5789142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196709699558419723984105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140764903461956477055830453 13196709699558419723984105)
  ·
    refine ⟨9897532274668814792988079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13196709699558419723984105 9897532274668814792988079)
    ·
      refine ⟨14846298412003222189482119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897532274668814792988079 14846298412003222189482119)
      ·
        refine ⟨22269447618004833284223179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14846298412003222189482119 22269447618004833284223179)
        ·
          refine ⟨33404171427007249926334769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22269447618004833284223179 33404171427007249926334769)
          ·
            refine ⟨25053128570255437444751077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33404171427007249926334769 25053128570255437444751077)
            ·
              refine ⟨4697461606922894520890827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25053128570255437444751077 4697461606922894520890827)
              ·
                refine ⟨7046192410384341781336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697461606922894520890827 7046192410384341781336241)
                ·
                  refine ⟨5284644307788256336002181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7046192410384341781336241 5284644307788256336002181)
                  ·
                    refine ⟨990870807710298063000409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5284644307788256336002181 990870807710298063000409)
                    ·
                      rfl

theorem cell23_5789142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5789142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789142 prefixEnd_5789142 := by exact prefixLift 5789142
  have htrace : WordTrace (prefixWord ++ tailWord_5789142) baseStart_5789142 baseEnd_5789142 := by
    simpa [prefixWord, tailWord_5789142, baseEnd_5789142] using wordTrace_append hprefix tailTrace_5789142
  have hstable : (prefixWord ++ tailWord_5789142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789142).length < 2 ^ (prefixWord ++ tailWord_5789142).sum := by decide
  have hdescent : baseEnd_5789142 < baseStart_5789142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789164 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_5789164 : Nat := 118140960795 + 5789164 * 2 ^ 59
def prefixEnd_5789164 : Nat := 4983230072969 + 3 ^ 40 * 5789164 * 2
def baseEnd_5789164 : Nat := 990874573235097700975375

theorem tailTrace_5789164 : CollatzResearch.WordTrace tailWord_5789164 prefixEnd_5789164 990874573235097700975375 := by
  unfold tailWord_5789164
  simp only [CollatzResearch.WordTrace]
  refine ⟨105574078799427506670523273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140765438399236675560697697 105574078799427506670523273)
  ·
    refine ⟨79180559099570630002892455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105574078799427506670523273 79180559099570630002892455)
    ·
      refine ⟨118770838649355945004338683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79180559099570630002892455 118770838649355945004338683)
      ·
        refine ⟨178156257974033917506508025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118770838649355945004338683 178156257974033917506508025)
        ·
          refine ⟨133617193480525438129881019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178156257974033917506508025 133617193480525438129881019)
          ·
            refine ⟨200425790220788157194821529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133617193480525438129881019 200425790220788157194821529)
            ·
              refine ⟨150319342665591117896116147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200425790220788157194821529 150319342665591117896116147)
              ·
                refine ⟨225479013998386676844174221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150319342665591117896116147 225479013998386676844174221)
                ·
                  refine ⟨84554630249395003816565333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225479013998386676844174221 84554630249395003816565333)
                  ·
                    refine ⟨990874573235097700975375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84554630249395003816565333 990874573235097700975375)
                    ·
                      rfl

theorem cell23_5789164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_5789164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789164 prefixEnd_5789164 := by exact prefixLift 5789164
  have htrace : WordTrace (prefixWord ++ tailWord_5789164) baseStart_5789164 baseEnd_5789164 := by
    simpa [prefixWord, tailWord_5789164, baseEnd_5789164] using wordTrace_append hprefix tailTrace_5789164
  have hstable : (prefixWord ++ tailWord_5789164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789164).length < 2 ^ (prefixWord ++ tailWord_5789164).sum := by decide
  have hdescent : baseEnd_5789164 < baseStart_5789164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789165 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5789165 : Nat := 118140960795 + 5789165 * 2 ^ 59
def prefixEnd_5789165 : Nat := 4983230072969 + 3 ^ 40 * 5789165 * 2
def baseEnd_5789165 : Nat := 2972624233185947599013621

theorem tailTrace_5789165 : CollatzResearch.WordTrace tailWord_5789165 prefixEnd_5789165 2972624233185947599013621 := by
  unfold tailWord_5789165
  simp only [CollatzResearch.WordTrace]
  refine ⟨211148194071851390511832949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140765462714567593674555299 211148194071851390511832949)
  ·
    refine ⟨19795143194236067860484339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211148194071851390511832949 19795143194236067860484339)
    ·
      refine ⟨29692714791354101790726509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19795143194236067860484339 29692714791354101790726509)
      ·
        refine ⟨11134768046757788171522441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29692714791354101790726509 11134768046757788171522441)
        ·
          refine ⟨8351076035068341128641831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11134768046757788171522441 8351076035068341128641831)
          ·
            refine ⟨12526614052602511692962747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351076035068341128641831 12526614052602511692962747)
            ·
              refine ⟨18789921078903767539444121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12526614052602511692962747 18789921078903767539444121)
              ·
                refine ⟨14092440809177825654583091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18789921078903767539444121 14092440809177825654583091)
                ·
                  refine ⟨21138661213766738481874637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14092440809177825654583091 21138661213766738481874637)
                  ·
                    refine ⟨7926997955162526930702989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21138661213766738481874637 7926997955162526930702989)
                    ·
                      refine ⟨2972624233185947599013621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7926997955162526930702989 2972624233185947599013621)
                      ·
                        rfl

theorem cell23_5789165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5789165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789165 prefixEnd_5789165 := by exact prefixLift 5789165
  have htrace : WordTrace (prefixWord ++ tailWord_5789165) baseStart_5789165 baseEnd_5789165 := by
    simpa [prefixWord, tailWord_5789165, baseEnd_5789165] using wordTrace_append hprefix tailTrace_5789165
  have hstable : (prefixWord ++ tailWord_5789165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789165).length < 2 ^ (prefixWord ++ tailWord_5789165).sum := by decide
  have hdescent : baseEnd_5789165 < baseStart_5789165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789198 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_5789198 : Nat := 118140960795 + 5789198 * 2 ^ 59
def prefixEnd_5789198 : Nat := 4983230072969 + 3 ^ 40 * 5789198 * 2
def baseEnd_5789198 : Nat := 990880392682515323300323

theorem tailTrace_5789198 : CollatzResearch.WordTrace tailWord_5789198 prefixEnd_5789198 990880392682515323300323 := by
  unfold tailWord_5789198
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393674710091479643473031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140766265120487891431856165 26393674710091479643473031)
  ·
    refine ⟨39590512065137219465209547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26393674710091479643473031 39590512065137219465209547)
    ·
      refine ⟨59385768097705829197814321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39590512065137219465209547 59385768097705829197814321)
      ·
        refine ⟨44539326073279371898360741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59385768097705829197814321 44539326073279371898360741)
        ·
          refine ⟨8351123638739882230942639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44539326073279371898360741 8351123638739882230942639)
          ·
            refine ⟨12526685458109823346413959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351123638739882230942639 12526685458109823346413959)
            ·
              refine ⟨18790028187164735019620939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12526685458109823346413959 18790028187164735019620939)
              ·
                refine ⟨28185042280747102529431409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18790028187164735019620939 28185042280747102529431409)
                ·
                  refine ⟨21138781710560326897073557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28185042280747102529431409 21138781710560326897073557)
                  ·
                    refine ⟨990880392682515323300323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21138781710560326897073557 990880392682515323300323)
                    ·
                      rfl

theorem cell23_5789198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_5789198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789198 prefixEnd_5789198 := by exact prefixLift 5789198
  have htrace : WordTrace (prefixWord ++ tailWord_5789198) baseStart_5789198 baseEnd_5789198 := by
    simpa [prefixWord, tailWord_5789198, baseEnd_5789198] using wordTrace_append hprefix tailTrace_5789198
  have hstable : (prefixWord ++ tailWord_5789198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789198).length < 2 ^ (prefixWord ++ tailWord_5789198).sum := by decide
  have hdescent : baseEnd_5789198 < baseStart_5789198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789201 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_5789201 : Nat := 118140960795 + 5789201 * 2 ^ 59
def prefixEnd_5789201 : Nat := 4983230072969 + 3 ^ 40 * 5789201 * 2
def baseEnd_5789201 : Nat := 2972642718489509458163455

theorem tailTrace_5789201 : CollatzResearch.WordTrace tailWord_5789201 prefixEnd_5789201 2972642718489509458163455 := by
  unfold tailWord_5789201
  simp only [CollatzResearch.WordTrace]
  refine ⟨211149507099720968660143457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140766338066480645773428971 211149507099720968660143457)
  ·
    refine ⟨158362130324790726495107593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211149507099720968660143457 158362130324790726495107593)
    ·
      refine ⟨118771597743593044871330695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158362130324790726495107593 118771597743593044871330695)
      ·
        refine ⟨178157396615389567306996043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118771597743593044871330695 178157396615389567306996043)
        ·
          refine ⟨267236094923084350960494065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178157396615389567306996043 267236094923084350960494065)
          ·
            refine ⟨200427071192313263220370549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267236094923084350960494065 200427071192313263220370549)
            ·
              refine ⟨18790037924279368426909739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200427071192313263220370549 18790037924279368426909739)
              ·
                refine ⟨28185056886419052640364609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18790037924279368426909739 28185056886419052640364609)
                ·
                  refine ⟨21138792664814289480273457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28185056886419052640364609 21138792664814289480273457)
                  ·
                    refine ⟨15854094498610717110205093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21138792664814289480273457 15854094498610717110205093)
                    ·
                      refine ⟨2972642718489509458163455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15854094498610717110205093 2972642718489509458163455)
                      ·
                        rfl

theorem cell23_5789201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_5789201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789201 prefixEnd_5789201 := by exact prefixLift 5789201
  have htrace : WordTrace (prefixWord ++ tailWord_5789201) baseStart_5789201 baseEnd_5789201 := by
    simpa [prefixWord, tailWord_5789201, baseEnd_5789201] using wordTrace_append hprefix tailTrace_5789201
  have hstable : (prefixWord ++ tailWord_5789201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789201).length < 2 ^ (prefixWord ++ tailWord_5789201).sum := by decide
  have hdescent : baseEnd_5789201 < baseStart_5789201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789205 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_5789205 : Nat := 118140960795 + 5789205 * 2 ^ 59
def prefixEnd_5789205 : Nat := 4983230072969 + 3 ^ 40 * 5789205 * 2
def baseEnd_5789205 : Nat := 2972644772412127442513437

theorem tailTrace_5789205 : CollatzResearch.WordTrace tailWord_5789205 prefixEnd_5789205 2972644772412127442513437 := by
  unfold tailWord_5789205
  simp only [CollatzResearch.WordTrace]
  refine ⟨211149652991706477343289069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140766435327804318228859379 211149652991706477343289069)
  ·
    refine ⟨79181119871889929003733401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211149652991706477343289069 79181119871889929003733401)
    ·
      refine ⟨59385839903917446752800051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79181119871889929003733401 59385839903917446752800051)
      ·
        refine ⟨89078759855876170129200077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59385839903917446752800051 89078759855876170129200077)
        ·
          refine ⟨33404534945953563798450029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89078759855876170129200077 33404534945953563798450029)
          ·
            refine ⟨12526700604732586424418761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33404534945953563798450029 12526700604732586424418761)
            ·
              refine ⟨9395025453549439818314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12526700604732586424418761 9395025453549439818314071)
              ·
                refine ⟨14092538180324159727471107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395025453549439818314071 14092538180324159727471107)
                ·
                  refine ⟨21138807270486239591206661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14092538180324159727471107 21138807270486239591206661)
                  ·
                    refine ⟨3963526363216169923351249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21138807270486239591206661 3963526363216169923351249)
                    ·
                      refine ⟨2972644772412127442513437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963526363216169923351249 2972644772412127442513437)
                      ·
                        rfl

theorem cell23_5789205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_5789205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789205 prefixEnd_5789205 := by exact prefixLift 5789205
  have htrace : WordTrace (prefixWord ++ tailWord_5789205) baseStart_5789205 baseEnd_5789205 := by
    simpa [prefixWord, tailWord_5789205, baseEnd_5789205] using wordTrace_append hprefix tailTrace_5789205
  have hstable : (prefixWord ++ tailWord_5789205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789205).length < 2 ^ (prefixWord ++ tailWord_5789205).sum := by decide
  have hdescent : baseEnd_5789205 < baseStart_5789205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789221 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_5789221 : Nat := 118140960795 + 5789221 * 2 ^ 59
def prefixEnd_5789221 : Nat := 4983230072969 + 3 ^ 40 * 5789221 * 2
def baseEnd_5789221 : Nat := 2972652988102599379913363

theorem tailTrace_5789221 : CollatzResearch.WordTrace tailWord_5789221 prefixEnd_5789221 2972652988102599379913363 := by
  unfold tailWord_5789221
  simp only [CollatzResearch.WordTrace]
  refine ⟨211150236559648512075871517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140766824373099008050581011 211150236559648512075871517)
  ·
    refine ⟨79181338709868192028451819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211150236559648512075871517 79181338709868192028451819)
    ·
      refine ⟨118772008064802288042677729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79181338709868192028451819 118772008064802288042677729)
      ·
        refine ⟨89079006048601716032008297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118772008064802288042677729 89079006048601716032008297)
        ·
          refine ⟨66809254536451287024006223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89079006048601716032008297 66809254536451287024006223)
          ·
            refine ⟨100213881804676930536009335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66809254536451287024006223 100213881804676930536009335)
            ·
              refine ⟨150320822707015395804014003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100213881804676930536009335 150320822707015395804014003)
              ·
                refine ⟨225481234060523093706021005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150320822707015395804014003 225481234060523093706021005)
                ·
                  refine ⟨84555462772696160139757877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225481234060523093706021005 84555462772696160139757877)
                  ·
                    refine ⟨7927074634940265013102301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84555462772696160139757877 7927074634940265013102301)
                    ·
                      refine ⟨2972652988102599379913363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7927074634940265013102301 2972652988102599379913363)
                      ·
                        rfl

theorem cell23_5789221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_5789221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789221 prefixEnd_5789221 := by exact prefixLift 5789221
  have htrace : WordTrace (prefixWord ++ tailWord_5789221) baseStart_5789221 baseEnd_5789221 := by
    simpa [prefixWord, tailWord_5789221, baseEnd_5789221] using wordTrace_append hprefix tailTrace_5789221
  have hstable : (prefixWord ++ tailWord_5789221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789221).length < 2 ^ (prefixWord ++ tailWord_5789221).sum := by decide
  have hdescent : baseEnd_5789221 < baseStart_5789221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789321 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_5789321 : Nat := 118140960795 + 5789321 * 2 ^ 59
def prefixEnd_5789321 : Nat := 4983230072969 + 3 ^ 40 * 5789321 * 2
def baseEnd_5789321 : Nat := 2972704336168048988662903

theorem tailTrace_5789321 : CollatzResearch.WordTrace tailWord_5789321 prefixEnd_5789321 2972704336168048988662903 := by
  unfold tailWord_5789321
  simp only [CollatzResearch.WordTrace]
  refine ⟨211153883859286229154511817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140769255906190819436341211 211153883859286229154511817)
  ·
    refine ⟨158365412894464671865883863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211153883859286229154511817 158365412894464671865883863)
    ·
      refine ⟨237548119341697007798825795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158365412894464671865883863 237548119341697007798825795)
      ·
        refine ⟨356322179012545511698238693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237548119341697007798825795 356322179012545511698238693)
        ·
          refine ⟨66810408564852283443419755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356322179012545511698238693 66810408564852283443419755)
          ·
            refine ⟨100215612847278425165129633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66810408564852283443419755 100215612847278425165129633)
            ·
              refine ⟨75161709635458818873847225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100215612847278425165129633 75161709635458818873847225)
              ·
                refine ⟨56371282226594114155385419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75161709635458818873847225 56371282226594114155385419)
                ·
                  refine ⟨84556923339891171233078129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56371282226594114155385419 84556923339891171233078129)
                  ·
                    refine ⟨63417692504918378424808597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84556923339891171233078129 63417692504918378424808597)
                    ·
                      refine ⟨2972704336168048988662903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63417692504918378424808597 2972704336168048988662903)
                      ·
                        rfl

theorem cell23_5789321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_5789321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789321 prefixEnd_5789321 := by exact prefixLift 5789321
  have htrace : WordTrace (prefixWord ++ tailWord_5789321) baseStart_5789321 baseEnd_5789321 := by
    simpa [prefixWord, tailWord_5789321, baseEnd_5789321] using wordTrace_append hprefix tailTrace_5789321
  have hstable : (prefixWord ++ tailWord_5789321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789321).length < 2 ^ (prefixWord ++ tailWord_5789321).sum := by decide
  have hdescent : baseEnd_5789321 < baseStart_5789321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789389 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5789389 : Nat := 118140960795 + 5789389 * 2 ^ 59
def prefixEnd_5789389 : Nat := 4983230072969 + 3 ^ 40 * 5789389 * 2
def baseEnd_5789389 : Nat := 2972739252852554722612591

theorem tailTrace_5789389 : CollatzResearch.WordTrace tailWord_5789389 prefixEnd_5789389 2972739252852554722612591 := by
  unfold tailWord_5789389
  simp only [CollatzResearch.WordTrace]
  refine ⟨211156364023039876767987221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140770909348693251178658147 211156364023039876767987221)
  ·
    refine ⟨9897954563579994223499401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211156364023039876767987221 9897954563579994223499401)
    ·
      refine ⟨7423465922684995667624551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9897954563579994223499401 7423465922684995667624551)
      ·
        refine ⟨11135198884027493501436827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423465922684995667624551 11135198884027493501436827)
        ·
          refine ⟨16702798326041240252155241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11135198884027493501436827 16702798326041240252155241)
          ·
            refine ⟨12527098744530930189116431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16702798326041240252155241 12527098744530930189116431)
            ·
              refine ⟨18790648116796395283674647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527098744530930189116431 18790648116796395283674647)
              ·
                refine ⟨28185972175194592925511971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18790648116796395283674647 28185972175194592925511971)
                ·
                  refine ⟨42278958262791889388267957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28185972175194592925511971 42278958262791889388267957)
                  ·
                    refine ⟨3963652337136739630150121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42278958262791889388267957 3963652337136739630150121)
                    ·
                      refine ⟨2972739252852554722612591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963652337136739630150121 2972739252852554722612591)
                      ·
                        rfl

theorem cell23_5789389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5789389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789389 prefixEnd_5789389 := by exact prefixLift 5789389
  have htrace : WordTrace (prefixWord ++ tailWord_5789389) baseStart_5789389 baseEnd_5789389 := by
    simpa [prefixWord, tailWord_5789389, baseEnd_5789389] using wordTrace_append hprefix tailTrace_5789389
  have hstable : (prefixWord ++ tailWord_5789389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789389).length < 2 ^ (prefixWord ++ tailWord_5789389).sum := by decide
  have hdescent : baseEnd_5789389 < baseStart_5789389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789391 : List Nat := [1, 1, 2, 1, 1, 3, 1, 13]
def baseStart_5789391 : Nat := 118140960795 + 5789391 * 2 ^ 59
def prefixEnd_5789391 : Nat := 4983230072969 + 3 ^ 40 * 5789391 * 2
def baseEnd_5789391 : Nat := 110101491844957915362503

theorem tailTrace_5789391 : CollatzResearch.WordTrace tailWord_5789391 prefixEnd_5789391 110101491844957915362503 := by
  unfold tailWord_5789391
  simp only [CollatzResearch.WordTrace]
  refine ⟨211156436969032631109560027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140770957979355087406373351 211156436969032631109560027)
  ·
    refine ⟨316734655453548946664340041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211156436969032631109560027 316734655453548946664340041)
    ·
      refine ⟨237550991590161709998255031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316734655453548946664340041 237550991590161709998255031)
      ·
        refine ⟨356326487385242564997382547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237550991590161709998255031 356326487385242564997382547)
        ·
          refine ⟨534489731077863847496073821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356326487385242564997382547 534489731077863847496073821)
          ·
            refine ⟨200433649154198942811027683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534489731077863847496073821 200433649154198942811027683)
            ·
              refine ⟨300650473731298414216541525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200433649154198942811027683 300650473731298414216541525)
              ·
                refine ⟨110101491844957915362503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 300650473731298414216541525 110101491844957915362503)
                ·
                  rfl

theorem cell23_5789391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 13].length) (baseStart_5789391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789391 prefixEnd_5789391 := by exact prefixLift 5789391
  have htrace : WordTrace (prefixWord ++ tailWord_5789391) baseStart_5789391 baseEnd_5789391 := by
    simpa [prefixWord, tailWord_5789391, baseEnd_5789391] using wordTrace_append hprefix tailTrace_5789391
  have hstable : (prefixWord ++ tailWord_5789391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789391).length < 2 ^ (prefixWord ++ tailWord_5789391).sum := by decide
  have hdescent : baseEnd_5789391 < baseStart_5789391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789396 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5789396 : Nat := 118140960795 + 5789396 * 2 ^ 59
def prefixEnd_5789396 : Nat := 4983230072969 + 3 ^ 40 * 5789396 * 2
def baseEnd_5789396 : Nat := 2972742847217136195225059

theorem tailTrace_5789396 : CollatzResearch.WordTrace tailWord_5789396 prefixEnd_5789396 2972742847217136195225059 := by
  unfold tailWord_5789396
  simp only [CollatzResearch.WordTrace]
  refine ⟨105578309667007258481746021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140771079556009677975661361 105578309667007258481746021)
  ·
    refine ⟨19795933062563860965327379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105578309667007258481746021 19795933062563860965327379)
    ·
      refine ⟨29693899593845791447991069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19795933062563860965327379 29693899593845791447991069)
      ·
        refine ⟨11135212347692171792996651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29693899593845791447991069 11135212347692171792996651)
        ·
          refine ⟨16702818521538257689494977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11135212347692171792996651 16702818521538257689494977)
          ·
            refine ⟨12527113891153693267121233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16702818521538257689494977 12527113891153693267121233)
            ·
              refine ⟨9395335418365269950340925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12527113891153693267121233 9395335418365269950340925)
              ·
                refine ⟨3523250781886976231377847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9395335418365269950340925 3523250781886976231377847)
                ·
                  refine ⟨5284876172830464347066771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523250781886976231377847 5284876172830464347066771)
                  ·
                    refine ⟨7927314259245696520600157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5284876172830464347066771 7927314259245696520600157)
                    ·
                      refine ⟨2972742847217136195225059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7927314259245696520600157 2972742847217136195225059)
                      ·
                        rfl

theorem cell23_5789396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5789396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789396 prefixEnd_5789396 := by exact prefixLift 5789396
  have htrace : WordTrace (prefixWord ++ tailWord_5789396) baseStart_5789396 baseEnd_5789396 := by
    simpa [prefixWord, tailWord_5789396, baseEnd_5789396] using wordTrace_append hprefix tailTrace_5789396
  have hstable : (prefixWord ++ tailWord_5789396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789396).length < 2 ^ (prefixWord ++ tailWord_5789396).sum := by decide
  have hdescent : baseEnd_5789396 < baseStart_5789396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789402 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_5789402 : Nat := 118140960795 + 5789402 * 2 ^ 59
def prefixEnd_5789402 : Nat := 4983230072969 + 3 ^ 40 * 5789402 * 2
def baseEnd_5789402 : Nat := 2972745928101063171750031

theorem tailTrace_5789402 : CollatzResearch.WordTrace tailWord_5789402 prefixEnd_5789402 2972745928101063171750031 := by
  unfold tailWord_5789402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52789209542998194997052615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140771225447995186658806973 52789209542998194997052615)
  ·
    refine ⟨79183814314497292495578923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52789209542998194997052615 79183814314497292495578923)
    ·
      refine ⟨118775721471745938743368385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79183814314497292495578923 118775721471745938743368385)
      ·
        refine ⟨89081791103809454057526289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118775721471745938743368385 89081791103809454057526289)
        ·
          refine ⟨66811343327857090543144717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89081791103809454057526289 66811343327857090543144717)
          ·
            refine ⟨25054253747946408953679269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66811343327857090543144717 25054253747946408953679269)
            ·
              refine ⟨4697672577739951678814863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25054253747946408953679269 4697672577739951678814863)
              ·
                refine ⟨7046508866609927518222295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697672577739951678814863 7046508866609927518222295)
                ·
                  refine ⟨10569763299914891277333443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7046508866609927518222295 10569763299914891277333443)
                  ·
                    refine ⟨15854644949872336916000165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10569763299914891277333443 15854644949872336916000165)
                    ·
                      refine ⟨2972745928101063171750031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15854644949872336916000165 2972745928101063171750031)
                      ·
                        rfl

theorem cell23_5789402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_5789402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789402 prefixEnd_5789402 := by exact prefixLift 5789402
  have htrace : WordTrace (prefixWord ++ tailWord_5789402) baseStart_5789402 baseEnd_5789402 := by
    simpa [prefixWord, tailWord_5789402, baseEnd_5789402] using wordTrace_append hprefix tailTrace_5789402
  have hstable : (prefixWord ++ tailWord_5789402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789402).length < 2 ^ (prefixWord ++ tailWord_5789402).sum := by decide
  have hdescent : baseEnd_5789402 < baseStart_5789402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789419 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 1, 2, 2]
def baseStart_5789419 : Nat := 118140960795 + 5789419 * 2 ^ 59
def prefixEnd_5789419 : Nat := 4983230072969 + 3 ^ 40 * 5789419 * 2
def baseEnd_5789419 : Nat := 2972754657272189605237453

theorem tailTrace_5789419 : CollatzResearch.WordTrace tailWord_5789419 prefixEnd_5789419 2972754657272189605237453 := by
  unfold tailWord_5789419
  simp only [CollatzResearch.WordTrace]
  refine ⟨211157458212931191891579311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140771638808620794594386207 211157458212931191891579311)
  ·
    refine ⟨316736187319396787837368967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211157458212931191891579311 316736187319396787837368967)
    ·
      refine ⟨475104280979095181756053451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316736187319396787837368967 475104280979095181756053451)
      ·
        refine ⟨712656421468642772634080177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475104280979095181756053451 712656421468642772634080177)
        ·
          refine ⟨534492316101482079475560133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712656421468642772634080177 534492316101482079475560133)
          ·
            refine ⟨100217309269027889901667525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 534492316101482079475560133 100217309269027889901667525)
            ·
              refine ⟨18790745487942729356562661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100217309269027889901667525 18790745487942729356562661)
              ·
                refine ⟨3523264778989261754355499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18790745487942729356562661 3523264778989261754355499)
                ·
                  refine ⟨5284897168483892631533249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523264778989261754355499 5284897168483892631533249)
                  ·
                    refine ⟨3963672876362919473649937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5284897168483892631533249 3963672876362919473649937)
                    ·
                      refine ⟨2972754657272189605237453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963672876362919473649937 2972754657272189605237453)
                      ·
                        rfl

theorem cell23_5789419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 2, 2].length) (baseStart_5789419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789419 prefixEnd_5789419 := by exact prefixLift 5789419
  have htrace : WordTrace (prefixWord ++ tailWord_5789419) baseStart_5789419 baseEnd_5789419 := by
    simpa [prefixWord, tailWord_5789419, baseEnd_5789419] using wordTrace_append hprefix tailTrace_5789419
  have hstable : (prefixWord ++ tailWord_5789419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789419).length < 2 ^ (prefixWord ++ tailWord_5789419).sum := by decide
  have hdescent : baseEnd_5789419 < baseStart_5789419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789448 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5789448 : Nat := 118140960795 + 5789448 * 2 ^ 59
def prefixEnd_5789448 : Nat := 4983230072969 + 3 ^ 40 * 5789448 * 2
def baseEnd_5789448 : Nat := 2972769548211169991774819

theorem tailTrace_5789448 : CollatzResearch.WordTrace tailWord_5789448 prefixEnd_5789448 2972769548211169991774819 := by
  unfold tailWord_5789448
  simp only [CollatzResearch.WordTrace]
  refine ⟨105579257964913064922192499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140772343953217419896256665 105579257964913064922192499)
  ·
    refine ⟨158368886947369597383288749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105579257964913064922192499 158368886947369597383288749)
    ·
      refine ⟨59388332605263599018733281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158368886947369597383288749 59388332605263599018733281)
      ·
        refine ⟨44541249453947699264049961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59388332605263599018733281 44541249453947699264049961)
        ·
          refine ⟨33405937090460774448037471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44541249453947699264049961 33405937090460774448037471)
          ·
            refine ⟨50108905635691161672056207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33405937090460774448037471 50108905635691161672056207)
            ·
              refine ⟨75163358453536742508084311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50108905635691161672056207 75163358453536742508084311)
              ·
                refine ⟨112745037680305113762126467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75163358453536742508084311 112745037680305113762126467)
                ·
                  refine ⟨169117556520457670643189701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112745037680305113762126467 169117556520457670643189701)
                  ·
                    refine ⟨31709541847585813245598069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169117556520457670643189701 31709541847585813245598069)
                    ·
                      refine ⟨2972769548211169991774819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31709541847585813245598069 2972769548211169991774819)
                      ·
                        rfl

theorem cell23_5789448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5789448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789448 prefixEnd_5789448 := by exact prefixLift 5789448
  have htrace : WordTrace (prefixWord ++ tailWord_5789448) baseStart_5789448 baseEnd_5789448 := by
    simpa [prefixWord, tailWord_5789448, baseEnd_5789448] using wordTrace_append hprefix tailTrace_5789448
  have hstable : (prefixWord ++ tailWord_5789448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789448).length < 2 ^ (prefixWord ++ tailWord_5789448).sum := by decide
  have hdescent : baseEnd_5789448 < baseStart_5789448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789470 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5789470 : Nat := 118140960795 + 5789470 * 2 ^ 59
def prefixEnd_5789470 : Nat := 4983230072969 + 3 ^ 40 * 5789470 * 2
def baseEnd_5789470 : Nat := 2972780844785568905699719

theorem tailTrace_5789470 : CollatzResearch.WordTrace tailWord_5789470 prefixEnd_5789470 2972780844785568905699719 := by
  unfold tailWord_5789470
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394914791968303450210733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140772878890497618401123909 26394914791968303450210733)
  ·
    refine ⟨9898093046988113793829025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26394914791968303450210733 9898093046988113793829025)
    ·
      refine ⟨7423569785241085345371769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9898093046988113793829025 7423569785241085345371769)
      ·
        refine ⟨5567677338930814009028827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7423569785241085345371769 5567677338930814009028827)
        ·
          refine ⟨8351516008396221013543241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567677338930814009028827 8351516008396221013543241)
          ·
            refine ⟨6263637006297165760157431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351516008396221013543241 6263637006297165760157431)
            ·
              refine ⟨9395455509445748640236147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263637006297165760157431 9395455509445748640236147)
              ·
                refine ⟨14093183264168622960354221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395455509445748640236147 14093183264168622960354221)
                ·
                  refine ⟨5284943724063233610132833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14093183264168622960354221 5284943724063233610132833)
                  ·
                    refine ⟨3963707793047425207599625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5284943724063233610132833 3963707793047425207599625)
                    ·
                      refine ⟨2972780844785568905699719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3963707793047425207599625 2972780844785568905699719)
                      ·
                        rfl

theorem cell23_5789470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5789470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789470 prefixEnd_5789470 := by exact prefixLift 5789470
  have htrace : WordTrace (prefixWord ++ tailWord_5789470) baseStart_5789470 baseEnd_5789470 := by
    simpa [prefixWord, tailWord_5789470, baseEnd_5789470] using wordTrace_append hprefix tailTrace_5789470
  have hstable : (prefixWord ++ tailWord_5789470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789470).length < 2 ^ (prefixWord ++ tailWord_5789470).sum := by decide
  have hdescent : baseEnd_5789470 < baseStart_5789470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789486 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5789486 : Nat := 118140960795 + 5789486 * 2 ^ 59
def prefixEnd_5789486 : Nat := 4983230072969 + 3 ^ 40 * 5789486 * 2
def baseEnd_5789486 : Nat := 2972789060476040843099645

theorem tailTrace_5789486 : CollatzResearch.WordTrace tailWord_5789486 prefixEnd_5789486 2972789060476040843099645 := by
  unfold tailWord_5789486
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394987737961057791783539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140773267935792308222845541 26394987737961057791783539)
  ·
    refine ⟨39592481606941586687675309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26394987737961057791783539 39592481606941586687675309)
    ·
      refine ⟨14847180602603095007878241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39592481606941586687675309 14847180602603095007878241)
      ·
        refine ⟨11135385451952321255908681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14847180602603095007878241 11135385451952321255908681)
        ·
          refine ⟨8351539088964240941931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11135385451952321255908681 8351539088964240941931511)
          ·
            refine ⟨12527308633446361412897267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351539088964240941931511 12527308633446361412897267)
            ·
              refine ⟨18790962950169542119345901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527308633446361412897267 18790962950169542119345901)
              ·
                refine ⟨7046611106313578294754713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18790962950169542119345901 7046611106313578294754713)
                ·
                  refine ⟨5284958329735183721066035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7046611106313578294754713 5284958329735183721066035)
                  ·
                    refine ⟨7927437494602775581599053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5284958329735183721066035 7927437494602775581599053)
                    ·
                      refine ⟨2972789060476040843099645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7927437494602775581599053 2972789060476040843099645)
                      ·
                        rfl

theorem cell23_5789486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5789486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789486 prefixEnd_5789486 := by exact prefixLift 5789486
  have htrace : WordTrace (prefixWord ++ tailWord_5789486) baseStart_5789486 baseEnd_5789486 := by
    simpa [prefixWord, tailWord_5789486, baseEnd_5789486] using wordTrace_append hprefix tailTrace_5789486
  have hstable : (prefixWord ++ tailWord_5789486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789486).length < 2 ^ (prefixWord ++ tailWord_5789486).sum := by decide
  have hdescent : baseEnd_5789486 < baseStart_5789486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789528 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_5789528 : Nat := 118140960795 + 5789528 * 2 ^ 59
def prefixEnd_5789528 : Nat := 4983230072969 + 3 ^ 40 * 5789528 * 2
def baseEnd_5789528 : Nat := 990936875554509892924817

theorem tailTrace_5789528 : CollatzResearch.WordTrace tailWord_5789528 prefixEnd_5789528 990936875554509892924817 := by
  unfold tailWord_5789528
  simp only [CollatzResearch.WordTrace]
  refine ⟨105580716884768151753648619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140774289179690869004864825 105580716884768151753648619)
  ·
    refine ⟨158371075327152227630472929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105580716884768151753648619 158371075327152227630472929)
    ·
      refine ⟨118778306495364170722854697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158371075327152227630472929 118778306495364170722854697)
      ·
        refine ⟨89083729871523128042141023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118778306495364170722854697 89083729871523128042141023)
        ·
          refine ⟨133625594807284692063211535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89083729871523128042141023 133625594807284692063211535)
          ·
            refine ⟨200438392210927038094817303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133625594807284692063211535 200438392210927038094817303)
            ·
              refine ⟨300657588316390557142225955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200438392210927038094817303 300657588316390557142225955)
              ·
                refine ⟨450986382474585835713338933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300657588316390557142225955 450986382474585835713338933)
                ·
                  refine ⟨42279973356992422098125525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450986382474585835713338933 42279973356992422098125525)
                  ·
                    refine ⟨990936875554509892924817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42279973356992422098125525 990936875554509892924817)
                    ·
                      rfl

theorem cell23_5789528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_5789528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789528 prefixEnd_5789528 := by exact prefixLift 5789528
  have htrace : WordTrace (prefixWord ++ tailWord_5789528) baseStart_5789528 baseEnd_5789528 := by
    simpa [prefixWord, tailWord_5789528, baseEnd_5789528] using wordTrace_append hprefix tailTrace_5789528
  have hstable : (prefixWord ++ tailWord_5789528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789528).length < 2 ^ (prefixWord ++ tailWord_5789528).sum := by decide
  have hdescent : baseEnd_5789528 < baseStart_5789528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789566 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_5789566 : Nat := 118140960795 + 5789566 * 2 ^ 59
def prefixEnd_5789566 : Nat := 4983230072969 + 3 ^ 40 * 5789566 * 2
def baseEnd_5789566 : Nat := 330314459880933392233253

theorem tailTrace_5789566 : CollatzResearch.WordTrace tailWord_5789566 prefixEnd_5789566 330314459880933392233253 := by
  unfold tailWord_5789566
  simp only [CollatzResearch.WordTrace]
  refine ⟨26395352467924829499647569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140775213162265757331453701 26395352467924829499647569)
  ·
    refine ⟨19796514350943622124735677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26395352467924829499647569 19796514350943622124735677)
    ·
      refine ⟨7423692881603858296775879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19796514350943622124735677 7423692881603858296775879)
      ·
        refine ⟨11135539322405787445163819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423692881603858296775879 11135539322405787445163819)
        ·
          refine ⟨16703308983608681167745729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11135539322405787445163819 16703308983608681167745729)
          ·
            refine ⟨12527481737706510875809297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16703308983608681167745729 12527481737706510875809297)
            ·
              refine ⟨9395611303279883156856973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12527481737706510875809297 9395611303279883156856973)
              ·
                refine ⟨3523354238729956183821365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9395611303279883156856973 3523354238729956183821365)
                ·
                  refine ⟨330314459880933392233253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523354238729956183821365 330314459880933392233253)
                  ·
                    rfl

theorem cell23_5789566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_5789566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789566 prefixEnd_5789566 := by exact prefixLift 5789566
  have htrace : WordTrace (prefixWord ++ tailWord_5789566) baseStart_5789566 baseEnd_5789566 := by
    simpa [prefixWord, tailWord_5789566, baseEnd_5789566] using wordTrace_append hprefix tailTrace_5789566
  have hstable : (prefixWord ++ tailWord_5789566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789566).length < 2 ^ (prefixWord ++ tailWord_5789566).sum := by decide
  have hdescent : baseEnd_5789566 < baseStart_5789566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789605 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 6]
def baseStart_5789605 : Nat := 118140960795 + 5789605 * 2 ^ 59
def prefixEnd_5789605 : Nat := 4983230072969 + 3 ^ 40 * 5789605 * 2
def baseEnd_5789605 : Nat := 330316684963769541945733

theorem tailTrace_5789605 : CollatzResearch.WordTrace tailWord_5789605 prefixEnd_5789605 330316684963769541945733 := by
  unfold tailWord_5789605
  simp only [CollatzResearch.WordTrace]
  refine ⟨211164242190257345657850269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140776161460171563771900179 211164242190257345657850269)
  ·
    refine ⟨79186590821346504621693851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211164242190257345657850269 79186590821346504621693851)
    ·
      refine ⟨118779886232019756932540777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79186590821346504621693851 118779886232019756932540777)
      ·
        refine ⟨89084914674014817699405583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118779886232019756932540777 89084914674014817699405583)
        ·
          refine ⟨133627372011022226549108375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89084914674014817699405583 133627372011022226549108375)
          ·
            refine ⟨200441058016533339823662563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133627372011022226549108375 200441058016533339823662563)
            ·
              refine ⟨300661587024800009735493845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200441058016533339823662563 300661587024800009735493845)
              ·
                refine ⟨7046755945893750228175637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300661587024800009735493845 7046755945893750228175637)
                ·
                  refine ⟨330316684963769541945733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7046755945893750228175637 330316684963769541945733)
                  ·
                    rfl

theorem cell23_5789605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_5789605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789605 prefixEnd_5789605 := by exact prefixLift 5789605
  have htrace : WordTrace (prefixWord ++ tailWord_5789605) baseStart_5789605 baseEnd_5789605 := by
    simpa [prefixWord, tailWord_5789605, baseEnd_5789605] using wordTrace_append hprefix tailTrace_5789605
  have hstable : (prefixWord ++ tailWord_5789605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789605).length < 2 ^ (prefixWord ++ tailWord_5789605).sum := by decide
  have hdescent : baseEnd_5789605 < baseStart_5789605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789615 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_5789615 : Nat := 118140960795 + 5789615 * 2 ^ 59
def prefixEnd_5789615 : Nat := 4983230072969 + 3 ^ 40 * 5789615 * 2
def baseEnd_5789615 : Nat := 2972855299480470838386551

theorem tailTrace_5789615 : CollatzResearch.WordTrace tailWord_5789615 prefixEnd_5789615 2972855299480470838386551 := by
  unfold tailWord_5789615
  simp only [CollatzResearch.WordTrace]
  refine ⟨211164606920221117365714299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140776404613480744910476199 211164606920221117365714299)
  ·
    refine ⟨316746910380331676048571449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211164606920221117365714299 316746910380331676048571449)
    ·
      refine ⟨237560182785248757036428587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316746910380331676048571449 237560182785248757036428587)
      ·
        refine ⟨356340274177873135554642881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237560182785248757036428587 356340274177873135554642881)
        ·
          refine ⟨267255205633404851665982161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356340274177873135554642881 267255205633404851665982161)
          ·
            refine ⟨200441404225053638749486621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267255205633404851665982161 200441404225053638749486621)
            ·
              refine ⟨75165526584395114531057483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200441404225053638749486621 75165526584395114531057483)
              ·
                refine ⟨112748289876592671796586225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75165526584395114531057483 112748289876592671796586225)
                ·
                  refine ⟨84561217407444503847439669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112748289876592671796586225 84561217407444503847439669)
                  ·
                    refine ⟨7927614131947922235697469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84561217407444503847439669 7927614131947922235697469)
                    ·
                      refine ⟨2972855299480470838386551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7927614131947922235697469 2972855299480470838386551)
                      ·
                        rfl

theorem cell23_5789615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_5789615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789615 prefixEnd_5789615 := by exact prefixLift 5789615
  have htrace : WordTrace (prefixWord ++ tailWord_5789615) baseStart_5789615 baseEnd_5789615 := by
    simpa [prefixWord, tailWord_5789615, baseEnd_5789615] using wordTrace_append hprefix tailTrace_5789615
  have hstable : (prefixWord ++ tailWord_5789615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789615).length < 2 ^ (prefixWord ++ tailWord_5789615).sum := by decide
  have hdescent : baseEnd_5789615 < baseStart_5789615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789652 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_5789652 : Nat := 118140960795 + 5789652 * 2 ^ 59
def prefixEnd_5789652 : Nat := 4983230072969 + 3 ^ 40 * 5789652 * 2
def baseEnd_5789652 : Nat := 990958099421562397874627

theorem tailTrace_5789652 : CollatzResearch.WordTrace tailWord_5789652 prefixEnd_5789652 990958099421562397874627 := by
  unfold tailWord_5789652
  simp only [CollatzResearch.WordTrace]
  refine ⟨105582978210543536342405605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140777304280724715123207473 105582978210543536342405605)
  ·
    refine ⟨19796808414476913064201051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105582978210543536342405605 19796808414476913064201051)
    ·
      refine ⟨29695212621715369596301577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19796808414476913064201051 29695212621715369596301577)
      ·
        refine ⟨22271409466286527197226183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29695212621715369596301577 22271409466286527197226183)
        ·
          refine ⟨33407114199429790795839275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22271409466286527197226183 33407114199429790795839275)
          ·
            refine ⟨50110671299144686193758913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33407114199429790795839275 50110671299144686193758913)
            ·
              refine ⟨37583003474358514645319185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50110671299144686193758913 37583003474358514645319185)
              ·
                refine ⟨28187252605768885983989389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37583003474358514645319185 28187252605768885983989389)
                ·
                  refine ⟨10570219727163332243996021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28187252605768885983989389 10570219727163332243996021)
                  ·
                    refine ⟨990958099421562397874627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10570219727163332243996021 990958099421562397874627)
                    ·
                      rfl

theorem cell23_5789652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_5789652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789652 prefixEnd_5789652 := by exact prefixLift 5789652
  have htrace : WordTrace (prefixWord ++ tailWord_5789652) baseStart_5789652 baseEnd_5789652 := by
    simpa [prefixWord, tailWord_5789652, baseEnd_5789652] using wordTrace_append hprefix tailTrace_5789652
  have hstable : (prefixWord ++ tailWord_5789652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789652).length < 2 ^ (prefixWord ++ tailWord_5789652).sum := by decide
  have hdescent : baseEnd_5789652 < baseStart_5789652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789675 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_5789675 : Nat := 118140960795 + 5789675 * 2 ^ 59
def prefixEnd_5789675 : Nat := 4983230072969 + 3 ^ 40 * 5789675 * 2
def baseEnd_5789675 : Nat := 2972886108319740603636275

theorem tailTrace_5789675 : CollatzResearch.WordTrace tailWord_5789675 prefixEnd_5789675 2972886108319740603636275 := by
  unfold tailWord_5789675
  simp only [CollatzResearch.WordTrace]
  refine ⟨211166795300003747612898479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140777863533335831741932319 211166795300003747612898479)
  ·
    refine ⟨316750192950005621419347719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211166795300003747612898479 316750192950005621419347719)
    ·
      refine ⟨475125289425008432129021579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316750192950005621419347719 475125289425008432129021579)
      ·
        refine ⟨712687934137512648193532369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475125289425008432129021579 712687934137512648193532369)
        ·
          refine ⟨534515950603134486145149277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712687934137512648193532369 534515950603134486145149277)
          ·
            refine ⟨200443481476175432304430979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534515950603134486145149277 200443481476175432304430979)
            ·
              refine ⟨300665222214263148456646469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200443481476175432304430979 300665222214263148456646469)
              ·
                refine ⟨56374729165174340335621213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300665222214263148456646469 56374729165174340335621213)
                ·
                  refine ⟨21140523436940377625857955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56374729165174340335621213 21140523436940377625857955)
                  ·
                    refine ⟨31710785155410566438786933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21140523436940377625857955 31710785155410566438786933)
                    ·
                      refine ⟨2972886108319740603636275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31710785155410566438786933 2972886108319740603636275)
                      ·
                        rfl

theorem cell23_5789675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_5789675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789675 prefixEnd_5789675 := by exact prefixLift 5789675
  have htrace : WordTrace (prefixWord ++ tailWord_5789675) baseStart_5789675 baseEnd_5789675 := by
    simpa [prefixWord, tailWord_5789675, baseEnd_5789675] using wordTrace_append hprefix tailTrace_5789675
  have hstable : (prefixWord ++ tailWord_5789675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789675).length < 2 ^ (prefixWord ++ tailWord_5789675).sum := by decide
  have hdescent : baseEnd_5789675 < baseStart_5789675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789700 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5789700 : Nat := 118140960795 + 5789700 * 2 ^ 59
def prefixEnd_5789700 : Nat := 4983230072969 + 3 ^ 40 * 5789700 * 2
def baseEnd_5789700 : Nat := 2972898945336103005823661

theorem tailTrace_5789700 : CollatzResearch.WordTrace tailWord_5789700 prefixEnd_5789700 2972898945336103005823661 := by
  unfold tailWord_5789700
  simp only [CollatzResearch.WordTrace]
  refine ⟨105583853562456588441279277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140778471416608784588372369 105583853562456588441279277)
  ·
    refine ⟨39593945085921220665479729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105583853562456588441279277 39593945085921220665479729)
    ·
      refine ⟨29695458814440915499109797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39593945085921220665479729 29695458814440915499109797)
      ·
        refine ⟨5567898527707671656083087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29695458814440915499109797 5567898527707671656083087)
        ·
          refine ⟨8351847791561507484124631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567898527707671656083087 8351847791561507484124631)
          ·
            refine ⟨12527771687342261226186947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351847791561507484124631 12527771687342261226186947)
            ·
              refine ⟨18791657531013391839280421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527771687342261226186947 18791657531013391839280421)
              ·
                refine ⟨3523435787065010969865079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18791657531013391839280421 3523435787065010969865079)
                ·
                  refine ⟨5285153680597516454797619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523435787065010969865079 5285153680597516454797619)
                  ·
                    refine ⟨7927730520896274682196429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5285153680597516454797619 7927730520896274682196429)
                    ·
                      refine ⟨2972898945336103005823661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7927730520896274682196429 2972898945336103005823661)
                      ·
                        rfl

theorem cell23_5789700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5789700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789700 prefixEnd_5789700 := by exact prefixLift 5789700
  have htrace : WordTrace (prefixWord ++ tailWord_5789700) baseStart_5789700 baseEnd_5789700 := by
    simpa [prefixWord, tailWord_5789700, baseEnd_5789700] using wordTrace_append hprefix tailTrace_5789700
  have hstable : (prefixWord ++ tailWord_5789700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789700).length < 2 ^ (prefixWord ++ tailWord_5789700).sum := by decide
  have hdescent : baseEnd_5789700 < baseStart_5789700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789715 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_5789715 : Nat := 118140960795 + 5789715 * 2 ^ 59
def prefixEnd_5789715 : Nat := 4983230072969 + 3 ^ 40 * 5789715 * 2
def baseEnd_5789715 : Nat := 2972906647545920447136091

theorem tailTrace_5789715 : CollatzResearch.WordTrace tailWord_5789715 prefixEnd_5789715 2972906647545920447136091 := by
  unfold tailWord_5789715
  simp only [CollatzResearch.WordTrace]
  refine ⟨211168254219858834444354599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140778836146572556296236399 211168254219858834444354599)
  ·
    refine ⟨316752381329788251666531899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211168254219858834444354599 316752381329788251666531899)
    ·
      refine ⟨475128571994682377499797849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316752381329788251666531899 475128571994682377499797849)
      ·
        refine ⟨356346428996011783124848387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475128571994682377499797849 356346428996011783124848387)
        ·
          refine ⟨534519643494017674687272581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356346428996011783124848387 534519643494017674687272581)
          ·
            refine ⟨100222433155128314003863609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 534519643494017674687272581 100222433155128314003863609)
            ·
              refine ⟨75166824866346235502897707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100222433155128314003863609 75166824866346235502897707)
              ·
                refine ⟨112750237299519353254346561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75166824866346235502897707 112750237299519353254346561)
                ·
                  refine ⟨84562677974639514940759921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112750237299519353254346561 84562677974639514940759921)
                  ·
                    refine ⟨63422008480979636205569941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84562677974639514940759921 63422008480979636205569941)
                    ·
                      refine ⟨2972906647545920447136091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63422008480979636205569941 2972906647545920447136091)
                      ·
                        rfl

theorem cell23_5789715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_5789715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789715 prefixEnd_5789715 := by exact prefixLift 5789715
  have htrace : WordTrace (prefixWord ++ tailWord_5789715) baseStart_5789715 baseEnd_5789715 := by
    simpa [prefixWord, tailWord_5789715, baseEnd_5789715] using wordTrace_append hprefix tailTrace_5789715
  have hstable : (prefixWord ++ tailWord_5789715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789715).length < 2 ^ (prefixWord ++ tailWord_5789715).sum := by decide
  have hdescent : baseEnd_5789715 < baseStart_5789715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5789729 : List Nat := [1, 2, 3, 2, 4, 1, 3, 7]
def baseStart_5789729 : Nat := 118140960795 + 5789729 * 2 ^ 59
def prefixEnd_5789729 : Nat := 4983230072969 + 3 ^ 40 * 5789729 * 2
def baseEnd_5789729 : Nat := 110107919862040125643001

theorem tailTrace_5789729 : CollatzResearch.WordTrace tailWord_5789729 prefixEnd_5789729 110107919862040125643001 := by
  unfold tailWord_5789729
  simp only [CollatzResearch.WordTrace]
  refine ⟨211168764841808114835364241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140779176561205409890242827 211168764841808114835364241)
  ·
    refine ⟨158376573631356086126523181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211168764841808114835364241 158376573631356086126523181)
    ·
      refine ⟨59391215111758532297446193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158376573631356086126523181 59391215111758532297446193)
      ·
        refine ⟨44543411333818899223084645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59391215111758532297446193 44543411333818899223084645)
        ·
          refine ⟨8351889625091043604328371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44543411333818899223084645 8351889625091043604328371)
          ·
            refine ⟨12527834437636565406492557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351889625091043604328371 12527834437636565406492557)
            ·
              refine ⟨4697937914113712027434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12527834437636565406492557 4697937914113712027434709)
              ·
                refine ⟨110107919862040125643001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4697937914113712027434709 110107919862040125643001)
                ·
                  rfl

theorem cell23_5789729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 7].length) (baseStart_5789729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5789729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5789729 prefixEnd_5789729 := by exact prefixLift 5789729
  have htrace : WordTrace (prefixWord ++ tailWord_5789729) baseStart_5789729 baseEnd_5789729 := by
    simpa [prefixWord, tailWord_5789729, baseEnd_5789729] using wordTrace_append hprefix tailTrace_5789729
  have hstable : (prefixWord ++ tailWord_5789729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5789729).length < 2 ^ (prefixWord ++ tailWord_5789729).sum := by decide
  have hdescent : baseEnd_5789729 < baseStart_5789729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5789729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
