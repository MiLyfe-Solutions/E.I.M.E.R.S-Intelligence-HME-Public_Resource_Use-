import V185TrunkScan22Chunk151

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1358175 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_1358175 : Nat := 118140960795 + 1358175 * 2 ^ 59
def prefixEnd_1358175 : Nat := 4983230072969 + 3 ^ 40 * 1358175 * 2
def baseEnd_1358175 : Nat := 464931058613552578510915

theorem tailTrace_1358175 : CollatzResearch.WordTrace tailWord_1358175 prefixEnd_1358175 464931058613552578510915 := by
  unfold tailWord_1358175
  simp only [CollatzResearch.WordTrace]
  refine ⟨49536711854571407668003979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33024474569714271778669319 49536711854571407668003979)
  ·
    refine ⟨74305067781857111502005969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49536711854571407668003979 74305067781857111502005969)
    ·
      refine ⟨55728800836392833626504477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74305067781857111502005969 55728800836392833626504477)
      ·
        refine ⟨20898300313647312609939179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55728800836392833626504477 20898300313647312609939179)
        ·
          refine ⟨31347450470470968914908769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20898300313647312609939179 31347450470470968914908769)
          ·
            refine ⟨23510587852853226686181577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31347450470470968914908769 23510587852853226686181577)
            ·
              refine ⟨17632940889639920014636183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23510587852853226686181577 17632940889639920014636183)
              ·
                refine ⟨26449411334459880021954275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17632940889639920014636183 26449411334459880021954275)
                ·
                  refine ⟨39674117001689820032931413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26449411334459880021954275 39674117001689820032931413)
                  ·
                    refine ⟨464931058613552578510915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39674117001689820032931413 464931058613552578510915)
                    ·
                      rfl

theorem cell22_1358175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_1358175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358175 prefixEnd_1358175 := by exact prefixLift 1358175
  have htrace : WordTrace (prefixWord ++ tailWord_1358175) baseStart_1358175 baseEnd_1358175 := by
    simpa [prefixWord, tailWord_1358175, baseEnd_1358175] using wordTrace_append hprefix tailTrace_1358175
  have hstable : (prefixWord ++ tailWord_1358175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358175).length < 2 ^ (prefixWord ++ tailWord_1358175).sum := by decide
  have hdescent : baseEnd_1358175 < baseStart_1358175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358194 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_1358194 : Nat := 118140960795 + 1358194 * 2 ^ 59
def prefixEnd_1358194 : Nat := 4983230072969 + 3 ^ 40 * 1358194 * 2
def baseEnd_1358194 : Nat := 464937562701842862285857

theorem tailTrace_1358194 : CollatzResearch.WordTrace tailWord_1358194 prefixEnd_1358194 464937562701842862285857 := by
  unfold tailWord_1358194
  simp only [CollatzResearch.WordTrace]
  refine ⟨12384351210375643478236409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33024936561001715941963757 12384351210375643478236409)
  ·
    refine ⟨9288263407781732608677307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12384351210375643478236409 9288263407781732608677307)
    ·
      refine ⟨13932395111672598913015961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9288263407781732608677307 13932395111672598913015961)
      ·
        refine ⟨10449296333754449184761971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13932395111672598913015961 10449296333754449184761971)
        ·
          refine ⟨15673944500631673777142957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10449296333754449184761971 15673944500631673777142957)
          ·
            refine ⟨5877729187736877666428609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15673944500631673777142957 5877729187736877666428609)
            ·
              refine ⟨4408296890802658249821457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877729187736877666428609 4408296890802658249821457)
              ·
                refine ⟨3306222668101993687366093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408296890802658249821457 3306222668101993687366093)
                ·
                  refine ⟨1239833500538247632762285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3306222668101993687366093 1239833500538247632762285)
                  ·
                    refine ⟨464937562701842862285857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239833500538247632762285 464937562701842862285857)
                    ·
                      rfl

theorem cell22_1358194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_1358194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358194 prefixEnd_1358194 := by exact prefixLift 1358194
  have htrace : WordTrace (prefixWord ++ tailWord_1358194) baseStart_1358194 baseEnd_1358194 := by
    simpa [prefixWord, tailWord_1358194, baseEnd_1358194] using wordTrace_append hprefix tailTrace_1358194
  have hstable : (prefixWord ++ tailWord_1358194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358194).length < 2 ^ (prefixWord ++ tailWord_1358194).sum := by decide
  have hdescent : baseEnd_1358194 < baseStart_1358194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358228 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1358228 : Nat := 118140960795 + 1358228 * 2 ^ 59
def prefixEnd_1358228 : Nat := 4983230072969 + 3 ^ 40 * 1358228 * 2
def baseEnd_1358228 : Nat := 464949201596678106935753

theorem tailTrace_1358228 : CollatzResearch.WordTrace tailWord_1358228 prefixEnd_1358228 464949201596678106935753 := by
  unfold tailWord_1358228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24769322461689698859841669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33025763282252931813122225 24769322461689698859841669)
  ·
    refine ⟨4644247961566818536220313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24769322461689698859841669 4644247961566818536220313)
    ·
      refine ⟨3483185971175113902165235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4644247961566818536220313 3483185971175113902165235)
      ·
        refine ⟨5224778956762670853247853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483185971175113902165235 5224778956762670853247853)
        ·
          refine ⟨1959292108786001569967945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5224778956762670853247853 1959292108786001569967945)
          ·
            refine ⟨1469469081589501177475959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1959292108786001569967945 1469469081589501177475959)
            ·
              refine ⟨2204203622384251766213939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469469081589501177475959 2204203622384251766213939)
              ·
                refine ⟨3306305433576377649320909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204203622384251766213939 3306305433576377649320909)
                ·
                  refine ⟨1239864537591141618495341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3306305433576377649320909 1239864537591141618495341)
                  ·
                    refine ⟨464949201596678106935753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239864537591141618495341 464949201596678106935753)
                    ·
                      rfl

theorem cell22_1358228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1358228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358228 prefixEnd_1358228 := by exact prefixLift 1358228
  have htrace : WordTrace (prefixWord ++ tailWord_1358228) baseStart_1358228 baseEnd_1358228 := by
    simpa [prefixWord, tailWord_1358228, baseEnd_1358228] using wordTrace_append hprefix tailTrace_1358228
  have hstable : (prefixWord ++ tailWord_1358228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358228).length < 2 ^ (prefixWord ++ tailWord_1358228).sum := by decide
  have hdescent : baseEnd_1358228 < baseStart_1358228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358241 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 5]
def baseStart_1358241 : Nat := 118140960795 + 1358241 * 2 ^ 59
def prefixEnd_1358241 : Nat := 4983230072969 + 3 ^ 40 * 1358241 * 2
def baseEnd_1358241 : Nat := 154984550587450135453571

theorem tailTrace_1358241 : CollatzResearch.WordTrace tailWord_1358241 prefixEnd_1358241 154984550587450135453571 := by
  unfold tailWord_1358241
  simp only [CollatzResearch.WordTrace]
  refine ⟨49539119072332300939906577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33026079381554867293271051 49539119072332300939906577)
  ·
    refine ⟨37154339304249225704929933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49539119072332300939906577 37154339304249225704929933)
    ·
      refine ⟨13932877239093459639348725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37154339304249225704929933 13932877239093459639348725)
      ·
        refine ⟨1306207241165011841188943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13932877239093459639348725 1306207241165011841188943)
        ·
          refine ⟨1959310861747517761783415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306207241165011841188943 1959310861747517761783415)
          ·
            refine ⟨2938966292621276642675123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959310861747517761783415 2938966292621276642675123)
            ·
              refine ⟨4408449438931914964012685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938966292621276642675123 4408449438931914964012685)
              ·
                refine ⟨1653168539599468111504757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4408449438931914964012685 1653168539599468111504757)
                ·
                  refine ⟨154984550587450135453571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1653168539599468111504757 154984550587450135453571)
                  ·
                    rfl

theorem cell22_1358241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_1358241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358241 prefixEnd_1358241 := by exact prefixLift 1358241
  have htrace : WordTrace (prefixWord ++ tailWord_1358241) baseStart_1358241 baseEnd_1358241 := by
    simpa [prefixWord, tailWord_1358241, baseEnd_1358241] using wordTrace_append hprefix tailTrace_1358241
  have hstable : (prefixWord ++ tailWord_1358241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358241).length < 2 ^ (prefixWord ++ tailWord_1358241).sum := by decide
  have hdescent : baseEnd_1358241 < baseStart_1358241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358301 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1358301 : Nat := 118140960795 + 1358301 * 2 ^ 59
def prefixEnd_1358301 : Nat := 4983230072969 + 3 ^ 40 * 1358301 * 2
def baseEnd_1358301 : Nat := 464974190988530249860529

theorem tailTrace_1358301 : CollatzResearch.WordTrace tailWord_1358301 prefixEnd_1358301 464974190988530249860529 := by
  unfold tailWord_1358301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49541307452114931187090757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33027538301409954124727171 49541307452114931187090757)
  ·
    refine ⟨9288995147271549597579517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49541307452114931187090757 9288995147271549597579517)
    ·
      refine ⟨3483373180226831099092319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9288995147271549597579517 3483373180226831099092319)
      ·
        refine ⟨5225059770340246648638479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3483373180226831099092319 5225059770340246648638479)
        ·
          refine ⟨7837589655510369972957719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5225059770340246648638479 7837589655510369972957719)
          ·
            refine ⟨11756384483265554959436579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837589655510369972957719 11756384483265554959436579)
            ·
              refine ⟨17634576724898332439154869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11756384483265554959436579 17634576724898332439154869)
              ·
                refine ⟨1653241567959218666170769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17634576724898332439154869 1653241567959218666170769)
                ·
                  refine ⟨1239931175969413999628077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653241567959218666170769 1239931175969413999628077)
                  ·
                    refine ⟨464974190988530249860529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239931175969413999628077 464974190988530249860529)
                    ·
                      rfl

theorem cell22_1358301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1358301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358301 prefixEnd_1358301 := by exact prefixLift 1358301
  have htrace : WordTrace (prefixWord ++ tailWord_1358301) baseStart_1358301 baseEnd_1358301 := by
    simpa [prefixWord, tailWord_1358301, baseEnd_1358301] using wordTrace_append hprefix tailTrace_1358301
  have hstable : (prefixWord ++ tailWord_1358301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358301).length < 2 ^ (prefixWord ++ tailWord_1358301).sum := by decide
  have hdescent : baseEnd_1358301 < baseStart_1358301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358346 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1358346 : Nat := 118140960795 + 1358346 * 2 ^ 59
def prefixEnd_1358346 : Nat := 4983230072969 + 3 ^ 40 * 1358346 * 2
def baseEnd_1358346 : Nat := 464989595408165132485391

theorem tailTrace_1358346 : CollatzResearch.WordTrace tailWord_1358346 prefixEnd_1358346 464989595408165132485391 := by
  unfold tailWord_1358346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385737184237975968119723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33028632491301269248319261 12385737184237975968119723)
  ·
    refine ⟨18578605776356963952179585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385737184237975968119723 18578605776356963952179585)
    ·
      refine ⟨13933954332267722964134689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18578605776356963952179585 13933954332267722964134689)
      ·
        refine ⟨10450465749200792223101017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13933954332267722964134689 10450465749200792223101017)
        ·
          refine ⟨7837849311900594167325763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10450465749200792223101017 7837849311900594167325763)
          ·
            refine ⟨11756773967850891250988645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837849311900594167325763 11756773967850891250988645)
            ·
              refine ⟨2204395118972042109560371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11756773967850891250988645 2204395118972042109560371)
              ·
                refine ⟨3306592678458063164340557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204395118972042109560371 3306592678458063164340557)
                ·
                  refine ⟨1239972254421773686627709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3306592678458063164340557 1239972254421773686627709)
                  ·
                    refine ⟨464989595408165132485391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239972254421773686627709 464989595408165132485391)
                    ·
                      rfl

theorem cell22_1358346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1358346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358346 prefixEnd_1358346 := by exact prefixLift 1358346
  have htrace : WordTrace (prefixWord ++ tailWord_1358346) baseStart_1358346 baseEnd_1358346 := by
    simpa [prefixWord, tailWord_1358346, baseEnd_1358346] using wordTrace_append hprefix tailTrace_1358346
  have hstable : (prefixWord ++ tailWord_1358346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358346).length < 2 ^ (prefixWord ++ tailWord_1358346).sum := by decide
  have hdescent : baseEnd_1358346 < baseStart_1358346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358440 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1358440 : Nat := 118140960795 + 1358440 * 2 ^ 59
def prefixEnd_1358440 : Nat := 4983230072969 + 3 ^ 40 * 1358440 * 2
def baseEnd_1358440 : Nat := 465021773529180220635103

theorem tailTrace_1358440 : CollatzResearch.WordTrace tailWord_1358440 prefixEnd_1358440 465021773529180220635103 := by
  unfold tailWord_1358440
  simp only [CollatzResearch.WordTrace]
  refine ⟨24773188599305678963200387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33030918132407571950933849 24773188599305678963200387)
  ·
    refine ⟨37159782898958518444800581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24773188599305678963200387 37159782898958518444800581)
    ·
      refine ⟨6967459293554722208400109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37159782898958518444800581 6967459293554722208400109)
      ·
        refine ⟨2612797235083020828150041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6967459293554722208400109 2612797235083020828150041)
        ·
          refine ⟨1959597926312265621112531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2612797235083020828150041 1959597926312265621112531)
          ·
            refine ⟨2939396889468398431668797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959597926312265621112531 2939396889468398431668797)
            ·
              refine ⟨1102273833550649411875799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2939396889468398431668797 1102273833550649411875799)
              ·
                refine ⟨1653410750325974117813699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102273833550649411875799 1653410750325974117813699)
                ·
                  refine ⟨2480116125488961176720549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653410750325974117813699 2480116125488961176720549)
                  ·
                    refine ⟨465021773529180220635103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2480116125488961176720549 465021773529180220635103)
                    ·
                      rfl

theorem cell22_1358440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1358440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358440 prefixEnd_1358440 := by exact prefixLift 1358440
  have htrace : WordTrace (prefixWord ++ tailWord_1358440) baseStart_1358440 baseEnd_1358440 := by
    simpa [prefixWord, tailWord_1358440, baseEnd_1358440] using wordTrace_append hprefix tailTrace_1358440
  have hstable : (prefixWord ++ tailWord_1358440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358440).length < 2 ^ (prefixWord ++ tailWord_1358440).sum := by decide
  have hdescent : baseEnd_1358440 < baseStart_1358440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358511 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 5]
def baseStart_1358511 : Nat := 118140960795 + 1358511 * 2 ^ 59
def prefixEnd_1358511 : Nat := 4983230072969 + 3 ^ 40 * 1358511 * 2
def baseEnd_1358511 : Nat := 155015359426719900703295

theorem tailTrace_1358511 : CollatzResearch.WordTrace tailWord_1358511 prefixEnd_1358511 155015359426719900703295 := by
  unfold tailWord_1358511
  simp only [CollatzResearch.WordTrace]
  refine ⟨49548966781354137052235387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33032644520902758034823591 49548966781354137052235387)
  ·
    refine ⟨74323450172031205578353081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49548966781354137052235387 74323450172031205578353081)
    ·
      refine ⟨55742587629023404183764811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74323450172031205578353081 55742587629023404183764811)
      ·
        refine ⟨83613881443535106275647217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55742587629023404183764811 83613881443535106275647217)
        ·
          refine ⟨62710411082651329706735413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83613881443535106275647217 62710411082651329706735413)
          ·
            refine ⟨5879101038998562160006445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62710411082651329706735413 5879101038998562160006445)
            ·
              refine ⟨2204662889624460810002417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5879101038998562160006445 2204662889624460810002417)
              ·
                refine ⟨1653497167218345607501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204662889624460810002417 1653497167218345607501813)
                ·
                  refine ⟨155015359426719900703295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1653497167218345607501813 155015359426719900703295)
                  ·
                    rfl

theorem cell22_1358511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 5].length) (baseStart_1358511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358511 prefixEnd_1358511 := by exact prefixLift 1358511
  have htrace : WordTrace (prefixWord ++ tailWord_1358511) baseStart_1358511 baseEnd_1358511 := by
    simpa [prefixWord, tailWord_1358511, baseEnd_1358511] using wordTrace_append hprefix tailTrace_1358511
  have hstable : (prefixWord ++ tailWord_1358511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358511).length < 2 ^ (prefixWord ++ tailWord_1358511).sum := by decide
  have hdescent : baseEnd_1358511 < baseStart_1358511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358526 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1358526 : Nat := 118140960795 + 1358526 * 2 ^ 59
def prefixEnd_1358526 : Nat := 4983230072969 + 3 ^ 40 * 1358526 * 2
def baseEnd_1358526 : Nat := 465051213086704662984839

theorem tailTrace_1358526 : CollatzResearch.WordTrace tailWord_1358526 prefixEnd_1358526 465051213086704662984839 := by
  unfold tailWord_1358526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193689234537474326753929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33033009250866529742687621 6193689234537474326753929)
  ·
    refine ⟨4645266925903105745065447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6193689234537474326753929 4645266925903105745065447)
    ·
      refine ⟨6967900388854658617598171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4645266925903105745065447 6967900388854658617598171)
      ·
        refine ⟨10451850583281987926397257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967900388854658617598171 10451850583281987926397257)
        ·
          refine ⟨7838887937461490944797943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10451850583281987926397257 7838887937461490944797943)
          ·
            refine ⟨11758331906192236417196915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838887937461490944797943 11758331906192236417196915)
            ·
              refine ⟨17637497859288354625795373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11758331906192236417196915 17637497859288354625795373)
              ·
                refine ⟨6614061697233132984673265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17637497859288354625795373 6614061697233132984673265)
                ·
                  refine ⟨4960546272924849738504949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6614061697233132984673265 4960546272924849738504949)
                  ·
                    refine ⟨465051213086704662984839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4960546272924849738504949 465051213086704662984839)
                    ·
                      rfl

theorem cell22_1358526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1358526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358526 prefixEnd_1358526 := by exact prefixLift 1358526
  have htrace : WordTrace (prefixWord ++ tailWord_1358526) baseStart_1358526 baseEnd_1358526 := by
    simpa [prefixWord, tailWord_1358526, baseEnd_1358526] using wordTrace_append hprefix tailTrace_1358526
  have hstable : (prefixWord ++ tailWord_1358526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358526).length < 2 ^ (prefixWord ++ tailWord_1358526).sum := by decide
  have hdescent : baseEnd_1358526 < baseStart_1358526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358528 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_1358528 : Nat := 118140960795 + 1358528 * 2 ^ 59
def prefixEnd_1358528 : Nat := 4983230072969 + 3 ^ 40 * 1358528 * 2
def baseEnd_1358528 : Nat := 155017299242525774811611

theorem tailTrace_1358528 : CollatzResearch.WordTrace tailWord_1358528 prefixEnd_1358528 155017299242525774811611 := by
  unfold tailWord_1358528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774793411146274477802119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33033057881528365970402825 24774793411146274477802119)
  ·
    refine ⟨37162190116719411716703179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24774793411146274477802119 37162190116719411716703179)
    ·
      refine ⟨55743285175079117575054769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37162190116719411716703179 55743285175079117575054769)
      ·
        refine ⟨41807463881309338181291077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55743285175079117575054769 41807463881309338181291077)
        ·
          refine ⟨7838899477745500908992077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41807463881309338181291077 7838899477745500908992077)
          ·
            refine ⟨2939587304154562840872029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7838899477745500908992077 2939587304154562840872029)
            ·
              refine ⟨1102345239057961065327011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2939587304154562840872029 1102345239057961065327011)
              ·
                refine ⟨1653517858586941597990517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102345239057961065327011 1653517858586941597990517)
                ·
                  refine ⟨155017299242525774811611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1653517858586941597990517 155017299242525774811611)
                  ·
                    rfl

theorem cell22_1358528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_1358528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358528 prefixEnd_1358528 := by exact prefixLift 1358528
  have htrace : WordTrace (prefixWord ++ tailWord_1358528) baseStart_1358528 baseEnd_1358528 := by
    simpa [prefixWord, tailWord_1358528, baseEnd_1358528] using wordTrace_append hprefix tailTrace_1358528
  have hstable : (prefixWord ++ tailWord_1358528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358528).length < 2 ^ (prefixWord ++ tailWord_1358528).sum := by decide
  have hdescent : baseEnd_1358528 < baseStart_1358528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358534 : List Nat := [6, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1358534 : Nat := 118140960795 + 1358534 * 2 ^ 59
def prefixEnd_1358534 : Nat := 4983230072969 + 3 ^ 40 * 1358534 * 2
def baseEnd_1358534 : Nat := 51672661294466145420535

theorem tailTrace_1358534 : CollatzResearch.WordTrace tailWord_1358534 prefixEnd_1358534 51672661294466145420535 := by
  unfold tailWord_1358534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548431426883462874385083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33033203773513874653548437 1548431426883462874385083)
  ·
    refine ⟨2322647140325194311577625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548431426883462874385083 2322647140325194311577625)
    ·
      refine ⟨1741985355243895733683219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2322647140325194311577625 1741985355243895733683219)
      ·
        refine ⟨2612978032865843600524829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741985355243895733683219 2612978032865843600524829)
        ·
          refine ⟨979866762324691350196811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2612978032865843600524829 979866762324691350196811)
          ·
            refine ⟨1469800143487037025295217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979866762324691350196811 1469800143487037025295217)
            ·
              refine ⟨1102350107615277768971413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469800143487037025295217 1102350107615277768971413)
              ·
                refine ⟨51672661294466145420535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1102350107615277768971413 51672661294466145420535)
                ·
                  rfl

theorem cell22_1358534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1358534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358534 prefixEnd_1358534 := by exact prefixLift 1358534
  have htrace : WordTrace (prefixWord ++ tailWord_1358534) baseStart_1358534 baseEnd_1358534 := by
    simpa [prefixWord, tailWord_1358534, baseEnd_1358534] using wordTrace_append hprefix tailTrace_1358534
  have hstable : (prefixWord ++ tailWord_1358534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358534).length < 2 ^ (prefixWord ++ tailWord_1358534).sum := by decide
  have hdescent : baseEnd_1358534 < baseStart_1358534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358549 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_1358549 : Nat := 118140960795 + 1358549 * 2 ^ 59
def prefixEnd_1358549 : Nat := 4983230072969 + 3 ^ 40 * 1358549 * 2
def baseEnd_1358549 : Nat := 465059086456740269659769

theorem tailTrace_1358549 : CollatzResearch.WordTrace tailWord_1358549 prefixEnd_1358549 465059086456740269659769 := by
  unfold tailWord_1358549
  simp only [CollatzResearch.WordTrace]
  refine ⟨49550352755216469542118701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33033568503477646361412467 49550352755216469542118701)
  ·
    refine ⟨18581382283206176078294513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49550352755216469542118701 18581382283206176078294513)
    ·
      refine ⟨13936036712404632058720885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18581382283206176078294513 13936036712404632058720885)
      ·
        refine ⟨1306503441787934255505083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13936036712404632058720885 1306503441787934255505083)
        ·
          refine ⟨1959755162681901383257625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306503441787934255505083 1959755162681901383257625)
          ·
            refine ⟨1469816372011426037443219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1959755162681901383257625 1469816372011426037443219)
            ·
              refine ⟨2204724558017139056164829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469816372011426037443219 2204724558017139056164829)
              ·
                refine ⟨826771709256427146061811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204724558017139056164829 826771709256427146061811)
                ·
                  refine ⟨1240157563884640719092717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826771709256427146061811 1240157563884640719092717)
                  ·
                    refine ⟨465059086456740269659769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240157563884640719092717 465059086456740269659769)
                    ·
                      rfl

theorem cell22_1358549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_1358549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358549 prefixEnd_1358549 := by exact prefixLift 1358549
  have htrace : WordTrace (prefixWord ++ tailWord_1358549) baseStart_1358549 baseEnd_1358549 := by
    simpa [prefixWord, tailWord_1358549, baseEnd_1358549] using wordTrace_append hprefix tailTrace_1358549
  have hstable : (prefixWord ++ tailWord_1358549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358549).length < 2 ^ (prefixWord ++ tailWord_1358549).sum := by decide
  have hdescent : baseEnd_1358549 < baseStart_1358549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358650 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_1358650 : Nat := 118140960795 + 1358650 * 2 ^ 59
def prefixEnd_1358650 : Nat := 4983230072969 + 3 ^ 40 * 1358650 * 2
def baseEnd_1358650 : Nat := 465093660820809672884459

theorem tailTrace_1358650 : CollatzResearch.WordTrace tailWord_1358650 prefixEnd_1358650 465093660820809672884459 := by
  unfold tailWord_1358650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388509131962640947886351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33036024351900375861030269 12388509131962640947886351)
  ·
    refine ⟨18582763697943961421829527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12388509131962640947886351 18582763697943961421829527)
    ·
      refine ⟨27874145546915942132744291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18582763697943961421829527 27874145546915942132744291)
      ·
        refine ⟨41811218320373913199116437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27874145546915942132744291 41811218320373913199116437)
        ·
          refine ⟨1959900858767527181208583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41811218320373913199116437 1959900858767527181208583)
          ·
            refine ⟨2939851288151290771812875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959900858767527181208583 2939851288151290771812875)
            ·
              refine ⟨4409776932226936157719313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939851288151290771812875 4409776932226936157719313)
              ·
                refine ⟨3307332699170202118289485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409776932226936157719313 3307332699170202118289485)
                ·
                  refine ⟨1240249762188825794358557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3307332699170202118289485 1240249762188825794358557)
                  ·
                    refine ⟨465093660820809672884459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240249762188825794358557 465093660820809672884459)
                    ·
                      rfl

theorem cell22_1358650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_1358650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358650 prefixEnd_1358650 := by exact prefixLift 1358650
  have htrace : WordTrace (prefixWord ++ tailWord_1358650) baseStart_1358650 baseEnd_1358650 := by
    simpa [prefixWord, tailWord_1358650, baseEnd_1358650] using wordTrace_append hprefix tailTrace_1358650
  have hstable : (prefixWord ++ tailWord_1358650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358650).length < 2 ^ (prefixWord ++ tailWord_1358650).sum := by decide
  have hdescent : baseEnd_1358650 < baseStart_1358650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358718 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1358718 : Nat := 118140960795 + 1358718 * 2 ^ 59
def prefixEnd_1358718 : Nat := 4983230072969 + 3 ^ 40 * 1358718 * 2
def baseEnd_1358718 : Nat := 465116938610480162184251

theorem tailTrace_1358718 : CollatzResearch.WordTrace tailWord_1358718 prefixEnd_1358718 465116938610480162184251 := by
  unfold tailWord_1358718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194564586450526425627601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33037677794402807603347205 6194564586450526425627601)
  ·
    refine ⟨4645923439837894819220701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6194564586450526425627601 4645923439837894819220701)
    ·
      refine ⟨1742221289939210557207763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4645923439837894819220701 1742221289939210557207763)
      ·
        refine ⟨2613331934908815835811645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742221289939210557207763 2613331934908815835811645)
        ·
          refine ⟨979999475590805938429367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2613331934908815835811645 979999475590805938429367)
          ·
            refine ⟨1469999213386208907644051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979999475590805938429367 1469999213386208907644051)
            ·
              refine ⟨2204998820079313361466077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469999213386208907644051 2204998820079313361466077)
              ·
                refine ⟨826874557529742510549779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204998820079313361466077 826874557529742510549779)
                ·
                  refine ⟨1240311836294613765824669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826874557529742510549779 1240311836294613765824669)
                  ·
                    refine ⟨465116938610480162184251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240311836294613765824669 465116938610480162184251)
                    ·
                      rfl

theorem cell22_1358718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1358718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358718 prefixEnd_1358718 := by exact prefixLift 1358718
  have htrace : WordTrace (prefixWord ++ tailWord_1358718) baseStart_1358718 baseEnd_1358718 := by
    simpa [prefixWord, tailWord_1358718, baseEnd_1358718] using wordTrace_append hprefix tailTrace_1358718
  have hstable : (prefixWord ++ tailWord_1358718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358718).length < 2 ^ (prefixWord ++ tailWord_1358718).sum := by decide
  have hdescent : baseEnd_1358718 < baseStart_1358718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358723 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 6, 3]
def baseStart_1358723 : Nat := 118140960795 + 1358723 * 2 ^ 59
def prefixEnd_1358723 : Nat := 4983230072969 + 3 ^ 40 * 1358723 * 2
def baseEnd_1358723 : Nat := 465118650212661815809235

theorem tailTrace_1358723 : CollatzResearch.WordTrace tailWord_1358723 prefixEnd_1358723 465118650212661815809235 := by
  unfold tailWord_1358723
  simp only [CollatzResearch.WordTrace]
  refine ⟨49556699056586097258952823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33037799371057398172635215 49556699056586097258952823)
  ·
    refine ⟨74335048584879145888429235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49556699056586097258952823 74335048584879145888429235)
    ·
      refine ⟨111502572877318718832643853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74335048584879145888429235 111502572877318718832643853)
      ·
        refine ⟨41813464828994519562241445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111502572877318718832643853 41813464828994519562241445)
        ·
          refine ⟨7840024655436472417920271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41813464828994519562241445 7840024655436472417920271)
          ·
            refine ⟨11760036983154708626880407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840024655436472417920271 11760036983154708626880407)
            ·
              refine ⟨17640055474732062940320611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760036983154708626880407 17640055474732062940320611)
              ·
                refine ⟨26460083212098094410480917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17640055474732062940320611 26460083212098094410480917)
                ·
                  refine ⟨1240316400567098175491293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26460083212098094410480917 1240316400567098175491293)
                  ·
                    refine ⟨465118650212661815809235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240316400567098175491293 465118650212661815809235)
                    ·
                      rfl

theorem cell22_1358723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3].length) (baseStart_1358723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358723 prefixEnd_1358723 := by exact prefixLift 1358723
  have htrace : WordTrace (prefixWord ++ tailWord_1358723) baseStart_1358723 baseEnd_1358723 := by
    simpa [prefixWord, tailWord_1358723, baseEnd_1358723] using wordTrace_append hprefix tailTrace_1358723
  have hstable : (prefixWord ++ tailWord_1358723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358723).length < 2 ^ (prefixWord ++ tailWord_1358723).sum := by decide
  have hdescent : baseEnd_1358723 < baseStart_1358723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358725 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 4]
def baseStart_1358725 : Nat := 118140960795 + 1358725 * 2 ^ 59
def prefixEnd_1358725 : Nat := 4983230072969 + 3 ^ 40 * 1358725 * 2
def baseEnd_1358725 : Nat := 155039778284511492419743

theorem tailTrace_1358725 : CollatzResearch.WordTrace tailWord_1358725 prefixEnd_1358725 155039778284511492419743 := by
  unfold tailWord_1358725
  simp only [CollatzResearch.WordTrace]
  refine ⟨49556772002578851600525629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33037848001719234400350419 49556772002578851600525629)
  ·
    refine ⟨18583789500967069350197111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49556772002578851600525629 18583789500967069350197111)
    ·
      refine ⟨27875684251450604025295667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18583789500967069350197111 27875684251450604025295667)
      ·
        refine ⟨41813526377175906037943501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27875684251450604025295667 41813526377175906037943501)
        ·
          refine ⟨15680072391440964764228813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41813526377175906037943501 15680072391440964764228813)
          ·
            refine ⟨5880027146790361786585805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15680072391440964764228813 5880027146790361786585805)
            ·
              refine ⟨2205010180046385669969677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5880027146790361786585805 2205010180046385669969677)
              ·
                refine ⟨826878817517394626238629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205010180046385669969677 826878817517394626238629)
                ·
                  refine ⟨155039778284511492419743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826878817517394626238629 155039778284511492419743)
                  ·
                    rfl

theorem cell22_1358725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_1358725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358725 prefixEnd_1358725 := by exact prefixLift 1358725
  have htrace : WordTrace (prefixWord ++ tailWord_1358725) baseStart_1358725 baseEnd_1358725 := by
    simpa [prefixWord, tailWord_1358725, baseEnd_1358725] using wordTrace_append hprefix tailTrace_1358725
  have hstable : (prefixWord ++ tailWord_1358725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358725).length < 2 ^ (prefixWord ++ tailWord_1358725).sum := by decide
  have hdescent : baseEnd_1358725 < baseStart_1358725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358740 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1358740 : Nat := 118140960795 + 1358740 * 2 ^ 59
def prefixEnd_1358740 : Nat := 4983230072969 + 3 ^ 40 * 1358740 * 2
def baseEnd_1358740 : Nat := 465124469660079438134183

theorem tailTrace_1358740 : CollatzResearch.WordTrace tailWord_1358740 prefixEnd_1358740 465124469660079438134183 := by
  unfold tailWord_1358740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24778659548762254581160837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33038212731683006108214449 24778659548762254581160837)
  ·
    refine ⟨4645998665392922733967657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24778659548762254581160837 4645998665392922733967657)
    ·
      refine ⟨3484498999044692050475743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4645998665392922733967657 3484498999044692050475743)
      ·
        refine ⟨5226748498567038075713615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484498999044692050475743 5226748498567038075713615)
        ·
          refine ⟨7840122747850557113570423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226748498567038075713615 7840122747850557113570423)
          ·
            refine ⟨11760184121775835670355635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840122747850557113570423 11760184121775835670355635)
            ·
              refine ⟨17640276182663753505533453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760184121775835670355635 17640276182663753505533453)
              ·
                refine ⟨6615103568498907564575045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17640276182663753505533453 6615103568498907564575045)
                ·
                  refine ⟨1240331919093545168357821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6615103568498907564575045 1240331919093545168357821)
                  ·
                    refine ⟨465124469660079438134183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240331919093545168357821 465124469660079438134183)
                    ·
                      rfl

theorem cell22_1358740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1358740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358740 prefixEnd_1358740 := by exact prefixLift 1358740
  have htrace : WordTrace (prefixWord ++ tailWord_1358740) baseStart_1358740 baseEnd_1358740 := by
    simpa [prefixWord, tailWord_1358740, baseEnd_1358740] using wordTrace_append hprefix tailTrace_1358740
  have hstable : (prefixWord ++ tailWord_1358740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358740).length < 2 ^ (prefixWord ++ tailWord_1358740).sum := by decide
  have hdescent : baseEnd_1358740 < baseStart_1358740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358753 : List Nat := [1, 2, 3, 4, 1, 1, 1, 9]
def baseStart_1358753 : Nat := 118140960795 + 1358753 * 2 ^ 59
def prefixEnd_1358753 : Nat := 4983230072969 + 3 ^ 40 * 1358753 * 2
def baseEnd_1358753 : Nat := 51680991091750193062127

theorem tailTrace_1358753 : CollatzResearch.WordTrace tailWord_1358753 prefixEnd_1358753 51680991091750193062127 := by
  unfold tailWord_1358753
  simp only [CollatzResearch.WordTrace]
  refine ⟨49557793246477412382544913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33038528830984941588363275 49557793246477412382544913)
  ·
    refine ⟨37168344934858059286908685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49557793246477412382544913 37168344934858059286908685)
    ·
      refine ⟨13938129350571772232590757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37168344934858059286908685 13938129350571772232590757)
      ·
        refine ⟨2613399253232207293610767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13938129350571772232590757 2613399253232207293610767)
        ·
          refine ⟨3920098879848310940416151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613399253232207293610767 3920098879848310940416151)
          ·
            refine ⟨5880148319772466410624227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920098879848310940416151 5880148319772466410624227)
            ·
              refine ⟨8820222479658699615936341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880148319772466410624227 8820222479658699615936341)
              ·
                refine ⟨51680991091750193062127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8820222479658699615936341 51680991091750193062127)
                ·
                  rfl

theorem cell22_1358753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 9].length) (baseStart_1358753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358753 prefixEnd_1358753 := by exact prefixLift 1358753
  have htrace : WordTrace (prefixWord ++ tailWord_1358753) baseStart_1358753 baseEnd_1358753 := by
    simpa [prefixWord, tailWord_1358753, baseEnd_1358753] using wordTrace_append hprefix tailTrace_1358753
  have hstable : (prefixWord ++ tailWord_1358753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358753).length < 2 ^ (prefixWord ++ tailWord_1358753).sum := by decide
  have hdescent : baseEnd_1358753 < baseStart_1358753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358772 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1358772 : Nat := 118140960795 + 1358772 * 2 ^ 59
def prefixEnd_1358772 : Nat := 4983230072969 + 3 ^ 40 * 1358772 * 2
def baseEnd_1358772 : Nat := 465135423914042021334085

theorem tailTrace_1358772 : CollatzResearch.WordTrace tailWord_1358772 prefixEnd_1358772 465135423914042021334085 := by
  unfold tailWord_1358772
  simp only [CollatzResearch.WordTrace]
  refine ⟨24779243116704289313743285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33038990822272385751657713 24779243116704289313743285)
  ·
    refine ⟨2323054042191027123163433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24779243116704289313743285 2323054042191027123163433)
    ·
      refine ⟨1742290531643270342372575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2323054042191027123163433 1742290531643270342372575)
      ·
        refine ⟨2613435797464905513558863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742290531643270342372575 2613435797464905513558863)
        ·
          refine ⟨3920153696197358270338295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613435797464905513558863 3920153696197358270338295)
          ·
            refine ⟨5880230544296037405507443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920153696197358270338295 5880230544296037405507443)
            ·
              refine ⟨8820345816444056108261165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880230544296037405507443 8820345816444056108261165)
              ·
                refine ⟨3307629681166521040597937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8820345816444056108261165 3307629681166521040597937)
                ·
                  refine ⟨2480722260874890780448453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3307629681166521040597937 2480722260874890780448453)
                  ·
                    refine ⟨465135423914042021334085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2480722260874890780448453 465135423914042021334085)
                    ·
                      rfl

theorem cell22_1358772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1358772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358772 prefixEnd_1358772 := by exact prefixLift 1358772
  have htrace : WordTrace (prefixWord ++ tailWord_1358772) baseStart_1358772 baseEnd_1358772 := by
    simpa [prefixWord, tailWord_1358772, baseEnd_1358772] using wordTrace_append hprefix tailTrace_1358772
  have hstable : (prefixWord ++ tailWord_1358772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358772).length < 2 ^ (prefixWord ++ tailWord_1358772).sum := by decide
  have hdescent : baseEnd_1358772 < baseStart_1358772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358860 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_1358860 : Nat := 118140960795 + 1358860 * 2 ^ 59
def prefixEnd_1358860 : Nat := 4983230072969 + 3 ^ 40 * 1358860 * 2
def baseEnd_1358860 : Nat := 155055182704146375044605

theorem tailTrace_1358860 : CollatzResearch.WordTrace tailWord_1358860 prefixEnd_1358860 155055182704146375044605 := by
  unfold tailWord_1358860
  simp only [CollatzResearch.WordTrace]
  refine ⟨24780847928544884828345017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33041130571393179771126689 24780847928544884828345017)
  ·
    refine ⟨18585635946408663621258763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24780847928544884828345017 18585635946408663621258763)
    ·
      refine ⟨27878453919612995431888145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18585635946408663621258763 27878453919612995431888145)
      ·
        refine ⟨20908840439709746573916109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27878453919612995431888145 20908840439709746573916109)
        ·
          refine ⟨7840815164891154965218541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20908840439709746573916109 7840815164891154965218541)
          ·
            refine ⟨2940305686834183111956953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7840815164891154965218541 2940305686834183111956953)
            ·
              refine ⟨2205229265125637333967715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2940305686834183111956953 2205229265125637333967715)
              ·
                refine ⟨3307843897688456000951573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205229265125637333967715 3307843897688456000951573)
                ·
                  refine ⟨155055182704146375044605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3307843897688456000951573 155055182704146375044605)
                  ·
                    rfl

theorem cell22_1358860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_1358860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358860 prefixEnd_1358860 := by exact prefixLift 1358860
  have htrace : WordTrace (prefixWord ++ tailWord_1358860) baseStart_1358860 baseEnd_1358860 := by
    simpa [prefixWord, tailWord_1358860, baseEnd_1358860] using wordTrace_append hprefix tailTrace_1358860
  have hstable : (prefixWord ++ tailWord_1358860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358860).length < 2 ^ (prefixWord ++ tailWord_1358860).sum := by decide
  have hdescent : baseEnd_1358860 < baseStart_1358860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358873 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_1358873 : Nat := 118140960795 + 1358873 * 2 ^ 59
def prefixEnd_1358873 : Nat := 4983230072969 + 3 ^ 40 * 1358873 * 2
def baseEnd_1358873 : Nat := 465169998278111424558775

theorem tailTrace_1358873 : CollatzResearch.WordTrace tailWord_1358873 prefixEnd_1358873 465169998278111424558775 := by
  unfold tailWord_1358873
  simp only [CollatzResearch.WordTrace]
  refine ⟨49562170006042672876913273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33041446670695115251275515 49562170006042672876913273)
  ·
    refine ⟨37171627504532004657684955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49562170006042672876913273 37171627504532004657684955)
    ·
      refine ⟨55757441256798006986527433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37171627504532004657684955 55757441256798006986527433)
      ·
        refine ⟨41818080942598505239895575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55757441256798006986527433 41818080942598505239895575)
        ·
          refine ⟨62727121413897757859843363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41818080942598505239895575 62727121413897757859843363)
          ·
            refine ⟨94090682120846636789765045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62727121413897757859843363 94090682120846636789765045)
            ·
              refine ⟨8821001448829372199040473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94090682120846636789765045 8821001448829372199040473)
              ·
                refine ⟨6615751086622029149280355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8821001448829372199040473 6615751086622029149280355)
                ·
                  refine ⟨9923626629933043723920533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6615751086622029149280355 9923626629933043723920533)
                  ·
                    refine ⟨465169998278111424558775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9923626629933043723920533 465169998278111424558775)
                    ·
                      rfl

theorem cell22_1358873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_1358873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358873 prefixEnd_1358873 := by exact prefixLift 1358873
  have htrace : WordTrace (prefixWord ++ tailWord_1358873) baseStart_1358873 baseEnd_1358873 := by
    simpa [prefixWord, tailWord_1358873, baseEnd_1358873] using wordTrace_append hprefix tailTrace_1358873
  have hstable : (prefixWord ++ tailWord_1358873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358873).length < 2 ^ (prefixWord ++ tailWord_1358873).sum := by decide
  have hdescent : baseEnd_1358873 < baseStart_1358873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358905 : List Nat := [1, 2, 1, 5, 2, 3, 8]
def baseStart_1358905 : Nat := 118140960795 + 1358905 * 2 ^ 59
def prefixEnd_1358905 : Nat := 4983230072969 + 3 ^ 40 * 1358905 * 2
def baseEnd_1358905 : Nat := 17228924167854592879951

theorem tailTrace_1358905 : CollatzResearch.WordTrace tailWord_1358905 prefixEnd_1358905 17228924167854592879951 := by
  unfold tailWord_1358905
  simp only [CollatzResearch.WordTrace]
  refine ⟨49563337141926742342078169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33042224761284494894718779 49563337141926742342078169)
  ·
    refine ⟨37172502856445056756558627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49563337141926742342078169 37172502856445056756558627)
    ·
      refine ⟨55758754284667585134837941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37172502856445056756558627 55758754284667585134837941)
      ·
        refine ⟨5227383214187586106391057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55758754284667585134837941 5227383214187586106391057)
        ·
          refine ⟨3920537410640689579793293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227383214187586106391057 3920537410640689579793293)
          ·
            refine ⟨1470201528990258592422485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3920537410640689579793293 1470201528990258592422485)
            ·
              refine ⟨17228924167854592879951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1470201528990258592422485 17228924167854592879951)
              ·
                rfl

theorem cell22_1358905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 8].length) (baseStart_1358905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358905 prefixEnd_1358905 := by exact prefixLift 1358905
  have htrace : WordTrace (prefixWord ++ tailWord_1358905) baseStart_1358905 baseEnd_1358905 := by
    simpa [prefixWord, tailWord_1358905, baseEnd_1358905] using wordTrace_append hprefix tailTrace_1358905
  have hstable : (prefixWord ++ tailWord_1358905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358905).length < 2 ^ (prefixWord ++ tailWord_1358905).sum := by decide
  have hdescent : baseEnd_1358905 < baseStart_1358905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359213 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1359213 : Nat := 118140960795 + 1359213 * 2 ^ 59
def prefixEnd_1359213 : Nat := 4983230072969 + 3 ^ 40 * 1359213 * 2
def baseEnd_1359213 : Nat := 465286387226463871057733

theorem tailTrace_1359213 : CollatzResearch.WordTrace tailWord_1359213 prefixEnd_1359213 465286387226463871057733 := by
  unfold tailWord_1359213
  simp only [CollatzResearch.WordTrace]
  refine ⟨49574570824810910944290293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33049713883207273962860195 49574570824810910944290293)
  ·
    refine ⟨4647616014826022901027215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49574570824810910944290293 4647616014826022901027215)
    ·
      refine ⟨6971424022239034351540823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647616014826022901027215 6971424022239034351540823)
      ·
        refine ⟨10457136033358551527311235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971424022239034351540823 10457136033358551527311235)
        ·
          refine ⟨15685704050037827290966853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457136033358551527311235 15685704050037827290966853)
          ·
            refine ⟨2941069509382092617056285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15685704050037827290966853 2941069509382092617056285)
            ·
              refine ⟨1102901066018284731396107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2941069509382092617056285 1102901066018284731396107)
              ·
                refine ⟨1654351599027427097094161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102901066018284731396107 1654351599027427097094161)
                ·
                  refine ⟨1240763699270570322820621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654351599027427097094161 1240763699270570322820621)
                  ·
                    refine ⟨465286387226463871057733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1240763699270570322820621 465286387226463871057733)
                    ·
                      rfl

theorem cell22_1359213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1359213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359213 prefixEnd_1359213 := by exact prefixLift 1359213
  have htrace : WordTrace (prefixWord ++ tailWord_1359213) baseStart_1359213 baseEnd_1359213 := by
    simpa [prefixWord, tailWord_1359213, baseEnd_1359213] using wordTrace_append hprefix tailTrace_1359213
  have hstable : (prefixWord ++ tailWord_1359213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359213).length < 2 ^ (prefixWord ++ tailWord_1359213).sum := by decide
  have hdescent : baseEnd_1359213 < baseStart_1359213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359237 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 7]
def baseStart_1359237 : Nat := 118140960795 + 1359237 * 2 ^ 59
def prefixEnd_1359237 : Nat := 4983230072969 + 3 ^ 40 * 1359237 * 2
def baseEnd_1359237 : Nat := 155098200972311936152553

theorem tailTrace_1359237 : CollatzResearch.WordTrace tailWord_1359237 prefixEnd_1359237 155098200972311936152553 := by
  unfold tailWord_1359237
  simp only [CollatzResearch.WordTrace]
  refine ⟨49575446176723963043163965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33050297451149308695442643 49575446176723963043163965)
  ·
    refine ⟨18590792316271486141186487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49575446176723963043163965 18590792316271486141186487)
    ·
      refine ⟨27886188474407229211779731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18590792316271486141186487 27886188474407229211779731)
      ·
        refine ⟨41829282711610843817669597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27886188474407229211779731 41829282711610843817669597)
        ·
          refine ⟨15685981016854066431626099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41829282711610843817669597 15685981016854066431626099)
          ·
            refine ⟨23528971525281099647439149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15685981016854066431626099 23528971525281099647439149)
            ·
              refine ⟨8823364321980412367789681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23528971525281099647439149 8823364321980412367789681)
              ·
                refine ⟨6617523241485309275842261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823364321980412367789681 6617523241485309275842261)
                ·
                  refine ⟨155098200972311936152553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6617523241485309275842261 155098200972311936152553)
                  ·
                    rfl

theorem cell22_1359237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_1359237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359237 prefixEnd_1359237 := by exact prefixLift 1359237
  have htrace : WordTrace (prefixWord ++ tailWord_1359237) baseStart_1359237 baseEnd_1359237 := by
    simpa [prefixWord, tailWord_1359237, baseEnd_1359237] using wordTrace_append hprefix tailTrace_1359237
  have hstable : (prefixWord ++ tailWord_1359237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359237).length < 2 ^ (prefixWord ++ tailWord_1359237).sum := by decide
  have hdescent : baseEnd_1359237 < baseStart_1359237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359331 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 1, 5]
def baseStart_1359331 : Nat := 118140960795 + 1359331 * 2 ^ 59
def prefixEnd_1359331 : Nat := 4983230072969 + 3 ^ 40 * 1359331 * 2
def baseEnd_1359331 : Nat := 465326781037950896607371

theorem tailTrace_1359331 : CollatzResearch.WordTrace tailWord_1359331 prefixEnd_1359331 465326781037950896607371 := by
  unfold tailWord_1359331
  simp only [CollatzResearch.WordTrace]
  refine ⟨49578874638383417097085847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33052583092255611398057231 49578874638383417097085847)
  ·
    refine ⟨74368311957575125645628771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49578874638383417097085847 74368311957575125645628771)
    ·
      refine ⟨111552467936362688468443157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74368311957575125645628771 111552467936362688468443157)
      ·
        refine ⟨5229021934517001021958273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111552467936362688468443157 5229021934517001021958273)
        ·
          refine ⟨3921766450887750766468705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5229021934517001021958273 3921766450887750766468705)
          ·
            refine ⟨2941324838165813074851529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3921766450887750766468705 2941324838165813074851529)
            ·
              refine ⟨2205993628624359806138647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2941324838165813074851529 2205993628624359806138647)
              ·
                refine ⟨3308990442936539709207971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205993628624359806138647 3308990442936539709207971)
                ·
                  refine ⟨4963485664404809563811957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308990442936539709207971 4963485664404809563811957)
                  ·
                    refine ⟨465326781037950896607371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4963485664404809563811957 465326781037950896607371)
                    ·
                      rfl

theorem cell22_1359331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_1359331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359331 prefixEnd_1359331 := by exact prefixLift 1359331
  have htrace : WordTrace (prefixWord ++ tailWord_1359331) baseStart_1359331 baseEnd_1359331 := by
    simpa [prefixWord, tailWord_1359331, baseEnd_1359331] using wordTrace_append hprefix tailTrace_1359331
  have hstable : (prefixWord ++ tailWord_1359331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359331).length < 2 ^ (prefixWord ++ tailWord_1359331).sum := by decide
  have hdescent : baseEnd_1359331 < baseStart_1359331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359346 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1359346 : Nat := 118140960795 + 1359346 * 2 ^ 59
def prefixEnd_1359346 : Nat := 4983230072969 + 3 ^ 40 * 1359346 * 2
def baseEnd_1359346 : Nat := 465331915844495857482325

theorem tailTrace_1359346 : CollatzResearch.WordTrace tailWord_1359346 prefixEnd_1359346 465331915844495857482325 := by
  unfold tailWord_1359346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394855433332268664720473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33052947822219383105921261 12394855433332268664720473)
  ·
    refine ⟨9296141574999201498540355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12394855433332268664720473 9296141574999201498540355)
    ·
      refine ⟨13944212362498802247810533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9296141574999201498540355 13944212362498802247810533)
      ·
        refine ⟨2614539817968525421464475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13944212362498802247810533 2614539817968525421464475)
        ·
          refine ⟨3921809726952788132196713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614539817968525421464475 3921809726952788132196713)
          ·
            refine ⟨2941357295214591099147535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3921809726952788132196713 2941357295214591099147535)
            ·
              refine ⟨4412035942821886648721303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941357295214591099147535 4412035942821886648721303)
              ·
                refine ⟨6618053914232829973081955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412035942821886648721303 6618053914232829973081955)
                ·
                  refine ⟨9927080871349244959622933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618053914232829973081955 9927080871349244959622933)
                  ·
                    refine ⟨465331915844495857482325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9927080871349244959622933 465331915844495857482325)
                    ·
                      rfl

theorem cell22_1359346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1359346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359346 prefixEnd_1359346 := by exact prefixLift 1359346
  have htrace : WordTrace (prefixWord ++ tailWord_1359346) baseStart_1359346 baseEnd_1359346 := by
    simpa [prefixWord, tailWord_1359346, baseEnd_1359346] using wordTrace_append hprefix tailTrace_1359346
  have hstable : (prefixWord ++ tailWord_1359346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359346).length < 2 ^ (prefixWord ++ tailWord_1359346).sum := by decide
  have hdescent : baseEnd_1359346 < baseStart_1359346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359406 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1359406 : Nat := 118140960795 + 1359406 * 2 ^ 59
def prefixEnd_1359406 : Nat := 4983230072969 + 3 ^ 40 * 1359406 * 2
def baseEnd_1359406 : Nat := 155117485023558566994047

theorem tailTrace_1359406 : CollatzResearch.WordTrace tailWord_1359406 prefixEnd_1359406 155117485023558566994047 := by
  unfold tailWord_1359406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197701264138963113258259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33054406742074469937377381 6197701264138963113258259)
  ·
    refine ⟨9296551896208444669887389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6197701264138963113258259 9296551896208444669887389)
    ·
      refine ⟨3486206961078166751207771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9296551896208444669887389 3486206961078166751207771)
      ·
        refine ⟨5229310441617250126811657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486206961078166751207771 5229310441617250126811657)
        ·
          refine ⟨3921982831212937595108743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5229310441617250126811657 3921982831212937595108743)
          ·
            refine ⟨5882974246819406392663115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921982831212937595108743 5882974246819406392663115)
            ·
              refine ⟨8824461370229109588994673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882974246819406392663115 8824461370229109588994673)
              ·
                refine ⟨6618346027671832191746005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8824461370229109588994673 6618346027671832191746005)
                ·
                  refine ⟨155117485023558566994047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6618346027671832191746005 155117485023558566994047)
                  ·
                    rfl

theorem cell22_1359406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1359406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359406 prefixEnd_1359406 := by exact prefixLift 1359406
  have htrace : WordTrace (prefixWord ++ tailWord_1359406) baseStart_1359406 baseEnd_1359406 := by
    simpa [prefixWord, tailWord_1359406, baseEnd_1359406] using wordTrace_append hprefix tailTrace_1359406
  have hstable : (prefixWord ++ tailWord_1359406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359406).length < 2 ^ (prefixWord ++ tailWord_1359406).sum := by decide
  have hdescent : baseEnd_1359406 < baseStart_1359406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359449 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_1359449 : Nat := 118140960795 + 1359449 * 2 ^ 59
def prefixEnd_1359449 : Nat := 4983230072969 + 3 ^ 40 * 1359449 * 2
def baseEnd_1359449 : Nat := 465367174849437922157009

theorem tailTrace_1359449 : CollatzResearch.WordTrace tailWord_1359449 prefixEnd_1359449 465367174849437922157009 := by
  unfold tailWord_1359449
  simp only [CollatzResearch.WordTrace]
  refine ⟨49583178451955923249881401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33055452301303948833254267 49583178451955923249881401)
  ·
    refine ⟨37187383838966942437411051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49583178451955923249881401 37187383838966942437411051)
    ·
      refine ⟨55781075758450413656116577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37187383838966942437411051 55781075758450413656116577)
      ·
        refine ⟨41835806818837810242087433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55781075758450413656116577 41835806818837810242087433)
        ·
          refine ⟨31376855114128357681565575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41835806818837810242087433 31376855114128357681565575)
          ·
            refine ⟨47065282671192536522348363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31376855114128357681565575 47065282671192536522348363)
            ·
              refine ⟨70597924006788804783522545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47065282671192536522348363 70597924006788804783522545)
              ·
                refine ⟨52948443005091603587641909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70597924006788804783522545 52948443005091603587641909)
                ·
                  refine ⟨4963916531727337836341429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52948443005091603587641909 4963916531727337836341429)
                  ·
                    refine ⟨465367174849437922157009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4963916531727337836341429 465367174849437922157009)
                    ·
                      rfl

theorem cell22_1359449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_1359449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359449 prefixEnd_1359449 := by exact prefixLift 1359449
  have htrace : WordTrace (prefixWord ++ tailWord_1359449) baseStart_1359449 baseEnd_1359449 := by
    simpa [prefixWord, tailWord_1359449, baseEnd_1359449] using wordTrace_append hprefix tailTrace_1359449
  have hstable : (prefixWord ++ tailWord_1359449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359449).length < 2 ^ (prefixWord ++ tailWord_1359449).sum := by decide
  have hdescent : baseEnd_1359449 < baseStart_1359449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359466 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1359466 : Nat := 118140960795 + 1359466 * 2 ^ 59
def prefixEnd_1359466 : Nat := 4983230072969 + 3 ^ 40 * 1359466 * 2
def baseEnd_1359466 : Nat := 465372994296855544481957

theorem tailTrace_1359466 : CollatzResearch.WordTrace tailWord_1359466 prefixEnd_1359466 465372994296855544481957 := by
  unfold tailWord_1359466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12395949623223583788312563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33055865661929556768833501 12395949623223583788312563)
  ·
    refine ⟨18593924434835375682468845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12395949623223583788312563 18593924434835375682468845)
    ·
      refine ⟨6972721663063265880925817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18593924434835375682468845 6972721663063265880925817)
      ·
        refine ⟨5229541247297449410694363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6972721663063265880925817 5229541247297449410694363)
        ·
          refine ⟨7844311870946174116041545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229541247297449410694363 7844311870946174116041545)
          ·
            refine ⟨5883233903209630587031159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7844311870946174116041545 5883233903209630587031159)
            ·
              refine ⟨8824850854814445880546739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5883233903209630587031159 8824850854814445880546739)
              ·
                refine ⟨13237276282221668820820109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8824850854814445880546739 13237276282221668820820109)
                ·
                  refine ⟨4963978605833125807807541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13237276282221668820820109 4963978605833125807807541)
                  ·
                    refine ⟨465372994296855544481957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4963978605833125807807541 465372994296855544481957)
                    ·
                      rfl

theorem cell22_1359466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1359466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359466 prefixEnd_1359466 := by exact prefixLift 1359466
  have htrace : WordTrace (prefixWord ++ tailWord_1359466) baseStart_1359466 baseEnd_1359466 := by
    simpa [prefixWord, tailWord_1359466, baseEnd_1359466] using wordTrace_append hprefix tailTrace_1359466
  have hstable : (prefixWord ++ tailWord_1359466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359466).length < 2 ^ (prefixWord ++ tailWord_1359466).sum := by decide
  have hdescent : baseEnd_1359466 < baseStart_1359466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359481 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_1359481 : Nat := 118140960795 + 1359481 * 2 ^ 59
def prefixEnd_1359481 : Nat := 4983230072969 + 3 ^ 40 * 1359481 * 2
def baseEnd_1359481 : Nat := 465378129103400505356911

theorem tailTrace_1359481 : CollatzResearch.WordTrace tailWord_1359481 prefixEnd_1359481 465378129103400505356911 := by
  unfold tailWord_1359481
  simp only [CollatzResearch.WordTrace]
  refine ⟨49584345587839992715046297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33056230391893328476697531 49584345587839992715046297)
  ·
    refine ⟨37188259190879994536284723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49584345587839992715046297 37188259190879994536284723)
    ·
      refine ⟨55782388786319991804427085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37188259190879994536284723 55782388786319991804427085)
      ·
        refine ⟨20918395794869996926660157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55782388786319991804427085 20918395794869996926660157)
        ·
          refine ⟨7844398423076248847497559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20918395794869996926660157 7844398423076248847497559)
          ·
            refine ⟨11766597634614373271246339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7844398423076248847497559 11766597634614373271246339)
            ·
              refine ⟨17649896451921559906869509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11766597634614373271246339 17649896451921559906869509)
              ·
                refine ⟨3309355584735292482538033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17649896451921559906869509 3309355584735292482538033)
                ·
                  refine ⟨2482016688551469361903525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309355584735292482538033 2482016688551469361903525)
                  ·
                    refine ⟨465378129103400505356911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2482016688551469361903525 465378129103400505356911)
                    ·
                      rfl

theorem cell22_1359481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_1359481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359481 prefixEnd_1359481 := by exact prefixLift 1359481
  have htrace : WordTrace (prefixWord ++ tailWord_1359481) baseStart_1359481 baseEnd_1359481 := by
    simpa [prefixWord, tailWord_1359481, baseEnd_1359481] using wordTrace_append hprefix tailTrace_1359481
  have hstable : (prefixWord ++ tailWord_1359481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359481).length < 2 ^ (prefixWord ++ tailWord_1359481).sum := by decide
  have hdescent : baseEnd_1359481 < baseStart_1359481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359483 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 2, 3]
def baseStart_1359483 : Nat := 118140960795 + 1359483 * 2 ^ 59
def prefixEnd_1359483 : Nat := 4983230072969 + 3 ^ 40 * 1359483 * 2
def baseEnd_1359483 : Nat := 465378813744273166806905

theorem tailTrace_1359483 : CollatzResearch.WordTrace tailWord_1359483 prefixEnd_1359483 465378813744273166806905 := by
  unfold tailWord_1359483
  simp only [CollatzResearch.WordTrace]
  refine ⟨49584418533832747056619103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33056279022555164704412735 49584418533832747056619103)
  ·
    refine ⟨74376627800749120584928655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49584418533832747056619103 74376627800749120584928655)
    ·
      refine ⟨111564941701123680877392983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74376627800749120584928655 111564941701123680877392983)
      ·
        refine ⟨167347412551685521316089475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111564941701123680877392983 167347412551685521316089475)
        ·
          refine ⟨251021118827528281974134213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167347412551685521316089475 251021118827528281974134213)
          ·
            refine ⟨47066459780161552870150165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251021118827528281974134213 47066459780161552870150165)
            ·
              refine ⟨2206240302195072790788289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47066459780161552870150165 2206240302195072790788289)
              ·
                refine ⟨1654680226646304593091217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206240302195072790788289 1654680226646304593091217)
                ·
                  refine ⟨1241010169984728444818413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654680226646304593091217 1241010169984728444818413)
                  ·
                    refine ⟨465378813744273166806905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241010169984728444818413 465378813744273166806905)
                    ·
                      rfl

theorem cell22_1359483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3].length) (baseStart_1359483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359483 prefixEnd_1359483 := by exact prefixLift 1359483
  have htrace : WordTrace (prefixWord ++ tailWord_1359483) baseStart_1359483 baseEnd_1359483 := by
    simpa [prefixWord, tailWord_1359483, baseEnd_1359483] using wordTrace_append hprefix tailTrace_1359483
  have hstable : (prefixWord ++ tailWord_1359483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359483).length < 2 ^ (prefixWord ++ tailWord_1359483).sum := by decide
  have hdescent : baseEnd_1359483 < baseStart_1359483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359485 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 4]
def baseStart_1359485 : Nat := 118140960795 + 1359485 * 2 ^ 59
def prefixEnd_1359485 : Nat := 4983230072969 + 3 ^ 40 * 1359485 * 2
def baseEnd_1359485 : Nat := 155126499461715276085633

theorem tailTrace_1359485 : CollatzResearch.WordTrace tailWord_1359485 prefixEnd_1359485 155126499461715276085633 := by
  unfold tailWord_1359485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49584491479825501398191909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33056327653217000932127939 49584491479825501398191909)
  ·
    refine ⟨9297092152467281512160983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49584491479825501398191909 9297092152467281512160983)
    ·
      refine ⟨13945638228700922268241475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9297092152467281512160983 13945638228700922268241475)
      ·
        refine ⟨20918457343051383402362213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13945638228700922268241475 20918457343051383402362213)
        ·
          refine ⟨3922210751822134387942915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20918457343051383402362213 3922210751822134387942915)
          ·
            refine ⟨5883316127733201581914373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3922210751822134387942915 5883316127733201581914373)
            ·
              refine ⟨1103121773949975296608945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5883316127733201581914373 1103121773949975296608945)
              ·
                refine ⟨827341330462481472456709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103121773949975296608945 827341330462481472456709)
                ·
                  refine ⟨155126499461715276085633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827341330462481472456709 155126499461715276085633)
                  ·
                    rfl

theorem cell22_1359485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_1359485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359485 prefixEnd_1359485 := by exact prefixLift 1359485
  have htrace : WordTrace (prefixWord ++ tailWord_1359485) baseStart_1359485 baseEnd_1359485 := by
    simpa [prefixWord, tailWord_1359485, baseEnd_1359485] using wordTrace_append hprefix tailTrace_1359485
  have hstable : (prefixWord ++ tailWord_1359485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359485).length < 2 ^ (prefixWord ++ tailWord_1359485).sum := by decide
  have hdescent : baseEnd_1359485 < baseStart_1359485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359534 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1359534 : Nat := 118140960795 + 1359534 * 2 ^ 59
def prefixEnd_1359534 : Nat := 4983230072969 + 3 ^ 40 * 1359534 * 2
def baseEnd_1359534 : Nat := 465396272086526033781749

theorem tailTrace_1359534 : CollatzResearch.WordTrace tailWord_1359534 prefixEnd_1359534 465396272086526033781749 := by
  unfold tailWord_1359534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198284832080997845840707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33057519104431988511150437 6198284832080997845840707)
  ·
    refine ⟨9297427248121496768761061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6198284832080997845840707 9297427248121496768761061)
    ·
      refine ⟨1743267609022780644142699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9297427248121496768761061 1743267609022780644142699)
      ·
        refine ⟨2614901413534170966214049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743267609022780644142699 2614901413534170966214049)
        ·
          refine ⟨1961176060150628224660537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2614901413534170966214049 1961176060150628224660537)
          ·
            refine ⟨1470882045112971168495403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961176060150628224660537 1470882045112971168495403)
            ·
              refine ⟨2206323067669456752743105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470882045112971168495403 2206323067669456752743105)
              ·
                refine ⟨1654742300752092564557329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206323067669456752743105 1654742300752092564557329)
                ·
                  refine ⟨1241056725564069423417997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654742300752092564557329 1241056725564069423417997)
                  ·
                    refine ⟨465396272086526033781749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241056725564069423417997 465396272086526033781749)
                    ·
                      rfl

theorem cell22_1359534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1359534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359534 prefixEnd_1359534 := by exact prefixLift 1359534
  have htrace : WordTrace (prefixWord ++ tailWord_1359534) baseStart_1359534 baseEnd_1359534 := by
    simpa [prefixWord, tailWord_1359534, baseEnd_1359534] using wordTrace_append hprefix tailTrace_1359534
  have hstable : (prefixWord ++ tailWord_1359534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359534).length < 2 ^ (prefixWord ++ tailWord_1359534).sum := by decide
  have hdescent : baseEnd_1359534 < baseStart_1359534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359545 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 1, 3]
def baseStart_1359545 : Nat := 118140960795 + 1359545 * 2 ^ 59
def prefixEnd_1359545 : Nat := 4983230072969 + 3 ^ 40 * 1359545 * 2
def baseEnd_1359545 : Nat := 465400037611325671756715

theorem tailTrace_1359545 : CollatzResearch.WordTrace tailWord_1359545 prefixEnd_1359545 465400037611325671756715 := by
  unfold tailWord_1359545
  simp only [CollatzResearch.WordTrace]
  refine ⟨49586679859608131645376089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33057786573072087763584059 49586679859608131645376089)
  ·
    refine ⟨37190009894706098734032067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49586679859608131645376089 37190009894706098734032067)
    ·
      refine ⟨55785014842059148101048101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37190009894706098734032067 55785014842059148101048101)
      ·
        refine ⟨10459690282886090268946519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55785014842059148101048101 10459690282886090268946519)
        ·
          refine ⟨15689535424329135403419779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10459690282886090268946519 15689535424329135403419779)
          ·
            refine ⟨23534303136493703105129669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15689535424329135403419779 23534303136493703105129669)
            ·
              refine ⟨4412681838092569332211813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23534303136493703105129669 4412681838092569332211813)
              ·
                refine ⟨827377844642356749789715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4412681838092569332211813 827377844642356749789715)
                ·
                  refine ⟨1241066766963535124684573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827377844642356749789715 1241066766963535124684573)
                  ·
                    refine ⟨465400037611325671756715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241066766963535124684573 465400037611325671756715)
                    ·
                      rfl

theorem cell22_1359545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_1359545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359545 prefixEnd_1359545 := by exact prefixLift 1359545
  have htrace : WordTrace (prefixWord ++ tailWord_1359545) baseStart_1359545 baseEnd_1359545 := by
    simpa [prefixWord, tailWord_1359545, baseEnd_1359545] using wordTrace_append hprefix tailTrace_1359545
  have hstable : (prefixWord ++ tailWord_1359545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359545).length < 2 ^ (prefixWord ++ tailWord_1359545).sum := by decide
  have hdescent : baseEnd_1359545 < baseStart_1359545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359588 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1359588 : Nat := 118140960795 + 1359588 * 2 ^ 59
def prefixEnd_1359588 : Nat := 4983230072969 + 3 ^ 40 * 1359588 * 2
def baseEnd_1359588 : Nat := 465414757390087892931583

theorem tailTrace_1359588 : CollatzResearch.WordTrace tailWord_1359588 prefixEnd_1359588 465414757390087892931583 := by
  unfold tailWord_1359588
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794124099226174994595709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33058832132301566659460945 24794124099226174994595709)
  ·
    refine ⟨9297796537209815622973391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24794124099226174994595709 9297796537209815622973391)
    ·
      refine ⟨13946694805814723434460087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9297796537209815622973391 13946694805814723434460087)
      ·
        refine ⟨20920042208722085151690131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13946694805814723434460087 20920042208722085151690131)
        ·
          refine ⟨31380063313083127727535197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20920042208722085151690131 31380063313083127727535197)
          ·
            refine ⟨11767523742406172897825699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31380063313083127727535197 11767523742406172897825699)
            ·
              refine ⟨17651285613609259346738549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767523742406172897825699 17651285613609259346738549)
              ·
                refine ⟨1654808026275868063756739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17651285613609259346738549 1654808026275868063756739)
                ·
                  refine ⟨2482212039413802095635109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1654808026275868063756739 2482212039413802095635109)
                  ·
                    refine ⟨465414757390087892931583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2482212039413802095635109 465414757390087892931583)
                    ·
                      rfl

theorem cell22_1359588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1359588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359588 prefixEnd_1359588 := by exact prefixLift 1359588
  have htrace : WordTrace (prefixWord ++ tailWord_1359588) baseStart_1359588 baseEnd_1359588 := by
    simpa [prefixWord, tailWord_1359588, baseEnd_1359588] using wordTrace_append hprefix tailTrace_1359588
  have hstable : (prefixWord ++ tailWord_1359588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359588).length < 2 ^ (prefixWord ++ tailWord_1359588).sum := by decide
  have hdescent : baseEnd_1359588 < baseStart_1359588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359603 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 4]
def baseStart_1359603 : Nat := 118140960795 + 1359603 * 2 ^ 59
def prefixEnd_1359603 : Nat := 4983230072969 + 3 ^ 40 * 1359603 * 2
def baseEnd_1359603 : Nat := 155139964065544284602179

theorem tailTrace_1359603 : CollatzResearch.WordTrace tailWord_1359603 prefixEnd_1359603 155139964065544284602179 := by
  unfold tailWord_1359603
  simp only [CollatzResearch.WordTrace]
  refine ⟨49588795293398007550987463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33059196862265338367324975 49588795293398007550987463)
  ·
    refine ⟨74383192940097011326481195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49588795293398007550987463 74383192940097011326481195)
    ·
      refine ⟨111574789410145516989721793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74383192940097011326481195 111574789410145516989721793)
      ·
        refine ⟨83681092057609137742291345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111574789410145516989721793 83681092057609137742291345)
        ·
          refine ⟨62760819043206853306718509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83681092057609137742291345 62760819043206853306718509)
          ·
            refine ⟨23535307141202569990019441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62760819043206853306718509 23535307141202569990019441)
            ·
              refine ⟨17651480355901927492514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23535307141202569990019441 17651480355901927492514581)
              ·
                refine ⟨827413141682902851211621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17651480355901927492514581 827413141682902851211621)
                ·
                  refine ⟨155139964065544284602179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827413141682902851211621 155139964065544284602179)
                  ·
                    rfl

theorem cell22_1359603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 4].length) (baseStart_1359603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359603 prefixEnd_1359603 := by exact prefixLift 1359603
  have htrace : WordTrace (prefixWord ++ tailWord_1359603) baseStart_1359603 baseEnd_1359603 := by
    simpa [prefixWord, tailWord_1359603, baseEnd_1359603] using wordTrace_append hprefix tailTrace_1359603
  have hstable : (prefixWord ++ tailWord_1359603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359603).length < 2 ^ (prefixWord ++ tailWord_1359603).sum := by decide
  have hdescent : baseEnd_1359603 < baseStart_1359603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359652 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_1359652 : Nat := 118140960795 + 1359652 * 2 ^ 59
def prefixEnd_1359652 : Nat := 4983230072969 + 3 ^ 40 * 1359652 * 2
def baseEnd_1359652 : Nat := 465436665898013059331387

theorem tailTrace_1359652 : CollatzResearch.WordTrace tailWord_1359652 prefixEnd_1359652 465436665898013059331387 := by
  unfold tailWord_1359652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24795291235110244459760605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33060388313480325946347473 24795291235110244459760605)
  ·
    refine ⟨9298234213166341672410227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24795291235110244459760605 9298234213166341672410227)
    ·
      refine ⟨13947351319749512508615341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9298234213166341672410227 13947351319749512508615341)
      ·
        refine ⟨5230256744906067190730753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13947351319749512508615341 5230256744906067190730753)
        ·
          refine ⟨3922692558679550393048065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5230256744906067190730753 3922692558679550393048065)
          ·
            refine ⟨2942019419009662794786049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922692558679550393048065 2942019419009662794786049)
            ·
              refine ⟨2206514564257247096089537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942019419009662794786049 2206514564257247096089537)
              ·
                refine ⟨1654885923192935322067153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206514564257247096089537 1654885923192935322067153)
                ·
                  refine ⟨1241164442394701491550365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1654885923192935322067153 1241164442394701491550365)
                  ·
                    refine ⟨465436665898013059331387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241164442394701491550365 465436665898013059331387)
                    ·
                      rfl

theorem cell22_1359652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_1359652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359652 prefixEnd_1359652 := by exact prefixLift 1359652
  have htrace : WordTrace (prefixWord ++ tailWord_1359652) baseStart_1359652 baseEnd_1359652 := by
    simpa [prefixWord, tailWord_1359652, baseEnd_1359652] using wordTrace_append hprefix tailTrace_1359652
  have hstable : (prefixWord ++ tailWord_1359652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359652).length < 2 ^ (prefixWord ++ tailWord_1359652).sum := by decide
  have hdescent : baseEnd_1359652 < baseStart_1359652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359697 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 1, 3]
def baseStart_1359697 : Nat := 118140960795 + 1359697 * 2 ^ 59
def prefixEnd_1359697 : Nat := 4983230072969 + 3 ^ 40 * 1359697 * 2
def baseEnd_1359697 : Nat := 465452070317647941956249

theorem tailTrace_1359697 : CollatzResearch.WordTrace tailWord_1359697 prefixEnd_1359697 465452070317647941956249 := by
  unfold tailWord_1359697
  simp only [CollatzResearch.WordTrace]
  refine ⟨49592223755057461604909345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33061482503371641069939563 49592223755057461604909345)
  ·
    refine ⟨37194167816293096203682009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49592223755057461604909345 37194167816293096203682009)
    ·
      refine ⟨27895625862219822152761507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37194167816293096203682009 27895625862219822152761507)
      ·
        refine ⟨41843438793329733229142261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27895625862219822152761507 41843438793329733229142261)
        ·
          refine ⟨3922822386874662490232087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41843438793329733229142261 3922822386874662490232087)
          ·
            refine ⟨5884233580311993735348131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3922822386874662490232087 5884233580311993735348131)
            ·
              refine ⟨8826350370467990603022197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5884233580311993735348131 8826350370467990603022197)
              ·
                refine ⟨827470347231374119033331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8826350370467990603022197 827470347231374119033331)
                ·
                  refine ⟨1241205520847061178549997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827470347231374119033331 1241205520847061178549997)
                  ·
                    refine ⟨465452070317647941956249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241205520847061178549997 465452070317647941956249)
                    ·
                      rfl

theorem cell22_1359697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_1359697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359697 prefixEnd_1359697 := by exact prefixLift 1359697
  have htrace : WordTrace (prefixWord ++ tailWord_1359697) baseStart_1359697 baseEnd_1359697 := by
    simpa [prefixWord, tailWord_1359697, baseEnd_1359697] using wordTrace_append hprefix tailTrace_1359697
  have hstable : (prefixWord ++ tailWord_1359697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359697).length < 2 ^ (prefixWord ++ tailWord_1359697).sum := by decide
  have hdescent : baseEnd_1359697 < baseStart_1359697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359714 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1359714 : Nat := 118140960795 + 1359714 * 2 ^ 59
def prefixEnd_1359714 : Nat := 4983230072969 + 3 ^ 40 * 1359714 * 2
def baseEnd_1359714 : Nat := 465457889765065564281197

theorem tailTrace_1359714 : CollatzResearch.WordTrace tailWord_1359714 prefixEnd_1359714 465457889765065564281197 := by
  unfold tailWord_1359714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398210948998968377069549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33061895863997249005518797 12398210948998968377069549)
  ·
    refine ⟨4649329105874613141401081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12398210948998968377069549 4649329105874613141401081)
    ·
      refine ⟨3486996829405959856050811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4649329105874613141401081 3486996829405959856050811)
      ·
        refine ⟨5230495244108939784076217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486996829405959856050811 5230495244108939784076217)
        ·
          refine ⟨3922871433081704838057163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5230495244108939784076217 3922871433081704838057163)
          ·
            refine ⟨5884307149622557257085745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3922871433081704838057163 5884307149622557257085745)
            ·
              refine ⟨4413230362216917942814309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5884307149622557257085745 4413230362216917942814309)
              ·
                refine ⟨827480692915672114277683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4413230362216917942814309 827480692915672114277683)
                ·
                  refine ⟨1241221039373508171416525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827480692915672114277683 1241221039373508171416525)
                  ·
                    refine ⟨465457889765065564281197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241221039373508171416525 465457889765065564281197)
                    ·
                      rfl

theorem cell22_1359714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1359714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359714 prefixEnd_1359714 := by exact prefixLift 1359714
  have htrace : WordTrace (prefixWord ++ tailWord_1359714) baseStart_1359714 baseEnd_1359714 := by
    simpa [prefixWord, tailWord_1359714, baseEnd_1359714] using wordTrace_append hprefix tailTrace_1359714
  have hstable : (prefixWord ++ tailWord_1359714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359714).length < 2 ^ (prefixWord ++ tailWord_1359714).sum := by decide
  have hdescent : baseEnd_1359714 < baseStart_1359714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359738 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_1359738 : Nat := 118140960795 + 1359738 * 2 ^ 59
def prefixEnd_1359738 : Nat := 4983230072969 + 3 ^ 40 * 1359738 * 2
def baseEnd_1359738 : Nat := 155155368485179167227041

theorem tailTrace_1359738 : CollatzResearch.WordTrace tailWord_1359738 prefixEnd_1359738 155155368485179167227041 := by
  unfold tailWord_1359738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398429786977231401787967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33062479431939283738101245 12398429786977231401787967)
  ·
    refine ⟨18597644680465847102681951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12398429786977231401787967 18597644680465847102681951)
    ·
      refine ⟨27896467020698770654022927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18597644680465847102681951 27896467020698770654022927)
      ·
        refine ⟨41844700531048155981034391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27896467020698770654022927 41844700531048155981034391)
        ·
          refine ⟨62767050796572233971551587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41844700531048155981034391 62767050796572233971551587)
          ·
            refine ⟨94150576194858350957327381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62767050796572233971551587 94150576194858350957327381)
            ·
              refine ⟨4413308259133985201124721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94150576194858350957327381 4413308259133985201124721)
              ·
                refine ⟨3309981194350488900843541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413308259133985201124721 3309981194350488900843541)
                ·
                  refine ⟨155155368485179167227041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3309981194350488900843541 155155368485179167227041)
                  ·
                    rfl

theorem cell22_1359738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_1359738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359738 prefixEnd_1359738 := by exact prefixLift 1359738
  have htrace : WordTrace (prefixWord ++ tailWord_1359738) baseStart_1359738 baseEnd_1359738 := by
    simpa [prefixWord, tailWord_1359738, baseEnd_1359738] using wordTrace_append hprefix tailTrace_1359738
  have hstable : (prefixWord ++ tailWord_1359738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359738).length < 2 ^ (prefixWord ++ tailWord_1359738).sum := by decide
  have hdescent : baseEnd_1359738 < baseStart_1359738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359753 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_1359753 : Nat := 118140960795 + 1359753 * 2 ^ 59
def prefixEnd_1359753 : Nat := 4983230072969 + 3 ^ 40 * 1359753 * 2
def baseEnd_1359753 : Nat := 465471240262082462556077

theorem tailTrace_1359753 : CollatzResearch.WordTrace tailWord_1359753 prefixEnd_1359753 465471240262082462556077 := by
  unfold tailWord_1359753
  simp only [CollatzResearch.WordTrace]
  refine ⟨49594266242854583168947913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33062844161903055445965275 49594266242854583168947913)
  ·
    refine ⟨37195699682140937376710935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49594266242854583168947913 37195699682140937376710935)
    ·
      refine ⟨55793549523211406065066403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37195699682140937376710935 55793549523211406065066403)
      ·
        refine ⟨83690324284817109097599605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55793549523211406065066403 83690324284817109097599605)
        ·
          refine ⟨7845967901701603977899963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83690324284817109097599605 7845967901701603977899963)
          ·
            refine ⟨11768951852552405966849945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845967901701603977899963 11768951852552405966849945)
            ·
              refine ⟨8826713889414304475137459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11768951852552405966849945 8826713889414304475137459)
              ·
                refine ⟨13240070834121456712706189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8826713889414304475137459 13240070834121456712706189)
                ·
                  refine ⟨4965026562795546267264821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13240070834121456712706189 4965026562795546267264821)
                  ·
                    refine ⟨465471240262082462556077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4965026562795546267264821 465471240262082462556077)
                    ·
                      rfl

theorem cell22_1359753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_1359753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359753 prefixEnd_1359753 := by exact prefixLift 1359753
  have htrace : WordTrace (prefixWord ++ tailWord_1359753) baseStart_1359753 baseEnd_1359753 := by
    simpa [prefixWord, tailWord_1359753, baseEnd_1359753] using wordTrace_append hprefix tailTrace_1359753
  have hstable : (prefixWord ++ tailWord_1359753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359753).length < 2 ^ (prefixWord ++ tailWord_1359753).sum := by decide
  have hdescent : baseEnd_1359753 < baseStart_1359753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359772 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1359772 : Nat := 118140960795 + 1359772 * 2 ^ 59
def prefixEnd_1359772 : Nat := 4983230072969 + 3 ^ 40 * 1359772 * 2
def baseEnd_1359772 : Nat := 155159248116790915443673

theorem tailTrace_1359772 : CollatzResearch.WordTrace tailWord_1359772 prefixEnd_1359772 155159248116790915443673 := by
  unfold tailWord_1359772
  simp only [CollatzResearch.WordTrace]
  refine ⟨24797479614892874706944785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33063306153190499609259713 24797479614892874706944785)
  ·
    refine ⟨18598109711169656030208589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24797479614892874706944785 18598109711169656030208589)
    ·
      refine ⟨6974291141688621011328221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18598109711169656030208589 6974291141688621011328221)
      ·
        refine ⟨2615359178133232879248083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6974291141688621011328221 2615359178133232879248083)
        ·
          refine ⟨3923038767199849318872125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2615359178133232879248083 3923038767199849318872125)
          ·
            refine ⟨1471139537699943494577047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3923038767199849318872125 1471139537699943494577047)
            ·
              refine ⟨2206709306549915241865571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471139537699943494577047 2206709306549915241865571)
              ·
                refine ⟨3310063959824872862798357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206709306549915241865571 3310063959824872862798357)
                ·
                  refine ⟨155159248116790915443673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3310063959824872862798357 155159248116790915443673)
                  ·
                    rfl

theorem cell22_1359772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1359772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359772 prefixEnd_1359772 := by exact prefixLift 1359772
  have htrace : WordTrace (prefixWord ++ tailWord_1359772) baseStart_1359772 baseEnd_1359772 := by
    simpa [prefixWord, tailWord_1359772, baseEnd_1359772] using wordTrace_append hprefix tailTrace_1359772
  have hstable : (prefixWord ++ tailWord_1359772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359772).length < 2 ^ (prefixWord ++ tailWord_1359772).sum := by decide
  have hdescent : baseEnd_1359772 < baseStart_1359772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359920 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_1359920 : Nat := 118140960795 + 1359920 * 2 ^ 59
def prefixEnd_1359920 : Nat := 4983230072969 + 3 ^ 40 * 1359920 * 2
def baseEnd_1359920 : Nat := 465528407774949693630565

theorem tailTrace_1359920 : CollatzResearch.WordTrace tailWord_1359920 prefixEnd_1359920 465528407774949693630565 := by
  unfold tailWord_1359920
  simp only [CollatzResearch.WordTrace]
  refine ⟨24800178616624785345138607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33066904822166380460184809 24800178616624785345138607)
  ·
    refine ⟨37200267924937178017707911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24800178616624785345138607 37200267924937178017707911)
    ·
      refine ⟨55800401887405767026561867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37200267924937178017707911 55800401887405767026561867)
      ·
        refine ⟨83700602831108650539842801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55800401887405767026561867 83700602831108650539842801)
        ·
          refine ⟨62775452123331487904882101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83700602831108650539842801 62775452123331487904882101)
          ·
            refine ⟨5885198636562326991082697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62775452123331487904882101 5885198636562326991082697)
            ·
              refine ⟨4413898977421745243312023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885198636562326991082697 4413898977421745243312023)
              ·
                refine ⟨6620848466132617864968035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413898977421745243312023 6620848466132617864968035)
                ·
                  refine ⟨9931272699198926797452053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620848466132617864968035 9931272699198926797452053)
                  ·
                    refine ⟨465528407774949693630565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9931272699198926797452053 465528407774949693630565)
                    ·
                      rfl

theorem cell22_1359920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_1359920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359920 prefixEnd_1359920 := by exact prefixLift 1359920
  have htrace : WordTrace (prefixWord ++ tailWord_1359920) baseStart_1359920 baseEnd_1359920 := by
    simpa [prefixWord, tailWord_1359920, baseEnd_1359920] using wordTrace_append hprefix tailTrace_1359920
  have hstable : (prefixWord ++ tailWord_1359920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359920).length < 2 ^ (prefixWord ++ tailWord_1359920).sum := by decide
  have hdescent : baseEnd_1359920 < baseStart_1359920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359922 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_1359922 : Nat := 118140960795 + 1359922 * 2 ^ 59
def prefixEnd_1359922 : Nat := 4983230072969 + 3 ^ 40 * 1359922 * 2
def baseEnd_1359922 : Nat := 465529092415822355080559

theorem tailTrace_1359922 : CollatzResearch.WordTrace tailWord_1359922 prefixEnd_1359922 465529092415822355080559 := by
  unfold tailWord_1359922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400107544810581257962505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33066953452828216687900013 12400107544810581257962505)
  ·
    refine ⟨9300080658607935943471879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12400107544810581257962505 9300080658607935943471879)
    ·
      refine ⟨13950120987911903915207819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9300080658607935943471879 13950120987911903915207819)
      ·
        refine ⟨20925181481867855872811729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13950120987911903915207819 20925181481867855872811729)
        ·
          refine ⟨15693886111400891904608797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20925181481867855872811729 15693886111400891904608797)
          ·
            refine ⟨5885207291775334464228299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15693886111400891904608797 5885207291775334464228299)
            ·
              refine ⟨8827810937663001696342449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885207291775334464228299 8827810937663001696342449)
              ·
                refine ⟨6620858203247251272256837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8827810937663001696342449 6620858203247251272256837)
                ·
                  refine ⟨1241410913108859613548157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6620858203247251272256837 1241410913108859613548157)
                  ·
                    refine ⟨465529092415822355080559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241410913108859613548157 465529092415822355080559)
                    ·
                      rfl

theorem cell22_1359922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_1359922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359922 prefixEnd_1359922 := by exact prefixLift 1359922
  have htrace : WordTrace (prefixWord ++ tailWord_1359922) baseStart_1359922 baseEnd_1359922 := by
    simpa [prefixWord, tailWord_1359922, baseEnd_1359922] using wordTrace_append hprefix tailTrace_1359922
  have hstable : (prefixWord ++ tailWord_1359922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359922).length < 2 ^ (prefixWord ++ tailWord_1359922).sum := by decide
  have hdescent : baseEnd_1359922 < baseStart_1359922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359937 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1359937 : Nat := 118140960795 + 1359937 * 2 ^ 59
def prefixEnd_1359937 : Nat := 4983230072969 + 3 ^ 40 * 1359937 * 2
def baseEnd_1359937 : Nat := 465534227222367315955513

theorem tailTrace_1359937 : CollatzResearch.WordTrace tailWord_1359937 prefixEnd_1359937 465534227222367315955513 := by
  unfold tailWord_1359937
  simp only [CollatzResearch.WordTrace]
  refine ⟨49600977274187982593646065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33067318182791988395764043 49600977274187982593646065)
  ·
    refine ⟨37200732955640986945234549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49600977274187982593646065 37200732955640986945234549)
    ·
      refine ⟨3487568714591342526115739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37200732955640986945234549 3487568714591342526115739)
      ·
        refine ⟨5231353071887013789173609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487568714591342526115739 5231353071887013789173609)
        ·
          refine ⟨3923514803915260341880207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231353071887013789173609 3923514803915260341880207)
          ·
            refine ⟨5885272205872890512820311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923514803915260341880207 5885272205872890512820311)
            ·
              refine ⟨8827908308809335769230467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885272205872890512820311 8827908308809335769230467)
              ·
                refine ⟨13241862463214003653845701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8827908308809335769230467 13241862463214003653845701)
                ·
                  refine ⟨2482849211852625685096069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13241862463214003653845701 2482849211852625685096069)
                  ·
                    refine ⟨465534227222367315955513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2482849211852625685096069 465534227222367315955513)
                    ·
                      rfl

theorem cell22_1359937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1359937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359937 prefixEnd_1359937 := by exact prefixLift 1359937
  have htrace : WordTrace (prefixWord ++ tailWord_1359937) baseStart_1359937 baseEnd_1359937 := by
    simpa [prefixWord, tailWord_1359937, baseEnd_1359937] using wordTrace_append hprefix tailTrace_1359937
  have hstable : (prefixWord ++ tailWord_1359937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359937).length < 2 ^ (prefixWord ++ tailWord_1359937).sum := by decide
  have hdescent : baseEnd_1359937 < baseStart_1359937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359997 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1359997 : Nat := 118140960795 + 1359997 * 2 ^ 59
def prefixEnd_1359997 : Nat := 4983230072969 + 3 ^ 40 * 1359997 * 2
def baseEnd_1359997 : Nat := 155184922149515719818443

theorem tailTrace_1359997 : CollatzResearch.WordTrace tailWord_1359997 prefixEnd_1359997 155184922149515719818443 := by
  unfold tailWord_1359997
  simp only [CollatzResearch.WordTrace]
  refine ⟨49603165653970612840830245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33068777102647075227220163 49603165653970612840830245)
  ·
    refine ⟨9300593560119489907655671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49603165653970612840830245 9300593560119489907655671)
    ·
      refine ⟨13950890340179234861483507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9300593560119489907655671 13950890340179234861483507)
      ·
        refine ⟨20926335510268852292225261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13950890340179234861483507 20926335510268852292225261)
        ·
          refine ⟨7847375816350819609584473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20926335510268852292225261 7847375816350819609584473)
          ·
            refine ⟨5885531862263114707188355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7847375816350819609584473 5885531862263114707188355)
            ·
              refine ⟨8828297793394672060782533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885531862263114707188355 8828297793394672060782533)
              ·
                refine ⟨1655305836261501011396725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8828297793394672060782533 1655305836261501011396725)
                ·
                  refine ⟨155184922149515719818443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1655305836261501011396725 155184922149515719818443)
                  ·
                    rfl

theorem cell22_1359997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1359997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1359997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1359997 prefixEnd_1359997 := by exact prefixLift 1359997
  have htrace : WordTrace (prefixWord ++ tailWord_1359997) baseStart_1359997 baseEnd_1359997 := by
    simpa [prefixWord, tailWord_1359997, baseEnd_1359997] using wordTrace_append hprefix tailTrace_1359997
  have hstable : (prefixWord ++ tailWord_1359997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359997).length < 2 ^ (prefixWord ++ tailWord_1359997).sum := by decide
  have hdescent : baseEnd_1359997 < baseStart_1359997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360022 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1360022 : Nat := 118140960795 + 1360022 * 2 ^ 59
def prefixEnd_1360022 : Nat := 4983230072969 + 3 ^ 40 * 1360022 * 2
def baseEnd_1360022 : Nat := 465563324459455427580253

theorem tailTrace_1360022 : CollatzResearch.WordTrace tailWord_1360022 prefixEnd_1360022 465563324459455427580253 := by
  unfold tailWord_1360022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100254842430002631905645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33069384985920028073660213 3100254842430002631905645)
  ·
    refine ⟨1162595565911250986964617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3100254842430002631905645 1162595565911250986964617)
    ·
      refine ⟨871946674433438240223463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1162595565911250986964617 871946674433438240223463)
      ·
        refine ⟨1307920011650157360335195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871946674433438240223463 1307920011650157360335195)
        ·
          refine ⟨1961880017475236040502793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307920011650157360335195 1961880017475236040502793)
          ·
            refine ⟨1471410013106427030377095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961880017475236040502793 1471410013106427030377095)
            ·
              refine ⟨2207115019659640545565643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471410013106427030377095 2207115019659640545565643)
              ·
                refine ⟨3310672529489460818348465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207115019659640545565643 3310672529489460818348465)
                ·
                  refine ⟨2483004397117095613761349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310672529489460818348465 2483004397117095613761349)
                  ·
                    refine ⟨465563324459455427580253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483004397117095613761349 465563324459455427580253)
                    ·
                      rfl

theorem cell22_1360022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1360022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360022 prefixEnd_1360022 := by exact prefixLift 1360022
  have htrace : WordTrace (prefixWord ++ tailWord_1360022) baseStart_1360022 baseEnd_1360022 := by
    simpa [prefixWord, tailWord_1360022, baseEnd_1360022] using wordTrace_append hprefix tailTrace_1360022
  have hstable : (prefixWord ++ tailWord_1360022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360022).length < 2 ^ (prefixWord ++ tailWord_1360022).sum := by decide
  have hdescent : baseEnd_1360022 < baseStart_1360022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360093 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1360093 : Nat := 118140960795 + 1360093 * 2 ^ 59
def prefixEnd_1360093 : Nat := 4983230072969 + 3 ^ 40 * 1360093 * 2
def baseEnd_1360093 : Nat := 155195876403478303018345

theorem tailTrace_1360093 : CollatzResearch.WordTrace tailWord_1360093 prefixEnd_1360093 155195876403478303018345 := by
  unfold tailWord_1360093
  simp only [CollatzResearch.WordTrace]
  refine ⟨49606667061622821236324933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33071111374415214157549955 49606667061622821236324933)
  ·
    refine ⟨9301250074054278981810925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49606667061622821236324933 9301250074054278981810925)
    ·
      refine ⟨3487968777770354618179097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9301250074054278981810925 3487968777770354618179097)
      ·
        refine ⟨2615976583327765963634323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3487968777770354618179097 2615976583327765963634323)
        ·
          refine ⟨3923964874991648945451485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2615976583327765963634323 3923964874991648945451485)
          ·
            refine ⟨1471486828121868354544307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3923964874991648945451485 1471486828121868354544307)
            ·
              refine ⟨2207230242182802531816461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471486828121868354544307 2207230242182802531816461)
              ·
                refine ⟨827711340818550949431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2207230242182802531816461 827711340818550949431173)
                ·
                  refine ⟨155195876403478303018345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827711340818550949431173 155195876403478303018345)
                  ·
                    rfl

theorem cell22_1360093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1360093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360093 prefixEnd_1360093 := by exact prefixLift 1360093
  have htrace : WordTrace (prefixWord ++ tailWord_1360093) baseStart_1360093 baseEnd_1360093 := by
    simpa [prefixWord, tailWord_1360093, baseEnd_1360093] using wordTrace_append hprefix tailTrace_1360093
  have hstable : (prefixWord ++ tailWord_1360093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360093).length < 2 ^ (prefixWord ++ tailWord_1360093).sum := by decide
  have hdescent : baseEnd_1360093 < baseStart_1360093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360170 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1360170 : Nat := 118140960795 + 1360170 * 2 ^ 59
def prefixEnd_1360170 : Nat := 4983230072969 + 3 ^ 40 * 1360170 * 2
def baseEnd_1360170 : Nat := 465613987884032374879799

theorem tailTrace_1360170 : CollatzResearch.WordTrace tailWord_1360170 prefixEnd_1360170 465613987884032374879799 := by
  unfold tailWord_1360170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12402368870585965846719491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33072983654895908924585309 12402368870585965846719491)
  ·
    refine ⟨18603553305878948770079237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12402368870585965846719491 18603553305878948770079237)
    ·
      refine ⟨3488166244852302894389857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18603553305878948770079237 3488166244852302894389857)
      ·
        refine ⟨2616124683639227170792393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3488166244852302894389857 2616124683639227170792393)
        ·
          refine ⟨1962093512729420378094295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2616124683639227170792393 1962093512729420378094295)
          ·
            refine ⟨2943140269094130567141443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962093512729420378094295 2943140269094130567141443)
            ·
              refine ⟨4414710403641195850712165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943140269094130567141443 4414710403641195850712165)
              ·
                refine ⟨827758200682724222008531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4414710403641195850712165 827758200682724222008531)
                ·
                  refine ⟨1241637301024086333012797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827758200682724222008531 1241637301024086333012797)
                  ·
                    refine ⟨465613987884032374879799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241637301024086333012797 465613987884032374879799)
                    ·
                      rfl

theorem cell22_1360170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1360170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360170 prefixEnd_1360170 := by exact prefixLift 1360170
  have htrace : WordTrace (prefixWord ++ tailWord_1360170) baseStart_1360170 baseEnd_1360170 := by
    simpa [prefixWord, tailWord_1360170, baseEnd_1360170] using wordTrace_append hprefix tailTrace_1360170
  have hstable : (prefixWord ++ tailWord_1360170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360170).length < 2 ^ (prefixWord ++ tailWord_1360170).sum := by decide
  have hdescent : baseEnd_1360170 < baseStart_1360170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360209 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_1360209 : Nat := 118140960795 + 1360209 * 2 ^ 59
def prefixEnd_1360209 : Nat := 4983230072969 + 3 ^ 40 * 1360209 * 2
def baseEnd_1360209 : Nat := 465627338381049273154679

theorem tailTrace_1360209 : CollatzResearch.WordTrace tailWord_1360209 prefixEnd_1360209 465627338381049273154679 := by
  unfold tailWord_1360209
  simp only [CollatzResearch.WordTrace]
  refine ⟨49610897929202573047547681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33073931952801715365031787 49610897929202573047547681)
  ·
    refine ⟨37208173446901929785660761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49610897929202573047547681 37208173446901929785660761)
    ·
      refine ⟨27906130085176447339245571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37208173446901929785660761 27906130085176447339245571)
      ·
        refine ⟨41859195127764671008868357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27906130085176447339245571 41859195127764671008868357)
        ·
          refine ⟨7848599086455875814162817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41859195127764671008868357 7848599086455875814162817)
          ·
            refine ⟨5886449314841906860622113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7848599086455875814162817 5886449314841906860622113)
            ·
              refine ⟨4414836986131430145466585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5886449314841906860622113 4414836986131430145466585)
              ·
                refine ⟨3311127739598572609099939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4414836986131430145466585 3311127739598572609099939)
                ·
                  refine ⟨4966691609397858913649909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311127739598572609099939 4966691609397858913649909)
                  ·
                    refine ⟨465627338381049273154679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4966691609397858913649909 465627338381049273154679)
                    ·
                      rfl

theorem cell22_1360209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_1360209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360209 prefixEnd_1360209 := by exact prefixLift 1360209
  have htrace : WordTrace (prefixWord ++ tailWord_1360209) baseStart_1360209 baseEnd_1360209 := by
    simpa [prefixWord, tailWord_1360209, baseEnd_1360209] using wordTrace_append hprefix tailTrace_1360209
  have hstable : (prefixWord ++ tailWord_1360209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360209).length < 2 ^ (prefixWord ++ tailWord_1360209).sum := by decide
  have hdescent : baseEnd_1360209 < baseStart_1360209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360288 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_1360288 : Nat := 118140960795 + 1360288 * 2 ^ 59
def prefixEnd_1360288 : Nat := 4983230072969 + 3 ^ 40 * 1360288 * 2
def baseEnd_1360288 : Nat := 465654381695519400429437

theorem tailTrace_1360288 : CollatzResearch.WordTrace tailWord_1360288 prefixEnd_1360288 465654381695519400429437 := by
  unfold tailWord_1360288
  simp only [CollatzResearch.WordTrace]
  refine ⟨24806889647958184769836759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33075852863944246359782345 24806889647958184769836759)
  ·
    refine ⟨37210334471937277154755139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24806889647958184769836759 37210334471937277154755139)
    ·
      refine ⟨55815501707905915732132709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37210334471937277154755139 55815501707905915732132709)
      ·
        refine ⟨10465406570232359199774883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55815501707905915732132709 10465406570232359199774883)
        ·
          refine ⟨15698109855348538799662325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10465406570232359199774883 15698109855348538799662325)
          ·
            refine ⟨1471697798938925512468343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15698109855348538799662325 1471697798938925512468343)
            ·
              refine ⟨2207546698408388268702515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471697798938925512468343 2207546698408388268702515)
              ·
                refine ⟨3311320047612582403053773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207546698408388268702515 3311320047612582403053773)
                ·
                  refine ⟨1241745017854718401145165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3311320047612582403053773 1241745017854718401145165)
                  ·
                    refine ⟨465654381695519400429437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241745017854718401145165 465654381695519400429437)
                    ·
                      rfl

theorem cell22_1360288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_1360288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360288 prefixEnd_1360288 := by exact prefixLift 1360288
  have htrace : WordTrace (prefixWord ++ tailWord_1360288) baseStart_1360288 baseEnd_1360288 := by
    simpa [prefixWord, tailWord_1360288, baseEnd_1360288] using wordTrace_append hprefix tailTrace_1360288
  have hstable : (prefixWord ++ tailWord_1360288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360288).length < 2 ^ (prefixWord ++ tailWord_1360288).sum := by decide
  have hdescent : baseEnd_1360288 < baseStart_1360288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360344 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1360344 : Nat := 118140960795 + 1360344 * 2 ^ 59
def prefixEnd_1360344 : Nat := 4983230072969 + 3 ^ 40 * 1360344 * 2
def baseEnd_1360344 : Nat := 465673551639953921029265

theorem tailTrace_1360344 : CollatzResearch.WordTrace tailWord_1360344 prefixEnd_1360344 465673551639953921029265 := by
  unfold tailWord_1360344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24807910891856745551856043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33077214522475660735808057 24807910891856745551856043)
  ·
    refine ⟨37211866337785118327784065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24807910891856745551856043 37211866337785118327784065)
    ·
      refine ⟨27908899753338838745838049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37211866337785118327784065 27908899753338838745838049)
      ·
        refine ⟨20931674815004129059378537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27908899753338838745838049 20931674815004129059378537)
        ·
          refine ⟨15698756111253096794533903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20931674815004129059378537 15698756111253096794533903)
          ·
            refine ⟨23548134166879645191800855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15698756111253096794533903 23548134166879645191800855)
            ·
              refine ⟨35322201250319467787701283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23548134166879645191800855 35322201250319467787701283)
              ·
                refine ⟨52983301875479201681551925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35322201250319467787701283 52983301875479201681551925)
                ·
                  refine ⟨4967184550826175157645493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52983301875479201681551925 4967184550826175157645493)
                  ·
                    refine ⟨465673551639953921029265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4967184550826175157645493 465673551639953921029265)
                    ·
                      rfl

theorem cell22_1360344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1360344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360344 prefixEnd_1360344 := by exact prefixLift 1360344
  have htrace : WordTrace (prefixWord ++ tailWord_1360344) baseStart_1360344 baseEnd_1360344 := by
    simpa [prefixWord, tailWord_1360344, baseEnd_1360344] using wordTrace_append hprefix tailTrace_1360344
  have hstable : (prefixWord ++ tailWord_1360344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360344).length < 2 ^ (prefixWord ++ tailWord_1360344).sum := by decide
  have hdescent : baseEnd_1360344 < baseStart_1360344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360391 : List Nat := [1, 1, 4, 3, 3, 1, 9]
def baseStart_1360391 : Nat := 118140960795 + 1360391 * 2 ^ 59
def prefixEnd_1360391 : Nat := 4983230072969 + 3 ^ 40 * 1360391 * 2
def baseEnd_1360391 : Nat := 17247764470387461670523

theorem tailTrace_1360391 : CollatzResearch.WordTrace tailWord_1360391 prefixEnd_1360391 17247764470387461670523 := by
  unfold tailWord_1360391
  simp only [CollatzResearch.WordTrace]
  refine ⟨49617536014543218130673027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33078357343028812087115351 49617536014543218130673027)
  ·
    refine ⟨74426304021814827196009541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49617536014543218130673027 74426304021814827196009541)
    ·
      refine ⟨13954932004090280099251789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74426304021814827196009541 13954932004090280099251789)
      ·
        refine ⟨5233099501533855037219421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13954932004090280099251789 5233099501533855037219421)
        ·
          refine ⟨1962412313075195638957283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5233099501533855037219421 1962412313075195638957283)
          ·
            refine ⟨2943618469612793458435925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962412313075195638957283 2943618469612793458435925)
            ·
              refine ⟨17247764470387461670523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2943618469612793458435925 17247764470387461670523)
              ·
                rfl

theorem cell22_1360391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 9].length) (baseStart_1360391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360391 prefixEnd_1360391 := by exact prefixLift 1360391
  have htrace : WordTrace (prefixWord ++ tailWord_1360391) baseStart_1360391 baseEnd_1360391 := by
    simpa [prefixWord, tailWord_1360391, baseEnd_1360391] using wordTrace_append hprefix tailTrace_1360391
  have hstable : (prefixWord ++ tailWord_1360391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360391).length < 2 ^ (prefixWord ++ tailWord_1360391).sum := by decide
  have hdescent : baseEnd_1360391 < baseStart_1360391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360395 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 2, 3]
def baseStart_1360395 : Nat := 118140960795 + 1360395 * 2 ^ 59
def prefixEnd_1360395 : Nat := 4983230072969 + 3 ^ 40 * 1360395 * 2
def baseEnd_1360395 : Nat := 465691009982206788004109

theorem tailTrace_1360395 : CollatzResearch.WordTrace tailWord_1360395 prefixEnd_1360395 465691009982206788004109 := by
  unfold tailWord_1360395
  simp only [CollatzResearch.WordTrace]
  refine ⟨49617681906528726813818639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33078454604352484542545759 49617681906528726813818639)
  ·
    refine ⟨74426522859793090220727959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49617681906528726813818639 74426522859793090220727959)
    ·
      refine ⟨111639784289689635331091939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74426522859793090220727959 111639784289689635331091939)
      ·
        refine ⟨167459676434534452996637909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111639784289689635331091939 167459676434534452996637909)
        ·
          refine ⟨3924836166434401242108701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 167459676434534452996637909 3924836166434401242108701)
          ·
            refine ⟨1471813562412900465790763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3924836166434401242108701 1471813562412900465790763)
            ·
              refine ⟨2207720343619350698686145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471813562412900465790763 2207720343619350698686145)
              ·
                refine ⟨1655790257714513024014609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207720343619350698686145 1655790257714513024014609)
                ·
                  refine ⟨1241842693285884768010957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1655790257714513024014609 1241842693285884768010957)
                  ·
                    refine ⟨465691009982206788004109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1241842693285884768010957 465691009982206788004109)
                    ·
                      rfl

theorem cell22_1360395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3].length) (baseStart_1360395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360395 prefixEnd_1360395 := by exact prefixLift 1360395
  have htrace : WordTrace (prefixWord ++ tailWord_1360395) baseStart_1360395 baseEnd_1360395 := by
    simpa [prefixWord, tailWord_1360395, baseEnd_1360395] using wordTrace_append hprefix tailTrace_1360395
  have hstable : (prefixWord ++ tailWord_1360395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360395).length < 2 ^ (prefixWord ++ tailWord_1360395).sum := by decide
  have hdescent : baseEnd_1360395 < baseStart_1360395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360397 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1360397 : Nat := 118140960795 + 1360397 * 2 ^ 59
def prefixEnd_1360397 : Nat := 4983230072969 + 3 ^ 40 * 1360397 * 2
def baseEnd_1360397 : Nat := 155230564874359816484701

theorem tailTrace_1360397 : CollatzResearch.WordTrace tailWord_1360397 prefixEnd_1360397 155230564874359816484701 := by
  unfold tailWord_1360397
  simp only [CollatzResearch.WordTrace]
  refine ⟨49617754852521481155391445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33078503235014320770260963 49617754852521481155391445)
  ·
    refine ⟨1162916129355972214579487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49617754852521481155391445 1162916129355972214579487)
    ·
      refine ⟨1744374194033958321869231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162916129355972214579487 1744374194033958321869231)
      ·
        refine ⟨2616561291050937482803847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744374194033958321869231 2616561291050937482803847)
        ·
          refine ⟨3924841936576406224205771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616561291050937482803847 3924841936576406224205771)
          ·
            refine ⟨5887262904864609336308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924841936576406224205771 5887262904864609336308657)
            ·
              refine ⟨4415447178648457002231493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5887262904864609336308657 4415447178648457002231493)
              ·
                refine ⟨827896345996585687918405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4415447178648457002231493 827896345996585687918405)
                ·
                  refine ⟨155230564874359816484701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827896345996585687918405 155230564874359816484701)
                  ·
                    rfl

theorem cell22_1360397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1360397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360397 prefixEnd_1360397 := by exact prefixLift 1360397
  have htrace : WordTrace (prefixWord ++ tailWord_1360397) baseStart_1360397 baseEnd_1360397 := by
    simpa [prefixWord, tailWord_1360397, baseEnd_1360397] using wordTrace_append hprefix tailTrace_1360397
  have hstable : (prefixWord ++ tailWord_1360397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360397).length < 2 ^ (prefixWord ++ tailWord_1360397).sum := by decide
  have hdescent : baseEnd_1360397 < baseStart_1360397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360511 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_1360511 : Nat := 118140960795 + 1360511 * 2 ^ 59
def prefixEnd_1360511 : Nat := 4983230072969 + 3 ^ 40 * 1360511 * 2
def baseEnd_1360511 : Nat := 465730719152821152103753

theorem tailTrace_1360511 : CollatzResearch.WordTrace tailWord_1360511 prefixEnd_1360511 465730719152821152103753 := by
  unfold tailWord_1360511
  simp only [CollatzResearch.WordTrace]
  refine ⟨49621912774108478625041387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33081275182738985750027591 49621912774108478625041387)
  ·
    refine ⟨74432869161162717937562081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49621912774108478625041387 74432869161162717937562081)
    ·
      refine ⟨55824651870872038453171561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74432869161162717937562081 55824651870872038453171561)
      ·
        refine ⟨41868488903154028839878671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55824651870872038453171561 41868488903154028839878671)
        ·
          refine ⟨62802733354731043259818007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41868488903154028839878671 62802733354731043259818007)
          ·
            refine ⟨94204100032096564889727011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62802733354731043259818007 94204100032096564889727011)
            ·
              refine ⟨141306150048144847334590517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94204100032096564889727011 141306150048144847334590517)
              ·
                refine ⟨13247451567013579437617861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141306150048144847334590517 13247451567013579437617861)
                ·
                  refine ⟨2483897168815046144553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13247451567013579437617861 2483897168815046144553349)
                  ·
                    refine ⟨465730719152821152103753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483897168815046144553349 465730719152821152103753)
                    ·
                      rfl

theorem cell22_1360511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_1360511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360511 prefixEnd_1360511 := by exact prefixLift 1360511
  have htrace : WordTrace (prefixWord ++ tailWord_1360511) baseStart_1360511 baseEnd_1360511 := by
    simpa [prefixWord, tailWord_1360511, baseEnd_1360511] using wordTrace_append hprefix tailTrace_1360511
  have hstable : (prefixWord ++ tailWord_1360511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360511).length < 2 ^ (prefixWord ++ tailWord_1360511).sum := by decide
  have hdescent : baseEnd_1360511 < baseStart_1360511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360515 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 4]
def baseStart_1360515 : Nat := 118140960795 + 1360515 * 2 ^ 59
def prefixEnd_1360515 : Nat := 4983230072969 + 3 ^ 40 * 1360515 * 2
def baseEnd_1360515 : Nat := 155244029478188825001247

theorem tailTrace_1360515 : CollatzResearch.WordTrace tailWord_1360515 prefixEnd_1360515 155244029478188825001247 := by
  unfold tailWord_1360515
  simp only [CollatzResearch.WordTrace]
  refine ⟨49622058666093987308186999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33081372444062658205457999 49622058666093987308186999)
  ·
    refine ⟨74433087999140980962280499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49622058666093987308186999 74433087999140980962280499)
    ·
      refine ⟨111649631998711471443420749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74433087999140980962280499 111649631998711471443420749)
      ·
        refine ⟨41868611999516801791282781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111649631998711471443420749 41868611999516801791282781)
        ·
          refine ⟨15700729499818800671731043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41868611999516801791282781 15700729499818800671731043)
          ·
            refine ⟨23551094249728201007596565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15700729499818800671731043 23551094249728201007596565)
            ·
              refine ⟨1103957542956009422231089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23551094249728201007596565 1103957542956009422231089)
              ·
                refine ⟨827968157217007066673317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103957542956009422231089 827968157217007066673317)
                ·
                  refine ⟨155244029478188825001247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 827968157217007066673317 155244029478188825001247)
                  ·
                    rfl

theorem cell22_1360515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 4].length) (baseStart_1360515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360515 prefixEnd_1360515 := by exact prefixLift 1360515
  have htrace : WordTrace (prefixWord ++ tailWord_1360515) baseStart_1360515 baseEnd_1360515 := by
    simpa [prefixWord, tailWord_1360515, baseEnd_1360515] using wordTrace_append hprefix tailTrace_1360515
  have hstable : (prefixWord ++ tailWord_1360515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360515).length < 2 ^ (prefixWord ++ tailWord_1360515).sum := by decide
  have hdescent : baseEnd_1360515 < baseStart_1360515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360530 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1360530 : Nat := 118140960795 + 1360530 * 2 ^ 59
def prefixEnd_1360530 : Nat := 4983230072969 + 3 ^ 40 * 1360530 * 2
def baseEnd_1360530 : Nat := 465737223241111435878695

theorem tailTrace_1360530 : CollatzResearch.WordTrace tailWord_1360530 prefixEnd_1360530 465737223241111435878695 := by
  unfold tailWord_1360530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405651440259911217495761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33081737174026429913322029 12405651440259911217495761)
  ·
    refine ⟨9304238580194933413121821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12405651440259911217495761 9304238580194933413121821)
    ·
      refine ⟨3489089467573100029920683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9304238580194933413121821 3489089467573100029920683)
      ·
        refine ⟨5233634201359650044881025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489089467573100029920683 5233634201359650044881025)
        ·
          refine ⟨3925225651019737533660769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5233634201359650044881025 3925225651019737533660769)
          ·
            refine ⟨2943919238264803150245577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3925225651019737533660769 2943919238264803150245577)
            ·
              refine ⟨2207939428698602362684183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943919238264803150245577 2207939428698602362684183)
              ·
                refine ⟨3311909143047903544026275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207939428698602362684183 3311909143047903544026275)
                ·
                  refine ⟨4967863714571855316039413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311909143047903544026275 4967863714571855316039413)
                  ·
                    refine ⟨465737223241111435878695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4967863714571855316039413 465737223241111435878695)
                    ·
                      rfl

theorem cell22_1360530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1360530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360530 prefixEnd_1360530 := by exact prefixLift 1360530
  have htrace : WordTrace (prefixWord ++ tailWord_1360530) baseStart_1360530 baseEnd_1360530 := by
    simpa [prefixWord, tailWord_1360530, baseEnd_1360530] using wordTrace_append hprefix tailTrace_1360530
  have hstable : (prefixWord ++ tailWord_1360530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360530).length < 2 ^ (prefixWord ++ tailWord_1360530).sum := by decide
  have hdescent : baseEnd_1360530 < baseStart_1360530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360551 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1360551 : Nat := 118140960795 + 1360551 * 2 ^ 59
def prefixEnd_1360551 : Nat := 4983230072969 + 3 ^ 40 * 1360551 * 2
def baseEnd_1360551 : Nat := 465744411970274381103631

theorem tailTrace_1360551 : CollatzResearch.WordTrace tailWord_1360551 prefixEnd_1360551 465744411970274381103631 := by
  unfold tailWord_1360551
  simp only [CollatzResearch.WordTrace]
  refine ⟨49623371693963565456497507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33082247795975710304331671 49623371693963565456497507)
  ·
    refine ⟨74435057540945348184746261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49623371693963565456497507 74435057540945348184746261)
    ·
      refine ⟨3489143322231813196159981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74435057540945348184746261 3489143322231813196159981)
      ·
        refine ⟨1308428745836929948559993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3489143322231813196159981 1308428745836929948559993)
        ·
          refine ⟨981321559377697461419995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308428745836929948559993 981321559377697461419995)
          ·
            refine ⟨1471982339066546192129993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981321559377697461419995 1471982339066546192129993)
            ·
              refine ⟨1103986754299909644097495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471982339066546192129993 1103986754299909644097495)
              ·
                refine ⟨1655980131449864466146243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103986754299909644097495 1655980131449864466146243)
                ·
                  refine ⟨2483970197174796699219365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655980131449864466146243 2483970197174796699219365)
                  ·
                    refine ⟨465744411970274381103631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2483970197174796699219365 465744411970274381103631)
                    ·
                      rfl

theorem cell22_1360551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1360551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360551 prefixEnd_1360551 := by exact prefixLift 1360551
  have htrace : WordTrace (prefixWord ++ tailWord_1360551) baseStart_1360551 baseEnd_1360551 := by
    simpa [prefixWord, tailWord_1360551, baseEnd_1360551] using wordTrace_append hprefix tailTrace_1360551
  have hstable : (prefixWord ++ tailWord_1360551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360551).length < 2 ^ (prefixWord ++ tailWord_1360551).sum := by decide
  have hdescent : baseEnd_1360551 < baseStart_1360551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360575 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 3, 3]
def baseStart_1360575 : Nat := 118140960795 + 1360575 * 2 ^ 59
def prefixEnd_1360575 : Nat := 4983230072969 + 3 ^ 40 * 1360575 * 2
def baseEnd_1360575 : Nat := 465752627660746318503557

theorem tailTrace_1360575 : CollatzResearch.WordTrace tailWord_1360575 prefixEnd_1360575 465752627660746318503557 := by
  unfold tailWord_1360575
  simp only [CollatzResearch.WordTrace]
  refine ⟨49624247045876617555371179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33082831363917745036914119 49624247045876617555371179)
  ·
    refine ⟨74436370568814926333056769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49624247045876617555371179 74436370568814926333056769)
    ·
      refine ⟨55827277926611194749792577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74436370568814926333056769 55827277926611194749792577)
      ·
        refine ⟨41870458444958396062344433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55827277926611194749792577 41870458444958396062344433)
        ·
          refine ⟨31402843833718797046758325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41870458444958396062344433 31402843833718797046758325)
          ·
            refine ⟨2944016609411137223133593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31402843833718797046758325 2944016609411137223133593)
            ·
              refine ⟨2208012457058352917350195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944016609411137223133593 2208012457058352917350195)
              ·
                refine ⟨3312018685587529376025293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208012457058352917350195 3312018685587529376025293)
                ·
                  refine ⟨1242007007095323516009485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3312018685587529376025293 1242007007095323516009485)
                  ·
                    refine ⟨465752627660746318503557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1242007007095323516009485 465752627660746318503557)
                    ·
                      rfl

theorem cell22_1360575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_1360575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360575 prefixEnd_1360575 := by exact prefixLift 1360575
  have htrace : WordTrace (prefixWord ++ tailWord_1360575) baseStart_1360575 baseEnd_1360575 := by
    simpa [prefixWord, tailWord_1360575, baseEnd_1360575] using wordTrace_append hprefix tailTrace_1360575
  have hstable : (prefixWord ++ tailWord_1360575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360575).length < 2 ^ (prefixWord ++ tailWord_1360575).sum := by decide
  have hdescent : baseEnd_1360575 < baseStart_1360575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360609 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 1, 3]
def baseStart_1360609 : Nat := 118140960795 + 1360609 * 2 ^ 59
def prefixEnd_1360609 : Nat := 4983230072969 + 3 ^ 40 * 1360609 * 2
def baseEnd_1360609 : Nat := 465764266555581563153453

theorem tailTrace_1360609 : CollatzResearch.WordTrace tailWord_1360609 prefixEnd_1360609 465764266555581563153453 := by
  unfold tailWord_1360609
  simp only [CollatzResearch.WordTrace]
  refine ⟨49625487127753441362108881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33083658085168960908072587 49625487127753441362108881)
  ·
    refine ⟨37219115345815081021581661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49625487127753441362108881 37219115345815081021581661)
    ·
      refine ⟨13957168254680655383093123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37219115345815081021581661 13957168254680655383093123)
      ·
        refine ⟨20935752382020983074639685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13957168254680655383093123 20935752382020983074639685)
        ·
          refine ⟨3925453571628934326494941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20935752382020983074639685 3925453571628934326494941)
          ·
            refine ⟨1472045089360850372435603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3925453571628934326494941 1472045089360850372435603)
            ·
              refine ⟨2208067634041275558653405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472045089360850372435603 2208067634041275558653405)
              ·
                refine ⟨828025362765478334495027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2208067634041275558653405 828025362765478334495027)
                ·
                  refine ⟨1242038044148217501742541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828025362765478334495027 1242038044148217501742541)
                  ·
                    refine ⟨465764266555581563153453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1242038044148217501742541 465764266555581563153453)
                    ·
                      rfl

theorem cell22_1360609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_1360609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360609 prefixEnd_1360609 := by exact prefixLift 1360609
  have htrace : WordTrace (prefixWord ++ tailWord_1360609) baseStart_1360609 baseEnd_1360609 := by
    simpa [prefixWord, tailWord_1360609, baseEnd_1360609] using wordTrace_append hprefix tailTrace_1360609
  have hstable : (prefixWord ++ tailWord_1360609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360609).length < 2 ^ (prefixWord ++ tailWord_1360609).sum := by decide
  have hdescent : baseEnd_1360609 < baseStart_1360609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360618 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_1360618 : Nat := 118140960795 + 1360618 * 2 ^ 59
def prefixEnd_1360618 : Nat := 4983230072969 + 3 ^ 40 * 1360618 * 2
def baseEnd_1360618 : Nat := 465767347439508539678425

theorem tailTrace_1360618 : CollatzResearch.WordTrace tailWord_1360618 prefixEnd_1360618 465767347439508539678425 := by
  unfold tailWord_1360618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12406453846180208974796627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33083876923147223932791005 12406453846180208974796627)
  ·
    refine ⟨18609680769270313462194941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12406453846180208974796627 18609680769270313462194941)
    ·
      refine ⟨6978630288476367548323103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18609680769270313462194941 6978630288476367548323103)
      ·
        refine ⟨10467945432714551322484655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6978630288476367548323103 10467945432714551322484655)
        ·
          refine ⟨15701918149071826983726983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467945432714551322484655 15701918149071826983726983)
          ·
            refine ⟨23552877223607740475590475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15701918149071826983726983 23552877223607740475590475)
            ·
              refine ⟨35329315835411610713385713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23552877223607740475590475 35329315835411610713385713)
              ·
                refine ⟨26496986876558708035039285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35329315835411610713385713 26496986876558708035039285)
                ·
                  refine ⟨2484092519677378878284933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26496986876558708035039285 2484092519677378878284933)
                  ·
                    refine ⟨465767347439508539678425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484092519677378878284933 465767347439508539678425)
                    ·
                      rfl

theorem cell22_1360618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_1360618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360618 prefixEnd_1360618 := by exact prefixLift 1360618
  have htrace : WordTrace (prefixWord ++ tailWord_1360618) baseStart_1360618 baseEnd_1360618 := by
    simpa [prefixWord, tailWord_1360618, baseEnd_1360618] using wordTrace_append hprefix tailTrace_1360618
  have hstable : (prefixWord ++ tailWord_1360618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360618).length < 2 ^ (prefixWord ++ tailWord_1360618).sum := by decide
  have hdescent : baseEnd_1360618 < baseStart_1360618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360680 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1360680 : Nat := 118140960795 + 1360680 * 2 ^ 59
def prefixEnd_1360680 : Nat := 4983230072969 + 3 ^ 40 * 1360680 * 2
def baseEnd_1360680 : Nat := 465788571306561044628235

theorem tailTrace_1360680 : CollatzResearch.WordTrace tailWord_1360680 prefixEnd_1360680 465788571306561044628235 := by
  unfold tailWord_1360680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24814038355248110243971747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33085384473664146991962329 24814038355248110243971747)
  ·
    refine ⟨37221057532872165365957621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24814038355248110243971747 37221057532872165365957621)
    ·
      refine ⟨3489474143706765503058527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37221057532872165365957621 3489474143706765503058527)
      ·
        refine ⟨5234211215560148254587791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489474143706765503058527 5234211215560148254587791)
        ·
          refine ⟨7851316823340222381881687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234211215560148254587791 7851316823340222381881687)
          ·
            refine ⟨11776975235010333572822531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851316823340222381881687 11776975235010333572822531)
            ·
              refine ⟨17665462852515500359233797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11776975235010333572822531 17665462852515500359233797)
              ·
                refine ⟨3312274284846656317356337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17665462852515500359233797 3312274284846656317356337)
                ·
                  refine ⟨2484205713634992238017253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3312274284846656317356337 2484205713634992238017253)
                  ·
                    refine ⟨465788571306561044628235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484205713634992238017253 465788571306561044628235)
                    ·
                      rfl

theorem cell22_1360680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1360680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360680 prefixEnd_1360680 := by exact prefixLift 1360680
  have htrace : WordTrace (prefixWord ++ tailWord_1360680) baseStart_1360680 baseEnd_1360680 := by
    simpa [prefixWord, tailWord_1360680, baseEnd_1360680] using wordTrace_append hprefix tailTrace_1360680
  have hstable : (prefixWord ++ tailWord_1360680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360680).length < 2 ^ (prefixWord ++ tailWord_1360680).sum := by decide
  have hdescent : baseEnd_1360680 < baseStart_1360680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360740 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_1360740 : Nat := 118140960795 + 1360740 * 2 ^ 59
def prefixEnd_1360740 : Nat := 4983230072969 + 3 ^ 40 * 1360740 * 2
def baseEnd_1360740 : Nat := 155269703510913629376017

theorem tailTrace_1360740 : CollatzResearch.WordTrace tailWord_1360740 prefixEnd_1360740 155269703510913629376017 := by
  unfold tailWord_1360740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815132545139425367563837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33086843393519233823418449 24815132545139425367563837)
  ·
    refine ⟨9305674704427284512836439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24815132545139425367563837 9305674704427284512836439)
    ·
      refine ⟨13958512056640926769254659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9305674704427284512836439 13958512056640926769254659)
      ·
        refine ⟨20937768084961390153881989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13958512056640926769254659 20937768084961390153881989)
        ·
          refine ⟨3925831515930260653852873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20937768084961390153881989 3925831515930260653852873)
          ·
            refine ⟨2944373636947695490389655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3925831515930260653852873 2944373636947695490389655)
            ·
              refine ⟨4416560455421543235584483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944373636947695490389655 4416560455421543235584483)
              ·
                refine ⟨6624840683132314853376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416560455421543235584483 6624840683132314853376725)
                ·
                  refine ⟨155269703510913629376017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6624840683132314853376725 155269703510913629376017)
                  ·
                    rfl

theorem cell22_1360740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_1360740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360740 prefixEnd_1360740 := by exact prefixLift 1360740
  have htrace : WordTrace (prefixWord ++ tailWord_1360740) baseStart_1360740 baseEnd_1360740 := by
    simpa [prefixWord, tailWord_1360740, baseEnd_1360740] using wordTrace_append hprefix tailTrace_1360740
  have hstable : (prefixWord ++ tailWord_1360740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360740).length < 2 ^ (prefixWord ++ tailWord_1360740).sum := by decide
  have hdescent : baseEnd_1360740 < baseStart_1360740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360744 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1360744 : Nat := 118140960795 + 1360744 * 2 ^ 59
def prefixEnd_1360744 : Nat := 4983230072969 + 3 ^ 40 * 1360744 * 2
def baseEnd_1360744 : Nat := 465810479814486211028039

theorem tailTrace_1360744 : CollatzResearch.WordTrace tailWord_1360744 prefixEnd_1360744 465810479814486211028039 := by
  unfold tailWord_1360744
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815205491132179709136643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33086940654842906278848857 24815205491132179709136643)
  ·
    refine ⟨37222808236698269563704965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24815205491132179709136643 37222808236698269563704965)
    ·
      refine ⟨6979276544380925543194681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37222808236698269563704965 6979276544380925543194681)
      ·
        refine ⟨5234457408285694157396011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979276544380925543194681 5234457408285694157396011)
        ·
          refine ⟨7851686112428541236094017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234457408285694157396011 7851686112428541236094017)
          ·
            refine ⟨5888764584321405927070513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7851686112428541236094017 5888764584321405927070513)
            ·
              refine ⟨4416573438241054445302885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888764584321405927070513 4416573438241054445302885)
              ·
                refine ⟨828107519670197708494291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4416573438241054445302885 828107519670197708494291)
                ·
                  refine ⟨1242161279505296562741437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828107519670197708494291 1242161279505296562741437)
                  ·
                    refine ⟨465810479814486211028039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1242161279505296562741437 465810479814486211028039)
                    ·
                      rfl

theorem cell22_1360744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1360744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360744 prefixEnd_1360744 := by exact prefixLift 1360744
  have htrace : WordTrace (prefixWord ++ tailWord_1360744) baseStart_1360744 baseEnd_1360744 := by
    simpa [prefixWord, tailWord_1360744, baseEnd_1360744] using wordTrace_append hprefix tailTrace_1360744
  have hstable : (prefixWord ++ tailWord_1360744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360744).length < 2 ^ (prefixWord ++ tailWord_1360744).sum := by decide
  have hdescent : baseEnd_1360744 < baseStart_1360744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360768 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_1360768 : Nat := 118140960795 + 1360768 * 2 ^ 59
def prefixEnd_1360768 : Nat := 4983230072969 + 3 ^ 40 * 1360768 * 2
def baseEnd_1360768 : Nat := 155272898501652716142655

theorem tailTrace_1360768 : CollatzResearch.WordTrace tailWord_1360768 prefixEnd_1360768 155272898501652716142655 := by
  unfold tailWord_1360768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815643167088705758573479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33087524222784941011431305 24815643167088705758573479)
  ·
    refine ⟨37223464750633058637860219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24815643167088705758573479 37223464750633058637860219)
    ·
      refine ⟨55835197125949587956790329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37223464750633058637860219 55835197125949587956790329)
      ·
        refine ⟨41876397844462190967592747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55835197125949587956790329 41876397844462190967592747)
        ·
          refine ⟨62814596766693286451389121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41876397844462190967592747 62814596766693286451389121)
          ·
            refine ⟨47110947575019964838541841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62814596766693286451389121 47110947575019964838541841)
            ·
              refine ⟨35333210681264973628906381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47110947575019964838541841 35333210681264973628906381)
              ·
                refine ⟨13249954005474365110839893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35333210681264973628906381 13249954005474365110839893)
                ·
                  refine ⟨155272898501652716142655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13249954005474365110839893 155272898501652716142655)
                  ·
                    rfl

theorem cell22_1360768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_1360768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360768 prefixEnd_1360768 := by exact prefixLift 1360768
  have htrace : WordTrace (prefixWord ++ tailWord_1360768) baseStart_1360768 baseEnd_1360768 := by
    simpa [prefixWord, tailWord_1360768, baseEnd_1360768] using wordTrace_append hprefix tailTrace_1360768
  have hstable : (prefixWord ++ tailWord_1360768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360768).length < 2 ^ (prefixWord ++ tailWord_1360768).sum := by decide
  have hdescent : baseEnd_1360768 < baseStart_1360768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360802 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1360802 : Nat := 118140960795 + 1360802 * 2 ^ 59
def prefixEnd_1360802 : Nat := 4983230072969 + 3 ^ 40 * 1360802 * 2
def baseEnd_1360802 : Nat := 155276778133264464359287

theorem tailTrace_1360802 : CollatzResearch.WordTrace tailWord_1360802 prefixEnd_1360802 155276778133264464359287 := by
  unfold tailWord_1360802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408131604013558830971165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33088350944036156882589773 12408131604013558830971165)
  ·
    refine ⟨4653049351505084561614187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12408131604013558830971165 4653049351505084561614187)
    ·
      refine ⟨6979574027257626842421281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653049351505084561614187 6979574027257626842421281)
      ·
        refine ⟨5234680520443220131815961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979574027257626842421281 5234680520443220131815961)
        ·
          refine ⟨3926010390332415098861971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234680520443220131815961 3926010390332415098861971)
          ·
            refine ⟨5889015585498622648292957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926010390332415098861971 5889015585498622648292957)
            ·
              refine ⟨2208380844561983493109859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5889015585498622648292957 2208380844561983493109859)
              ·
                refine ⟨3312571266842975239664789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208380844561983493109859 3312571266842975239664789)
                ·
                  refine ⟨155276778133264464359287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3312571266842975239664789 155276778133264464359287)
                  ·
                    rfl

theorem cell22_1360802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1360802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360802 prefixEnd_1360802 := by exact prefixLift 1360802
  have htrace : WordTrace (prefixWord ++ tailWord_1360802) baseStart_1360802 baseEnd_1360802 := by
    simpa [prefixWord, tailWord_1360802, baseEnd_1360802] using wordTrace_append hprefix tailTrace_1360802
  have hstable : (prefixWord ++ tailWord_1360802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360802).length < 2 ^ (prefixWord ++ tailWord_1360802).sum := by decide
  have hdescent : baseEnd_1360802 < baseStart_1360802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360830 : List Nat := [4, 2, 1, 1, 1, 2, 1, 10]
def baseStart_1360830 : Nat := 118140960795 + 1360830 * 2 ^ 59
def prefixEnd_1360830 : Nat := 4983230072969 + 3 ^ 40 * 1360830 * 2
def baseEnd_1360830 : Nat := 51759991041334517041975

theorem tailTrace_1360830 : CollatzResearch.WordTrace tailWord_1360830 prefixEnd_1360830 51759991041334517041975 := by
  unfold tailWord_1360830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204193457494099513237993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33089031773301864070602629 6204193457494099513237993)
  ·
    refine ⟨4653145093120574634928495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6204193457494099513237993 4653145093120574634928495)
    ·
      refine ⟨6979717639680861952392743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653145093120574634928495 6979717639680861952392743)
      ·
        refine ⟨10469576459521292928589115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979717639680861952392743 10469576459521292928589115)
        ·
          refine ⟨15704364689281939392883673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469576459521292928589115 15704364689281939392883673)
          ·
            refine ⟨11778273516961454544662755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15704364689281939392883673 11778273516961454544662755)
            ·
              refine ⟨17667410275442181816994133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778273516961454544662755 17667410275442181816994133)
              ·
                refine ⟨51759991041334517041975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17667410275442181816994133 51759991041334517041975)
                ·
                  rfl

theorem cell22_1360830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_1360830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360830 prefixEnd_1360830 := by exact prefixLift 1360830
  have htrace : WordTrace (prefixWord ++ tailWord_1360830) baseStart_1360830 baseEnd_1360830 := by
    simpa [prefixWord, tailWord_1360830, baseEnd_1360830] using wordTrace_append hprefix tailTrace_1360830
  have hstable : (prefixWord ++ tailWord_1360830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360830).length < 2 ^ (prefixWord ++ tailWord_1360830).sum := by decide
  have hdescent : baseEnd_1360830 < baseStart_1360830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360832 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_1360832 : Nat := 118140960795 + 1360832 * 2 ^ 59
def prefixEnd_1360832 : Nat := 4983230072969 + 3 ^ 40 * 1360832 * 2
def baseEnd_1360832 : Nat := 465840604012883314827769

theorem tailTrace_1360832 : CollatzResearch.WordTrace tailWord_1360832 prefixEnd_1360832 465840604012883314827769 := by
  unfold tailWord_1360832
  simp only [CollatzResearch.WordTrace]
  refine ⟨24816810302972775223738375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33089080403963700298317833 24816810302972775223738375)
  ·
    refine ⟨37225215454459162835607563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24816810302972775223738375 37225215454459162835607563)
    ·
      refine ⟨55837823181688744253411345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37225215454459162835607563 55837823181688744253411345)
      ·
        refine ⟨41878367386266558190058509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55837823181688744253411345 41878367386266558190058509)
        ·
          refine ⟨15704387769849959321271941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41878367386266558190058509 15704387769849959321271941)
          ·
            refine ⟨2944572706846867372738489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15704387769849959321271941 2944572706846867372738489)
            ·
              refine ⟨2208429530135150529553867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944572706846867372738489 2208429530135150529553867)
              ·
                refine ⟨3312644295202725794330801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208429530135150529553867 3312644295202725794330801)
                ·
                  refine ⟨2484483221402044345748101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3312644295202725794330801 2484483221402044345748101)
                  ·
                    refine ⟨465840604012883314827769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484483221402044345748101 465840604012883314827769)
                    ·
                      rfl

theorem cell22_1360832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_1360832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360832 prefixEnd_1360832 := by exact prefixLift 1360832
  have htrace : WordTrace (prefixWord ++ tailWord_1360832) baseStart_1360832 baseEnd_1360832 := by
    simpa [prefixWord, tailWord_1360832, baseEnd_1360832] using wordTrace_append hprefix tailTrace_1360832
  have hstable : (prefixWord ++ tailWord_1360832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360832).length < 2 ^ (prefixWord ++ tailWord_1360832).sum := by decide
  have hdescent : baseEnd_1360832 < baseStart_1360832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360853 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 4]
def baseStart_1360853 : Nat := 118140960795 + 1360853 * 2 ^ 59
def prefixEnd_1360853 : Nat := 4983230072969 + 3 ^ 40 * 1360853 * 2
def baseEnd_1360853 : Nat := 155282597580682086684235

theorem tailTrace_1360853 : CollatzResearch.WordTrace tailWord_1360853 prefixEnd_1360853 155282597580682086684235 := by
  unfold tailWord_1360853
  simp only [CollatzResearch.WordTrace]
  refine ⟨49634386538869471033991213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33089591025912980689327475 49634386538869471033991213)
  ·
    refine ⟨18612894952076051637746705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49634386538869471033991213 18612894952076051637746705)
    ·
      refine ⟨13959671214057038728310029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18612894952076051637746705 13959671214057038728310029)
      ·
        refine ⟨5234876705271389523116261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13959671214057038728310029 5234876705271389523116261)
        ·
          refine ⟨981539382238385535584299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5234876705271389523116261 981539382238385535584299)
          ·
            refine ⟨1472309073357578303376449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981539382238385535584299 1472309073357578303376449)
            ·
              refine ⟨1104231805018183727532337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472309073357578303376449 1104231805018183727532337)
              ·
                refine ⟨828173853763637795649253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104231805018183727532337 828173853763637795649253)
                ·
                  refine ⟨155282597580682086684235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828173853763637795649253 155282597580682086684235)
                  ·
                    rfl

theorem cell22_1360853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_1360853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360853 prefixEnd_1360853 := by exact prefixLift 1360853
  have htrace : WordTrace (prefixWord ++ tailWord_1360853) baseStart_1360853 baseEnd_1360853 := by
    simpa [prefixWord, tailWord_1360853, baseEnd_1360853] using wordTrace_append hprefix tailTrace_1360853
  have hstable : (prefixWord ++ tailWord_1360853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360853).length < 2 ^ (prefixWord ++ tailWord_1360853).sum := by decide
  have hdescent : baseEnd_1360853 < baseStart_1360853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360954 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_1360954 : Nat := 118140960795 + 1360954 * 2 ^ 59
def prefixEnd_1360954 : Nat := 4983230072969 + 3 ^ 40 * 1360954 * 2
def baseEnd_1360954 : Nat := 155294122368705221092465

theorem tailTrace_1360954 : CollatzResearch.WordTrace tailWord_1360954 prefixEnd_1360954 155294122368705221092465 := by
  unfold tailWord_1360954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409517577875891320854479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33092046874335710188945277 12409517577875891320854479)
  ·
    refine ⟨18614276366813836981281719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12409517577875891320854479 18614276366813836981281719)
    ·
      refine ⟨27921414550220755471922579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18614276366813836981281719 27921414550220755471922579)
      ·
        refine ⟨41882121825331133207883869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27921414550220755471922579 41882121825331133207883869)
        ·
          refine ⟨15705795684499174952956451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41882121825331133207883869 15705795684499174952956451)
          ·
            refine ⟨23558693526748762429434677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15705795684499174952956451 23558693526748762429434677)
            ·
              refine ⟨2208627518132696477759501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23558693526748762429434677 2208627518132696477759501)
              ·
                refine ⟨828235319299761179159813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2208627518132696477759501 828235319299761179159813)
                ·
                  refine ⟨155294122368705221092465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828235319299761179159813 155294122368705221092465)
                  ·
                    rfl

theorem cell22_1360954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_1360954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360954 prefixEnd_1360954 := by exact prefixLift 1360954
  have htrace : WordTrace (prefixWord ++ tailWord_1360954) baseStart_1360954 baseEnd_1360954 := by
    simpa [prefixWord, tailWord_1360954, baseEnd_1360954] using wordTrace_append hprefix tailTrace_1360954
  have hstable : (prefixWord ++ tailWord_1360954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360954).length < 2 ^ (prefixWord ++ tailWord_1360954).sum := by decide
  have hdescent : baseEnd_1360954 < baseStart_1360954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360965 : List Nat := [1, 3, 1, 1, 1, 3, 12]
def baseStart_1360965 : Nat := 118140960795 + 1360965 * 2 ^ 59
def prefixEnd_1360965 : Nat := 4983230072969 + 3 ^ 40 * 1360965 * 2
def baseEnd_1360965 : Nat := 17255041949293159305643

theorem tailTrace_1360965 : CollatzResearch.WordTrace tailWord_1360965 prefixEnd_1360965 17255041949293159305643 := by
  unfold tailWord_1360965
  simp only [CollatzResearch.WordTrace]
  refine ⟨49638471514463714162068349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33092314342975809441378899 49638471514463714162068349)
  ·
    refine ⟨18614426817923892810775631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49638471514463714162068349 18614426817923892810775631)
    ·
      refine ⟨27921640226885839216163447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18614426817923892810775631 27921640226885839216163447)
      ·
        refine ⟨41882460340328758824245171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27921640226885839216163447 41882460340328758824245171)
        ·
          refine ⟨62823690510493138236367757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41882460340328758824245171 62823690510493138236367757)
          ·
            refine ⟨23558883941434926838637909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62823690510493138236367757 23558883941434926838637909)
            ·
              refine ⟨17255041949293159305643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23558883941434926838637909 17255041949293159305643)
              ·
                rfl

theorem cell22_1360965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 12].length) (baseStart_1360965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360965 prefixEnd_1360965 := by exact prefixLift 1360965
  have htrace : WordTrace (prefixWord ++ tailWord_1360965) baseStart_1360965 baseEnd_1360965 := by
    simpa [prefixWord, tailWord_1360965, baseEnd_1360965] using wordTrace_append hprefix tailTrace_1360965
  have hstable : (prefixWord ++ tailWord_1360965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360965).length < 2 ^ (prefixWord ++ tailWord_1360965).sum := by decide
  have hdescent : baseEnd_1360965 < baseStart_1360965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360967 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1360967 : Nat := 118140960795 + 1360967 * 2 ^ 59
def prefixEnd_1360967 : Nat := 4983230072969 + 3 ^ 40 * 1360967 * 2
def baseEnd_1360967 : Nat := 465886817271787962702355

theorem tailTrace_1360967 : CollatzResearch.WordTrace tailWord_1360967 prefixEnd_1360967 465886817271787962702355 := by
  unfold tailWord_1360967
  simp only [CollatzResearch.WordTrace]
  refine ⟨49638544460456468503641155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33092362973637645669094103 49638544460456468503641155)
  ·
    refine ⟨74457816690684702755461733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49638544460456468503641155 74457816690684702755461733)
    ·
      refine ⟨13960840629503381766649075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74457816690684702755461733 13960840629503381766649075)
      ·
        refine ⟨20941260944255072649973613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13960840629503381766649075 20941260944255072649973613)
        ·
          refine ⟨7852972854095652243740105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20941260944255072649973613 7852972854095652243740105)
          ·
            refine ⟨5889729640571739182805079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7852972854095652243740105 5889729640571739182805079)
            ·
              refine ⟨8834594460857608774207619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889729640571739182805079 8834594460857608774207619)
              ·
                refine ⟨13251891691286413161311429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8834594460857608774207619 13251891691286413161311429)
                ·
                  refine ⟨2484729692116202467745893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13251891691286413161311429 2484729692116202467745893)
                  ·
                    refine ⟨465886817271787962702355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484729692116202467745893 465886817271787962702355)
                    ·
                      rfl

theorem cell22_1360967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1360967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360967 prefixEnd_1360967 := by exact prefixLift 1360967
  have htrace : WordTrace (prefixWord ++ tailWord_1360967) baseStart_1360967 baseEnd_1360967 := by
    simpa [prefixWord, tailWord_1360967, baseEnd_1360967] using wordTrace_append hprefix tailTrace_1360967
  have hstable : (prefixWord ++ tailWord_1360967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360967).length < 2 ^ (prefixWord ++ tailWord_1360967).sum := by decide
  have hdescent : baseEnd_1360967 < baseStart_1360967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360990 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1360990 : Nat := 118140960795 + 1360990 * 2 ^ 59
def prefixEnd_1360990 : Nat := 4983230072969 + 3 ^ 40 * 1360990 * 2
def baseEnd_1360990 : Nat := 465894690641823569377285

theorem tailTrace_1360990 : CollatzResearch.WordTrace tailWord_1360990 prefixEnd_1360990 465894690641823569377285 := by
  unfold tailWord_1360990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204922917421642928966053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33092922226248762287818949 6204922917421642928966053)
  ·
    refine ⟨1163423047016558049181135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6204922917421642928966053 1163423047016558049181135)
    ·
      refine ⟨1745134570524837073771703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163423047016558049181135 1745134570524837073771703)
      ·
        refine ⟨2617701855787255610657555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745134570524837073771703 2617701855787255610657555)
        ·
          refine ⟨3926552783680883415986333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617701855787255610657555 3926552783680883415986333)
          ·
            refine ⟨1472457293880331280994875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3926552783680883415986333 1472457293880331280994875)
            ·
              refine ⟨2208685940820496921492313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472457293880331280994875 2208685940820496921492313)
              ·
                refine ⟨1656514455615372691119235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208685940820496921492313 1656514455615372691119235)
                ·
                  refine ⟨2484771683423059036678853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656514455615372691119235 2484771683423059036678853)
                  ·
                    refine ⟨465894690641823569377285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484771683423059036678853 465894690641823569377285)
                    ·
                      rfl

theorem cell22_1360990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1360990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1360990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1360990 prefixEnd_1360990 := by exact prefixLift 1360990
  have htrace : WordTrace (prefixWord ++ tailWord_1360990) baseStart_1360990 baseEnd_1360990 := by
    simpa [prefixWord, tailWord_1360990, baseEnd_1360990] using wordTrace_append hprefix tailTrace_1360990
  have hstable : (prefixWord ++ tailWord_1360990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360990).length < 2 ^ (prefixWord ++ tailWord_1360990).sum := by decide
  have hdescent : baseEnd_1360990 < baseStart_1360990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361078 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1361078 : Nat := 118140960795 + 1361078 * 2 ^ 59
def prefixEnd_1361078 : Nat := 4983230072969 + 3 ^ 40 * 1361078 * 2
def baseEnd_1361078 : Nat := 155308271613406891059005

theorem tailTrace_1361078 : CollatzResearch.WordTrace tailWord_1361078 prefixEnd_1361078 155308271613406891059005 := by
  unfold tailWord_1361078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102662060190895903808243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33095061975369556307287925 3102662060190895903808243)
  ·
    refine ⟨4653993090286343855712365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3102662060190895903808243 4653993090286343855712365)
    ·
      refine ⟨1745247408857378945892137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4653993090286343855712365 1745247408857378945892137)
      ·
        refine ⟨1308935556643034209419103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745247408857378945892137 1308935556643034209419103)
        ·
          refine ⟨1963403334964551314128655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308935556643034209419103 1963403334964551314128655)
          ·
            refine ⟨2945105002446826971192983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963403334964551314128655 2945105002446826971192983)
            ·
              refine ⟨4417657503670240456789475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945105002446826971192983 4417657503670240456789475)
              ·
                refine ⟨6626486255505360685184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417657503670240456789475 6626486255505360685184213)
                ·
                  refine ⟨155308271613406891059005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6626486255505360685184213 155308271613406891059005)
                  ·
                    rfl

theorem cell22_1361078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1361078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361078 prefixEnd_1361078 := by exact prefixLift 1361078
  have htrace : WordTrace (prefixWord ++ tailWord_1361078) baseStart_1361078 baseEnd_1361078 := by
    simpa [prefixWord, tailWord_1361078, baseEnd_1361078] using wordTrace_append hprefix tailTrace_1361078
  have hstable : (prefixWord ++ tailWord_1361078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361078).length < 2 ^ (prefixWord ++ tailWord_1361078).sum := by decide
  have hdescent : baseEnd_1361078 < baseStart_1361078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361087 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_1361087 : Nat := 118140960795 + 1361087 * 2 ^ 59
def prefixEnd_1361087 : Nat := 4983230072969 + 3 ^ 40 * 1361087 * 2
def baseEnd_1361087 : Nat := 465927895724147649701987

theorem tailTrace_1361087 : CollatzResearch.WordTrace tailWord_1361087 prefixEnd_1361087 465927895724147649701987 := by
  unfold tailWord_1361087
  simp only [CollatzResearch.WordTrace]
  refine ⟨49642921220021728998009515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33095280813347819332006343 49642921220021728998009515)
  ·
    refine ⟨74464381830032593497014273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49642921220021728998009515 74464381830032593497014273)
    ·
      refine ⟨55848286372524445122760705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74464381830032593497014273 55848286372524445122760705)
      ·
        refine ⟨41886214779393333842070529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55848286372524445122760705 41886214779393333842070529)
        ·
          refine ⟨31414661084545000381552897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41886214779393333842070529 31414661084545000381552897)
          ·
            refine ⟨23560995813408750286164673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31414661084545000381552897 23560995813408750286164673)
            ·
              refine ⟨17670746860056562714623505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23560995813408750286164673 17670746860056562714623505)
              ·
                refine ⟨13253060145042422035967629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17670746860056562714623505 13253060145042422035967629)
                ·
                  refine ⟨4969897554390908263487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13253060145042422035967629 4969897554390908263487861)
                  ·
                    refine ⟨465927895724147649701987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4969897554390908263487861 465927895724147649701987)
                    ·
                      rfl

theorem cell22_1361087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_1361087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361087 prefixEnd_1361087 := by exact prefixLift 1361087
  have htrace : WordTrace (prefixWord ++ tailWord_1361087) baseStart_1361087 baseEnd_1361087 := by
    simpa [prefixWord, tailWord_1361087, baseEnd_1361087] using wordTrace_append hprefix tailTrace_1361087
  have hstable : (prefixWord ++ tailWord_1361087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361087).length < 2 ^ (prefixWord ++ tailWord_1361087).sum := by decide
  have hdescent : baseEnd_1361087 < baseStart_1361087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361170 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1361170 : Nat := 118140960795 + 1361170 * 2 ^ 59
def prefixEnd_1361170 : Nat := 4983230072969 + 3 ^ 40 * 1361170 * 2
def baseEnd_1361170 : Nat := 465956308320363099876733

theorem tailTrace_1361170 : CollatzResearch.WordTrace tailWord_1361170 prefixEnd_1361170 465956308320363099876733 := by
  unfold tailWord_1361170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411487119680258543320241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33097298985814022782187309 12411487119680258543320241)
  ·
    refine ⟨9308615339760193907490181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12411487119680258543320241 9308615339760193907490181)
    ·
      refine ⟨1745365376205036357654409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9308615339760193907490181 1745365376205036357654409)
      ·
        refine ⟨1309024032153777268240807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745365376205036357654409 1309024032153777268240807)
        ·
          refine ⟨1963536048230665902361211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309024032153777268240807 1963536048230665902361211)
          ·
            refine ⟨2945304072345998853541817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963536048230665902361211 2945304072345998853541817)
            ·
              refine ⟨2208978054259499140156363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945304072345998853541817 2208978054259499140156363)
              ·
                refine ⟨3313467081389248710234545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208978054259499140156363 3313467081389248710234545)
                ·
                  refine ⟨2485100311041936532675909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313467081389248710234545 2485100311041936532675909)
                  ·
                    refine ⟨465956308320363099876733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2485100311041936532675909 465956308320363099876733)
                    ·
                      rfl

theorem cell22_1361170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1361170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361170 prefixEnd_1361170 := by exact prefixLift 1361170
  have htrace : WordTrace (prefixWord ++ tailWord_1361170) baseStart_1361170 baseEnd_1361170 := by
    simpa [prefixWord, tailWord_1361170, baseEnd_1361170] using wordTrace_append hprefix tailTrace_1361170
  have hstable : (prefixWord ++ tailWord_1361170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361170).length < 2 ^ (prefixWord ++ tailWord_1361170).sum := by decide
  have hdescent : baseEnd_1361170 < baseStart_1361170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361241 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 4]
def baseStart_1361241 : Nat := 118140960795 + 1361241 * 2 ^ 59
def prefixEnd_1361241 : Nat := 4983230072969 + 3 ^ 40 * 1361241 * 2
def baseEnd_1361241 : Nat := 155326871023780860450505

theorem tailTrace_1361241 : CollatzResearch.WordTrace tailWord_1361241 prefixEnd_1361241 155326871023780860450505 := by
  unfold tailWord_1361241
  simp only [CollatzResearch.WordTrace]
  refine ⟨49648538061463813299115577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33099025374309208866077051 49648538061463813299115577)
  ·
    refine ⟨37236403546097859974336683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49648538061463813299115577 37236403546097859974336683)
    ·
      refine ⟨55854605319146789961505025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37236403546097859974336683 55854605319146789961505025)
      ·
        refine ⟨41890953989360092471128769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55854605319146789961505025 41890953989360092471128769)
        ·
          refine ⟨31418215492020069353346577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41890953989360092471128769 31418215492020069353346577)
          ·
            refine ⟨23563661619015052015009933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31418215492020069353346577 23563661619015052015009933)
            ·
              refine ⟨8836373107130644505628725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23563661619015052015009933 8836373107130644505628725)
              ·
                refine ⟨828409978793497922402693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8836373107130644505628725 828409978793497922402693)
                ·
                  refine ⟨155326871023780860450505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828409978793497922402693 155326871023780860450505)
                  ·
                    rfl

theorem cell22_1361241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_1361241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361241 prefixEnd_1361241 := by exact prefixLift 1361241
  have htrace : WordTrace (prefixWord ++ tailWord_1361241) baseStart_1361241 baseEnd_1361241 := by
    simpa [prefixWord, tailWord_1361241, baseEnd_1361241] using wordTrace_append hprefix tailTrace_1361241
  have hstable : (prefixWord ++ tailWord_1361241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361241).length < 2 ^ (prefixWord ++ tailWord_1361241).sum := by decide
  have hdescent : baseEnd_1361241 < baseStart_1361241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361258 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_1361258 : Nat := 118140960795 + 1361258 * 2 ^ 59
def prefixEnd_1361258 : Nat := 4983230072969 + 3 ^ 40 * 1361258 * 2
def baseEnd_1361258 : Nat := 155328810839586734558821

theorem tailTrace_1361258 : CollatzResearch.WordTrace tailWord_1361258 prefixEnd_1361258 155328810839586734558821 := by
  unfold tailWord_1361258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412289525600556300621107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33099438734934816801656285 12412289525600556300621107)
  ·
    refine ⟨18618434288400834450931661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12412289525600556300621107 18618434288400834450931661)
    ·
      refine ⟨6981912858150312919099373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18618434288400834450931661 6981912858150312919099373)
      ·
        refine ⟨2618217321806367344662265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6981912858150312919099373 2618217321806367344662265)
        ·
          refine ⟨1963662991354775508496699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2618217321806367344662265 1963662991354775508496699)
          ·
            refine ⟨2945494487032163262745049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963662991354775508496699 2945494487032163262745049)
            ·
              refine ⟨2209120865274122447058787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945494487032163262745049 2209120865274122447058787)
              ·
                refine ⟨3313681297911183670588181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209120865274122447058787 3313681297911183670588181)
                ·
                  refine ⟨155328810839586734558821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3313681297911183670588181 155328810839586734558821)
                  ·
                    rfl

theorem cell22_1361258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_1361258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361258 prefixEnd_1361258 := by exact prefixLift 1361258
  have htrace : WordTrace (prefixWord ++ tailWord_1361258) baseStart_1361258 baseEnd_1361258 := by
    simpa [prefixWord, tailWord_1361258, baseEnd_1361258] using wordTrace_append hprefix tailTrace_1361258
  have hstable : (prefixWord ++ tailWord_1361258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361258).length < 2 ^ (prefixWord ++ tailWord_1361258).sum := by decide
  have hdescent : baseEnd_1361258 < baseStart_1361258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361301 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_1361301 : Nat := 118140960795 + 1361301 * 2 ^ 59
def prefixEnd_1361301 : Nat := 4983230072969 + 3 ^ 40 * 1361301 * 2
def baseEnd_1361301 : Nat := 466001152297522424851331

theorem tailTrace_1361301 : CollatzResearch.WordTrace tailWord_1361301 prefixEnd_1361301 466001152297522424851331 := by
  unfold tailWord_1361301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49650726441246443546299757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33100484294164295697533171 49650726441246443546299757)
  ·
    refine ⟨18619022415467416329862409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49650726441246443546299757 18619022415467416329862409)
    ·
      refine ⟨13964266811600562247396807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18619022415467416329862409 13964266811600562247396807)
      ·
        refine ⟨20946400217400843371095211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13964266811600562247396807 20946400217400843371095211)
        ·
          refine ⟨31419600326101265056642817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20946400217400843371095211 31419600326101265056642817)
          ·
            refine ⟨23564700244575948792482113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31419600326101265056642817 23564700244575948792482113)
            ·
              refine ⟨17673525183431961594361585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23564700244575948792482113 17673525183431961594361585)
              ·
                refine ⟨13255143887573971195771189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17673525183431961594361585 13255143887573971195771189)
                ·
                  refine ⟨1242669739460059799603549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13255143887573971195771189 1242669739460059799603549)
                  ·
                    refine ⟨466001152297522424851331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1242669739460059799603549 466001152297522424851331)
                    ·
                      rfl

theorem cell22_1361301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_1361301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361301 prefixEnd_1361301 := by exact prefixLift 1361301
  have htrace : WordTrace (prefixWord ++ tailWord_1361301) baseStart_1361301 baseEnd_1361301 := by
    simpa [prefixWord, tailWord_1361301, baseEnd_1361301] using wordTrace_append hprefix tailTrace_1361301
  have hstable : (prefixWord ++ tailWord_1361301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361301).length < 2 ^ (prefixWord ++ tailWord_1361301).sum := by decide
  have hdescent : baseEnd_1361301 < baseStart_1361301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361391 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_1361391 : Nat := 118140960795 + 1361391 * 2 ^ 59
def prefixEnd_1361391 : Nat := 4983230072969 + 3 ^ 40 * 1361391 * 2
def baseEnd_1361391 : Nat := 466031961136792190101055

theorem tailTrace_1361391 : CollatzResearch.WordTrace tailWord_1361391 prefixEnd_1361391 466031961136792190101055 := by
  unfold tailWord_1361391
  simp only [CollatzResearch.WordTrace]
  refine ⟨49654009010920388917076027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33102672673946925944717351 49654009010920388917076027)
  ·
    refine ⟨74481013516380583375614041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49654009010920388917076027 74481013516380583375614041)
    ·
      refine ⟨55860760137285437531710531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74481013516380583375614041 55860760137285437531710531)
      ·
        refine ⟨83791140205928156297565797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55860760137285437531710531 83791140205928156297565797)
        ·
          refine ⟨15710838788611529305793587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83791140205928156297565797 15710838788611529305793587)
          ·
            refine ⟨23566258182917293958690381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15710838788611529305793587 23566258182917293958690381)
            ·
              refine ⟨8837346818593985234508893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23566258182917293958690381 8837346818593985234508893)
              ·
                refine ⟨3314005056972744462940835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8837346818593985234508893 3314005056972744462940835)
                ·
                  refine ⟨4971007585459116694411253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314005056972744462940835 4971007585459116694411253)
                  ·
                    refine ⟨466031961136792190101055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4971007585459116694411253 466031961136792190101055)
                    ·
                      rfl

theorem cell22_1361391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_1361391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361391 prefixEnd_1361391 := by exact prefixLift 1361391
  have htrace : WordTrace (prefixWord ++ tailWord_1361391) baseStart_1361391 baseEnd_1361391 := by
    simpa [prefixWord, tailWord_1361391, baseEnd_1361391] using wordTrace_append hprefix tailTrace_1361391
  have hstable : (prefixWord ++ tailWord_1361391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361391).length < 2 ^ (prefixWord ++ tailWord_1361391).sum := by decide
  have hdescent : baseEnd_1361391 < baseStart_1361391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361466 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_1361466 : Nat := 118140960795 + 1361466 * 2 ^ 59
def prefixEnd_1361466 : Nat := 4983230072969 + 3 ^ 40 * 1361466 * 2
def baseEnd_1361466 : Nat := 155352545056505664825275

theorem tailTrace_1361466 : CollatzResearch.WordTrace tailWord_1361466 prefixEnd_1361466 155352545056505664825275 := by
  unfold tailWord_1361466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12414186121412169181514063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33104496323765784484037501 12414186121412169181514063)
  ·
    refine ⟨18621279182118253772271095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12414186121412169181514063 18621279182118253772271095)
    ·
      refine ⟨27931918773177380658406643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18621279182118253772271095 27931918773177380658406643)
      ·
        refine ⟨41897878159766070987609965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27931918773177380658406643 41897878159766070987609965)
        ·
          refine ⟨15711704309912276620353737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41897878159766070987609965 15711704309912276620353737)
          ·
            refine ⟨11783778232434207465265303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15711704309912276620353737 11783778232434207465265303)
            ·
              refine ⟨17675667348651311197897955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11783778232434207465265303 17675667348651311197897955)
              ·
                refine ⟨26513501022976966796846933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17675667348651311197897955 26513501022976966796846933)
                ·
                  refine ⟨155352545056505664825275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26513501022976966796846933 155352545056505664825275)
                  ·
                    rfl

theorem cell22_1361466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_1361466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361466 prefixEnd_1361466 := by exact prefixLift 1361466
  have htrace : WordTrace (prefixWord ++ tailWord_1361466) baseStart_1361466 baseEnd_1361466 := by
    simpa [prefixWord, tailWord_1361466, baseEnd_1361466] using wordTrace_append hprefix tailTrace_1361466
  have hstable : (prefixWord ++ tailWord_1361466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361466).length < 2 ^ (prefixWord ++ tailWord_1361466).sum := by decide
  have hdescent : baseEnd_1361466 < baseStart_1361466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361481 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_1361481 : Nat := 118140960795 + 1361481 * 2 ^ 59
def prefixEnd_1361481 : Nat := 4983230072969 + 3 ^ 40 * 1361481 * 2
def baseEnd_1361481 : Nat := 466062769976061955350779

theorem tailTrace_1361481 : CollatzResearch.WordTrace tailWord_1361481 prefixEnd_1361481 466062769976061955350779 := by
  unfold tailWord_1361481
  simp only [CollatzResearch.WordTrace]
  refine ⟨49657291580594334287852297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33104861053729556191901531 49657291580594334287852297)
  ·
    refine ⟨37242968685445750715889223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49657291580594334287852297 37242968685445750715889223)
    ·
      refine ⟨55864453028168626073833835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37242968685445750715889223 55864453028168626073833835)
      ·
        refine ⟨83796679542252939110750753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55864453028168626073833835 83796679542252939110750753)
        ·
          refine ⟨62847509656689704333063065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83796679542252939110750753 62847509656689704333063065)
          ·
            refine ⟨47135632242517278249797299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62847509656689704333063065 47135632242517278249797299)
            ·
              refine ⟨70703448363775917374695949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47135632242517278249797299 70703448363775917374695949)
              ·
                refine ⟨26513793136415969015510981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70703448363775917374695949 26513793136415969015510981)
                ·
                  refine ⟨4971336213077994190408309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26513793136415969015510981 4971336213077994190408309)
                  ·
                    refine ⟨466062769976061955350779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4971336213077994190408309 466062769976061955350779)
                    ·
                      rfl

theorem cell22_1361481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_1361481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361481 prefixEnd_1361481 := by exact prefixLift 1361481
  have htrace : WordTrace (prefixWord ++ tailWord_1361481) baseStart_1361481 baseEnd_1361481 := by
    simpa [prefixWord, tailWord_1361481, baseEnd_1361481] using wordTrace_append hprefix tailTrace_1361481
  have hstable : (prefixWord ++ tailWord_1361481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361481).length < 2 ^ (prefixWord ++ tailWord_1361481).sum := by decide
  have hdescent : baseEnd_1361481 < baseStart_1361481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361496 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1361496 : Nat := 118140960795 + 1361496 * 2 ^ 59
def prefixEnd_1361496 : Nat := 4983230072969 + 3 ^ 40 * 1361496 * 2
def baseEnd_1361496 : Nat := 466067904782606916225733

theorem tailTrace_1361496 : CollatzResearch.WordTrace tailWord_1361496 prefixEnd_1361496 466067904782606916225733 := by
  unfold tailWord_1361496
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828919337769995924824171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33105225783693327899765561 24828919337769995924824171)
  ·
    refine ⟨37243379006654993887236257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24828919337769995924824171 37243379006654993887236257)
    ·
      refine ⟨27932534254991245415427193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37243379006654993887236257 27932534254991245415427193)
      ·
        refine ⟨20949400691243434061570395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27932534254991245415427193 20949400691243434061570395)
        ·
          refine ⟨31424101036865151092355593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20949400691243434061570395 31424101036865151092355593)
          ·
            refine ⟨23568075777648863319266695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31424101036865151092355593 23568075777648863319266695)
            ·
              refine ⟨35352113666473294978900043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23568075777648863319266695 35352113666473294978900043)
              ·
                refine ⟨53028170499709942468350065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35352113666473294978900043 53028170499709942468350065)
                ·
                  refine ⟨39771127874782456851262549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53028170499709942468350065 39771127874782456851262549)
                  ·
                    refine ⟨466067904782606916225733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39771127874782456851262549 466067904782606916225733)
                    ·
                      rfl

theorem cell22_1361496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1361496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361496 prefixEnd_1361496 := by exact prefixLift 1361496
  have htrace : WordTrace (prefixWord ++ tailWord_1361496) baseStart_1361496 baseEnd_1361496 := by
    simpa [prefixWord, tailWord_1361496, baseEnd_1361496] using wordTrace_append hprefix tailTrace_1361496
  have hstable : (prefixWord ++ tailWord_1361496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361496).length < 2 ^ (prefixWord ++ tailWord_1361496).sum := by decide
  have hdescent : baseEnd_1361496 < baseStart_1361496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361500 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1361500 : Nat := 118140960795 + 1361500 * 2 ^ 59
def prefixEnd_1361500 : Nat := 4983230072969 + 3 ^ 40 * 1361500 * 2
def baseEnd_1361500 : Nat := 155356424688117413041907

theorem tailTrace_1361500 : CollatzResearch.WordTrace tailWord_1361500 prefixEnd_1361500 155356424688117413041907 := by
  unfold tailWord_1361500
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828992283762750266396977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33105323045017000355195969 24828992283762750266396977)
  ·
    refine ⟨18621744212822062699797733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24828992283762750266396977 18621744212822062699797733)
    ·
      refine ⟨3491577039904136756212075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18621744212822062699797733 3491577039904136756212075)
      ·
        refine ⟨5237365559856205134318113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491577039904136756212075 5237365559856205134318113)
        ·
          refine ⟨3928024169892153850738585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5237365559856205134318113 3928024169892153850738585)
          ·
            refine ⟨2946018127419115388053939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928024169892153850738585 2946018127419115388053939)
            ·
              refine ⟨4419027191128673082080909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946018127419115388053939 4419027191128673082080909)
              ·
                refine ⟨1657135196673252405780341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4419027191128673082080909 1657135196673252405780341)
                ·
                  refine ⟨155356424688117413041907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657135196673252405780341 155356424688117413041907)
                  ·
                    rfl

theorem cell22_1361500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1361500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361500 prefixEnd_1361500 := by exact prefixLift 1361500
  have htrace : WordTrace (prefixWord ++ tailWord_1361500) baseStart_1361500 baseEnd_1361500 := by
    simpa [prefixWord, tailWord_1361500, baseEnd_1361500] using wordTrace_append hprefix tailTrace_1361500
  have hstable : (prefixWord ++ tailWord_1361500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361500).length < 2 ^ (prefixWord ++ tailWord_1361500).sum := by decide
  have hdescent : baseEnd_1361500 < baseStart_1361500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361560 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1361560 : Nat := 118140960795 + 1361560 * 2 ^ 59
def prefixEnd_1361560 : Nat := 4983230072969 + 3 ^ 40 * 1361560 * 2
def baseEnd_1361560 : Nat := 466089813290532082625537

theorem tailTrace_1361560 : CollatzResearch.WordTrace tailWord_1361560 prefixEnd_1361560 466089813290532082625537 := by
  unfold tailWord_1361560
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830086473654065389989067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33106781964872087186652089 24830086473654065389989067)
  ·
    refine ⟨37245129710481098084983601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24830086473654065389989067 37245129710481098084983601)
    ·
      refine ⟨27933847282860823563737701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37245129710481098084983601 27933847282860823563737701)
      ·
        refine ⟨5237596365536404418200819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27933847282860823563737701 5237596365536404418200819)
        ·
          refine ⟨7856394548304606627301229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5237596365536404418200819 7856394548304606627301229)
          ·
            refine ⟨2946147955614227485237961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7856394548304606627301229 2946147955614227485237961)
            ·
              refine ⟨2209610966710670613928471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946147955614227485237961 2209610966710670613928471)
              ·
                refine ⟨3314416450066005920892707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209610966710670613928471 3314416450066005920892707)
                ·
                  refine ⟨4971624675099008881339061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314416450066005920892707 4971624675099008881339061)
                  ·
                    refine ⟨466089813290532082625537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4971624675099008881339061 466089813290532082625537)
                    ·
                      rfl

theorem cell22_1361560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1361560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361560 prefixEnd_1361560 := by exact prefixLift 1361560
  have htrace : WordTrace (prefixWord ++ tailWord_1361560) baseStart_1361560 baseEnd_1361560 := by
    simpa [prefixWord, tailWord_1361560, baseEnd_1361560] using wordTrace_append hprefix tailTrace_1361560
  have hstable : (prefixWord ++ tailWord_1361560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361560).length < 2 ^ (prefixWord ++ tailWord_1361560).sum := by decide
  have hdescent : baseEnd_1361560 < baseStart_1361560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361695 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_1361695 : Nat := 118140960795 + 1361695 * 2 ^ 59
def prefixEnd_1361695 : Nat := 4983230072969 + 3 ^ 40 * 1361695 * 2
def baseEnd_1361695 : Nat := 466136026549436730500123

theorem tailTrace_1361695 : CollatzResearch.WordTrace tailWord_1361695 prefixEnd_1361695 466136026549436730500123 := by
  unfold tailWord_1361695
  simp only [CollatzResearch.WordTrace]
  refine ⟨49665096801819048836142539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33110064534546032557428359 49665096801819048836142539)
  ·
    refine ⟨74497645202728573254213809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49665096801819048836142539 74497645202728573254213809)
    ·
      refine ⟨55873233902046429940660357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74497645202728573254213809 55873233902046429940660357)
      ·
        refine ⟨10476231356633705613873817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55873233902046429940660357 10476231356633705613873817)
        ·
          refine ⟨7857173517475279210405363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10476231356633705613873817 7857173517475279210405363)
          ·
            refine ⟨11785760276212918815608045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7857173517475279210405363 11785760276212918815608045)
            ·
              refine ⟨4419660103579844555853017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11785760276212918815608045 4419660103579844555853017)
              ·
                refine ⟨3314745077684883416889763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4419660103579844555853017 3314745077684883416889763)
                ·
                  refine ⟨4972117616527325125334645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314745077684883416889763 4972117616527325125334645)
                  ·
                    refine ⟨466136026549436730500123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4972117616527325125334645 466136026549436730500123)
                    ·
                      rfl

theorem cell22_1361695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_1361695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361695 prefixEnd_1361695 := by exact prefixLift 1361695
  have htrace : WordTrace (prefixWord ++ tailWord_1361695) baseStart_1361695 baseEnd_1361695 := by
    simpa [prefixWord, tailWord_1361695, baseEnd_1361695] using wordTrace_append hprefix tailTrace_1361695
  have hstable : (prefixWord ++ tailWord_1361695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361695).length < 2 ^ (prefixWord ++ tailWord_1361695).sum := by decide
  have hdescent : baseEnd_1361695 < baseStart_1361695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361708 : List Nat := [2, 2, 1, 1, 1, 15]
def baseStart_1361708 : Nat := 118140960795 + 1361708 * 2 ^ 59
def prefixEnd_1361708 : Nat := 4983230072969 + 3 ^ 40 * 1361708 * 2
def baseEnd_1361708 : Nat := 5754820700186531233643

theorem tailTrace_1361708 : CollatzResearch.WordTrace tailWord_1361708 prefixEnd_1361708 5754820700186531233643 := by
  unfold tailWord_1361708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24832785475385976028182889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33110380633847968037577185 24832785475385976028182889)
  ·
    refine ⟨18624589106539482021137167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24832785475385976028182889 18624589106539482021137167)
    ·
      refine ⟨27936883659809223031705751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18624589106539482021137167 27936883659809223031705751)
      ·
        refine ⟨41905325489713834547558627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27936883659809223031705751 41905325489713834547558627)
        ·
          refine ⟨62857988234570751821337941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41905325489713834547558627 62857988234570751821337941)
          ·
            refine ⟨5754820700186531233643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 62857988234570751821337941 5754820700186531233643)
            ·
              rfl

theorem cell22_1361708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 15].length) (baseStart_1361708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361708 prefixEnd_1361708 := by exact prefixLift 1361708
  have htrace : WordTrace (prefixWord ++ tailWord_1361708) baseStart_1361708 baseEnd_1361708 := by
    simpa [prefixWord, tailWord_1361708, baseEnd_1361708] using wordTrace_append hprefix tailTrace_1361708
  have hstable : (prefixWord ++ tailWord_1361708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361708).length < 2 ^ (prefixWord ++ tailWord_1361708).sum := by decide
  have hdescent : baseEnd_1361708 < baseStart_1361708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361714 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_1361714 : Nat := 118140960795 + 1361714 * 2 ^ 59
def prefixEnd_1361714 : Nat := 4983230072969 + 3 ^ 40 * 1361714 * 2
def baseEnd_1361714 : Nat := 155380843545909004758355

theorem tailTrace_1361714 : CollatzResearch.WordTrace tailWord_1361714 prefixEnd_1361714 155380843545909004758355 := by
  unfold tailWord_1361714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416447447187553770271049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33110526525833476720722797 12416447447187553770271049)
  ·
    refine ⟨9312335585390665327703287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12416447447187553770271049 9312335585390665327703287)
    ·
      refine ⟨13968503378085997991554931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9312335585390665327703287 13968503378085997991554931)
      ·
        refine ⟨20952755067128996987332397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13968503378085997991554931 20952755067128996987332397)
        ·
          refine ⟨7857283150173373870249649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20952755067128996987332397 7857283150173373870249649)
          ·
            refine ⟨5892962362630030402687237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7857283150173373870249649 5892962362630030402687237)
            ·
              refine ⟨1104930442993130700503857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5892962362630030402687237 1104930442993130700503857)
              ·
                refine ⟨828697832244848025377893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104930442993130700503857 828697832244848025377893)
                ·
                  refine ⟨155380843545909004758355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 828697832244848025377893 155380843545909004758355)
                  ·
                    rfl

theorem cell22_1361714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_1361714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361714 prefixEnd_1361714 := by exact prefixLift 1361714
  have htrace : WordTrace (prefixWord ++ tailWord_1361714) baseStart_1361714 baseEnd_1361714 := by
    simpa [prefixWord, tailWord_1361714, baseEnd_1361714] using wordTrace_append hprefix tailTrace_1361714
  have hstable : (prefixWord ++ tailWord_1361714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361714).length < 2 ^ (prefixWord ++ tailWord_1361714).sum := by decide
  have hdescent : baseEnd_1361714 < baseStart_1361714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361774 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1361774 : Nat := 118140960795 + 1361774 * 2 ^ 59
def prefixEnd_1361774 : Nat := 4983230072969 + 3 ^ 40 * 1361774 * 2
def baseEnd_1361774 : Nat := 466163069863906857774881

theorem tailTrace_1361774 : CollatzResearch.WordTrace tailWord_1361774 prefixEnd_1361774 466163069863906857774881 := by
  unfold tailWord_1361774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208497271066605666033547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33111985445688563552178917 6208497271066605666033547)
  ·
    refine ⟨9312745906599908499050321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208497271066605666033547 9312745906599908499050321)
    ·
      refine ⟨6984559429949931374287741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9312745906599908499050321 6984559429949931374287741)
      ·
        refine ⟨2619209786231224265357903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6984559429949931374287741 2619209786231224265357903)
        ·
          refine ⟨3928814679346836398036855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619209786231224265357903 3928814679346836398036855)
          ·
            refine ⟨5893222019020254597055283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928814679346836398036855 5893222019020254597055283)
            ·
              refine ⟨8839833028530381895582925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893222019020254597055283 8839833028530381895582925)
              ·
                refine ⟨3314937385698893210843597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8839833028530381895582925 3314937385698893210843597)
                ·
                  refine ⟨1243101519637084954066349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3314937385698893210843597 1243101519637084954066349)
                  ·
                    refine ⟨466163069863906857774881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243101519637084954066349 466163069863906857774881)
                    ·
                      rfl

theorem cell22_1361774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1361774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361774 prefixEnd_1361774 := by exact prefixLift 1361774
  have htrace : WordTrace (prefixWord ++ tailWord_1361774) baseStart_1361774 baseEnd_1361774 := by
    simpa [prefixWord, tailWord_1361774, baseEnd_1361774] using wordTrace_append hprefix tailTrace_1361774
  have hstable : (prefixWord ++ tailWord_1361774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361774).length < 2 ^ (prefixWord ++ tailWord_1361774).sum := by decide
  have hdescent : baseEnd_1361774 < baseStart_1361774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361785 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_1361785 : Nat := 118140960795 + 1361785 * 2 ^ 59
def prefixEnd_1361785 : Nat := 4983230072969 + 3 ^ 40 * 1361785 * 2
def baseEnd_1361785 : Nat := 466166835388706495749847

theorem tailTrace_1361785 : CollatzResearch.WordTrace tailWord_1361785 prefixEnd_1361785 466166835388706495749847 := by
  unfold tailWord_1361785
  simp only [CollatzResearch.WordTrace]
  refine ⟨49668379371492994206918809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33112252914328662804612539 49668379371492994206918809)
  ·
    refine ⟨37251284528619745655189107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49668379371492994206918809 37251284528619745655189107)
    ·
      refine ⟨55876926792929618482783661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37251284528619745655189107 55876926792929618482783661)
      ·
        refine ⟨20953847547348606931043873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55876926792929618482783661 20953847547348606931043873)
        ·
          refine ⟨15715385660511455198282905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20953847547348606931043873 15715385660511455198282905)
          ·
            refine ⟨11786539245383591398712179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15715385660511455198282905 11786539245383591398712179)
            ·
              refine ⟨17679808868075387098068269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11786539245383591398712179 17679808868075387098068269)
              ·
                refine ⟨6629928325528270161775601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17679808868075387098068269 6629928325528270161775601)
                ·
                  refine ⟨4972446244146202621331701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6629928325528270161775601 4972446244146202621331701)
                  ·
                    refine ⟨466166835388706495749847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4972446244146202621331701 466166835388706495749847)
                    ·
                      rfl

theorem cell22_1361785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_1361785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361785 prefixEnd_1361785 := by exact prefixLift 1361785
  have htrace : WordTrace (prefixWord ++ tailWord_1361785) baseStart_1361785 baseEnd_1361785 := by
    simpa [prefixWord, tailWord_1361785, baseEnd_1361785] using wordTrace_append hprefix tailTrace_1361785
  have hstable : (prefixWord ++ tailWord_1361785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361785).length < 2 ^ (prefixWord ++ tailWord_1361785).sum := by decide
  have hdescent : baseEnd_1361785 < baseStart_1361785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361817 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_1361817 : Nat := 118140960795 + 1361817 * 2 ^ 59
def prefixEnd_1361817 : Nat := 4983230072969 + 3 ^ 40 * 1361817 * 2
def baseEnd_1361817 : Nat := 466177789642669078949749

theorem tailTrace_1361817 : CollatzResearch.WordTrace tailWord_1361817 prefixEnd_1361817 466177789642669078949749 := by
  unfold tailWord_1361817
  simp only [CollatzResearch.WordTrace]
  refine ⟨49669546507377063672083705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33113031004918042448055803 49669546507377063672083705)
  ·
    refine ⟨37252159880532797754062779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49669546507377063672083705 37252159880532797754062779)
    ·
      refine ⟨55878239820799196631094169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37252159880532797754062779 55878239820799196631094169)
      ·
        refine ⟨41908679865599397473320627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55878239820799196631094169 41908679865599397473320627)
        ·
          refine ⟨62863019798399096209980941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41908679865599397473320627 62863019798399096209980941)
          ·
            refine ⟨23573632424399661078742853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62863019798399096209980941 23573632424399661078742853)
            ·
              refine ⟨4420056079574936452264285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23573632424399661078742853 4420056079574936452264285)
              ·
                refine ⟨1657521029840601169599107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420056079574936452264285 1657521029840601169599107)
                ·
                  refine ⟨2486281544760901754398661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657521029840601169599107 2486281544760901754398661)
                  ·
                    refine ⟨466177789642669078949749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2486281544760901754398661 466177789642669078949749)
                    ·
                      rfl

theorem cell22_1361817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_1361817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361817 prefixEnd_1361817 := by exact prefixLift 1361817
  have htrace : WordTrace (prefixWord ++ tailWord_1361817) baseStart_1361817 baseEnd_1361817 := by
    simpa [prefixWord, tailWord_1361817, baseEnd_1361817] using wordTrace_append hprefix tailTrace_1361817
  have hstable : (prefixWord ++ tailWord_1361817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361817).length < 2 ^ (prefixWord ++ tailWord_1361817).sum := by decide
  have hdescent : baseEnd_1361817 < baseStart_1361817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361838 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_1361838 : Nat := 118140960795 + 1361838 * 2 ^ 59
def prefixEnd_1361838 : Nat := 4983230072969 + 3 ^ 40 * 1361838 * 2
def baseEnd_1361838 : Nat := 155394992790610674724895

theorem tailTrace_1361838 : CollatzResearch.WordTrace tailWord_1361838 prefixEnd_1361838 155394992790610674724895 := by
  unfold tailWord_1361838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208789055037623032324771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33113541626867322839065445 6208789055037623032324771)
  ·
    refine ⟨9313183582556434548487157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208789055037623032324771 9313183582556434548487157)
    ·
      refine ⟨873110960864665738920671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9313183582556434548487157 873110960864665738920671)
      ·
        refine ⟨1309666441296998608381007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873110960864665738920671 1309666441296998608381007)
        ·
          refine ⟨1964499661945497912571511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309666441296998608381007 1964499661945497912571511)
          ·
            refine ⟨2946749492918246868857267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964499661945497912571511 2946749492918246868857267)
            ·
              refine ⟨4420124239377370303285901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946749492918246868857267 4420124239377370303285901)
              ·
                refine ⟨1657546589766513863732213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420124239377370303285901 1657546589766513863732213)
                ·
                  refine ⟨155394992790610674724895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657546589766513863732213 155394992790610674724895)
                  ·
                    rfl

theorem cell22_1361838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_1361838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361838 prefixEnd_1361838 := by exact prefixLift 1361838
  have htrace : WordTrace (prefixWord ++ tailWord_1361838) baseStart_1361838 baseEnd_1361838 := by
    simpa [prefixWord, tailWord_1361838, baseEnd_1361838] using wordTrace_append hprefix tailTrace_1361838
  have hstable : (prefixWord ++ tailWord_1361838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361838).length < 2 ^ (prefixWord ++ tailWord_1361838).sum := by decide
  have hdescent : baseEnd_1361838 < baseStart_1361838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361881 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_1361881 : Nat := 118140960795 + 1361881 * 2 ^ 59
def prefixEnd_1361881 : Nat := 4983230072969 + 3 ^ 40 * 1361881 * 2
def baseEnd_1361881 : Nat := 466199698150594245349553

theorem tailTrace_1361881 : CollatzResearch.WordTrace tailWord_1361881 prefixEnd_1361881 466199698150594245349553 := by
  unfold tailWord_1361881
  simp only [CollatzResearch.WordTrace]
  refine ⟨49671880779145202602413497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33114587186096801734942331 49671880779145202602413497)
  ·
    refine ⟨37253910584358901951810123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49671880779145202602413497 37253910584358901951810123)
    ·
      refine ⟨55880865876538352927715185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37253910584358901951810123 55880865876538352927715185)
      ·
        refine ⟨41910649407403764695786389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55880865876538352927715185 41910649407403764695786389)
        ·
          refine ⟨1964561690972051470114987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41910649407403764695786389 1964561690972051470114987)
          ·
            refine ⟨2946842536458077205172481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964561690972051470114987 2946842536458077205172481)
            ·
              refine ⟨2210131902343557903879361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946842536458077205172481 2210131902343557903879361)
              ·
                refine ⟨1657598926757668427909521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210131902343557903879361 1657598926757668427909521)
                ·
                  refine ⟨1243199195068251320932141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1657598926757668427909521 1243199195068251320932141)
                  ·
                    refine ⟨466199698150594245349553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243199195068251320932141 466199698150594245349553)
                    ·
                      rfl

theorem cell22_1361881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_1361881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361881 prefixEnd_1361881 := by exact prefixLift 1361881
  have htrace : WordTrace (prefixWord ++ tailWord_1361881) baseStart_1361881 baseEnd_1361881 := by
    simpa [prefixWord, tailWord_1361881, baseEnd_1361881] using wordTrace_append hprefix tailTrace_1361881
  have hstable : (prefixWord ++ tailWord_1361881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361881).length < 2 ^ (prefixWord ++ tailWord_1361881).sum := by decide
  have hdescent : baseEnd_1361881 < baseStart_1361881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361969 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_1361969 : Nat := 118140960795 + 1361969 * 2 ^ 59
def prefixEnd_1361969 : Nat := 4983230072969 + 3 ^ 40 * 1361969 * 2
def baseEnd_1361969 : Nat := 466229822348991349149283

theorem tailTrace_1361969 : CollatzResearch.WordTrace tailWord_1361969 prefixEnd_1361969 466229822348991349149283 := by
  unfold tailWord_1361969
  simp only [CollatzResearch.WordTrace]
  refine ⟨49675090402826393631616961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33116726935217595754411307 49675090402826393631616961)
  ·
    refine ⟨37256317802119795223712721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49675090402826393631616961 37256317802119795223712721)
    ·
      refine ⟨27942238351589846417784541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37256317802119795223712721 27942238351589846417784541)
      ·
        refine ⟨10478339381846192406669203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27942238351589846417784541 10478339381846192406669203)
        ·
          refine ⟨15717509072769288610003805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10478339381846192406669203 15717509072769288610003805)
          ·
            refine ⟨5894065902288483228751427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15717509072769288610003805 5894065902288483228751427)
            ·
              refine ⟨8841098853432724843127141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894065902288483228751427 8841098853432724843127141)
              ·
                refine ⟨1657706035018635908086339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8841098853432724843127141 1657706035018635908086339)
                ·
                  refine ⟨2486559052527953862129509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657706035018635908086339 2486559052527953862129509)
                  ·
                    refine ⟨466229822348991349149283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2486559052527953862129509 466229822348991349149283)
                    ·
                      rfl

theorem cell22_1361969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_1361969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1361969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1361969 prefixEnd_1361969 := by exact prefixLift 1361969
  have htrace : WordTrace (prefixWord ++ tailWord_1361969) baseStart_1361969 baseEnd_1361969 := by
    simpa [prefixWord, tailWord_1361969, baseEnd_1361969] using wordTrace_append hprefix tailTrace_1361969
  have hstable : (prefixWord ++ tailWord_1361969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361969).length < 2 ^ (prefixWord ++ tailWord_1361969).sum := by decide
  have hdescent : baseEnd_1361969 < baseStart_1361969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362016 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_1362016 : Nat := 118140960795 + 1362016 * 2 ^ 59
def prefixEnd_1362016 : Nat := 4983230072969 + 3 ^ 40 * 1362016 * 2
def baseEnd_1362016 : Nat := 466245911409498893224139

theorem tailTrace_1362016 : CollatzResearch.WordTrace tailWord_1362016 prefixEnd_1362016 466245911409498893224139 := by
  unfold tailWord_1362016
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838402316828060329288951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33117869755770747105718601 24838402316828060329288951)
  ·
    refine ⟨37257603475242090493933427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24838402316828060329288951 37257603475242090493933427)
    ·
      refine ⟨55886405212863135740900141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37257603475242090493933427 55886405212863135740900141)
      ·
        refine ⟨20957401954823675902837553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55886405212863135740900141 20957401954823675902837553)
        ·
          refine ⟨15718051466117756927128165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20957401954823675902837553 15718051466117756927128165)
          ·
            refine ⟨2947134649897079423836531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15718051466117756927128165 2947134649897079423836531)
            ·
              refine ⟨4420701974845619135754797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947134649897079423836531 4420701974845619135754797)
              ·
                refine ⟨1657763240567107175908049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420701974845619135754797 1657763240567107175908049)
                ·
                  refine ⟨1243322430425330381931037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1657763240567107175908049 1243322430425330381931037)
                  ·
                    refine ⟨466245911409498893224139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243322430425330381931037 466245911409498893224139)
                    ·
                      rfl

theorem cell22_1362016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_1362016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362016 prefixEnd_1362016 := by exact prefixLift 1362016
  have htrace : WordTrace (prefixWord ++ tailWord_1362016) baseStart_1362016 baseEnd_1362016 := by
    simpa [prefixWord, tailWord_1362016, baseEnd_1362016] using wordTrace_append hprefix tailTrace_1362016
  have hstable : (prefixWord ++ tailWord_1362016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362016).length < 2 ^ (prefixWord ++ tailWord_1362016).sum := by decide
  have hdescent : baseEnd_1362016 < baseStart_1362016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362042 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1362042 : Nat := 118140960795 + 1362042 * 2 ^ 59
def prefixEnd_1362042 : Nat := 4983230072969 + 3 ^ 40 * 1362042 * 2
def baseEnd_1362042 : Nat := 466254811740843492074059

theorem tailTrace_1362042 : CollatzResearch.WordTrace tailWord_1362042 prefixEnd_1362042 466254811740843492074059 := by
  unfold tailWord_1362042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419438232890481774756095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33118501954374618066016253 12419438232890481774756095)
  ·
    refine ⟨18629157349335722662134143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12419438232890481774756095 18629157349335722662134143)
    ·
      refine ⟨27943736024003583993201215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18629157349335722662134143 27943736024003583993201215)
      ·
        refine ⟨41915604036005375989801823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27943736024003583993201215 41915604036005375989801823)
        ·
          refine ⟨62873406054008063984702735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41915604036005375989801823 62873406054008063984702735)
          ·
            refine ⟨94310109081012095977054103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62873406054008063984702735 94310109081012095977054103)
            ·
              refine ⟨141465163621518143965581155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94310109081012095977054103 141465163621518143965581155)
              ·
                refine ⟨212197745432277215948371733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141465163621518143965581155 212197745432277215948371733)
                ·
                  refine ⟨9946769317137994497579925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212197745432277215948371733 9946769317137994497579925)
                  ·
                    refine ⟨466254811740843492074059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9946769317137994497579925 466254811740843492074059)
                    ·
                      rfl

theorem cell22_1362042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1362042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362042 prefixEnd_1362042 := by exact prefixLift 1362042
  have htrace : WordTrace (prefixWord ++ tailWord_1362042) baseStart_1362042 baseEnd_1362042 := by
    simpa [prefixWord, tailWord_1362042, baseEnd_1362042] using wordTrace_append hprefix tailTrace_1362042
  have hstable : (prefixWord ++ tailWord_1362042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362042).length < 2 ^ (prefixWord ++ tailWord_1362042).sum := by decide
  have hdescent : baseEnd_1362042 < baseStart_1362042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362108 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_1362108 : Nat := 118140960795 + 1362108 * 2 ^ 59
def prefixEnd_1362108 : Nat := 4983230072969 + 3 ^ 40 * 1362108 * 2
def baseEnd_1362108 : Nat := 155425801629880439974619

theorem tailTrace_1362108 : CollatzResearch.WordTrace tailWord_1362108 prefixEnd_1362108 155425801629880439974619 := by
  unfold tailWord_1362108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840080074661410185463489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33120106766215213580617985 24840080074661410185463489)
  ·
    refine ⟨18630060055996057639097617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24840080074661410185463489 18630060055996057639097617)
    ·
      refine ⟨13972545041997043229323213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18630060055996057639097617 13972545041997043229323213)
      ·
        refine ⟨5239704390748891210996205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13972545041997043229323213 5239704390748891210996205)
        ·
          refine ⟨1964889146530834204123577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5239704390748891210996205 1964889146530834204123577)
          ·
            refine ⟨1473666859898125653092683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964889146530834204123577 1473666859898125653092683)
            ·
              refine ⟨2210500289847188479639025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473666859898125653092683 2210500289847188479639025)
              ·
                refine ⟨1657875217385391359729269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210500289847188479639025 1657875217385391359729269)
                ·
                  refine ⟨155425801629880439974619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657875217385391359729269 155425801629880439974619)
                  ·
                    rfl

theorem cell22_1362108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_1362108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362108 prefixEnd_1362108 := by exact prefixLift 1362108
  have htrace : WordTrace (prefixWord ++ tailWord_1362108) baseStart_1362108 baseEnd_1362108 := by
    simpa [prefixWord, tailWord_1362108, baseEnd_1362108] using wordTrace_append hprefix tailTrace_1362108
  have hstable : (prefixWord ++ tailWord_1362108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362108).length < 2 ^ (prefixWord ++ tailWord_1362108).sum := by decide
  have hdescent : baseEnd_1362108 < baseStart_1362108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362146 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1362146 : Nat := 118140960795 + 1362146 * 2 ^ 59
def prefixEnd_1362146 : Nat := 4983230072969 + 3 ^ 40 * 1362146 * 2
def baseEnd_1362146 : Nat := 466290413066221887473741

theorem tailTrace_1362146 : CollatzResearch.WordTrace tailWord_1362146 prefixEnd_1362146 466290413066221887473741 := by
  unfold tailWord_1362146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12420386530796288215202573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33121030748790101907206861 12420386530796288215202573)
  ·
    refine ⟨4657644949048608080700965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12420386530796288215202573 4657644949048608080700965)
    ·
      refine ⟨873308427946614015131431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4657644949048608080700965 873308427946614015131431)
      ·
        refine ⟨1309962641919921022697147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873308427946614015131431 1309962641919921022697147)
        ·
          refine ⟨1964943962879881534045721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309962641919921022697147 1964943962879881534045721)
          ·
            refine ⟨1473707972159911150534291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964943962879881534045721 1473707972159911150534291)
            ·
              refine ⟨2210561958239866725801437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473707972159911150534291 2210561958239866725801437)
              ·
                refine ⟨828960734339950022175539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2210561958239866725801437 828960734339950022175539)
                ·
                  refine ⟨1243441101509925033263309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 828960734339950022175539 1243441101509925033263309)
                  ·
                    refine ⟨466290413066221887473741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243441101509925033263309 466290413066221887473741)
                    ·
                      rfl

theorem cell22_1362146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1362146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362146 prefixEnd_1362146 := by exact prefixLift 1362146
  have htrace : WordTrace (prefixWord ++ tailWord_1362146) baseStart_1362146 baseEnd_1362146 := by
    simpa [prefixWord, tailWord_1362146, baseEnd_1362146] using wordTrace_append hprefix tailTrace_1362146
  have hstable : (prefixWord ++ tailWord_1362146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362146).length < 2 ^ (prefixWord ++ tailWord_1362146).sum := by decide
  have hdescent : baseEnd_1362146 < baseStart_1362146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362166 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1362166 : Nat := 118140960795 + 1362166 * 2 ^ 59
def prefixEnd_1362166 : Nat := 4983230072969 + 3 ^ 40 * 1362166 * 2
def baseEnd_1362166 : Nat := 466297259474948501973679

theorem tailTrace_1362166 : CollatzResearch.WordTrace tailWord_1362166 prefixEnd_1362166 466297259474948501973679 := by
  unfold tailWord_1362166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105142223944543517283647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33121517055408464184358901 3105142223944543517283647)
  ·
    refine ⟨4657713335916815275925471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3105142223944543517283647 4657713335916815275925471)
    ·
      refine ⟨6986570003875222913888207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657713335916815275925471 6986570003875222913888207)
      ·
        refine ⟨10479855005812834370832311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6986570003875222913888207 10479855005812834370832311)
        ·
          refine ⟨15719782508719251556248467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10479855005812834370832311 15719782508719251556248467)
          ·
            refine ⟨23579673763078877334372701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15719782508719251556248467 23579673763078877334372701)
            ·
              refine ⟨8842377661154579000389763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23579673763078877334372701 8842377661154579000389763)
              ·
                refine ⟨13263566491731868500584645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8842377661154579000389763 13263566491731868500584645)
                ·
                  refine ⟨2486918717199725343859621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13263566491731868500584645 2486918717199725343859621)
                  ·
                    refine ⟨466297259474948501973679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2486918717199725343859621 466297259474948501973679)
                    ·
                      rfl

theorem cell22_1362166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1362166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362166 prefixEnd_1362166 := by exact prefixLift 1362166
  have htrace : WordTrace (prefixWord ++ tailWord_1362166) baseStart_1362166 baseEnd_1362166 := by
    simpa [prefixWord, tailWord_1362166, baseEnd_1362166] using wordTrace_append hprefix tailTrace_1362166
  have hstable : (prefixWord ++ tailWord_1362166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362166).length < 2 ^ (prefixWord ++ tailWord_1362166).sum := by decide
  have hdescent : baseEnd_1362166 < baseStart_1362166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362185 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_1362185 : Nat := 118140960795 + 1362185 * 2 ^ 59
def prefixEnd_1362185 : Nat := 4983230072969 + 3 ^ 40 * 1362185 * 2
def baseEnd_1362185 : Nat := 466303763563238785748621

theorem tailTrace_1362185 : CollatzResearch.WordTrace tailWord_1362185 prefixEnd_1362185 466303763563238785748621 := by
  unfold tailWord_1362185
  simp only [CollatzResearch.WordTrace]
  refine ⟨49682968570043862521480009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33121979046695908347653339 49682968570043862521480009)
  ·
    refine ⟨37262226427532896891110007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49682968570043862521480009 37262226427532896891110007)
    ·
      refine ⟨55893339641299345336665011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37262226427532896891110007 55893339641299345336665011)
      ·
        refine ⟨83840009461949018004997517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55893339641299345336665011 83840009461949018004997517)
        ·
          refine ⟨31440003548230881751874069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83840009461949018004997517 31440003548230881751874069)
          ·
            refine ⟨1473750166323322582119097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31440003548230881751874069 1473750166323322582119097)
            ·
              refine ⟨1105312624742491936589323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473750166323322582119097 1105312624742491936589323)
              ·
                refine ⟨1657968937113737904883985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105312624742491936589323 1657968937113737904883985)
                ·
                  refine ⟨1243476702835303428662989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1657968937113737904883985 1243476702835303428662989)
                  ·
                    refine ⟨466303763563238785748621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243476702835303428662989 466303763563238785748621)
                    ·
                      rfl

theorem cell22_1362185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_1362185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362185 prefixEnd_1362185 := by exact prefixLift 1362185
  have htrace : WordTrace (prefixWord ++ tailWord_1362185) baseStart_1362185 baseEnd_1362185 := by
    simpa [prefixWord, tailWord_1362185, baseEnd_1362185] using wordTrace_append hprefix tailTrace_1362185
  have hstable : (prefixWord ++ tailWord_1362185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362185).length < 2 ^ (prefixWord ++ tailWord_1362185).sum := by decide
  have hdescent : baseEnd_1362185 < baseStart_1362185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362209 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 9]
def baseStart_1362209 : Nat := 118140960795 + 1362209 * 2 ^ 59
def prefixEnd_1362209 : Nat := 4983230072969 + 3 ^ 40 * 1362209 * 2
def baseEnd_1362209 : Nat := 155437326417903574382849

theorem tailTrace_1362209 : CollatzResearch.WordTrace tailWord_1362209 prefixEnd_1362209 155437326417903574382849 := by
  unfold tailWord_1362209
  simp only [CollatzResearch.WordTrace]
  refine ⟨49683843921956914620353681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33122562614637943080235787 49683843921956914620353681)
  ·
    refine ⟨37262882941467685965265261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49683843921956914620353681 37262882941467685965265261)
    ·
      refine ⟨13973581103050382236974473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37262882941467685965265261 13973581103050382236974473)
      ·
        refine ⟨10480185827287786677730855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13973581103050382236974473 10480185827287786677730855)
        ·
          refine ⟨15720278740931680016596283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10480185827287786677730855 15720278740931680016596283)
          ·
            refine ⟨23580418111397520024894425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15720278740931680016596283 23580418111397520024894425)
            ·
              refine ⟨17685313583548140018670819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23580418111397520024894425 17685313583548140018670819)
              ·
                refine ⟨26527970375322210028006229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17685313583548140018670819 26527970375322210028006229)
                ·
                  refine ⟨155437326417903574382849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26527970375322210028006229 155437326417903574382849)
                  ·
                    rfl

theorem cell22_1362209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_1362209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362209 prefixEnd_1362209 := by exact prefixLift 1362209
  have htrace : WordTrace (prefixWord ++ tailWord_1362209) baseStart_1362209 baseEnd_1362209 := by
    simpa [prefixWord, tailWord_1362209, baseEnd_1362209] using wordTrace_append hprefix tailTrace_1362209
  have hstable : (prefixWord ++ tailWord_1362209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362209).length < 2 ^ (prefixWord ++ tailWord_1362209).sum := by decide
  have hdescent : baseEnd_1362209 < baseStart_1362209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362215 : List Nat := [1, 1, 8, 1, 2, 9]
def baseStart_1362215 : Nat := 118140960795 + 1362215 * 2 ^ 59
def prefixEnd_1362215 : Nat := 4983230072969 + 3 ^ 40 * 1362215 * 2
def baseEnd_1362215 : Nat := 5756963372547267993809

theorem tailTrace_1362215 : CollatzResearch.WordTrace tailWord_1362215 prefixEnd_1362215 5756963372547267993809 := by
  unfold tailWord_1362215
  simp only [CollatzResearch.WordTrace]
  refine ⟨49684062759935177645072099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33122708506623451763381399 49684062759935177645072099)
  ·
    refine ⟨74526094139902766467608149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49684062759935177645072099 74526094139902766467608149)
    ·
      refine ⟨873352665701985544542283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 74526094139902766467608149 873352665701985544542283)
      ·
        refine ⟨1310028998552978316813425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873352665701985544542283 1310028998552978316813425)
        ·
          refine ⟨982521748914733737610069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310028998552978316813425 982521748914733737610069)
          ·
            refine ⟨5756963372547267993809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 982521748914733737610069 5756963372547267993809)
            ·
              rfl

theorem cell22_1362215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 9].length) (baseStart_1362215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362215 prefixEnd_1362215 := by exact prefixLift 1362215
  have htrace : WordTrace (prefixWord ++ tailWord_1362215) baseStart_1362215 baseEnd_1362215 := by
    simpa [prefixWord, tailWord_1362215, baseEnd_1362215] using wordTrace_append hprefix tailTrace_1362215
  have hstable : (prefixWord ++ tailWord_1362215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362215).length < 2 ^ (prefixWord ++ tailWord_1362215).sum := by decide
  have hdescent : baseEnd_1362215 < baseStart_1362215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362256 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_1362256 : Nat := 118140960795 + 1362256 * 2 ^ 59
def prefixEnd_1362256 : Nat := 4983230072969 + 3 ^ 40 * 1362256 * 2
def baseEnd_1362256 : Nat := 466328068314218267223403

theorem tailTrace_1362256 : CollatzResearch.WordTrace tailWord_1362256 prefixEnd_1362256 466328068314218267223403 := by
  unfold tailWord_1362256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842779076393320823657311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33123705435191094431543081 24842779076393320823657311)
  ·
    refine ⟨37264168614589981235485967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24842779076393320823657311 37264168614589981235485967)
    ·
      refine ⟨55896252921884971853228951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37264168614589981235485967 55896252921884971853228951)
      ·
        refine ⟨83844379382827457779843427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55896252921884971853228951 83844379382827457779843427)
        ·
          refine ⟨125766569074241186669765141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83844379382827457779843427 125766569074241186669765141)
          ·
            refine ⟨5895307925355055625145241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125766569074241186669765141 5895307925355055625145241)
            ·
              refine ⟨4421480944016291718858931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5895307925355055625145241 4421480944016291718858931)
              ·
                refine ⟨6632221416024437578288397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421480944016291718858931 6632221416024437578288397)
                ·
                  refine ⟨2487083031009164091858149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6632221416024437578288397 2487083031009164091858149)
                  ·
                    refine ⟨466328068314218267223403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2487083031009164091858149 466328068314218267223403)
                    ·
                      rfl

theorem cell22_1362256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_1362256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362256 prefixEnd_1362256 := by exact prefixLift 1362256
  have htrace : WordTrace (prefixWord ++ tailWord_1362256) baseStart_1362256 baseEnd_1362256 := by
    simpa [prefixWord, tailWord_1362256, baseEnd_1362256] using wordTrace_append hprefix tailTrace_1362256
  have hstable : (prefixWord ++ tailWord_1362256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362256).length < 2 ^ (prefixWord ++ tailWord_1362256).sum := by decide
  have hdescent : baseEnd_1362256 < baseStart_1362256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362288 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_1362288 : Nat := 118140960795 + 1362288 * 2 ^ 59
def prefixEnd_1362288 : Nat := 4983230072969 + 3 ^ 40 * 1362288 * 2
def baseEnd_1362288 : Nat := 155446340856060283474435

theorem tailTrace_1362288 : CollatzResearch.WordTrace tailWord_1362288 prefixEnd_1362288 155446340856060283474435 := by
  unfold tailWord_1362288
  simp only [CollatzResearch.WordTrace]
  refine ⟨24843362644335355556239759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33124483525780474074986345 24843362644335355556239759)
  ·
    refine ⟨37265043966503033334359639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24843362644335355556239759 37265043966503033334359639)
    ·
      refine ⟨55897565949754550001539459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37265043966503033334359639 55897565949754550001539459)
      ·
        refine ⟨83846348924631825002309189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55897565949754550001539459 83846348924631825002309189)
        ·
          refine ⟨15721190423368467187932973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83846348924631825002309189 15721190423368467187932973)
          ·
            refine ⟨5895446408763175195474865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15721190423368467187932973 5895446408763175195474865)
            ·
              refine ⟨4421584806572381396606149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5895446408763175195474865 4421584806572381396606149)
              ·
                refine ⟨829047151232321511863653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4421584806572381396606149 829047151232321511863653)
                ·
                  refine ⟨155446340856060283474435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829047151232321511863653 155446340856060283474435)
                  ·
                    rfl

theorem cell22_1362288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_1362288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362288 prefixEnd_1362288 := by exact prefixLift 1362288
  have htrace : WordTrace (prefixWord ++ tailWord_1362288) baseStart_1362288 baseEnd_1362288 := by
    simpa [prefixWord, tailWord_1362288, baseEnd_1362288] using wordTrace_append hprefix tailTrace_1362288
  have hstable : (prefixWord ++ tailWord_1362288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362288).length < 2 ^ (prefixWord ++ tailWord_1362288).sum := by decide
  have hdescent : baseEnd_1362288 < baseStart_1362288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362301 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1362301 : Nat := 118140960795 + 1362301 * 2 ^ 59
def prefixEnd_1362301 : Nat := 4983230072969 + 3 ^ 40 * 1362301 * 2
def baseEnd_1362301 : Nat := 466343472733853149848265

theorem tailTrace_1362301 : CollatzResearch.WordTrace tailWord_1362301 prefixEnd_1362301 466343472733853149848265 := by
  unfold tailWord_1362301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49687199437623614332702757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33124799625082409555135171 49687199437623614332702757)
  ·
    refine ⟨9316349894554427687381767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49687199437623614332702757 9316349894554427687381767)
    ·
      refine ⟨13974524841831641531072651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9316349894554427687381767 13974524841831641531072651)
      ·
        refine ⟨20961787262747462296608977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13974524841831641531072651 20961787262747462296608977)
        ·
          refine ⟨15721340447060596722456733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20961787262747462296608977 15721340447060596722456733)
          ·
            refine ⟨5895502667647723770921275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15721340447060596722456733 5895502667647723770921275)
            ·
              refine ⟨8843254001471585656381913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895502667647723770921275 8843254001471585656381913)
              ·
                refine ⟨6632440501103689242286435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843254001471585656381913 6632440501103689242286435)
                ·
                  refine ⟨9948660751655533863429653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632440501103689242286435 9948660751655533863429653)
                  ·
                    refine ⟨466343472733853149848265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9948660751655533863429653 466343472733853149848265)
                    ·
                      rfl

theorem cell22_1362301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1362301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362301 prefixEnd_1362301 := by exact prefixLift 1362301
  have htrace : WordTrace (prefixWord ++ tailWord_1362301) baseStart_1362301 baseEnd_1362301 := by
    simpa [prefixWord, tailWord_1362301, baseEnd_1362301] using wordTrace_append hprefix tailTrace_1362301
  have hstable : (prefixWord ++ tailWord_1362301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362301).length < 2 ^ (prefixWord ++ tailWord_1362301).sum := by decide
  have hdescent : baseEnd_1362301 < baseStart_1362301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362316 : List Nat := [2, 2, 1, 2, 1, 5, 1, 8]
def baseStart_1362316 : Nat := 118140960795 + 1362316 * 2 ^ 59
def prefixEnd_1362316 : Nat := 4983230072969 + 3 ^ 40 * 1362316 * 2
def baseEnd_1362316 : Nat := 51816511948933123413691

theorem tailTrace_1362316 : CollatzResearch.WordTrace tailWord_1362316 prefixEnd_1362316 51816511948933123413691 := by
  unfold tailWord_1362316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24843873266284635947249401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33125164355046181262999201 24843873266284635947249401)
  ·
    refine ⟨18632904949713476960437051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24843873266284635947249401 18632904949713476960437051)
    ·
      refine ⟨27949357424570215440655577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18632904949713476960437051 27949357424570215440655577)
      ·
        refine ⟨20962018068427661580491683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27949357424570215440655577 20962018068427661580491683)
        ·
          refine ⟨31443027102641492370737525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20962018068427661580491683 31443027102641492370737525)
          ·
            refine ⟨2947783790872639909756643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31443027102641492370737525 2947783790872639909756643)
            ·
              refine ⟨4421675686308959864634965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947783790872639909756643 4421675686308959864634965)
              ·
                refine ⟨51816511948933123413691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4421675686308959864634965 51816511948933123413691)
                ·
                  rfl

theorem cell22_1362316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_1362316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362316 prefixEnd_1362316 := by exact prefixLift 1362316
  have htrace : WordTrace (prefixWord ++ tailWord_1362316) baseStart_1362316 baseEnd_1362316 := by
    simpa [prefixWord, tailWord_1362316, baseEnd_1362316] using wordTrace_append hprefix tailTrace_1362316
  have hstable : (prefixWord ++ tailWord_1362316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362316).length < 2 ^ (prefixWord ++ tailWord_1362316).sum := by decide
  have hdescent : baseEnd_1362316 < baseStart_1362316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362318 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1362318 : Nat := 118140960795 + 1362318 * 2 ^ 59
def prefixEnd_1362318 : Nat := 4983230072969 + 3 ^ 40 * 1362318 * 2
def baseEnd_1362318 : Nat := 466349292181270772173213

theorem tailTrace_1362318 : CollatzResearch.WordTrace tailWord_1362318 prefixEnd_1362318 466349292181270772173213 := by
  unfold tailWord_1362318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210977434820253279508951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33125212985708017490714405 6210977434820253279508951)
  ·
    refine ⟨9316466152230379919263427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6210977434820253279508951 9316466152230379919263427)
    ·
      refine ⟨13974699228345569878895141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9316466152230379919263427 13974699228345569878895141)
      ·
        refine ⟨2620256105314794352292839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13974699228345569878895141 2620256105314794352292839)
        ·
          refine ⟨3930384157972191528439259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620256105314794352292839 3930384157972191528439259)
          ·
            refine ⟨5895576236958287292658889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930384157972191528439259 5895576236958287292658889)
            ·
              refine ⟨4421682177718715469494167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5895576236958287292658889 4421682177718715469494167)
              ·
                refine ⟨6632523266578073204241251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421682177718715469494167 6632523266578073204241251)
                ·
                  refine ⟨9948784899867109806361877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632523266578073204241251 9948784899867109806361877)
                  ·
                    refine ⟨466349292181270772173213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9948784899867109806361877 466349292181270772173213)
                    ·
                      rfl

theorem cell22_1362318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1362318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362318 prefixEnd_1362318 := by exact prefixLift 1362318
  have htrace : WordTrace (prefixWord ++ tailWord_1362318) baseStart_1362318 baseEnd_1362318 := by
    simpa [prefixWord, tailWord_1362318, baseEnd_1362318] using wordTrace_append hprefix tailTrace_1362318
  have hstable : (prefixWord ++ tailWord_1362318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362318).length < 2 ^ (prefixWord ++ tailWord_1362318).sum := by decide
  have hdescent : baseEnd_1362318 < baseStart_1362318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362333 : List Nat := [1, 4, 2, 1, 4, 2, 8]
def baseStart_1362333 : Nat := 118140960795 + 1362333 * 2 ^ 59
def prefixEnd_1362333 : Nat := 4983230072969 + 3 ^ 40 * 1362333 * 2
def baseEnd_1362333 : Nat := 17272386184733916038821

theorem tailTrace_1362333 : CollatzResearch.WordTrace tailWord_1362333 prefixEnd_1362333 17272386184733916038821 := by
  unfold tailWord_1362333
  simp only [CollatzResearch.WordTrace]
  refine ⟨49688366573507683797867653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33125577715671789198578435 49688366573507683797867653)
  ·
    refine ⟨9316568732532690712100185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49688366573507683797867653 9316568732532690712100185)
    ·
      refine ⟨6987426549399518034075139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9316568732532690712100185 6987426549399518034075139)
      ·
        refine ⟨10481139824099277051112709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987426549399518034075139 10481139824099277051112709)
        ·
          refine ⟨1965213717018614447083633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10481139824099277051112709 1965213717018614447083633)
          ·
            refine ⟨1473910287763960835312725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965213717018614447083633 1473910287763960835312725)
            ·
              refine ⟨17272386184733916038821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1473910287763960835312725 17272386184733916038821)
              ·
                rfl

theorem cell22_1362333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 8].length) (baseStart_1362333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362333 prefixEnd_1362333 := by exact prefixLift 1362333
  have htrace : WordTrace (prefixWord ++ tailWord_1362333) baseStart_1362333 baseEnd_1362333 := by
    simpa [prefixWord, tailWord_1362333, baseEnd_1362333] using wordTrace_append hprefix tailTrace_1362333
  have hstable : (prefixWord ++ tailWord_1362333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362333).length < 2 ^ (prefixWord ++ tailWord_1362333).sum := by decide
  have hdescent : baseEnd_1362333 < baseStart_1362333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362369 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1362369 : Nat := 118140960795 + 1362369 * 2 ^ 59
def prefixEnd_1362369 : Nat := 4983230072969 + 3 ^ 40 * 1362369 * 2
def baseEnd_1362369 : Nat := 466366750523523639148057

theorem tailTrace_1362369 : CollatzResearch.WordTrace tailWord_1362369 prefixEnd_1362369 466366750523523639148057 := by
  unfold tailWord_1362369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49689679601377261946178161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33126453067584841297452107 49689679601377261946178161)
  ·
    refine ⟨37267259701032946459633621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49689679601377261946178161 37267259701032946459633621)
    ·
      refine ⟨873451399242959682647663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37267259701032946459633621 873451399242959682647663)
      ·
        refine ⟨1310177098864439523971495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873451399242959682647663 1310177098864439523971495)
        ·
          refine ⟨1965265648296659285957243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310177098864439523971495 1965265648296659285957243)
          ·
            refine ⟨2947898472444988928935865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965265648296659285957243 2947898472444988928935865)
            ·
              refine ⟨2210923854333741696701899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947898472444988928935865 2210923854333741696701899)
              ·
                refine ⟨3316385781500612545052849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210923854333741696701899 3316385781500612545052849)
                ·
                  refine ⟨2487289336125459408789637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3316385781500612545052849 2487289336125459408789637)
                  ·
                    refine ⟨466366750523523639148057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2487289336125459408789637 466366750523523639148057)
                    ·
                      rfl

theorem cell22_1362369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1362369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362369 prefixEnd_1362369 := by exact prefixLift 1362369
  have htrace : WordTrace (prefixWord ++ tailWord_1362369) baseStart_1362369 baseEnd_1362369 := by
    simpa [prefixWord, tailWord_1362369, baseEnd_1362369] using wordTrace_append hprefix tailTrace_1362369
  have hstable : (prefixWord ++ tailWord_1362369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362369).length < 2 ^ (prefixWord ++ tailWord_1362369).sum := by decide
  have hdescent : baseEnd_1362369 < baseStart_1362369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362399 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 1, 3]
def baseStart_1362399 : Nat := 118140960795 + 1362399 * 2 ^ 59
def prefixEnd_1362399 : Nat := 4983230072969 + 3 ^ 40 * 1362399 * 2
def baseEnd_1362399 : Nat := 466377020136613560897965

theorem tailTrace_1362399 : CollatzResearch.WordTrace tailWord_1362399 prefixEnd_1362399 466377020136613560897965 := by
  unfold tailWord_1362399
  simp only [CollatzResearch.WordTrace]
  refine ⟨49690773791268577069770251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33127182527512384713180167 49690773791268577069770251)
  ·
    refine ⟨74536160686902865604655377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49690773791268577069770251 74536160686902865604655377)
    ·
      refine ⟨55902120515177149203491533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74536160686902865604655377 55902120515177149203491533)
      ·
        refine ⟨20963295193191430951309325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55902120515177149203491533 20963295193191430951309325)
        ·
          refine ⟨7861235697446786606740997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20963295193191430951309325 7861235697446786606740997)
          ·
            refine ⟨1473981693271272488763937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7861235697446786606740997 1473981693271272488763937)
            ·
              refine ⟨1105486269953454366572953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473981693271272488763937 1105486269953454366572953)
              ·
                refine ⟨829114702465090774929715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105486269953454366572953 829114702465090774929715)
                ·
                  refine ⟨1243672053697636162394573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829114702465090774929715 1243672053697636162394573)
                  ·
                    refine ⟨466377020136613560897965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243672053697636162394573 466377020136613560897965)
                    ·
                      rfl

theorem cell22_1362399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_1362399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362399 prefixEnd_1362399 := by exact prefixLift 1362399
  have htrace : WordTrace (prefixWord ++ tailWord_1362399) baseStart_1362399 baseEnd_1362399 := by
    simpa [prefixWord, tailWord_1362399, baseEnd_1362399] using wordTrace_append hprefix tailTrace_1362399
  have hstable : (prefixWord ++ tailWord_1362399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362399).length < 2 ^ (prefixWord ++ tailWord_1362399).sum := by decide
  have hdescent : baseEnd_1362399 < baseStart_1362399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362408 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1362408 : Nat := 118140960795 + 1362408 * 2 ^ 59
def prefixEnd_1362408 : Nat := 4983230072969 + 3 ^ 40 * 1362408 * 2
def baseEnd_1362408 : Nat := 466380101020540537422937

theorem tailTrace_1362408 : CollatzResearch.WordTrace tailWord_1362408 prefixEnd_1362408 466380101020540537422937 := by
  unfold tailWord_1362408
  simp only [CollatzResearch.WordTrace]
  refine ⟨24845551024117985803423939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33127401365490647737898585 24845551024117985803423939)
  ·
    refine ⟨37268326536176978705135909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24845551024117985803423939 37268326536176978705135909)
    ·
      refine ⟨6987811225533183507212983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37268326536176978705135909 6987811225533183507212983)
      ·
        refine ⟨10481716838299775260819475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987811225533183507212983 10481716838299775260819475)
        ·
          refine ⟨15722575257449662891229213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10481716838299775260819475 15722575257449662891229213)
          ·
            refine ⟨5895965721543623584210955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15722575257449662891229213 5895965721543623584210955)
            ·
              refine ⟨8843948582315435376316433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895965721543623584210955 8843948582315435376316433)
              ·
                refine ⟨6632961436736576532237325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843948582315435376316433 6632961436736576532237325)
                ·
                  refine ⟨2487360538776216199588997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6632961436736576532237325 2487360538776216199588997)
                  ·
                    refine ⟨466380101020540537422937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2487360538776216199588997 466380101020540537422937)
                    ·
                      rfl

theorem cell22_1362408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1362408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362408 prefixEnd_1362408 := by exact prefixLift 1362408
  have htrace : WordTrace (prefixWord ++ tailWord_1362408) baseStart_1362408 baseEnd_1362408 := by
    simpa [prefixWord, tailWord_1362408, baseEnd_1362408] using wordTrace_append hprefix tailTrace_1362408
  have hstable : (prefixWord ++ tailWord_1362408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362408).length < 2 ^ (prefixWord ++ tailWord_1362408).sum := by decide
  have hdescent : baseEnd_1362408 < baseStart_1362408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362451 : List Nat := [1, 1, 1, 2, 1, 5, 11]
def baseStart_1362451 : Nat := 118140960795 + 1362451 * 2 ^ 59
def prefixEnd_1362451 : Nat := 4983230072969 + 3 ^ 40 * 1362451 * 2
def baseEnd_1362451 : Nat := 17273882251826028096215

theorem tailTrace_1362451 : CollatzResearch.WordTrace tailWord_1362451 prefixEnd_1362451 17273882251826028096215 := by
  unfold tailWord_1362451
  simp only [CollatzResearch.WordTrace]
  refine ⟨49692670387080189950663207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33128446924720126633775471 49692670387080189950663207)
  ·
    refine ⟨74539005580620284925994811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49692670387080189950663207 74539005580620284925994811)
    ·
      refine ⟨111808508370930427388992217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74539005580620284925994811 111808508370930427388992217)
      ·
        refine ⟨83856381278197820541744163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111808508370930427388992217 83856381278197820541744163)
        ·
          refine ⟨125784571917296730812616245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83856381278197820541744163 125784571917296730812616245)
          ·
            refine ⟨11792303617246568513682773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125784571917296730812616245 11792303617246568513682773)
            ·
              refine ⟨17273882251826028096215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11792303617246568513682773 17273882251826028096215)
              ·
                rfl

theorem cell22_1362451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 11].length) (baseStart_1362451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362451 prefixEnd_1362451 := by exact prefixLift 1362451
  have htrace : WordTrace (prefixWord ++ tailWord_1362451) baseStart_1362451 baseEnd_1362451 := by
    simpa [prefixWord, tailWord_1362451, baseEnd_1362451] using wordTrace_append hprefix tailTrace_1362451
  have hstable : (prefixWord ++ tailWord_1362451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362451).length < 2 ^ (prefixWord ++ tailWord_1362451).sum := by decide
  have hdescent : baseEnd_1362451 < baseStart_1362451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362453 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1362453 : Nat := 118140960795 + 1362453 * 2 ^ 59
def prefixEnd_1362453 : Nat := 4983230072969 + 3 ^ 40 * 1362453 * 2
def baseEnd_1362453 : Nat := 466395505440175420047799

theorem tailTrace_1362453 : CollatzResearch.WordTrace tailWord_1362453 prefixEnd_1362453 466395505440175420047799 := by
  unfold tailWord_1362453
  simp only [CollatzResearch.WordTrace]
  refine ⟨49692743333072944292236013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33128495555381962861490675 49692743333072944292236013)
  ·
    refine ⟨18634778749902354109588505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49692743333072944292236013 18634778749902354109588505)
    ·
      refine ⟨13976084062426765582191379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18634778749902354109588505 13976084062426765582191379)
      ·
        refine ⟨20964126093640148373287069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13976084062426765582191379 20964126093640148373287069)
        ·
          refine ⟨7861547285115055639982651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20964126093640148373287069 7861547285115055639982651)
          ·
            refine ⟨11792320927672583459973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7861547285115055639982651 11792320927672583459973977)
            ·
              refine ⟨8844240695754437594980483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11792320927672583459973977 8844240695754437594980483)
              ·
                refine ⟨13266361043631656392470725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8844240695754437594980483 13266361043631656392470725)
                ·
                  refine ⟨2487442695680935573588261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13266361043631656392470725 2487442695680935573588261)
                  ·
                    refine ⟨466395505440175420047799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2487442695680935573588261 466395505440175420047799)
                    ·
                      rfl

theorem cell22_1362453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1362453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362453 prefixEnd_1362453 := by exact prefixLift 1362453
  have htrace : WordTrace (prefixWord ++ tailWord_1362453) baseStart_1362453 baseEnd_1362453 := by
    simpa [prefixWord, tailWord_1362453, baseEnd_1362453] using wordTrace_append hprefix tailTrace_1362453
  have hstable : (prefixWord ++ tailWord_1362453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362453).length < 2 ^ (prefixWord ++ tailWord_1362453).sum := by decide
  have hdescent : baseEnd_1362453 < baseStart_1362453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362472 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1362472 : Nat := 118140960795 + 1362472 * 2 ^ 59
def prefixEnd_1362472 : Nat := 4983230072969 + 3 ^ 40 * 1362472 * 2
def baseEnd_1362472 : Nat := 466402009528465703822741

theorem tailTrace_1362472 : CollatzResearch.WordTrace tailWord_1362472 prefixEnd_1362472 466402009528465703822741 := by
  unfold tailWord_1362472
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846718160002055268588835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33128957546669407024785113 24846718160002055268588835)
  ·
    refine ⟨37270077240003082902883253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24846718160002055268588835 37270077240003082902883253)
    ·
      refine ⟨3494069741250289022145305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37270077240003082902883253 3494069741250289022145305)
      ·
        refine ⟨2620552305937716766608979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3494069741250289022145305 2620552305937716766608979)
        ·
          refine ⟨3930828458906575149913469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620552305937716766608979 3930828458906575149913469)
          ·
            refine ⟨1474060672089965681217551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3930828458906575149913469 1474060672089965681217551)
            ·
              refine ⟨2211091008134948521826327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474060672089965681217551 2211091008134948521826327)
              ·
                refine ⟨3316636512202422782739491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211091008134948521826327 3316636512202422782739491)
                ·
                  refine ⟨4974954768303634174109237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316636512202422782739491 4974954768303634174109237)
                  ·
                    refine ⟨466402009528465703822741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4974954768303634174109237 466402009528465703822741)
                    ·
                      rfl

theorem cell22_1362472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1362472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362472 prefixEnd_1362472 := by exact prefixLift 1362472
  have htrace : WordTrace (prefixWord ++ tailWord_1362472) baseStart_1362472 baseEnd_1362472 := by
    simpa [prefixWord, tailWord_1362472, baseEnd_1362472] using wordTrace_append hprefix tailTrace_1362472
  have hstable : (prefixWord ++ tailWord_1362472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362472).length < 2 ^ (prefixWord ++ tailWord_1362472).sum := by decide
  have hdescent : baseEnd_1362472 < baseStart_1362472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362502 : List Nat := [6, 1, 1, 1, 2, 3, 8]
def baseStart_1362502 : Nat := 118140960795 + 1362502 * 2 ^ 59
def prefixEnd_1362502 : Nat := 4983230072969 + 3 ^ 40 * 1362502 * 2
def baseEnd_1362502 : Nat := 17274528857094652798987

theorem tailTrace_1362502 : CollatzResearch.WordTrace tailWord_1362502 prefixEnd_1362502 17274528857094652798987 := by
  unfold tailWord_1362502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552954078434232051899055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33129687006596950440513173 1552954078434232051899055)
  ·
    refine ⟨2329431117651348077848583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1552954078434232051899055 2329431117651348077848583)
    ·
      refine ⟨3494146676477022116772875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2329431117651348077848583 3494146676477022116772875)
      ·
        refine ⟨5241220014715533175159313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494146676477022116772875 5241220014715533175159313)
        ·
          refine ⟨3930915011036649881369485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5241220014715533175159313 3930915011036649881369485)
          ·
            refine ⟨1474093129138743705513557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3930915011036649881369485 1474093129138743705513557)
            ·
              refine ⟨17274528857094652798987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1474093129138743705513557 17274528857094652798987)
              ·
                rfl

theorem cell22_1362502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 8].length) (baseStart_1362502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362502 prefixEnd_1362502 := by exact prefixLift 1362502
  have htrace : WordTrace (prefixWord ++ tailWord_1362502) baseStart_1362502 baseEnd_1362502 := by
    simpa [prefixWord, tailWord_1362502, baseEnd_1362502] using wordTrace_append hprefix tailTrace_1362502
  have hstable : (prefixWord ++ tailWord_1362502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362502).length < 2 ^ (prefixWord ++ tailWord_1362502).sum := by decide
  have hdescent : baseEnd_1362502 < baseStart_1362502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362513 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 7]
def baseStart_1362513 : Nat := 118140960795 + 1362513 * 2 ^ 59
def prefixEnd_1362513 : Nat := 4983230072969 + 3 ^ 40 * 1362513 * 2
def baseEnd_1362513 : Nat := 155472014888785087849205

theorem tailTrace_1362513 : CollatzResearch.WordTrace tailWord_1362513 prefixEnd_1362513 155472014888785087849205 := by
  unfold tailWord_1362513
  simp only [CollatzResearch.WordTrace]
  refine ⟨49694931712855574539420193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33129954475237049692946795 49694931712855574539420193)
  ·
    refine ⟨37271198784641680904565145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49694931712855574539420193 37271198784641680904565145)
    ·
      refine ⟨27953399088481260678423859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37271198784641680904565145 27953399088481260678423859)
      ·
        refine ⟨41930098632721891017635789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27953399088481260678423859 41930098632721891017635789)
        ·
          refine ⟨15723786987270709131613421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41930098632721891017635789 15723786987270709131613421)
          ·
            refine ⟨5896420120226515924355033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15723786987270709131613421 5896420120226515924355033)
            ·
              refine ⟨4422315090169886943266275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5896420120226515924355033 4422315090169886943266275)
              ·
                refine ⟨6633472635254830414899413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422315090169886943266275 6633472635254830414899413)
                ·
                  refine ⟨155472014888785087849205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6633472635254830414899413 155472014888785087849205)
                  ·
                    rfl

theorem cell22_1362513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_1362513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362513 prefixEnd_1362513 := by exact prefixLift 1362513
  have htrace : WordTrace (prefixWord ++ tailWord_1362513) baseStart_1362513 baseEnd_1362513 := by
    simpa [prefixWord, tailWord_1362513, baseEnd_1362513] using wordTrace_append hprefix tailTrace_1362513
  have hstable : (prefixWord ++ tailWord_1362513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362513).length < 2 ^ (prefixWord ++ tailWord_1362513).sum := by decide
  have hdescent : baseEnd_1362513 < baseStart_1362513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362517 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1362517 : Nat := 118140960795 + 1362517 * 2 ^ 59
def prefixEnd_1362517 : Nat := 4983230072969 + 3 ^ 40 * 1362517 * 2
def baseEnd_1362517 : Nat := 466417413948100586447603

theorem tailTrace_1362517 : CollatzResearch.WordTrace tailWord_1362517 prefixEnd_1362517 466417413948100586447603 := by
  unfold tailWord_1362517
  simp only [CollatzResearch.WordTrace]
  refine ⟨49695077604841083222565805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33130051736560722148377203 49695077604841083222565805)
  ·
    refine ⟨18635654101815406208462177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49695077604841083222565805 18635654101815406208462177)
    ·
      refine ⟨13976740576361554656346633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18635654101815406208462177 13976740576361554656346633)
      ·
        refine ⟨10482555432271165992259975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13976740576361554656346633 10482555432271165992259975)
        ·
          refine ⟨15723833148406748988389963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10482555432271165992259975 15723833148406748988389963)
          ·
            refine ⟨23585749722610123482584945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15723833148406748988389963 23585749722610123482584945)
            ·
              refine ⟨17689312291957592611938709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23585749722610123482584945 17689312291957592611938709)
              ·
                refine ⟨829186513685512153684627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17689312291957592611938709 829186513685512153684627)
                ·
                  refine ⟨1243779770528268230526941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829186513685512153684627 1243779770528268230526941)
                  ·
                    refine ⟨466417413948100586447603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243779770528268230526941 466417413948100586447603)
                    ·
                      rfl

theorem cell22_1362517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1362517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362517 prefixEnd_1362517 := by exact prefixLift 1362517
  have htrace : WordTrace (prefixWord ++ tailWord_1362517) baseStart_1362517 baseEnd_1362517 := by
    simpa [prefixWord, tailWord_1362517, baseEnd_1362517] using wordTrace_append hprefix tailTrace_1362517
  have hstable : (prefixWord ++ tailWord_1362517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362517).length < 2 ^ (prefixWord ++ tailWord_1362517).sum := by decide
  have hdescent : baseEnd_1362517 < baseStart_1362517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362528 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_1362528 : Nat := 118140960795 + 1362528 * 2 ^ 59
def prefixEnd_1362528 : Nat := 4983230072969 + 3 ^ 40 * 1362528 * 2
def baseEnd_1362528 : Nat := 466421179472900224422569

theorem tailTrace_1362528 : CollatzResearch.WordTrace tailWord_1362528 prefixEnd_1362528 466421179472900224422569 := by
  unfold tailWord_1362528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847739403900616050608119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33130319205200821400810825 24847739403900616050608119)
  ·
    refine ⟨37271609105850924075912179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24847739403900616050608119 37271609105850924075912179)
    ·
      refine ⟨55907413658776386113868269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37271609105850924075912179 55907413658776386113868269)
      ·
        refine ⟨20965280122041144792700601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55907413658776386113868269 20965280122041144792700601)
        ·
          refine ⟨15723960091530858594525451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20965280122041144792700601 15723960091530858594525451)
          ·
            refine ⟨23585940137296287891788177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15723960091530858594525451 23585940137296287891788177)
            ·
              refine ⟨17689455102972215918841133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23585940137296287891788177 17689455102972215918841133)
              ·
                refine ⟨6633545663614580969565425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17689455102972215918841133 6633545663614580969565425)
                ·
                  refine ⟨4975159247710935727174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6633545663614580969565425 4975159247710935727174069)
                  ·
                    refine ⟨466421179472900224422569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4975159247710935727174069 466421179472900224422569)
                    ·
                      rfl

theorem cell22_1362528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_1362528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362528 prefixEnd_1362528 := by exact prefixLift 1362528
  have htrace : WordTrace (prefixWord ++ tailWord_1362528) baseStart_1362528 baseEnd_1362528 := by
    simpa [prefixWord, tailWord_1362528, baseEnd_1362528] using wordTrace_append hprefix tailTrace_1362528
  have hstable : (prefixWord ++ tailWord_1362528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362528).length < 2 ^ (prefixWord ++ tailWord_1362528).sum := by decide
  have hdescent : baseEnd_1362528 < baseStart_1362528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 4]
def baseStart_1362575 : Nat := 118140960795 + 1362575 * 2 ^ 59
def prefixEnd_1362575 : Nat := 4983230072969 + 3 ^ 40 * 1362575 * 2
def baseEnd_1362575 : Nat := 155479089511135922832475

theorem tailTrace_1362575 : CollatzResearch.WordTrace tailWord_1362575 prefixEnd_1362575 155479089511135922832475 := by
  unfold tailWord_1362575
  simp only [CollatzResearch.WordTrace]
  refine ⟨49697193038630959128177179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33131462025753972752118119 49697193038630959128177179)
  ·
    refine ⟨74545789557946438692265769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49697193038630959128177179 74545789557946438692265769)
    ·
      refine ⟨55909342168459829019199327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74545789557946438692265769 55909342168459829019199327)
      ·
        refine ⟨83864013252689743528798991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55909342168459829019199327 83864013252689743528798991)
        ·
          refine ⟨125796019879034615293198487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83864013252689743528798991 125796019879034615293198487)
          ·
            refine ⟨188694029818551922939797731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125796019879034615293198487 188694029818551922939797731)
            ·
              refine ⟨283041044727827884409696597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188694029818551922939797731 283041044727827884409696597)
              ·
                refine ⟨829221810726058255106533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 283041044727827884409696597 829221810726058255106533)
                ·
                  refine ⟨155479089511135922832475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829221810726058255106533 155479089511135922832475)
                  ·
                    rfl

theorem cell22_1362575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 4].length) (baseStart_1362575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362575 prefixEnd_1362575 := by exact prefixLift 1362575
  have htrace : WordTrace (prefixWord ++ tailWord_1362575) baseStart_1362575 baseEnd_1362575 := by
    simpa [prefixWord, tailWord_1362575, baseEnd_1362575] using wordTrace_append hprefix tailTrace_1362575
  have hstable : (prefixWord ++ tailWord_1362575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362575).length < 2 ^ (prefixWord ++ tailWord_1362575).sum := by decide
  have hdescent : baseEnd_1362575 < baseStart_1362575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362624 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_1362624 : Nat := 118140960795 + 1362624 * 2 ^ 59
def prefixEnd_1362624 : Nat := 4983230072969 + 3 ^ 40 * 1362624 * 2
def baseEnd_1362624 : Nat := 466454042234787974022275

theorem tailTrace_1362624 : CollatzResearch.WordTrace tailWord_1362624 prefixEnd_1362624 466454042234787974022275 := by
  unfold tailWord_1362624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24849490107726720248355463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33132653476968960331140617 24849490107726720248355463)
  ·
    refine ⟨37274235161590080372533195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24849490107726720248355463 37274235161590080372533195)
    ·
      refine ⟨55911352742385120558799793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37274235161590080372533195 55911352742385120558799793)
      ·
        refine ⟨41933514556788840419099845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55911352742385120558799793 41933514556788840419099845)
        ·
          refine ⟨7862533979397907578581221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41933514556788840419099845 7862533979397907578581221)
          ·
            refine ⟨1474225121137107670983979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7862533979397907578581221 1474225121137107670983979)
            ·
              refine ⟨2211337681705661506475969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474225121137107670983979 2211337681705661506475969)
              ·
                refine ⟨1658503261279246129856977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2211337681705661506475969 1658503261279246129856977)
                ·
                  refine ⟨1243877445959434597392733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1658503261279246129856977 1243877445959434597392733)
                  ·
                    refine ⟨466454042234787974022275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243877445959434597392733 466454042234787974022275)
                    ·
                      rfl

theorem cell22_1362624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_1362624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362624 prefixEnd_1362624 := by exact prefixLift 1362624
  have htrace : WordTrace (prefixWord ++ tailWord_1362624) baseStart_1362624 baseEnd_1362624 := by
    simpa [prefixWord, tailWord_1362624, baseEnd_1362624] using wordTrace_append hprefix tailTrace_1362624
  have hstable : (prefixWord ++ tailWord_1362624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362624).length < 2 ^ (prefixWord ++ tailWord_1362624).sum := by decide
  have hdescent : baseEnd_1362624 < baseStart_1362624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362686 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1362686 : Nat := 118140960795 + 1362686 * 2 ^ 59
def prefixEnd_1362686 : Nat := 4983230072969 + 3 ^ 40 * 1362686 * 2
def baseEnd_1362686 : Nat := 466475266101840478972085

theorem tailTrace_1362686 : CollatzResearch.WordTrace tailWord_1362686 prefixEnd_1362686 466475266101840478972085 := by
  unfold tailWord_1362686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212655192653603135683489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33134161027485883390311941 6212655192653603135683489)
  ·
    refine ⟨4659491394490202351762617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6212655192653603135683489 4659491394490202351762617)
    ·
      refine ⟨3494618545867651763821963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4659491394490202351762617 3494618545867651763821963)
      ·
        refine ⟨5241927818801477645732945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494618545867651763821963 5241927818801477645732945)
        ·
          refine ⟨3931445864101108234299709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5241927818801477645732945 3931445864101108234299709)
          ·
            refine ⟨1474292199037915587862391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3931445864101108234299709 1474292199037915587862391)
            ·
              refine ⟨2211438298556873381793587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474292199037915587862391 2211438298556873381793587)
              ·
                refine ⟨3317157447835310072690381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211438298556873381793587 3317157447835310072690381)
                ·
                  refine ⟨1243934042938241277258893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3317157447835310072690381 1243934042938241277258893)
                  ·
                    refine ⟨466475266101840478972085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1243934042938241277258893 466475266101840478972085)
                    ·
                      rfl

theorem cell22_1362686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1362686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362686 prefixEnd_1362686 := by exact prefixLift 1362686
  have htrace : WordTrace (prefixWord ++ tailWord_1362686) baseStart_1362686 baseEnd_1362686 := by
    simpa [prefixWord, tailWord_1362686, baseEnd_1362686] using wordTrace_append hprefix tailTrace_1362686
  have hstable : (prefixWord ++ tailWord_1362686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362686).length < 2 ^ (prefixWord ++ tailWord_1362686).sum := by decide
  have hdescent : baseEnd_1362686 < baseStart_1362686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362785 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1362785 : Nat := 118140960795 + 1362785 * 2 ^ 59
def prefixEnd_1362785 : Nat := 4983230072969 + 3 ^ 40 * 1362785 * 2
def baseEnd_1362785 : Nat := 466509155825037220746781

theorem tailTrace_1362785 : CollatzResearch.WordTrace tailWord_1362785 prefixEnd_1362785 466509155825037220746781 := by
  unfold tailWord_1362785
  simp only [CollatzResearch.WordTrace]
  refine ⟨49704852367870164993321809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33136568245246776662214539 49704852367870164993321809)
  ·
    refine ⟨37278639275902623744991357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49704852367870164993321809 37278639275902623744991357)
    ·
      refine ⟨13979489728463483904371759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37278639275902623744991357 13979489728463483904371759)
      ·
        refine ⟨20969234592695225856557639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13979489728463483904371759 20969234592695225856557639)
        ·
          refine ⟨31453851889042838784836459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20969234592695225856557639 31453851889042838784836459)
          ·
            refine ⟨47180777833564258177254689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31453851889042838784836459 47180777833564258177254689)
            ·
              refine ⟨35385583375173193632941017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47180777833564258177254689 35385583375173193632941017)
              ·
                refine ⟨26539187531379895224705763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35385583375173193632941017 26539187531379895224705763)
                ·
                  refine ⟨39808781297069842837058645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26539187531379895224705763 39808781297069842837058645)
                  ·
                    refine ⟨466509155825037220746781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39808781297069842837058645 466509155825037220746781)
                    ·
                      rfl

theorem cell22_1362785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1362785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362785 prefixEnd_1362785 := by exact prefixLift 1362785
  have htrace : WordTrace (prefixWord ++ tailWord_1362785) baseStart_1362785 baseEnd_1362785 := by
    simpa [prefixWord, tailWord_1362785, baseEnd_1362785] using wordTrace_append hprefix tailTrace_1362785
  have hstable : (prefixWord ++ tailWord_1362785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362785).length < 2 ^ (prefixWord ++ tailWord_1362785).sum := by decide
  have hdescent : baseEnd_1362785 < baseStart_1362785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362855 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1362855 : Nat := 118140960795 + 1362855 * 2 ^ 59
def prefixEnd_1362855 : Nat := 4983230072969 + 3 ^ 40 * 1362855 * 2
def baseEnd_1362855 : Nat := 466533118255580371496567

theorem tailTrace_1362855 : CollatzResearch.WordTrace tailWord_1362855 prefixEnd_1362855 466533118255580371496567 := by
  unfold tailWord_1362855
  simp only [CollatzResearch.WordTrace]
  refine ⟨49707405477616566948370019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33138270318411044632246679 49707405477616566948370019)
  ·
    refine ⟨74561108216424850422555029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49707405477616566948370019 74561108216424850422555029)
    ·
      refine ⟨3495051947644914863557267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74561108216424850422555029 3495051947644914863557267)
      ·
        refine ⟨5242577921467372295335901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3495051947644914863557267 5242577921467372295335901)
        ·
          refine ⟨1965966720550264610750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5242577921467372295335901 1965966720550264610750963)
          ·
            refine ⟨2948950080825396916126445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965966720550264610750963 2948950080825396916126445)
            ·
              refine ⟨1105856280309523843547417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2948950080825396916126445 1105856280309523843547417)
              ·
                refine ⟨829392210232142882660563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105856280309523843547417 829392210232142882660563)
                ·
                  refine ⟨1244088315348214323990845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829392210232142882660563 1244088315348214323990845)
                  ·
                    refine ⟨466533118255580371496567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244088315348214323990845 466533118255580371496567)
                    ·
                      rfl

theorem cell22_1362855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1362855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362855 prefixEnd_1362855 := by exact prefixLift 1362855
  have htrace : WordTrace (prefixWord ++ tailWord_1362855) baseStart_1362855 baseEnd_1362855 := by
    simpa [prefixWord, tailWord_1362855, baseEnd_1362855] using wordTrace_append hprefix tailTrace_1362855
  have hstable : (prefixWord ++ tailWord_1362855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362855).length < 2 ^ (prefixWord ++ tailWord_1362855).sum := by decide
  have hdescent : baseEnd_1362855 < baseStart_1362855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362868 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1362868 : Nat := 118140960795 + 1362868 * 2 ^ 59
def prefixEnd_1362868 : Nat := 4983230072969 + 3 ^ 40 * 1362868 * 2
def baseEnd_1362868 : Nat := 155512522807084223640509

theorem tailTrace_1362868 : CollatzResearch.WordTrace tailWord_1362868 prefixEnd_1362868 155512522807084223640509 := by
  unfold tailWord_1362868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24853939813284735084296629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33138586417712980112395505 24853939813284735084296629)
  ·
    refine ⟨2330056857495443914152809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24853939813284735084296629 2330056857495443914152809)
    ·
      refine ⟨1747542643121582935614607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2330056857495443914152809 1747542643121582935614607)
      ·
        refine ⟨2621313964682374403421911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747542643121582935614607 2621313964682374403421911)
        ·
          refine ⟨3931970947023561605132867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621313964682374403421911 3931970947023561605132867)
          ·
            refine ⟨5897956420535342407699301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3931970947023561605132867 5897956420535342407699301)
            ·
              refine ⟨1105866828850376701443619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5897956420535342407699301 1105866828850376701443619)
              ·
                refine ⟨1658800243275565052165429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105866828850376701443619 1658800243275565052165429)
                ·
                  refine ⟨155512522807084223640509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1658800243275565052165429 155512522807084223640509)
                  ·
                    rfl

theorem cell22_1362868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1362868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362868 prefixEnd_1362868 := by exact prefixLift 1362868
  have htrace : WordTrace (prefixWord ++ tailWord_1362868) baseStart_1362868 baseEnd_1362868 := by
    simpa [prefixWord, tailWord_1362868, baseEnd_1362868] using wordTrace_append hprefix tailTrace_1362868
  have hstable : (prefixWord ++ tailWord_1362868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362868).length < 2 ^ (prefixWord ++ tailWord_1362868).sum := by decide
  have hdescent : baseEnd_1362868 < baseStart_1362868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362894 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1362894 : Nat := 118140960795 + 1362894 * 2 ^ 59
def prefixEnd_1362894 : Nat := 4983230072969 + 3 ^ 40 * 1362894 * 2
def baseEnd_1362894 : Nat := 466546468752597269771447

theorem tailTrace_1362894 : CollatzResearch.WordTrace tailWord_1362894 prefixEnd_1362894 466546468752597269771447 := by
  unfold tailWord_1362894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213603490559409576129967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33139218616316851072693157 6213603490559409576129967)
  ·
    refine ⟨9320405235839114364194951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213603490559409576129967 9320405235839114364194951)
    ·
      refine ⟨13980607853758671546292427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9320405235839114364194951 13980607853758671546292427)
      ·
        refine ⟨20970911780638007319438641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13980607853758671546292427 20970911780638007319438641)
        ·
          refine ⟨15728183835478505489578981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20970911780638007319438641 15728183835478505489578981)
          ·
            refine ⟨2949034469152219779296059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15728183835478505489578981 2949034469152219779296059)
            ·
              refine ⟨4423551703728329668944089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949034469152219779296059 4423551703728329668944089)
              ·
                refine ⟨3317663777796247251708067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4423551703728329668944089 3317663777796247251708067)
                ·
                  refine ⟨4976495666694370877562101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317663777796247251708067 4976495666694370877562101)
                  ·
                    refine ⟨466546468752597269771447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4976495666694370877562101 466546468752597269771447)
                    ·
                      rfl

theorem cell22_1362894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1362894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362894 prefixEnd_1362894 := by exact prefixLift 1362894
  have htrace : WordTrace (prefixWord ++ tailWord_1362894) baseStart_1362894 baseEnd_1362894 := by
    simpa [prefixWord, tailWord_1362894, baseEnd_1362894] using wordTrace_append hprefix tailTrace_1362894
  have hstable : (prefixWord ++ tailWord_1362894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362894).length < 2 ^ (prefixWord ++ tailWord_1362894).sum := by decide
  have hdescent : baseEnd_1362894 < baseStart_1362894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362898 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1362898 : Nat := 118140960795 + 1362898 * 2 ^ 59
def prefixEnd_1362898 : Nat := 4983230072969 + 3 ^ 40 * 1362898 * 2
def baseEnd_1362898 : Nat := 466547838034342592671435

theorem tailTrace_1362898 : CollatzResearch.WordTrace tailWord_1362898 prefixEnd_1362898 466547838034342592671435 := by
  unfold tailWord_1362898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427243454115196323046337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33139315877640523528123565 12427243454115196323046337)
  ·
    refine ⟨9320432590586397242284753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12427243454115196323046337 9320432590586397242284753)
    ·
      refine ⟨6990324442939797931713565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9320432590586397242284753 6990324442939797931713565)
      ·
        refine ⟨2621371666102424224392587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6990324442939797931713565 2621371666102424224392587)
        ·
          refine ⟨3932057499153636336588881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621371666102424224392587 3932057499153636336588881)
          ·
            refine ⟨2949043124365227252441661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932057499153636336588881 2949043124365227252441661)
            ·
              refine ⟨1105891171636960219665623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2949043124365227252441661 1105891171636960219665623)
              ·
                refine ⟨1658836757455440329498435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105891171636960219665623 1658836757455440329498435)
                ·
                  refine ⟨2488255136183160494247653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658836757455440329498435 2488255136183160494247653)
                  ·
                    refine ⟨466547838034342592671435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488255136183160494247653 466547838034342592671435)
                    ·
                      rfl

theorem cell22_1362898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1362898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362898 prefixEnd_1362898 := by exact prefixLift 1362898
  have htrace : WordTrace (prefixWord ++ tailWord_1362898) baseStart_1362898 baseEnd_1362898 := by
    simpa [prefixWord, tailWord_1362898, baseEnd_1362898] using wordTrace_append hprefix tailTrace_1362898
  have hstable : (prefixWord ++ tailWord_1362898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362898).length < 2 ^ (prefixWord ++ tailWord_1362898).sum := by decide
  have hdescent : baseEnd_1362898 < baseStart_1362898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362937 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_1362937 : Nat := 118140960795 + 1362937 * 2 ^ 59
def prefixEnd_1362937 : Nat := 4983230072969 + 3 ^ 40 * 1362937 * 2
def baseEnd_1362937 : Nat := 466561188531359490946315

theorem tailTrace_1362937 : CollatzResearch.WordTrace tailWord_1362937 prefixEnd_1362937 466561188531359490946315 := by
  unfold tailWord_1362937
  simp only [CollatzResearch.WordTrace]
  refine ⟨49710396263319494952855065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33140264175546329968570043 49710396263319494952855065)
  ·
    refine ⟨37282797197489621214641299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49710396263319494952855065 37282797197489621214641299)
    ·
      refine ⟨55924195796234431821961949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37282797197489621214641299 55924195796234431821961949)
      ·
        refine ⟨20971573423587911933235731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55924195796234431821961949 20971573423587911933235731)
        ·
          refine ⟨31457360135381867899853597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20971573423587911933235731 31457360135381867899853597)
          ·
            refine ⟨11796510050768200462445099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31457360135381867899853597 11796510050768200462445099)
            ·
              refine ⟨17694765076152300693667649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11796510050768200462445099 17694765076152300693667649)
              ·
                refine ⟨13271073807114225520250737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17694765076152300693667649 13271073807114225520250737)
                ·
                  refine ⟨9953305355335669140188053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13271073807114225520250737 9953305355335669140188053)
                  ·
                    refine ⟨466561188531359490946315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9953305355335669140188053 466561188531359490946315)
                    ·
                      rfl

theorem cell22_1362937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_1362937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362937 prefixEnd_1362937 := by exact prefixLift 1362937
  have htrace : WordTrace (prefixWord ++ tailWord_1362937) baseStart_1362937 baseEnd_1362937 := by
    simpa [prefixWord, tailWord_1362937, baseEnd_1362937] using wordTrace_append hprefix tailTrace_1362937
  have hstable : (prefixWord ++ tailWord_1362937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362937).length < 2 ^ (prefixWord ++ tailWord_1362937).sum := by decide
  have hdescent : baseEnd_1362937 < baseStart_1362937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362969 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 5]
def baseStart_1362969 : Nat := 118140960795 + 1362969 * 2 ^ 59
def prefixEnd_1362969 : Nat := 4983230072969 + 3 ^ 40 * 1362969 * 2
def baseEnd_1362969 : Nat := 155524047595107358048739

theorem tailTrace_1362969 : CollatzResearch.WordTrace tailWord_1362969 prefixEnd_1362969 155524047595107358048739 := by
  unfold tailWord_1362969
  simp only [CollatzResearch.WordTrace]
  refine ⟨49711563399203564418019961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33141042266135709612013307 49711563399203564418019961)
  ·
    refine ⟨37283672549402673313514971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49711563399203564418019961 37283672549402673313514971)
    ·
      refine ⟨55925508824104009970272457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37283672549402673313514971 55925508824104009970272457)
      ·
        refine ⟨41944131618078007477704343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55925508824104009970272457 41944131618078007477704343)
        ·
          refine ⟨62916197427117011216556515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41944131618078007477704343 62916197427117011216556515)
          ·
            refine ⟨94374296140675516824834773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62916197427117011216556515 94374296140675516824834773)
            ·
              refine ⟨2211897565797082425582065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94374296140675516824834773 2211897565797082425582065)
              ·
                refine ⟨1658923174347811819186549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2211897565797082425582065 1658923174347811819186549)
                ·
                  refine ⟨155524047595107358048739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1658923174347811819186549 155524047595107358048739)
                  ·
                    rfl

theorem cell22_1362969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_1362969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362969 prefixEnd_1362969 := by exact prefixLift 1362969
  have htrace : WordTrace (prefixWord ++ tailWord_1362969) baseStart_1362969 baseEnd_1362969 := by
    simpa [prefixWord, tailWord_1362969, baseEnd_1362969] using wordTrace_append hprefix tailTrace_1362969
  have hstable : (prefixWord ++ tailWord_1362969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362969).length < 2 ^ (prefixWord ++ tailWord_1362969).sum := by decide
  have hdescent : baseEnd_1362969 < baseStart_1362969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1362973 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1362973 : Nat := 118140960795 + 1362973 * 2 ^ 59
def prefixEnd_1362973 : Nat := 4983230072969 + 3 ^ 40 * 1362973 * 2
def baseEnd_1362973 : Nat := 466573512067067397046205

theorem tailTrace_1362973 : CollatzResearch.WordTrace tailWord_1362973 prefixEnd_1362973 466573512067067397046205 := by
  unfold tailWord_1362973
  simp only [CollatzResearch.WordTrace]
  refine ⟨49711709291189073101165573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33141139527459382067443715 49711709291189073101165573)
  ·
    refine ⟨9320945492097951206468545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49711709291189073101165573 9320945492097951206468545)
    ·
      refine ⟨6990709119073463404851409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9320945492097951206468545 6990709119073463404851409)
      ·
        refine ⟨5243031839305097553638557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6990709119073463404851409 5243031839305097553638557)
        ·
          refine ⟨1966136939739411582614459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5243031839305097553638557 1966136939739411582614459)
          ·
            refine ⟨2949205409609117373921689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966136939739411582614459 2949205409609117373921689)
            ·
              refine ⟨2211904057206838030441267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949205409609117373921689 2211904057206838030441267)
              ·
                refine ⟨3317856085810257045661901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211904057206838030441267 3317856085810257045661901)
                ·
                  refine ⟨1244196032178846392123213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3317856085810257045661901 1244196032178846392123213)
                  ·
                    refine ⟨466573512067067397046205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244196032178846392123213 466573512067067397046205)
                    ·
                      rfl

theorem cell22_1362973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1362973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1362973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1362973 prefixEnd_1362973 := by exact prefixLift 1362973
  have htrace : WordTrace (prefixWord ++ tailWord_1362973) baseStart_1362973 baseEnd_1362973 := by
    simpa [prefixWord, tailWord_1362973, baseEnd_1362973] using wordTrace_append hprefix tailTrace_1362973
  have hstable : (prefixWord ++ tailWord_1362973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1362973).length < 2 ^ (prefixWord ++ tailWord_1362973).sum := by decide
  have hdescent : baseEnd_1362973 < baseStart_1362973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1362973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363037 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 5]
def baseStart_1363037 : Nat := 118140960795 + 1363037 * 2 ^ 59
def prefixEnd_1363037 : Nat := 4983230072969 + 3 ^ 40 * 1363037 * 2
def baseEnd_1363037 : Nat := 155531806858330854482003

theorem tailTrace_1363037 : CollatzResearch.WordTrace tailWord_1363037 prefixEnd_1363037 155531806858330854482003 := by
  unfold tailWord_1363037
  simp only [CollatzResearch.WordTrace]
  refine ⟨49714043562957212031495365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33142695708638141354330243 49714043562957212031495365)
  ·
    refine ⟨9321383168054477255905381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49714043562957212031495365 9321383168054477255905381)
    ·
      refine ⟨1747759344010214485482259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9321383168054477255905381 1747759344010214485482259)
      ·
        refine ⟨2621639016015321728223389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747759344010214485482259 2621639016015321728223389)
        ·
          refine ⟨983114631005745648083771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2621639016015321728223389 983114631005745648083771)
          ·
            refine ⟨1474671946508618472125657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983114631005745648083771 1474671946508618472125657)
            ·
              refine ⟨1106003959881463854094243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474671946508618472125657 1106003959881463854094243)
              ·
                refine ⟨1659005939822195781141365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106003959881463854094243 1659005939822195781141365)
                ·
                  refine ⟨155531806858330854482003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1659005939822195781141365 155531806858330854482003)
                  ·
                    rfl

theorem cell22_1363037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_1363037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363037 prefixEnd_1363037 := by exact prefixLift 1363037
  have htrace : WordTrace (prefixWord ++ tailWord_1363037) baseStart_1363037 baseEnd_1363037 := by
    simpa [prefixWord, tailWord_1363037, baseEnd_1363037] using wordTrace_append hprefix tailTrace_1363037
  have hstable : (prefixWord ++ tailWord_1363037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363037).length < 2 ^ (prefixWord ++ tailWord_1363037).sum := by decide
  have hdescent : baseEnd_1363037 < baseStart_1363037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363044 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1363044 : Nat := 118140960795 + 1363044 * 2 ^ 59
def prefixEnd_1363044 : Nat := 4983230072969 + 3 ^ 40 * 1363044 * 2
def baseEnd_1363044 : Nat := 466597816818046878520987

theorem tailTrace_1363044 : CollatzResearch.WordTrace tailWord_1363044 prefixEnd_1363044 466597816818046878520987 := by
  unfold tailWord_1363044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857149436965926113500093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33142865915954568151333457 24857149436965926113500093)
  ·
    refine ⟨9321431038862222292562535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24857149436965926113500093 9321431038862222292562535)
    ·
      refine ⟨13982146558293333438843803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321431038862222292562535 13982146558293333438843803)
      ·
        refine ⟨20973219837440000158265705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982146558293333438843803 20973219837440000158265705)
        ·
          refine ⟨15729914878080000118699279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20973219837440000158265705 15729914878080000118699279)
          ·
            refine ⟨23594872317120000178048919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729914878080000118699279 23594872317120000178048919)
            ·
              refine ⟨35392308475680000267073379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23594872317120000178048919 35392308475680000267073379)
              ·
                refine ⟨53088462713520000400610069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35392308475680000267073379 53088462713520000400610069)
                ·
                  refine ⟨2488521689696250018778597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53088462713520000400610069 2488521689696250018778597)
                  ·
                    refine ⟨466597816818046878520987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488521689696250018778597 466597816818046878520987)
                    ·
                      rfl

theorem cell22_1363044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1363044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363044 prefixEnd_1363044 := by exact prefixLift 1363044
  have htrace : WordTrace (prefixWord ++ tailWord_1363044) baseStart_1363044 baseEnd_1363044 := by
    simpa [prefixWord, tailWord_1363044, baseEnd_1363044] using wordTrace_append hprefix tailTrace_1363044
  have hstable : (prefixWord ++ tailWord_1363044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363044).length < 2 ^ (prefixWord ++ tailWord_1363044).sum := by decide
  have hdescent : baseEnd_1363044 < baseStart_1363044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363080 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1363080 : Nat := 118140960795 + 1363080 * 2 ^ 59
def prefixEnd_1363080 : Nat := 4983230072969 + 3 ^ 40 * 1363080 * 2
def baseEnd_1363080 : Nat := 466610140353754784620877

theorem tailTrace_1363080 : CollatzResearch.WordTrace tailWord_1363080 prefixEnd_1363080 466610140353754784620877 := by
  unfold tailWord_1363080
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857805950900715187655347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33143741267867620250207129 24857805950900715187655347)
  ·
    refine ⟨37286708926351072781483021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24857805950900715187655347 37286708926351072781483021)
    ·
      refine ⟨13982515847381652293056133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37286708926351072781483021 13982515847381652293056133)
      ·
        refine ⟨2621721721384059804948025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13982515847381652293056133 2621721721384059804948025)
        ·
          refine ⟨1966291291038044853711019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2621721721384059804948025 1966291291038044853711019)
          ·
            refine ⟨2949436936557067280566529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966291291038044853711019 2949436936557067280566529)
            ·
              refine ⟨2212077702417800460424897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949436936557067280566529 2212077702417800460424897)
              ·
                refine ⟨1659058276813350345318673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212077702417800460424897 1659058276813350345318673)
                ·
                  refine ⟨1244293707610012758989005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1659058276813350345318673 1244293707610012758989005)
                  ·
                    refine ⟨466610140353754784620877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244293707610012758989005 466610140353754784620877)
                    ·
                      rfl

theorem cell22_1363080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1363080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363080 prefixEnd_1363080 := by exact prefixLift 1363080
  have htrace : WordTrace (prefixWord ++ tailWord_1363080) baseStart_1363080 baseEnd_1363080 := by
    simpa [prefixWord, tailWord_1363080, baseEnd_1363080] using wordTrace_append hprefix tailTrace_1363080
  have hstable : (prefixWord ++ tailWord_1363080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363080).length < 2 ^ (prefixWord ++ tailWord_1363080).sum := by decide
  have hdescent : baseEnd_1363080 < baseStart_1363080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363108 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_1363108 : Nat := 118140960795 + 1363108 * 2 ^ 59
def prefixEnd_1363108 : Nat := 4983230072969 + 3 ^ 40 * 1363108 * 2
def baseEnd_1363108 : Nat := 466619725325972044920791

theorem tailTrace_1363108 : CollatzResearch.WordTrace tailWord_1363108 prefixEnd_1363108 466619725325972044920791 := by
  unfold tailWord_1363108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24858316572849995578664989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33144422097133327438219985 24858316572849995578664989)
  ·
    refine ⟨9321868714818748341999371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24858316572849995578664989 9321868714818748341999371)
    ·
      refine ⟨13982803072228122512999057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321868714818748341999371 13982803072228122512999057)
      ·
        refine ⟨10487102304171091884749293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13982803072228122512999057 10487102304171091884749293)
        ·
          refine ⟨3932663364064159456780985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10487102304171091884749293 3932663364064159456780985)
          ·
            refine ⟨2949497523048119592585739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932663364064159456780985 2949497523048119592585739)
            ·
              refine ⟨4424246284572179388878609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949497523048119592585739 4424246284572179388878609)
              ·
                refine ⟨3318184713429134541658957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424246284572179388878609 3318184713429134541658957)
                ·
                  refine ⟨1244319267535925453122109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3318184713429134541658957 1244319267535925453122109)
                  ·
                    refine ⟨466619725325972044920791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244319267535925453122109 466619725325972044920791)
                    ·
                      rfl

theorem cell22_1363108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_1363108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363108 prefixEnd_1363108 := by exact prefixLift 1363108
  have htrace : WordTrace (prefixWord ++ tailWord_1363108) baseStart_1363108 baseEnd_1363108 := by
    simpa [prefixWord, tailWord_1363108, baseEnd_1363108] using wordTrace_append hprefix tailTrace_1363108
  have hstable : (prefixWord ++ tailWord_1363108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363108).length < 2 ^ (prefixWord ++ tailWord_1363108).sum := by decide
  have hdescent : baseEnd_1363108 < baseStart_1363108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363168 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_1363168 : Nat := 118140960795 + 1363168 * 2 ^ 59
def prefixEnd_1363168 : Nat := 4983230072969 + 3 ^ 40 * 1363168 * 2
def baseEnd_1363168 : Nat := 466640264552151888420607

theorem tailTrace_1363168 : CollatzResearch.WordTrace tailWord_1363168 prefixEnd_1363168 466640264552151888420607 := by
  unfold tailWord_1363168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859410762741310702257079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33145881016988414269676105 24859410762741310702257079)
  ·
    refine ⟨37289116144111966053385619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24859410762741310702257079 37289116144111966053385619)
    ·
      refine ⟨55933674216167949080078429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37289116144111966053385619 55933674216167949080078429)
      ·
        refine ⟨20975127831062980905029411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55933674216167949080078429 20975127831062980905029411)
        ·
          refine ⟨31462691746594471357544117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20975127831062980905029411 31462691746594471357544117)
          ·
            refine ⟨2949627351243231689769761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31462691746594471357544117 2949627351243231689769761)
            ·
              refine ⟨2212220513432423767327321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949627351243231689769761 2212220513432423767327321)
              ·
                refine ⟨1659165385074317825495491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212220513432423767327321 1659165385074317825495491)
                ·
                  refine ⟨2488748077611476738243237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659165385074317825495491 2488748077611476738243237)
                  ·
                    refine ⟨466640264552151888420607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488748077611476738243237 466640264552151888420607)
                    ·
                      rfl

theorem cell22_1363168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_1363168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363168 prefixEnd_1363168 := by exact prefixLift 1363168
  have htrace : WordTrace (prefixWord ++ tailWord_1363168) baseStart_1363168 baseEnd_1363168 := by
    simpa [prefixWord, tailWord_1363168, baseEnd_1363168] using wordTrace_append hprefix tailTrace_1363168
  have hstable : (prefixWord ++ tailWord_1363168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363168).length < 2 ^ (prefixWord ++ tailWord_1363168).sum := by decide
  have hdescent : baseEnd_1363168 < baseStart_1363168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363211 : List Nat := [1, 1, 1, 1, 5, 4, 2, 7]
def baseStart_1363211 : Nat := 118140960795 + 1363211 * 2 ^ 59
def prefixEnd_1363211 : Nat := 4983230072969 + 3 ^ 40 * 1363211 * 2
def baseEnd_1363211 : Nat := 51850553814546012177275

theorem tailTrace_1363211 : CollatzResearch.WordTrace tailWord_1363211 prefixEnd_1363211 51850553814546012177275 := by
  unfold tailWord_1363211
  simp only [CollatzResearch.WordTrace]
  refine ⟨49720389864326839748329487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33146926576217893165552991 49720389864326839748329487)
  ·
    refine ⟨74580584796490259622494231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49720389864326839748329487 74580584796490259622494231)
    ·
      refine ⟨111870877194735389433741347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74580584796490259622494231 111870877194735389433741347)
      ·
        refine ⟨167806315792103084150612021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111870877194735389433741347 167806315792103084150612021)
        ·
          refine ⟨15731842105509664139119877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167806315792103084150612021 15731842105509664139119877)
          ·
            refine ⟨2949720394783062026084977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15731842105509664139119877 2949720394783062026084977)
            ·
              refine ⟨2212290296087296519563733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949720394783062026084977 2212290296087296519563733)
              ·
                refine ⟨51850553814546012177275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2212290296087296519563733 51850553814546012177275)
                ·
                  rfl

theorem cell22_1363211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 7].length) (baseStart_1363211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363211 prefixEnd_1363211 := by exact prefixLift 1363211
  have htrace : WordTrace (prefixWord ++ tailWord_1363211) baseStart_1363211 baseEnd_1363211 := by
    simpa [prefixWord, tailWord_1363211, baseEnd_1363211] using wordTrace_append hprefix tailTrace_1363211
  have hstable : (prefixWord ++ tailWord_1363211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363211).length < 2 ^ (prefixWord ++ tailWord_1363211).sum := by decide
  have hdescent : baseEnd_1363211 < baseStart_1363211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363271 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1363271 : Nat := 118140960795 + 1363271 * 2 ^ 59
def prefixEnd_1363271 : Nat := 4983230072969 + 3 ^ 40 * 1363271 * 2
def baseEnd_1363271 : Nat := 466675523557093953095291

theorem tailTrace_1363271 : CollatzResearch.WordTrace tailWord_1363271 prefixEnd_1363271 466675523557093953095291 := by
  unfold tailWord_1363271
  simp only [CollatzResearch.WordTrace]
  refine ⟨49722578244109469995513667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33148385496072979997009111 49722578244109469995513667)
  ·
    refine ⟨74583867366164204993270501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49722578244109469995513667 74583867366164204993270501)
    ·
      refine ⟨13984475131155788436238219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74583867366164204993270501 13984475131155788436238219)
      ·
        refine ⟨20976712696733682654357329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13984475131155788436238219 20976712696733682654357329)
        ·
          refine ⟨15732534522550261990767997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20976712696733682654357329 15732534522550261990767997)
          ·
            refine ⟨5899700445956348246537999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15732534522550261990767997 5899700445956348246537999)
            ·
              refine ⟨8849550668934522369806999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899700445956348246537999 8849550668934522369806999)
              ·
                refine ⟨13274326003401783554710499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8849550668934522369806999 13274326003401783554710499)
                ·
                  refine ⟨19911489005102675332065749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13274326003401783554710499 19911489005102675332065749)
                  ·
                    refine ⟨466675523557093953095291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19911489005102675332065749 466675523557093953095291)
                    ·
                      rfl

theorem cell22_1363271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1363271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363271 prefixEnd_1363271 := by exact prefixLift 1363271
  have htrace : WordTrace (prefixWord ++ tailWord_1363271) baseStart_1363271 baseEnd_1363271 := by
    simpa [prefixWord, tailWord_1363271, baseEnd_1363271] using wordTrace_append hprefix tailTrace_1363271
  have hstable : (prefixWord ++ tailWord_1363271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363271).length < 2 ^ (prefixWord ++ tailWord_1363271).sum := by decide
  have hdescent : baseEnd_1363271 < baseStart_1363271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363301 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 8]
def baseStart_1363301 : Nat := 118140960795 + 1363301 * 2 ^ 59
def prefixEnd_1363301 : Nat := 4983230072969 + 3 ^ 40 * 1363301 * 2
def baseEnd_1363301 : Nat := 155561931056727958281733

theorem tailTrace_1363301 : CollatzResearch.WordTrace tailWord_1363301 prefixEnd_1363301 155561931056727958281733 := by
  unfold tailWord_1363301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49723672434000785119105757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33149114956000523412737171 49723672434000785119105757)
  ·
    refine ⟨18646377162750294419664659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49723672434000785119105757 18646377162750294419664659)
    ·
      refine ⟨27969565744125441629496989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18646377162750294419664659 27969565744125441629496989)
      ·
        refine ⟨10488587154047040611061371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27969565744125441629496989 10488587154047040611061371)
        ·
          refine ⟨15732880731070560916592057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10488587154047040611061371 15732880731070560916592057)
          ·
            refine ⟨11799660548302920687444043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15732880731070560916592057 11799660548302920687444043)
            ·
              refine ⟨17699490822454381031166065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11799660548302920687444043 17699490822454381031166065)
              ·
                refine ⟨13274618116840785773374549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17699490822454381031166065 13274618116840785773374549)
                ·
                  refine ⟨155561931056727958281733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13274618116840785773374549 155561931056727958281733)
                  ·
                    rfl

theorem cell22_1363301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_1363301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363301 prefixEnd_1363301 := by exact prefixLift 1363301
  have htrace : WordTrace (prefixWord ++ tailWord_1363301) baseStart_1363301 baseEnd_1363301 := by
    simpa [prefixWord, tailWord_1363301, baseEnd_1363301] using wordTrace_append hprefix tailTrace_1363301
  have hstable : (prefixWord ++ tailWord_1363301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363301).length < 2 ^ (prefixWord ++ tailWord_1363301).sum := by decide
  have hdescent : baseEnd_1363301 < baseStart_1363301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363333 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1363333 : Nat := 118140960795 + 1363333 * 2 ^ 59
def prefixEnd_1363333 : Nat := 4983230072969 + 3 ^ 40 * 1363333 * 2
def baseEnd_1363333 : Nat := 466696747424146458045101

theorem tailTrace_1363333 : CollatzResearch.WordTrace tailWord_1363333 prefixEnd_1363333 466696747424146458045101 := by
  unfold tailWord_1363333
  simp only [CollatzResearch.WordTrace]
  refine ⟨49724839569884854584270653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33149893046589903056180435 49724839569884854584270653)
  ·
    refine ⟨18646814838706820469101495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49724839569884854584270653 18646814838706820469101495)
    ·
      refine ⟨27970222258060230703652243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18646814838706820469101495 27970222258060230703652243)
      ·
        refine ⟨41955333387090346055478365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27970222258060230703652243 41955333387090346055478365)
        ·
          refine ⟨15733250020158879770804387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41955333387090346055478365 15733250020158879770804387)
          ·
            refine ⟨23599875030238319656206581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15733250020158879770804387 23599875030238319656206581)
            ·
              refine ⟨2212488284084842467769367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23599875030238319656206581 2212488284084842467769367)
              ·
                refine ⟨3318732426127263701654051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212488284084842467769367 3318732426127263701654051)
                ·
                  refine ⟨4978098639190895552481077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3318732426127263701654051 4978098639190895552481077)
                  ·
                    refine ⟨466696747424146458045101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4978098639190895552481077 466696747424146458045101)
                    ·
                      rfl

theorem cell22_1363333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1363333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363333 prefixEnd_1363333 := by exact prefixLift 1363333
  have htrace : WordTrace (prefixWord ++ tailWord_1363333) baseStart_1363333 baseEnd_1363333 := by
    simpa [prefixWord, tailWord_1363333, baseEnd_1363333] using wordTrace_append hprefix tailTrace_1363333
  have hstable : (prefixWord ++ tailWord_1363333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363333).length < 2 ^ (prefixWord ++ tailWord_1363333).sum := by decide
  have hdescent : baseEnd_1363333 < baseStart_1363333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363423 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_1363423 : Nat := 118140960795 + 1363423 * 2 ^ 59
def prefixEnd_1363423 : Nat := 4983230072969 + 3 ^ 40 * 1363423 * 2
def baseEnd_1363423 : Nat := 466727556263416223294825

theorem tailTrace_1363423 : CollatzResearch.WordTrace tailWord_1363423 prefixEnd_1363423 466727556263416223294825 := by
  unfold tailWord_1363423
  simp only [CollatzResearch.WordTrace]
  refine ⟨49728122139558799955046923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33152081426372533303364615 49728122139558799955046923)
  ·
    refine ⟨74592183209338199932570385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49728122139558799955046923 74592183209338199932570385)
    ·
      refine ⟨55944137407003649949427789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74592183209338199932570385 55944137407003649949427789)
      ·
        refine ⟨20979051527626368731035421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55944137407003649949427789 20979051527626368731035421)
        ·
          refine ⟨7867144322859888274138283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20979051527626368731035421 7867144322859888274138283)
          ·
            refine ⟨11800716484289832411207425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867144322859888274138283 11800716484289832411207425)
            ·
              refine ⟨8850537363217374308405569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11800716484289832411207425 8850537363217374308405569)
              ·
                refine ⟨6637903022413030731304177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8850537363217374308405569 6637903022413030731304177)
                ·
                  refine ⟨4978427266809773048478133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6637903022413030731304177 4978427266809773048478133)
                  ·
                    refine ⟨466727556263416223294825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4978427266809773048478133 466727556263416223294825)
                    ·
                      rfl

theorem cell22_1363423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_1363423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363423 prefixEnd_1363423 := by exact prefixLift 1363423
  have htrace : WordTrace (prefixWord ++ tailWord_1363423) baseStart_1363423 baseEnd_1363423 := by
    simpa [prefixWord, tailWord_1363423, baseEnd_1363423] using wordTrace_append hprefix tailTrace_1363423
  have hstable : (prefixWord ++ tailWord_1363423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363423).length < 2 ^ (prefixWord ++ tailWord_1363423).sum := by decide
  have hdescent : baseEnd_1363423 < baseStart_1363423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363425 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 5]
def baseStart_1363425 : Nat := 118140960795 + 1363425 * 2 ^ 59
def prefixEnd_1363425 : Nat := 4983230072969 + 3 ^ 40 * 1363425 * 2
def baseEnd_1363425 : Nat := 155576080301429628248273

theorem tailTrace_1363425 : CollatzResearch.WordTrace tailWord_1363425 prefixEnd_1363425 155576080301429628248273 := by
  unfold tailWord_1363425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49728195085551554296619729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33152130057034369531079819 49728195085551554296619729)
  ·
    refine ⟨37296146314163665722464797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49728195085551554296619729 37296146314163665722464797)
    ·
      refine ⟨13986054867811374645924299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37296146314163665722464797 13986054867811374645924299)
      ·
        refine ⟨20979082301717061968886449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986054867811374645924299 20979082301717061968886449)
        ·
          refine ⟨15734311726287796476664837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20979082301717061968886449 15734311726287796476664837)
          ·
            refine ⟨2950183448678961839374657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15734311726287796476664837 2950183448678961839374657)
            ·
              refine ⟨2212637586509221379530993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950183448678961839374657 2212637586509221379530993)
              ·
                refine ⟨1659478189881916034648245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212637586509221379530993 1659478189881916034648245)
                ·
                  refine ⟨155576080301429628248273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1659478189881916034648245 155576080301429628248273)
                  ·
                    rfl

theorem cell22_1363425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_1363425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363425 prefixEnd_1363425 := by exact prefixLift 1363425
  have htrace : WordTrace (prefixWord ++ tailWord_1363425) baseStart_1363425 baseEnd_1363425 := by
    simpa [prefixWord, tailWord_1363425, baseEnd_1363425] using wordTrace_append hprefix tailTrace_1363425
  have hstable : (prefixWord ++ tailWord_1363425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363425).length < 2 ^ (prefixWord ++ tailWord_1363425).sum := by decide
  have hdescent : baseEnd_1363425 < baseStart_1363425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363429 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_1363429 : Nat := 118140960795 + 1363429 * 2 ^ 59
def prefixEnd_1363429 : Nat := 4983230072969 + 3 ^ 40 * 1363429 * 2
def baseEnd_1363429 : Nat := 466729610186034207644807

theorem tailTrace_1363429 : CollatzResearch.WordTrace tailWord_1363429 prefixEnd_1363429 466729610186034207644807 := by
  unfold tailWord_1363429
  simp only [CollatzResearch.WordTrace]
  refine ⟨49728340977537062979765341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33152227318358041986510227 49728340977537062979765341)
  ·
    refine ⟨18648127866576398617412003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49728340977537062979765341 18648127866576398617412003)
    ·
      refine ⟨27972191799864597926118005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18648127866576398617412003 27972191799864597926118005)
      ·
        refine ⟨2622392981237306055573563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27972191799864597926118005 2622392981237306055573563)
        ·
          refine ⟨3933589471855959083360345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622392981237306055573563 3933589471855959083360345)
          ·
            refine ⟨2950192103891969312520259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3933589471855959083360345 2950192103891969312520259)
            ·
              refine ⟨4425288155837953968780389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950192103891969312520259 4425288155837953968780389)
              ·
                refine ⟨829741529219616369146323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4425288155837953968780389 829741529219616369146323)
                ·
                  refine ⟨1244612293829424553719485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829741529219616369146323 1244612293829424553719485)
                  ·
                    refine ⟨466729610186034207644807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244612293829424553719485 466729610186034207644807)
                    ·
                      rfl

theorem cell22_1363429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_1363429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363429 prefixEnd_1363429 := by exact prefixLift 1363429
  have htrace : WordTrace (prefixWord ++ tailWord_1363429) baseStart_1363429 baseEnd_1363429 := by
    simpa [prefixWord, tailWord_1363429, baseEnd_1363429] using wordTrace_append hprefix tailTrace_1363429
  have hstable : (prefixWord ++ tailWord_1363429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363429).length < 2 ^ (prefixWord ++ tailWord_1363429).sum := by decide
  have hdescent : baseEnd_1363429 < baseStart_1363429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363453 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1363453 : Nat := 118140960795 + 1363453 * 2 ^ 59
def prefixEnd_1363453 : Nat := 4983230072969 + 3 ^ 40 * 1363453 * 2
def baseEnd_1363453 : Nat := 155579275292168715014911

theorem tailTrace_1363453 : CollatzResearch.WordTrace tailWord_1363453 prefixEnd_1363453 155579275292168715014911 := by
  unfold tailWord_1363453
  simp only [CollatzResearch.WordTrace]
  refine ⟨49729216329450115078639013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33152810886300076719092675 49729216329450115078639013)
  ·
    refine ⟨9324228061771896577244815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49729216329450115078639013 9324228061771896577244815)
    ·
      refine ⟨13986342092657844865867223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9324228061771896577244815 13986342092657844865867223)
      ·
        refine ⟨20979513138986767298800835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13986342092657844865867223 20979513138986767298800835)
        ·
          refine ⟨31469269708480150948201253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20979513138986767298800835 31469269708480150948201253)
          ·
            refine ⟨5900488070340028302787735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31469269708480150948201253 5900488070340028302787735)
            ·
              refine ⟨8850732105510042454181603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900488070340028302787735 8850732105510042454181603)
              ·
                refine ⟨13276098158265063681272405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850732105510042454181603 13276098158265063681272405)
                ·
                  refine ⟨155579275292168715014911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13276098158265063681272405 155579275292168715014911)
                  ·
                    rfl

theorem cell22_1363453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1363453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363453 prefixEnd_1363453 := by exact prefixLift 1363453
  have htrace : WordTrace (prefixWord ++ tailWord_1363453) baseStart_1363453 baseEnd_1363453 := by
    simpa [prefixWord, tailWord_1363453, baseEnd_1363453] using wordTrace_append hprefix tailTrace_1363453
  have hstable : (prefixWord ++ tailWord_1363453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363453).length < 2 ^ (prefixWord ++ tailWord_1363453).sum := by decide
  have hdescent : baseEnd_1363453 < baseStart_1363453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363476 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1363476 : Nat := 118140960795 + 1363476 * 2 ^ 59
def prefixEnd_1363476 : Nat := 4983230072969 + 3 ^ 40 * 1363476 * 2
def baseEnd_1363476 : Nat := 155581899748847250573221

theorem tailTrace_1363476 : CollatzResearch.WordTrace tailWord_1363476 prefixEnd_1363476 155581899748847250573221 := by
  unfold tailWord_1363476
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865027604183395003363141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33153370138911193337817521 24865027604183395003363141)
  ·
    refine ⟨4662192675784386563130589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24865027604183395003363141 4662192675784386563130589)
    ·
      refine ⟨1748322253419144961173971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4662192675784386563130589 1748322253419144961173971)
      ·
        refine ⟨2622483380128717441760957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748322253419144961173971 2622483380128717441760957)
        ·
          refine ⟨983431267548269040660359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622483380128717441760957 983431267548269040660359)
          ·
            refine ⟨1475146901322403560990539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983431267548269040660359 1475146901322403560990539)
            ·
              refine ⟨2212720351983605341485809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475146901322403560990539 2212720351983605341485809)
              ·
                refine ⟨1659540263987704006114357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212720351983605341485809 1659540263987704006114357)
                ·
                  refine ⟨155581899748847250573221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1659540263987704006114357 155581899748847250573221)
                  ·
                    rfl

theorem cell22_1363476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1363476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363476 prefixEnd_1363476 := by exact prefixLift 1363476
  have htrace : WordTrace (prefixWord ++ tailWord_1363476) baseStart_1363476 baseEnd_1363476 := by
    simpa [prefixWord, tailWord_1363476, baseEnd_1363476] using wordTrace_append hprefix tailTrace_1363476
  have hstable : (prefixWord ++ tailWord_1363476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363476).length < 2 ^ (prefixWord ++ tailWord_1363476).sum := by decide
  have hdescent : baseEnd_1363476 < baseStart_1363476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363502 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1363502 : Nat := 118140960795 + 1363502 * 2 ^ 59
def prefixEnd_1363502 : Nat := 4983230072969 + 3 ^ 40 * 1363502 * 2
def baseEnd_1363502 : Nat := 466754599577886350569583

theorem tailTrace_1363502 : CollatzResearch.WordTrace tailWord_1363502 prefixEnd_1363502 466754599577886350569583 := by
  unfold tailWord_1363502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216375438284074555896595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33154002337515064298115173 6216375438284074555896595)
  ·
    refine ⟨9324563157426111833844893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6216375438284074555896595 9324563157426111833844893)
    ·
      refine ⟨3496711184034791937691835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9324563157426111833844893 3496711184034791937691835)
      ·
        refine ⟨5245066776052187906537753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496711184034791937691835 5245066776052187906537753)
        ·
          refine ⟨3933800082039140929903315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5245066776052187906537753 3933800082039140929903315)
          ·
            refine ⟨5900700123058711394854973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933800082039140929903315 5900700123058711394854973)
            ·
              refine ⟨2212762546147016773070615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5900700123058711394854973 2212762546147016773070615)
              ·
                refine ⟨3319143819220525159605923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212762546147016773070615 3319143819220525159605923)
                ·
                  refine ⟨4978715728830787739408885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319143819220525159605923 4978715728830787739408885)
                  ·
                    refine ⟨466754599577886350569583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4978715728830787739408885 466754599577886350569583)
                    ·
                      rfl

theorem cell22_1363502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1363502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363502 prefixEnd_1363502 := by exact prefixLift 1363502
  have htrace : WordTrace (prefixWord ++ tailWord_1363502) baseStart_1363502 baseEnd_1363502 := by
    simpa [prefixWord, tailWord_1363502, baseEnd_1363502] using wordTrace_append hprefix tailTrace_1363502
  have hstable : (prefixWord ++ tailWord_1363502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363502).length < 2 ^ (prefixWord ++ tailWord_1363502).sum := by decide
  have hdescent : baseEnd_1363502 < baseStart_1363502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363528 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1363528 : Nat := 118140960795 + 1363528 * 2 ^ 59
def prefixEnd_1363528 : Nat := 4983230072969 + 3 ^ 40 * 1363528 * 2
def baseEnd_1363528 : Nat := 466763499909230949419503

theorem tailTrace_1363528 : CollatzResearch.WordTrace tailWord_1363528 prefixEnd_1363528 466763499909230949419503 := by
  unfold tailWord_1363528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865975902089201443809619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33154634536118935258412825 24865975902089201443809619)
  ·
    refine ⟨37298963853133802165714429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24865975902089201443809619 37298963853133802165714429)
    ·
      refine ⟨13987111444925175812142911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37298963853133802165714429 13987111444925175812142911)
      ·
        refine ⟨20980667167387763718214367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13987111444925175812142911 20980667167387763718214367)
        ·
          refine ⟨31471000751081645577321551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20980667167387763718214367 31471000751081645577321551)
          ·
            refine ⟨47206501126622468365982327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31471000751081645577321551 47206501126622468365982327)
            ·
              refine ⟨70809751689933702548973491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47206501126622468365982327 70809751689933702548973491)
              ·
                refine ⟨106214627534900553823460237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70809751689933702548973491 106214627534900553823460237)
                ·
                  refine ⟨39830485325587707683797589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106214627534900553823460237 39830485325587707683797589)
                  ·
                    refine ⟨466763499909230949419503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39830485325587707683797589 466763499909230949419503)
                    ·
                      rfl

theorem cell22_1363528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1363528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363528 prefixEnd_1363528 := by exact prefixLift 1363528
  have htrace : WordTrace (prefixWord ++ tailWord_1363528) baseStart_1363528 baseEnd_1363528 := by
    simpa [prefixWord, tailWord_1363528, baseEnd_1363528] using wordTrace_append hprefix tailTrace_1363528
  have hstable : (prefixWord ++ tailWord_1363528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363528).length < 2 ^ (prefixWord ++ tailWord_1363528).sum := by decide
  have hdescent : baseEnd_1363528 < baseStart_1363528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363549 : List Nat := [1, 4, 4, 2, 1, 1, 2, 7]
def baseStart_1363549 : Nat := 118140960795 + 1363549 * 2 ^ 59
def prefixEnd_1363549 : Nat := 4983230072969 + 3 ^ 40 * 1363549 * 2
def baseEnd_1363549 : Nat := 51863409848710432738271

theorem tailTrace_1363549 : CollatzResearch.WordTrace tailWord_1363549 prefixEnd_1363549 51863409848710432738271 := by
  unfold tailWord_1363549
  simp only [CollatzResearch.WordTrace]
  refine ⟨49732717737102323474133701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33155145158068215649422467 49732717737102323474133701)
  ·
    refine ⟨9324884575706685651400069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49732717737102323474133701 9324884575706685651400069)
    ·
      refine ⟨1748415857945003559637513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9324884575706685651400069 1748415857945003559637513)
      ·
        refine ⟨1311311893458752669728135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1748415857945003559637513 1311311893458752669728135)
        ·
          refine ⟨1966967840188129004592203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311311893458752669728135 1966967840188129004592203)
          ·
            refine ⟨2950451760282193506888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966967840188129004592203 2950451760282193506888305)
            ·
              refine ⟨2212838820211645130166229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950451760282193506888305 2212838820211645130166229)
              ·
                refine ⟨51863409848710432738271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2212838820211645130166229 51863409848710432738271)
                ·
                  rfl

theorem cell22_1363549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 7].length) (baseStart_1363549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363549 prefixEnd_1363549 := by exact prefixLift 1363549
  have htrace : WordTrace (prefixWord ++ tailWord_1363549) baseStart_1363549 baseEnd_1363549 := by
    simpa [prefixWord, tailWord_1363549, baseEnd_1363549] using wordTrace_append hprefix tailTrace_1363549
  have hstable : (prefixWord ++ tailWord_1363549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363549).length < 2 ^ (prefixWord ++ tailWord_1363549).sum := by decide
  have hdescent : baseEnd_1363549 < baseStart_1363549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363598 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_1363598 : Nat := 118140960795 + 1363598 * 2 ^ 59
def prefixEnd_1363598 : Nat := 4983230072969 + 3 ^ 40 * 1363598 * 2
def baseEnd_1363598 : Nat := 466787462339774100169289

theorem tailTrace_1363598 : CollatzResearch.WordTrace tailWord_1363598 prefixEnd_1363598 466787462339774100169289 := by
  unfold tailWord_1363598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216813114240600605333431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33156336609283203228444965 6216813114240600605333431)
  ·
    refine ⟨9325219671360900908000147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6216813114240600605333431 9325219671360900908000147)
    ·
      refine ⟨13987829507041351362000221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9325219671360900908000147 13987829507041351362000221)
      ·
        refine ⟨5245436065140506760750083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13987829507041351362000221 5245436065140506760750083)
        ·
          refine ⟨7868154097710760141125125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245436065140506760750083 7868154097710760141125125)
          ·
            refine ⟨1475278893320767526460961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7868154097710760141125125 1475278893320767526460961)
            ·
              refine ⟨1106459169990575644845721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475278893320767526460961 1106459169990575644845721)
              ·
                refine ⟨829844377492931733634291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106459169990575644845721 829844377492931733634291)
                ·
                  refine ⟨1244766566239397600451437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829844377492931733634291 1244766566239397600451437)
                  ·
                    refine ⟨466787462339774100169289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244766566239397600451437 466787462339774100169289)
                    ·
                      rfl

theorem cell22_1363598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_1363598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363598 prefixEnd_1363598 := by exact prefixLift 1363598
  have htrace : WordTrace (prefixWord ++ tailWord_1363598) baseStart_1363598 baseEnd_1363598 := by
    simpa [prefixWord, tailWord_1363598, baseEnd_1363598] using wordTrace_append hprefix tailTrace_1363598
  have hstable : (prefixWord ++ tailWord_1363598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363598).length < 2 ^ (prefixWord ++ tailWord_1363598).sum := by decide
  have hdescent : baseEnd_1363598 < baseStart_1363598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363635 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_1363635 : Nat := 118140960795 + 1363635 * 2 ^ 59
def prefixEnd_1363635 : Nat := 4983230072969 + 3 ^ 40 * 1363635 * 2
def baseEnd_1363635 : Nat := 466800128195918336994175

theorem tailTrace_1363635 : CollatzResearch.WordTrace tailWord_1363635 prefixEnd_1363635 466800128195918336994175 := by
  unfold tailWord_1363635
  simp only [CollatzResearch.WordTrace]
  refine ⟨49735854414790760161764359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33157236276527173441176239 49735854414790760161764359)
  ·
    refine ⟨74603781622186140242646539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49735854414790760161764359 74603781622186140242646539)
    ·
      refine ⟨111905672433279210363969809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74603781622186140242646539 111905672433279210363969809)
      ·
        refine ⟨83929254324959407772977357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111905672433279210363969809 83929254324959407772977357)
        ·
          refine ⟨31473470371859777914866509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83929254324959407772977357 31473470371859777914866509)
          ·
            refine ⟨11802551389447416718074941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31473470371859777914866509 11802551389447416718074941)
            ·
              refine ⟨4425956771042781269278103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11802551389447416718074941 4425956771042781269278103)
              ·
                refine ⟨6638935156564171903917155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425956771042781269278103 6638935156564171903917155)
                ·
                  refine ⟨9958402734846257855875733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6638935156564171903917155 9958402734846257855875733)
                  ·
                    refine ⟨466800128195918336994175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9958402734846257855875733 466800128195918336994175)
                    ·
                      rfl

theorem cell22_1363635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_1363635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363635 prefixEnd_1363635 := by exact prefixLift 1363635
  have htrace : WordTrace (prefixWord ++ tailWord_1363635) baseStart_1363635 baseEnd_1363635 := by
    simpa [prefixWord, tailWord_1363635, baseEnd_1363635] using wordTrace_append hprefix tailTrace_1363635
  have hstable : (prefixWord ++ tailWord_1363635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363635).length < 2 ^ (prefixWord ++ tailWord_1363635).sum := by decide
  have hdescent : baseEnd_1363635 < baseStart_1363635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363639 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 4]
def baseStart_1363639 : Nat := 118140960795 + 1363639 * 2 ^ 59
def prefixEnd_1363639 : Nat := 4983230072969 + 3 ^ 40 * 1363639 * 2
def baseEnd_1363639 : Nat := 155600499159221219964721

theorem tailTrace_1363639 : CollatzResearch.WordTrace tailWord_1363639 prefixEnd_1363639 155600499159221219964721 := by
  unfold tailWord_1363639
  simp only [CollatzResearch.WordTrace]
  refine ⟨49736000306776268844909971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33157333537850845896606647 49736000306776268844909971)
  ·
    refine ⟨74604000460164403267364957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49736000306776268844909971 74604000460164403267364957)
    ·
      refine ⟨27976500172561651225261859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74604000460164403267364957 27976500172561651225261859)
      ·
        refine ⟨41964750258842476837892789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27976500172561651225261859 41964750258842476837892789)
        ·
          refine ⟨3934195336766482203552449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41964750258842476837892789 3934195336766482203552449)
          ·
            refine ⟨2950646502574861652664337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3934195336766482203552449 2950646502574861652664337)
            ·
              refine ⟨2212984876931146239498253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2950646502574861652664337 2212984876931146239498253)
              ·
                refine ⟨829869328849179839811845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2212984876931146239498253 829869328849179839811845)
                ·
                  refine ⟨155600499159221219964721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 829869328849179839811845 155600499159221219964721)
                  ·
                    rfl

theorem cell22_1363639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 4].length) (baseStart_1363639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363639 prefixEnd_1363639 := by exact prefixLift 1363639
  have htrace : WordTrace (prefixWord ++ tailWord_1363639) baseStart_1363639 baseEnd_1363639 := by
    simpa [prefixWord, tailWord_1363639, baseEnd_1363639] using wordTrace_append hprefix tailTrace_1363639
  have hstable : (prefixWord ++ tailWord_1363639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363639).length < 2 ^ (prefixWord ++ tailWord_1363639).sum := by decide
  have hdescent : baseEnd_1363639 < baseStart_1363639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363652 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1363652 : Nat := 118140960795 + 1363652 * 2 ^ 59
def prefixEnd_1363652 : Nat := 4983230072969 + 3 ^ 40 * 1363652 * 2
def baseEnd_1363652 : Nat := 466805947643335959319123

theorem tailTrace_1363652 : CollatzResearch.WordTrace tailWord_1363652 prefixEnd_1363652 466805947643335959319123 := by
  unfold tailWord_1363652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868237227864586032566605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33157649637152781376755473 24868237227864586032566605)
  ·
    refine ⟨9325588960449219762212477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24868237227864586032566605 9325588960449219762212477)
    ·
      refine ⟨3497095860168457410829679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9325588960449219762212477 3497095860168457410829679)
      ·
        refine ⟨5245643790252686116244519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497095860168457410829679 5245643790252686116244519)
        ·
          refine ⟨7868465685379029174366779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245643790252686116244519 7868465685379029174366779)
          ·
            refine ⟨11802698528068543761550169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868465685379029174366779 11802698528068543761550169)
            ·
              refine ⟨8852023896051407821162627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11802698528068543761550169 8852023896051407821162627)
              ·
                refine ⟨13278035844077111731743941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852023896051407821162627 13278035844077111731743941)
                ·
                  refine ⟨2489631720764458449701989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13278035844077111731743941 2489631720764458449701989)
                  ·
                    refine ⟨466805947643335959319123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489631720764458449701989 466805947643335959319123)
                    ·
                      rfl

theorem cell22_1363652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1363652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363652 prefixEnd_1363652 := by exact prefixLift 1363652
  have htrace : WordTrace (prefixWord ++ tailWord_1363652) baseStart_1363652 baseEnd_1363652 := by
    simpa [prefixWord, tailWord_1363652, baseEnd_1363652] using wordTrace_append hprefix tailTrace_1363652
  have hstable : (prefixWord ++ tailWord_1363652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363652).length < 2 ^ (prefixWord ++ tailWord_1363652).sum := by decide
  have hdescent : baseEnd_1363652 < baseStart_1363652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363680 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_1363680 : Nat := 118140960795 + 1363680 * 2 ^ 59
def prefixEnd_1363680 : Nat := 4983230072969 + 3 ^ 40 * 1363680 * 2
def baseEnd_1363680 : Nat := 466815532615553219619037

theorem tailTrace_1363680 : CollatzResearch.WordTrace tailWord_1363680 prefixEnd_1363680 466815532615553219619037 := by
  unfold tailWord_1363680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868747849813866423576247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33158330466418488564768329 24868747849813866423576247)
  ·
    refine ⟨37303121774720799635364371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24868747849813866423576247 37303121774720799635364371)
    ·
      refine ⟨55954682662081199453046557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37303121774720799635364371 55954682662081199453046557)
      ·
        refine ⟨20983005998280449794892459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55954682662081199453046557 20983005998280449794892459)
        ·
          refine ⟨31474508997420674692338689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20983005998280449794892459 31474508997420674692338689)
          ·
            refine ⟨23605881748065506019254017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31474508997420674692338689 23605881748065506019254017)
            ·
              refine ⟨17704411311049129514440513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23605881748065506019254017 17704411311049129514440513)
              ·
                refine ⟨13278308483286847135830385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17704411311049129514440513 13278308483286847135830385)
                ·
                  refine ⟨9958731362465135351872789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13278308483286847135830385 9958731362465135351872789)
                  ·
                    refine ⟨466815532615553219619037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9958731362465135351872789 466815532615553219619037)
                    ·
                      rfl

theorem cell22_1363680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_1363680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363680 prefixEnd_1363680 := by exact prefixLift 1363680
  have htrace : WordTrace (prefixWord ++ tailWord_1363680) baseStart_1363680 baseEnd_1363680 := by
    simpa [prefixWord, tailWord_1363680, baseEnd_1363680] using wordTrace_append hprefix tailTrace_1363680
  have hstable : (prefixWord ++ tailWord_1363680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363680).length < 2 ^ (prefixWord ++ tailWord_1363680).sum := by decide
  have hdescent : baseEnd_1363680 < baseStart_1363680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363695 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 9]
def baseStart_1363695 : Nat := 118140960795 + 1363695 * 2 ^ 59
def prefixEnd_1363695 : Nat := 4983230072969 + 3 ^ 40 * 1363695 * 2
def baseEnd_1363695 : Nat := 155606889140699393497997

theorem tailTrace_1363695 : CollatzResearch.WordTrace tailWord_1363695 prefixEnd_1363695 155606889140699393497997 := by
  unfold tailWord_1363695
  simp only [CollatzResearch.WordTrace]
  refine ⟨49738042794573390408948539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33158695196382260272632359 49738042794573390408948539)
  ·
    refine ⟨74607064191860085613422809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49738042794573390408948539 74607064191860085613422809)
    ·
      refine ⟨55955298143895064210067107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74607064191860085613422809 55955298143895064210067107)
      ·
        refine ⟨83932947215842596315100661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55955298143895064210067107 83932947215842596315100661)
        ·
          refine ⟨7868713801485243404540687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83932947215842596315100661 7868713801485243404540687)
          ·
            refine ⟨11803070702227865106811031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868713801485243404540687 11803070702227865106811031)
            ·
              refine ⟨17704606053341797660216547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11803070702227865106811031 17704606053341797660216547)
              ·
                refine ⟨26556909080012696490324821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17704606053341797660216547 26556909080012696490324821)
                ·
                  refine ⟨155606889140699393497997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26556909080012696490324821 155606889140699393497997)
                  ·
                    rfl

theorem cell22_1363695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_1363695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363695 prefixEnd_1363695 := by exact prefixLift 1363695
  have htrace : WordTrace (prefixWord ++ tailWord_1363695) baseStart_1363695 baseEnd_1363695 := by
    simpa [prefixWord, tailWord_1363695, baseEnd_1363695] using wordTrace_append hprefix tailTrace_1363695
  have hstable : (prefixWord ++ tailWord_1363695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363695).length < 2 ^ (prefixWord ++ tailWord_1363695).sum := by decide
  have hdescent : baseEnd_1363695 < baseStart_1363695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363716 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1363716 : Nat := 118140960795 + 1363716 * 2 ^ 59
def prefixEnd_1363716 : Nat := 4983230072969 + 3 ^ 40 * 1363716 * 2
def baseEnd_1363716 : Nat := 466827856151261125718927

theorem tailTrace_1363716 : CollatzResearch.WordTrace tailWord_1363716 prefixEnd_1363716 466827856151261125718927 := by
  unfold tailWord_1363716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24869404363748655497731501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33159205818331540663642001 24869404363748655497731501)
  ·
    refine ⟨9326026636405745811649313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24869404363748655497731501 9326026636405745811649313)
    ·
      refine ⟨6994519977304309358736985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9326026636405745811649313 6994519977304309358736985)
      ·
        refine ⟨5245889982978232019052739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6994519977304309358736985 5245889982978232019052739)
        ·
          refine ⟨7868834974467348028579109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245889982978232019052739 7868834974467348028579109)
          ·
            refine ⟨1475406557712627755358583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7868834974467348028579109 1475406557712627755358583)
            ·
              refine ⟨2213109836568941633037875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475406557712627755358583 2213109836568941633037875)
              ·
                refine ⟨3319664754853412449556813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213109836568941633037875 3319664754853412449556813)
                ·
                  refine ⟨1244874283070029668583805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3319664754853412449556813 1244874283070029668583805)
                  ·
                    refine ⟨466827856151261125718927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244874283070029668583805 466827856151261125718927)
                    ·
                      rfl

theorem cell22_1363716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1363716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363716 prefixEnd_1363716 := by exact prefixLift 1363716
  have htrace : WordTrace (prefixWord ++ tailWord_1363716) baseStart_1363716 baseEnd_1363716 := by
    simpa [prefixWord, tailWord_1363716, baseEnd_1363716] using wordTrace_append hprefix tailTrace_1363716
  have hstable : (prefixWord ++ tailWord_1363716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363716).length < 2 ^ (prefixWord ++ tailWord_1363716).sum := by decide
  have hdescent : baseEnd_1363716 < baseStart_1363716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_1363755 : Nat := 118140960795 + 1363755 * 2 ^ 59
def prefixEnd_1363755 : Nat := 4983230072969 + 3 ^ 40 * 1363755 * 2
def baseEnd_1363755 : Nat := 466841206648278023993807

theorem tailTrace_1363755 : CollatzResearch.WordTrace tailWord_1363755 prefixEnd_1363755 466841206648278023993807 := by
  unfold tailWord_1363755
  simp only [CollatzResearch.WordTrace]
  refine ⟨49740231174356020656132719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33160154116237347104088479 49740231174356020656132719)
  ·
    refine ⟨74610346761534030984199079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49740231174356020656132719 74610346761534030984199079)
    ·
      refine ⟨111915520142301046476298619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74610346761534030984199079 111915520142301046476298619)
      ·
        refine ⟨167873280213451569714447929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111915520142301046476298619 167873280213451569714447929)
        ·
          refine ⟨125904960160088677285835947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167873280213451569714447929 125904960160088677285835947)
          ·
            refine ⟨188857440240133015928753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125904960160088677285835947 188857440240133015928753921)
            ·
              refine ⟨141643080180099761946565441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188857440240133015928753921 141643080180099761946565441)
              ·
                refine ⟨106232310135074821459924081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141643080180099761946565441 106232310135074821459924081)
                ·
                  refine ⟨79674232601306116094943061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106232310135074821459924081 79674232601306116094943061)
                  ·
                    refine ⟨466841206648278023993807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79674232601306116094943061 466841206648278023993807)
                    ·
                      rfl

theorem cell22_1363755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_1363755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363755 prefixEnd_1363755 := by exact prefixLift 1363755
  have htrace : WordTrace (prefixWord ++ tailWord_1363755) baseStart_1363755 baseEnd_1363755 := by
    simpa [prefixWord, tailWord_1363755, baseEnd_1363755] using wordTrace_append hprefix tailTrace_1363755
  have hstable : (prefixWord ++ tailWord_1363755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363755).length < 2 ^ (prefixWord ++ tailWord_1363755).sum := by decide
  have hdescent : baseEnd_1363755 < baseStart_1363755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363834 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_1363834 : Nat := 118140960795 + 1363834 * 2 ^ 59
def prefixEnd_1363834 : Nat := 4983230072969 + 3 ^ 40 * 1363834 * 2
def baseEnd_1363834 : Nat := 466868249962748151268565

theorem tailTrace_1363834 : CollatzResearch.WordTrace tailWord_1363834 prefixEnd_1363834 466868249962748151268565 := by
  unfold tailWord_1363834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12435778135267454287064639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33162075027379878098839037 12435778135267454287064639)
  ·
    refine ⟨18653667202901181430596959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12435778135267454287064639 18653667202901181430596959)
    ·
      refine ⟨27980500804351772145895439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18653667202901181430596959 27980500804351772145895439)
      ·
        refine ⟨41970751206527658218843159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27980500804351772145895439 41970751206527658218843159)
        ·
          refine ⟨62956126809791487328264739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41970751206527658218843159 62956126809791487328264739)
          ·
            refine ⟨94434190214687230992397109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62956126809791487328264739 94434190214687230992397109)
            ·
              refine ⟨8853205332626927905537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94434190214687230992397109 8853205332626927905537229)
              ·
                refine ⟨3319951999735097964576461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8853205332626927905537229 3319951999735097964576461)
                ·
                  refine ⟨1244981999900661736716173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3319951999735097964576461 1244981999900661736716173)
                  ·
                    refine ⟨466868249962748151268565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1244981999900661736716173 466868249962748151268565)
                    ·
                      rfl

theorem cell22_1363834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_1363834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363834 prefixEnd_1363834 := by exact prefixLift 1363834
  have htrace : WordTrace (prefixWord ++ tailWord_1363834) baseStart_1363834 baseEnd_1363834 := by
    simpa [prefixWord, tailWord_1363834, baseEnd_1363834] using wordTrace_append hprefix tailTrace_1363834
  have hstable : (prefixWord ++ tailWord_1363834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363834).length < 2 ^ (prefixWord ++ tailWord_1363834).sum := by decide
  have hdescent : baseEnd_1363834 < baseStart_1363834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363943 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 4]
def baseStart_1363943 : Nat := 118140960795 + 1363943 * 2 ^ 59
def prefixEnd_1363943 : Nat := 4983230072969 + 3 ^ 40 * 1363943 * 2
def baseEnd_1363943 : Nat := 155635187630102733431077

theorem tailTrace_1363943 : CollatzResearch.WordTrace tailWord_1363943 prefixEnd_1363943 155635187630102733431077 := by
  unfold tailWord_1363943
  simp only [CollatzResearch.WordTrace]
  refine ⟨49747088097674928763976483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33164725398449952509317655 49747088097674928763976483)
  ·
    refine ⟨74620632146512393145964725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49747088097674928763976483 74620632146512393145964725)
    ·
      refine ⟨6995684263735536857434193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74620632146512393145964725 6995684263735536857434193)
      ·
        refine ⟨5246763197801652643075645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6995684263735536857434193 5246763197801652643075645)
        ·
          refine ⟨1967536199175619741153367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5246763197801652643075645 1967536199175619741153367)
          ·
            refine ⟨2951304298763429611730051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967536199175619741153367 2951304298763429611730051)
            ·
              refine ⟨4426956448145144417595077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951304298763429611730051 4426956448145144417595077)
              ·
                refine ⟨830054334027214578299077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4426956448145144417595077 830054334027214578299077)
                ·
                  refine ⟨155635187630102733431077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830054334027214578299077 155635187630102733431077)
                  ·
                    rfl

theorem cell22_1363943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 4].length) (baseStart_1363943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363943 prefixEnd_1363943 := by exact prefixLift 1363943
  have htrace : WordTrace (prefixWord ++ tailWord_1363943) baseStart_1363943 baseEnd_1363943 := by
    simpa [prefixWord, tailWord_1363943, baseEnd_1363943] using wordTrace_append hprefix tailTrace_1363943
  have hstable : (prefixWord ++ tailWord_1363943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363943).length < 2 ^ (prefixWord ++ tailWord_1363943).sum := by decide
  have hdescent : baseEnd_1363943 < baseStart_1363943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363958 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1363958 : Nat := 118140960795 + 1363958 * 2 ^ 59
def prefixEnd_1363958 : Nat := 4983230072969 + 3 ^ 40 * 1363958 * 2
def baseEnd_1363958 : Nat := 466910697696853161168185

theorem tailTrace_1363958 : CollatzResearch.WordTrace tailWord_1363958 prefixEnd_1363958 466910697696853161168185 := by
  unfold tailWord_1363958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109227199538786645360783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33165090128413724217181685 3109227199538786645360783)
  ·
    refine ⟨4663840799308179968041175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3109227199538786645360783 4663840799308179968041175)
    ·
      refine ⟨6995761198962269952061763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663840799308179968041175 6995761198962269952061763)
      ·
        refine ⟨10493641798443404928092645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995761198962269952061763 10493641798443404928092645)
        ·
          refine ⟨1967557837208138424017371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10493641798443404928092645 1967557837208138424017371)
          ·
            refine ⟨2951336755812207636026057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967557837208138424017371 2951336755812207636026057)
            ·
              refine ⟨2213502566859155727019543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951336755812207636026057 2213502566859155727019543)
              ·
                refine ⟨3320253850288733590529315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213502566859155727019543 3320253850288733590529315)
                ·
                  refine ⟨4980380775433100385793973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3320253850288733590529315 4980380775433100385793973)
                  ·
                    refine ⟨466910697696853161168185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4980380775433100385793973 466910697696853161168185)
                    ·
                      rfl

theorem cell22_1363958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1363958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363958 prefixEnd_1363958 := by exact prefixLift 1363958
  have htrace : WordTrace (prefixWord ++ tailWord_1363958) baseStart_1363958 baseEnd_1363958 := by
    simpa [prefixWord, tailWord_1363958, baseEnd_1363958] using wordTrace_append hprefix tailTrace_1363958
  have hstable : (prefixWord ++ tailWord_1363958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363958).length < 2 ^ (prefixWord ++ tailWord_1363958).sum := by decide
  have hdescent : baseEnd_1363958 < baseStart_1363958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363988 : List Nat := [2, 4, 3, 2, 1, 1, 9]
def baseStart_1363988 : Nat := 118140960795 + 1363988 * 2 ^ 59
def prefixEnd_1363988 : Nat := 4983230072969 + 3 ^ 40 * 1363988 * 2
def baseEnd_1363988 : Nat := 17293369159627521589559

theorem tailTrace_1363988 : CollatzResearch.WordTrace tailWord_1363988 prefixEnd_1363988 17293369159627521589559 := by
  unfold tailWord_1363988
  simp only [CollatzResearch.WordTrace]
  refine ⟨24874364691255950724682309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33165819588341267632909745 24874364691255950724682309)
  ·
    refine ⟨4663943379610490760877933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24874364691255950724682309 4663943379610490760877933)
    ·
      refine ⟨1748978767353934035329225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4663943379610490760877933 1748978767353934035329225)
      ·
        refine ⟨1311734075515450526496919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1748978767353934035329225 1311734075515450526496919)
        ·
          refine ⟨1967601113273175789745379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311734075515450526496919 1967601113273175789745379)
          ·
            refine ⟨2951401669909763684618069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967601113273175789745379 2951401669909763684618069)
            ·
              refine ⟨17293369159627521589559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2951401669909763684618069 17293369159627521589559)
              ·
                rfl

theorem cell22_1363988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 9].length) (baseStart_1363988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363988 prefixEnd_1363988 := by exact prefixLift 1363988
  have htrace : WordTrace (prefixWord ++ tailWord_1363988) baseStart_1363988 baseEnd_1363988 := by
    simpa [prefixWord, tailWord_1363988, baseEnd_1363988] using wordTrace_append hprefix tailTrace_1363988
  have hstable : (prefixWord ++ tailWord_1363988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363988).length < 2 ^ (prefixWord ++ tailWord_1363988).sum := by decide
  have hdescent : baseEnd_1363988 < baseStart_1363988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1363999 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 7]
def baseStart_1363999 : Nat := 118140960795 + 1363999 * 2 ^ 59
def prefixEnd_1363999 : Nat := 4983230072969 + 3 ^ 40 * 1363999 * 2
def baseEnd_1363999 : Nat := 155641577611580906964353

theorem tailTrace_1363999 : CollatzResearch.WordTrace tailWord_1363999 prefixEnd_1363999 155641577611580906964353 := by
  unfold tailWord_1363999
  simp only [CollatzResearch.WordTrace]
  refine ⟨49749130585472050328015051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33166087056981366885343367 49749130585472050328015051)
  ·
    refine ⟨74623695878208075492022577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49749130585472050328015051 74623695878208075492022577)
    ·
      refine ⟨55967771908656056619016933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74623695878208075492022577 55967771908656056619016933)
      ·
        refine ⟨10493957232873010616065675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55967771908656056619016933 10493957232873010616065675)
        ·
          refine ⟨15740935849309515924098513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10493957232873010616065675 15740935849309515924098513)
          ·
            refine ⟨11805701886982136943073885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15740935849309515924098513 11805701886982136943073885)
            ·
              refine ⟨4427138207618301353652707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11805701886982136943073885 4427138207618301353652707)
              ·
                refine ⟨6640707311427452030479061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427138207618301353652707 6640707311427452030479061)
                ·
                  refine ⟨155641577611580906964353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6640707311427452030479061 155641577611580906964353)
                  ·
                    rfl

theorem cell22_1363999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_1363999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1363999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1363999 prefixEnd_1363999 := by exact prefixLift 1363999
  have htrace : WordTrace (prefixWord ++ tailWord_1363999) baseStart_1363999 baseEnd_1363999 := by
    simpa [prefixWord, tailWord_1363999, baseEnd_1363999] using wordTrace_append hprefix tailTrace_1363999
  have hstable : (prefixWord ++ tailWord_1363999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1363999).length < 2 ^ (prefixWord ++ tailWord_1363999).sum := by decide
  have hdescent : baseEnd_1363999 < baseStart_1363999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1363999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364003 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 1, 3]
def baseStart_1364003 : Nat := 118140960795 + 1364003 * 2 ^ 59
def prefixEnd_1364003 : Nat := 4983230072969 + 3 ^ 40 * 1364003 * 2
def baseEnd_1364003 : Nat := 466926102116488043793047

theorem tailTrace_1364003 : CollatzResearch.WordTrace tailWord_1364003 prefixEnd_1364003 466926102116488043793047 := by
  unfold tailWord_1364003
  simp only [CollatzResearch.WordTrace]
  refine ⟨49749276477457559011160663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33166184318305039340773775 49749276477457559011160663)
  ·
    refine ⟨74623914716186338516740995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49749276477457559011160663 74623914716186338516740995)
    ·
      refine ⟨111935872074279507775111493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74623914716186338516740995 111935872074279507775111493)
      ·
        refine ⟨20987976013927407707833405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111935872074279507775111493 20987976013927407707833405)
        ·
          refine ⟨7870491005222777890437527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20987976013927407707833405 7870491005222777890437527)
          ·
            refine ⟨11805736507834166835656291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7870491005222777890437527 11805736507834166835656291)
            ·
              refine ⟨17708604761751250253484437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11805736507834166835656291 17708604761751250253484437)
              ·
                refine ⟨830090848207089855632083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17708604761751250253484437 830090848207089855632083)
                ·
                  refine ⟨1245136272310634783448125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830090848207089855632083 1245136272310634783448125)
                  ·
                    refine ⟨466926102116488043793047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245136272310634783448125 466926102116488043793047)
                    ·
                      rfl

theorem cell22_1364003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 3].length) (baseStart_1364003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364003 prefixEnd_1364003 := by exact prefixLift 1364003
  have htrace : WordTrace (prefixWord ++ tailWord_1364003) baseStart_1364003 baseEnd_1364003 := by
    simpa [prefixWord, tailWord_1364003, baseEnd_1364003] using wordTrace_append hprefix tailTrace_1364003
  have hstable : (prefixWord ++ tailWord_1364003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364003).length < 2 ^ (prefixWord ++ tailWord_1364003).sum := by decide
  have hdescent : baseEnd_1364003 < baseStart_1364003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364044 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_1364044 : Nat := 118140960795 + 1364044 * 2 ^ 59
def prefixEnd_1364044 : Nat := 4983230072969 + 3 ^ 40 * 1364044 * 2
def baseEnd_1364044 : Nat := 155646712418125867839307

theorem tailTrace_1364044 : CollatzResearch.WordTrace tailWord_1364044 prefixEnd_1364044 155646712418125867839307 := by
  unfold tailWord_1364044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24875385935154511506701593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33167181246872682008935457 24875385935154511506701593)
  ·
    refine ⟨18656539451365883630026195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24875385935154511506701593 18656539451365883630026195)
    ·
      refine ⟨27984809177048825445039293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18656539451365883630026195 27984809177048825445039293)
      ·
        refine ⟨10494303441393309541889735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27984809177048825445039293 10494303441393309541889735)
        ·
          refine ⟨15741455162089964312834603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10494303441393309541889735 15741455162089964312834603)
          ·
            refine ⟨23612182743134946469251905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15741455162089964312834603 23612182743134946469251905)
            ·
              refine ⟨17709137057351209851938929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23612182743134946469251905 17709137057351209851938929)
              ·
                refine ⟨13281852793013407388954197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17709137057351209851938929 13281852793013407388954197)
                ·
                  refine ⟨155646712418125867839307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13281852793013407388954197 155646712418125867839307)
                  ·
                    rfl

theorem cell22_1364044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_1364044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364044 prefixEnd_1364044 := by exact prefixLift 1364044
  have htrace : WordTrace (prefixWord ++ tailWord_1364044) baseStart_1364044 baseEnd_1364044 := by
    simpa [prefixWord, tailWord_1364044, baseEnd_1364044] using wordTrace_append hprefix tailTrace_1364044
  have hstable : (prefixWord ++ tailWord_1364044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364044).length < 2 ^ (prefixWord ++ tailWord_1364044).sum := by decide
  have hdescent : baseEnd_1364044 < baseStart_1364044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364121 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_1364121 : Nat := 118140960795 + 1364121 * 2 ^ 59
def prefixEnd_1364121 : Nat := 4983230072969 + 3 ^ 40 * 1364121 * 2
def baseEnd_1364121 : Nat := 466966495927975069342685

theorem tailTrace_1364121 : CollatzResearch.WordTrace tailWord_1364121 prefixEnd_1364121 466966495927975069342685 := by
  unfold tailWord_1364121
  simp only [CollatzResearch.WordTrace]
  refine ⟨49753580291030065163956217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33169053527353376775970811 49753580291030065163956217)
  ·
    refine ⟨37315185218272548872967163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49753580291030065163956217 37315185218272548872967163)
    ·
      refine ⟨55972777827408823309450745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37315185218272548872967163 55972777827408823309450745)
      ·
        refine ⟨41979583370556617482088059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55972777827408823309450745 41979583370556617482088059)
        ·
          refine ⟨62969375055834926223132089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41979583370556617482088059 62969375055834926223132089)
          ·
            refine ⟨47227031291876194667349067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62969375055834926223132089 47227031291876194667349067)
            ·
              refine ⟨70840546937814292001023601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47227031291876194667349067 70840546937814292001023601)
              ·
                refine ⟨53130410203360719000767701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70840546937814292001023601 53130410203360719000767701)
                ·
                  refine ⟨1245243989141266851580493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53130410203360719000767701 1245243989141266851580493)
                  ·
                    refine ⟨466966495927975069342685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245243989141266851580493 466966495927975069342685)
                    ·
                      rfl

theorem cell22_1364121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_1364121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364121 prefixEnd_1364121 := by exact prefixLift 1364121
  have htrace : WordTrace (prefixWord ++ tailWord_1364121) baseStart_1364121 baseEnd_1364121 := by
    simpa [prefixWord, tailWord_1364121, baseEnd_1364121] using wordTrace_append hprefix tailTrace_1364121
  have hstable : (prefixWord ++ tailWord_1364121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364121).length < 2 ^ (prefixWord ++ tailWord_1364121).sum := by decide
  have hdescent : baseEnd_1364121 < baseStart_1364121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364148 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1364148 : Nat := 118140960795 + 1364148 * 2 ^ 59
def prefixEnd_1364148 : Nat := 4983230072969 + 3 ^ 40 * 1364148 * 2
def baseEnd_1364148 : Nat := 466975738579755998917603

theorem tailTrace_1364148 : CollatzResearch.WordTrace tailWord_1364148 prefixEnd_1364148 466975738579755998917603 := by
  unfold tailWord_1364148
  simp only [CollatzResearch.WordTrace]
  refine ⟨24877282530966124387594549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33169710041288165850126065 24877282530966124387594549)
  ·
    refine ⟨2332245237278074161336989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24877282530966124387594549 2332245237278074161336989)
    ·
      refine ⟨874591963979277810501371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2332245237278074161336989 874591963979277810501371)
      ·
        refine ⟨1311887945968916715752057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874591963979277810501371 1311887945968916715752057)
        ·
          refine ⟨983915959476687536814043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311887945968916715752057 983915959476687536814043)
          ·
            refine ⟨1475873939215031305221065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983915959476687536814043 1475873939215031305221065)
            ·
              refine ⟨1106905454411273478915799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475873939215031305221065 1106905454411273478915799)
              ·
                refine ⟨1660358181616910218373699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106905454411273478915799 1660358181616910218373699)
                ·
                  refine ⟨2490537272425365327560549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660358181616910218373699 2490537272425365327560549)
                  ·
                    refine ⟨466975738579755998917603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490537272425365327560549 466975738579755998917603)
                    ·
                      rfl

theorem cell22_1364148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1364148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364148 prefixEnd_1364148 := by exact prefixLift 1364148
  have htrace : WordTrace (prefixWord ++ tailWord_1364148) baseStart_1364148 baseEnd_1364148 := by
    simpa [prefixWord, tailWord_1364148, baseEnd_1364148] using wordTrace_append hprefix tailTrace_1364148
  have hstable : (prefixWord ++ tailWord_1364148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364148).length < 2 ^ (prefixWord ++ tailWord_1364148).sum := by decide
  have hdescent : baseEnd_1364148 < baseStart_1364148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364155 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 1, 3]
def baseStart_1364155 : Nat := 118140960795 + 1364155 * 2 ^ 59
def prefixEnd_1364155 : Nat := 4983230072969 + 3 ^ 40 * 1364155 * 2
def baseEnd_1364155 : Nat := 466978134822810313992581

theorem tailTrace_1364155 : CollatzResearch.WordTrace tailWord_1364155 prefixEnd_1364155 466978134822810313992581 := by
  unfold tailWord_1364155
  simp only [CollatzResearch.WordTrace]
  refine ⟨49754820372906888970693919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33169880248604592647129279 49754820372906888970693919)
  ·
    refine ⟨74632230559360333456040879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49754820372906888970693919 74632230559360333456040879)
    ·
      refine ⟨111948345839040500184061319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74632230559360333456040879 111948345839040500184061319)
      ·
        refine ⟨167922518758560750276091979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111948345839040500184061319 167922518758560750276091979)
        ·
          refine ⟨251883778137841125414137969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167922518758560750276091979 251883778137841125414137969)
          ·
            refine ⟨188912833603380844060603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251883778137841125414137969 188912833603380844060603477)
            ·
              refine ⟨2213822268789619266335197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 188912833603380844060603477 2213822268789619266335197)
              ·
                refine ⟨830183350796107224875699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2213822268789619266335197 830183350796107224875699)
                ·
                  refine ⟨1245275026194160837313549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830183350796107224875699 1245275026194160837313549)
                  ·
                    refine ⟨466978134822810313992581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245275026194160837313549 466978134822810313992581)
                    ·
                      rfl

theorem cell22_1364155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 3].length) (baseStart_1364155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364155 prefixEnd_1364155 := by exact prefixLift 1364155
  have htrace : WordTrace (prefixWord ++ tailWord_1364155) baseStart_1364155 baseEnd_1364155 := by
    simpa [prefixWord, tailWord_1364155, baseEnd_1364155] using wordTrace_append hprefix tailTrace_1364155
  have hstable : (prefixWord ++ tailWord_1364155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364155).length < 2 ^ (prefixWord ++ tailWord_1364155).sum := by decide
  have hdescent : baseEnd_1364155 < baseStart_1364155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364172 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1364172 : Nat := 118140960795 + 1364172 * 2 ^ 59
def prefixEnd_1364172 : Nat := 4983230072969 + 3 ^ 40 * 1364172 * 2
def baseEnd_1364172 : Nat := 466983954270227936317529

theorem tailTrace_1364172 : CollatzResearch.WordTrace tailWord_1364172 prefixEnd_1364172 466983954270227936317529 := by
  unfold tailWord_1364172
  simp only [CollatzResearch.WordTrace]
  refine ⟨24877720206922650437031385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33170293609230200582708513 24877720206922650437031385)
  ·
    refine ⟨18658290155191987827773539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24877720206922650437031385 18658290155191987827773539)
    ·
      refine ⟨27987435232787981741660309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18658290155191987827773539 27987435232787981741660309)
      ·
        refine ⟨1311911026536936644140327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27987435232787981741660309 1311911026536936644140327)
        ·
          refine ⟨1967866539805404966210491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311911026536936644140327 1967866539805404966210491)
          ·
            refine ⟨2951799809708107449315737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967866539805404966210491 2951799809708107449315737)
            ·
              refine ⟨2213849857281080586986803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951799809708107449315737 2213849857281080586986803)
              ·
                refine ⟨3320774785921620880480205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213849857281080586986803 3320774785921620880480205)
                ·
                  refine ⟨1245290544720607830180077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3320774785921620880480205 1245290544720607830180077)
                  ·
                    refine ⟨466983954270227936317529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245290544720607830180077 466983954270227936317529)
                    ·
                      rfl

theorem cell22_1364172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1364172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364172 prefixEnd_1364172 := by exact prefixLift 1364172
  have htrace : WordTrace (prefixWord ++ tailWord_1364172) baseStart_1364172 baseEnd_1364172 := by
    simpa [prefixWord, tailWord_1364172, baseEnd_1364172] using wordTrace_append hprefix tailTrace_1364172
  have hstable : (prefixWord ++ tailWord_1364172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364172).length < 2 ^ (prefixWord ++ tailWord_1364172).sum := by decide
  have hdescent : baseEnd_1364172 < baseStart_1364172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364211 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_1364211 : Nat := 118140960795 + 1364211 * 2 ^ 59
def prefixEnd_1364211 : Nat := 4983230072969 + 3 ^ 40 * 1364211 * 2
def baseEnd_1364211 : Nat := 466997304767244834592409

theorem tailTrace_1364211 : CollatzResearch.WordTrace tailWord_1364211 prefixEnd_1364211 466997304767244834592409 := by
  unfold tailWord_1364211
  simp only [CollatzResearch.WordTrace]
  refine ⟨49756862860704010534732487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33171241907136007023154991 49756862860704010534732487)
  ·
    refine ⟨74635294291056015802098731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49756862860704010534732487 74635294291056015802098731)
    ·
      refine ⟨111952941436584023703148097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74635294291056015802098731 111952941436584023703148097)
      ·
        refine ⟨83964706077438017777361073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111952941436584023703148097 83964706077438017777361073)
        ·
          refine ⟨62973529558078513333020805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83964706077438017777361073 62973529558078513333020805)
          ·
            refine ⟨11807536792139721249941401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62973529558078513333020805 11807536792139721249941401)
            ·
              refine ⟨8855652594104790937456051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11807536792139721249941401 8855652594104790937456051)
              ·
                refine ⟨13283478891157186406184077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8855652594104790937456051 13283478891157186406184077)
                ·
                  refine ⟨4981304584183944902319029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13283478891157186406184077 4981304584183944902319029)
                  ·
                    refine ⟨466997304767244834592409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4981304584183944902319029 466997304767244834592409)
                    ·
                      rfl

theorem cell22_1364211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_1364211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364211 prefixEnd_1364211 := by exact prefixLift 1364211
  have htrace : WordTrace (prefixWord ++ tailWord_1364211) baseStart_1364211 baseEnd_1364211 := by
    simpa [prefixWord, tailWord_1364211, baseEnd_1364211] using wordTrace_append hprefix tailTrace_1364211
  have hstable : (prefixWord ++ tailWord_1364211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364211).length < 2 ^ (prefixWord ++ tailWord_1364211).sum := by decide
  have hdescent : baseEnd_1364211 < baseStart_1364211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364241 : List Nat := [1, 2, 2, 1, 1, 5, 1, 9]
def baseStart_1364241 : Nat := 118140960795 + 1364241 * 2 ^ 59
def prefixEnd_1364241 : Nat := 4983230072969 + 3 ^ 40 * 1364241 * 2
def baseEnd_1364241 : Nat := 51889730486703861815813

theorem tailTrace_1364241 : CollatzResearch.WordTrace tailWord_1364241 prefixEnd_1364241 51889730486703861815813 := by
  unfold tailWord_1364241
  simp only [CollatzResearch.WordTrace]
  refine ⟨49757957050595325658324577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33171971367063550438883051 49757957050595325658324577)
  ·
    refine ⟨37318467787946494243743433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49757957050595325658324577 37318467787946494243743433)
    ·
      refine ⟨27988850840959870682807575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37318467787946494243743433 27988850840959870682807575)
      ·
        refine ⟨41983276261439806024211363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27988850840959870682807575 41983276261439806024211363)
        ·
          refine ⟨62974914392159709036317045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41983276261439806024211363 62974914392159709036317045)
          ·
            refine ⟨5903898224264972722154723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62974914392159709036317045 5903898224264972722154723)
            ·
              refine ⟨8855847336397459083232085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903898224264972722154723 8855847336397459083232085)
              ·
                refine ⟨51889730486703861815813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8855847336397459083232085 51889730486703861815813)
                ·
                  rfl

theorem cell22_1364241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 9].length) (baseStart_1364241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364241 prefixEnd_1364241 := by exact prefixLift 1364241
  have htrace : WordTrace (prefixWord ++ tailWord_1364241) baseStart_1364241 baseEnd_1364241 := by
    simpa [prefixWord, tailWord_1364241, baseEnd_1364241] using wordTrace_append hprefix tailTrace_1364241
  have hstable : (prefixWord ++ tailWord_1364241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364241).length < 2 ^ (prefixWord ++ tailWord_1364241).sum := by decide
  have hdescent : baseEnd_1364241 < baseStart_1364241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364258 : List Nat := [3, 3, 1, 1, 3, 1, 2, 8]
def baseStart_1364258 : Nat := 118140960795 + 1364258 * 2 ^ 59
def prefixEnd_1364258 : Nat := 4983230072969 + 3 ^ 40 * 1364258 * 2
def baseEnd_1364258 : Nat := 51890377091972486518585

theorem tailTrace_1364258 : CollatzResearch.WordTrace tailWord_1364258 prefixEnd_1364258 51890377091972486518585 := by
  unfold tailWord_1364258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439644272883434390423357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33172384727689158374462285 12439644272883434390423357)
  ·
    refine ⟨4664866602331287896408759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12439644272883434390423357 4664866602331287896408759)
    ·
      refine ⟨6997299903496931844613139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664866602331287896408759 6997299903496931844613139)
      ·
        refine ⟨10495949855245397766919709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6997299903496931844613139 10495949855245397766919709)
        ·
          refine ⟨3935981195717024162594891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10495949855245397766919709 3935981195717024162594891)
          ·
            refine ⟨5903971793575536243892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935981195717024162594891 5903971793575536243892337)
            ·
              refine ⟨4427978845181652182919253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5903971793575536243892337 4427978845181652182919253)
              ·
                refine ⟨51890377091972486518585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4427978845181652182919253 51890377091972486518585)
                ·
                  rfl

theorem cell22_1364258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_1364258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364258 prefixEnd_1364258 := by exact prefixLift 1364258
  have htrace : WordTrace (prefixWord ++ tailWord_1364258) baseStart_1364258 baseEnd_1364258 := by
    simpa [prefixWord, tailWord_1364258, baseEnd_1364258] using wordTrace_append hprefix tailTrace_1364258
  have hstable : (prefixWord ++ tailWord_1364258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364258).length < 2 ^ (prefixWord ++ tailWord_1364258).sum := by decide
  have hdescent : baseEnd_1364258 < baseStart_1364258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364260 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_1364260 : Nat := 118140960795 + 1364260 * 2 ^ 59
def prefixEnd_1364260 : Nat := 4983230072969 + 3 ^ 40 * 1364260 * 2
def baseEnd_1364260 : Nat := 467014078468625040117259

theorem tailTrace_1364260 : CollatzResearch.WordTrace tailWord_1364260 prefixEnd_1364260 467014078468625040117259 := by
  unfold tailWord_1364260
  simp only [CollatzResearch.WordTrace]
  refine ⟨24879325018763245951633117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33172433358350994602177489 24879325018763245951633117)
  ·
    refine ⟨9329746882036217231862419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24879325018763245951633117 9329746882036217231862419)
    ·
      refine ⟨13994620323054325847793629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9329746882036217231862419 13994620323054325847793629)
      ·
        refine ⟨5247982621145372192922611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13994620323054325847793629 5247982621145372192922611)
        ·
          refine ⟨7871973931718058289383917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247982621145372192922611 7871973931718058289383917)
          ·
            refine ⟨2951990224394271858518969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7871973931718058289383917 2951990224394271858518969)
            ·
              refine ⟨2213992668295703893889227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2951990224394271858518969 2213992668295703893889227)
              ·
                refine ⟨3320989002443555840833841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213992668295703893889227 3320989002443555840833841)
                ·
                  refine ⟨2490741751832666880625381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3320989002443555840833841 2490741751832666880625381)
                  ·
                    refine ⟨467014078468625040117259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2490741751832666880625381 467014078468625040117259)
                    ·
                      rfl

theorem cell22_1364260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_1364260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364260 prefixEnd_1364260 := by exact prefixLift 1364260
  have htrace : WordTrace (prefixWord ++ tailWord_1364260) baseStart_1364260 baseEnd_1364260 := by
    simpa [prefixWord, tailWord_1364260, baseEnd_1364260] using wordTrace_append hprefix tailTrace_1364260
  have hstable : (prefixWord ++ tailWord_1364260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364260).length < 2 ^ (prefixWord ++ tailWord_1364260).sum := by decide
  have hdescent : baseEnd_1364260 < baseStart_1364260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364292 : List Nat := [2, 3, 4, 1, 2, 2, 1, 7]
def baseStart_1364292 : Nat := 118140960795 + 1364292 * 2 ^ 59
def prefixEnd_1364292 : Nat := 4983230072969 + 3 ^ 40 * 1364292 * 2
def baseEnd_1364292 : Nat := 51891670302509735924129

theorem tailTrace_1364292 : CollatzResearch.WordTrace tailWord_1364292 prefixEnd_1364292 51891670302509735924129 := by
  unfold tailWord_1364292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24879908586705280684215565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33173211448940374245620753 24879908586705280684215565)
  ·
    refine ⟨9329965720014480256580837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24879908586705280684215565 9329965720014480256580837)
    ·
      refine ⟨1749368572502715048108907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9329965720014480256580837 1749368572502715048108907)
      ·
        refine ⟨2624052858754072572163361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749368572502715048108907 2624052858754072572163361)
        ·
          refine ⟨1968039644065554429122521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2624052858754072572163361 1968039644065554429122521)
          ·
            refine ⟨1476029733049165821841891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968039644065554429122521 1476029733049165821841891)
            ·
              refine ⟨2214044599573748732762837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476029733049165821841891 2214044599573748732762837)
              ·
                refine ⟨51891670302509735924129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2214044599573748732762837 51891670302509735924129)
                ·
                  rfl

theorem cell22_1364292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_1364292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364292 prefixEnd_1364292 := by exact prefixLift 1364292
  have htrace : WordTrace (prefixWord ++ tailWord_1364292) baseStart_1364292 baseEnd_1364292 := by
    simpa [prefixWord, tailWord_1364292, baseEnd_1364292] using wordTrace_append hprefix tailTrace_1364292
  have hstable : (prefixWord ++ tailWord_1364292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364292).length < 2 ^ (prefixWord ++ tailWord_1364292).sum := by decide
  have hdescent : baseEnd_1364292 < baseStart_1364292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364414 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1364414 : Nat := 118140960795 + 1364414 * 2 ^ 59
def prefixEnd_1364414 : Nat := 4983230072969 + 3 ^ 40 * 1364414 * 2
def baseEnd_1364414 : Nat := 467066795815819971766787

theorem tailTrace_1364414 : CollatzResearch.WordTrace tailWord_1364414 prefixEnd_1364414 467066795815819971766787 := by
  unfold tailWord_1364414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220533359871072025546537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33176177919312384136248197 6220533359871072025546537)
  ·
    refine ⟨4665400019903304019159903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6220533359871072025546537 4665400019903304019159903)
    ·
      refine ⟨6998100029854956028739855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665400019903304019159903 6998100029854956028739855)
      ·
        refine ⟨10497150044782434043109783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998100029854956028739855 10497150044782434043109783)
        ·
          refine ⟨15745725067173651064664675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10497150044782434043109783 15745725067173651064664675)
          ·
            refine ⟨23618587600760476596997013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15745725067173651064664675 23618587600760476596997013)
            ·
              refine ⟨1107121293785647340484235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23618587600760476596997013 1107121293785647340484235)
              ·
                refine ⟨1660681940678471010726353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107121293785647340484235 1660681940678471010726353)
                ·
                  refine ⟨1245511455508853258044765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1660681940678471010726353 1245511455508853258044765)
                  ·
                    refine ⟨467066795815819971766787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245511455508853258044765 467066795815819971766787)
                    ·
                      rfl

theorem cell22_1364414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1364414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364414 prefixEnd_1364414 := by exact prefixLift 1364414
  have htrace : WordTrace (prefixWord ++ tailWord_1364414) baseStart_1364414 baseEnd_1364414 := by
    simpa [prefixWord, tailWord_1364414, baseEnd_1364414] using wordTrace_append hprefix tailTrace_1364414
  have hstable : (prefixWord ++ tailWord_1364414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364414).length < 2 ^ (prefixWord ++ tailWord_1364414).sum := by decide
  have hdescent : baseEnd_1364414 < baseStart_1364414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364425 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_1364425 : Nat := 118140960795 + 1364425 * 2 ^ 59
def prefixEnd_1364425 : Nat := 4983230072969 + 3 ^ 40 * 1364425 * 2
def baseEnd_1364425 : Nat := 467070561340619609741753

theorem tailTrace_1364425 : CollatzResearch.WordTrace tailWord_1364425 prefixEnd_1364425 467070561340619609741753 := by
  unfold tailWord_1364425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49764668081928725083022729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33176445387952483388681819 49764668081928725083022729)
  ·
    refine ⟨37323501061446543812267047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49764668081928725083022729 37323501061446543812267047)
    ·
      refine ⟨55985251592169815718400571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37323501061446543812267047 55985251592169815718400571)
      ·
        refine ⟨83977877388254723577600857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55985251592169815718400571 83977877388254723577600857)
        ·
          refine ⟨62983408041191042683200643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83977877388254723577600857 62983408041191042683200643)
          ·
            refine ⟨94475112061786564024800965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62983408041191042683200643 94475112061786564024800965)
            ·
              refine ⟨17714083511584980754650181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94475112061786564024800965 17714083511584980754650181)
              ·
                refine ⟨3321390658422183891496909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17714083511584980754650181 3321390658422183891496909)
                ·
                  refine ⟨1245521496908318959311341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3321390658422183891496909 1245521496908318959311341)
                  ·
                    refine ⟨467070561340619609741753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245521496908318959311341 467070561340619609741753)
                    ·
                      rfl

theorem cell22_1364425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_1364425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364425 prefixEnd_1364425 := by exact prefixLift 1364425
  have htrace : WordTrace (prefixWord ++ tailWord_1364425) baseStart_1364425 baseEnd_1364425 := by
    simpa [prefixWord, tailWord_1364425, baseEnd_1364425] using wordTrace_append hprefix tailTrace_1364425
  have hstable : (prefixWord ++ tailWord_1364425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364425).length < 2 ^ (prefixWord ++ tailWord_1364425).sum := by decide
  have hdescent : baseEnd_1364425 < baseStart_1364425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364450 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1364450 : Nat := 118140960795 + 1364450 * 2 ^ 59
def prefixEnd_1364450 : Nat := 4983230072969 + 3 ^ 40 * 1364450 * 2
def baseEnd_1364450 : Nat := 155693039783842625955559

theorem tailTrace_1364450 : CollatzResearch.WordTrace tailWord_1364450 prefixEnd_1364450 155693039783842625955559 := by
  unfold tailWord_1364450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441394976709538588170701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33177053271225436235121869 12441394976709538588170701)
  ·
    refine ⟨4665523116266076970564013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12441394976709538588170701 4665523116266076970564013)
    ·
      refine ⟨1749571168599778863961505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4665523116266076970564013 1749571168599778863961505)
      ·
        refine ⟨1312178376449834147971129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749571168599778863961505 1312178376449834147971129)
        ·
          refine ⟨984133782337375610978347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312178376449834147971129 984133782337375610978347)
          ·
            refine ⟨1476200673506063416467521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984133782337375610978347 1476200673506063416467521)
            ·
              refine ⟨1107150505129547562350641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476200673506063416467521 1107150505129547562350641)
              ·
                refine ⟨830362878847160671762981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107150505129547562350641 830362878847160671762981)
                ·
                  refine ⟨155693039783842625955559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830362878847160671762981 155693039783842625955559)
                  ·
                    rfl

theorem cell22_1364450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1364450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364450 prefixEnd_1364450 := by exact prefixLift 1364450
  have htrace : WordTrace (prefixWord ++ tailWord_1364450) baseStart_1364450 baseEnd_1364450 := by
    simpa [prefixWord, tailWord_1364450, baseEnd_1364450] using wordTrace_append hprefix tailTrace_1364450
  have hstable : (prefixWord ++ tailWord_1364450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364450).length < 2 ^ (prefixWord ++ tailWord_1364450).sum := by decide
  have hdescent : baseEnd_1364450 < baseStart_1364450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364485 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1364485 : Nat := 118140960795 + 1364485 * 2 ^ 59
def prefixEnd_1364485 : Nat := 4983230072969 + 3 ^ 40 * 1364485 * 2
def baseEnd_1364485 : Nat := 467091100566799453241569

theorem tailTrace_1364485 : CollatzResearch.WordTrace tailWord_1364485 prefixEnd_1364485 467091100566799453241569 := by
  unfold tailWord_1364485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49766856461711355330206909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33177904307807570220137939 49766856461711355330206909)
  ·
    refine ⟨18662571173141758248827591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49766856461711355330206909 18662571173141758248827591)
    ·
      refine ⟨27993856759712637373241387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18662571173141758248827591 27993856759712637373241387)
      ·
        refine ⟨41990785139568956059862081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27993856759712637373241387 41990785139568956059862081)
        ·
          refine ⟨31493088854676717044896561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41990785139568956059862081 31493088854676717044896561)
          ·
            refine ⟨23619816641007537783672421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31493088854676717044896561 23619816641007537783672421)
            ·
              refine ⟨4428715620188913334438579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23619816641007537783672421 4428715620188913334438579)
              ·
                refine ⟨6643073430283370001657869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428715620188913334438579 6643073430283370001657869)
                ·
                  refine ⟨2491152536356263750621701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6643073430283370001657869 2491152536356263750621701)
                  ·
                    refine ⟨467091100566799453241569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491152536356263750621701 467091100566799453241569)
                    ·
                      rfl

theorem cell22_1364485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1364485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364485 prefixEnd_1364485 := by exact prefixLift 1364485
  have htrace : WordTrace (prefixWord ++ tailWord_1364485) baseStart_1364485 baseEnd_1364485 := by
    simpa [prefixWord, tailWord_1364485, baseEnd_1364485] using wordTrace_append hprefix tailTrace_1364485
  have hstable : (prefixWord ++ tailWord_1364485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364485).length < 2 ^ (prefixWord ++ tailWord_1364485).sum := by decide
  have hdescent : baseEnd_1364485 < baseStart_1364485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364493 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1364493 : Nat := 118140960795 + 1364493 * 2 ^ 59
def prefixEnd_1364493 : Nat := 4983230072969 + 3 ^ 40 * 1364493 * 2
def baseEnd_1364493 : Nat := 467093839130290099041545

theorem tailTrace_1364493 : CollatzResearch.WordTrace tailWord_1364493 prefixEnd_1364493 467093839130290099041545 := by
  unfold tailWord_1364493
  simp only [CollatzResearch.WordTrace]
  refine ⟨49767148245682372696498133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33178098830454915130998755 49767148245682372696498133)
  ·
    refine ⟨1166417537008180610074175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49767148245682372696498133 1166417537008180610074175)
    ·
      refine ⟨1749626305512270915111263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166417537008180610074175 1749626305512270915111263)
      ·
        refine ⟨2624439458268406372666895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749626305512270915111263 2624439458268406372666895)
        ·
          refine ⟨3936659187402609559000343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624439458268406372666895 3936659187402609559000343)
          ·
            refine ⟨5904988781103914338500515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936659187402609559000343 5904988781103914338500515)
            ·
              refine ⟨8857483171655871507750773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904988781103914338500515 8857483171655871507750773)
              ·
                refine ⟨830389047342737953851635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8857483171655871507750773 830389047342737953851635)
                ·
                  refine ⟨1245583571014106930777453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830389047342737953851635 1245583571014106930777453)
                  ·
                    refine ⟨467093839130290099041545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245583571014106930777453 467093839130290099041545)
                    ·
                      rfl

theorem cell22_1364493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1364493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364493 prefixEnd_1364493 := by exact prefixLift 1364493
  have htrace : WordTrace (prefixWord ++ tailWord_1364493) baseStart_1364493 baseEnd_1364493 := by
    simpa [prefixWord, tailWord_1364493, baseEnd_1364493] using wordTrace_append hprefix tailTrace_1364493
  have hstable : (prefixWord ++ tailWord_1364493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364493).length < 2 ^ (prefixWord ++ tailWord_1364493).sum := by decide
  have hdescent : baseEnd_1364493 < baseStart_1364493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364517 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 4]
def baseStart_1364517 : Nat := 118140960795 + 1364517 * 2 ^ 59
def prefixEnd_1364517 : Nat := 4983230072969 + 3 ^ 40 * 1364517 * 2
def baseEnd_1364517 : Nat := 155700684940254012147157

theorem tailTrace_1364517 : CollatzResearch.WordTrace tailWord_1364517 prefixEnd_1364517 155700684940254012147157 := by
  unfold tailWord_1364517
  simp only [CollatzResearch.WordTrace]
  refine ⟨49768023597595424795371805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33178682398396949863581203 49768023597595424795371805)
  ·
    refine ⟨18663008849098284298264427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49768023597595424795371805 18663008849098284298264427)
    ·
      refine ⟨27994513273647426447396641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18663008849098284298264427 27994513273647426447396641)
      ·
        refine ⟨20995884955235569835547481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27994513273647426447396641 20995884955235569835547481)
        ·
          refine ⟨15746913716426677376660611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20995884955235569835547481 15746913716426677376660611)
          ·
            refine ⟨23620370574640016064990917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15746913716426677376660611 23620370574640016064990917)
            ·
              refine ⟨4428819482745003012185797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23620370574640016064990917 4428819482745003012185797)
              ·
                refine ⟨830403653014688064784837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4428819482745003012185797 830403653014688064784837)
                ·
                  refine ⟨155700684940254012147157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830403653014688064784837 155700684940254012147157)
                  ·
                    rfl

theorem cell22_1364517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_1364517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364517 prefixEnd_1364517 := by exact prefixLift 1364517
  have htrace : WordTrace (prefixWord ++ tailWord_1364517) baseStart_1364517 baseEnd_1364517 := by
    simpa [prefixWord, tailWord_1364517, baseEnd_1364517] using wordTrace_append hprefix tailTrace_1364517
  have hstable : (prefixWord ++ tailWord_1364517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364517).length < 2 ^ (prefixWord ++ tailWord_1364517).sum := by decide
  have hdescent : baseEnd_1364517 < baseStart_1364517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364530 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1364530 : Nat := 118140960795 + 1364530 * 2 ^ 59
def prefixEnd_1364530 : Nat := 4983230072969 + 3 ^ 40 * 1364530 * 2
def baseEnd_1364530 : Nat := 467106504986434335866431

theorem tailTrace_1364530 : CollatzResearch.WordTrace tailWord_1364530 prefixEnd_1364530 467106504986434335866431 := by
  unfold tailWord_1364530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442124436637082003898761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33178998497698885343730029 12442124436637082003898761)
  ·
    refine ⟨9331593327477811502924071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12442124436637082003898761 9331593327477811502924071)
    ·
      refine ⟨13997389991216717254386107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9331593327477811502924071 13997389991216717254386107)
      ·
        refine ⟨20996084986825075881579161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13997389991216717254386107 20996084986825075881579161)
        ·
          refine ⟨15747063740118806911184371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20996084986825075881579161 15747063740118806911184371)
          ·
            refine ⟨23620595610178210366776557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747063740118806911184371 23620595610178210366776557)
            ·
              refine ⟨8857723353816828887541209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23620595610178210366776557 8857723353816828887541209)
              ·
                refine ⟨6643292515362621665655907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8857723353816828887541209 6643292515362621665655907)
                ·
                  refine ⟨9964938773043932498483861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6643292515362621665655907 9964938773043932498483861)
                  ·
                    refine ⟨467106504986434335866431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9964938773043932498483861 467106504986434335866431)
                    ·
                      rfl

theorem cell22_1364530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1364530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364530 prefixEnd_1364530 := by exact prefixLift 1364530
  have htrace : WordTrace (prefixWord ++ tailWord_1364530) baseStart_1364530 baseEnd_1364530 := by
    simpa [prefixWord, tailWord_1364530, baseEnd_1364530] using wordTrace_append hprefix tailTrace_1364530
  have hstable : (prefixWord ++ tailWord_1364530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364530).length < 2 ^ (prefixWord ++ tailWord_1364530).sum := by decide
  have hdescent : baseEnd_1364530 < baseStart_1364530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364622 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1364622 : Nat := 118140960795 + 1364622 * 2 ^ 59
def prefixEnd_1364622 : Nat := 4983230072969 + 3 ^ 40 * 1364622 * 2
def baseEnd_1364622 : Nat := 467137998466576762566149

theorem tailTrace_1364622 : CollatzResearch.WordTrace tailWord_1364622 prefixEnd_1364622 467137998466576762566149 := by
  unfold tailWord_1364622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221481657776878465993015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33181235508143351818629413 6221481657776878465993015)
  ·
    refine ⟨9332222486665317698989523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6221481657776878465993015 9332222486665317698989523)
    ·
      refine ⟨13998333729997976548484285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9332222486665317698989523 13998333729997976548484285)
      ·
        refine ⟨5249375148749241205681607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13998333729997976548484285 5249375148749241205681607)
        ·
          refine ⟨7874062723123861808522411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5249375148749241205681607 7874062723123861808522411)
          ·
            refine ⟨11811094084685792712783617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7874062723123861808522411 11811094084685792712783617)
            ·
              refine ⟨8858320563514344534587713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11811094084685792712783617 8858320563514344534587713)
              ·
                refine ⟨6643740422635758400940785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8858320563514344534587713 6643740422635758400940785)
                ·
                  refine ⟨4982805316976818800705589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643740422635758400940785 4982805316976818800705589)
                  ·
                    refine ⟨467137998466576762566149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4982805316976818800705589 467137998466576762566149)
                    ·
                      rfl

theorem cell22_1364622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1364622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364622 prefixEnd_1364622 := by exact prefixLift 1364622
  have htrace : WordTrace (prefixWord ++ tailWord_1364622) baseStart_1364622 baseEnd_1364622 := by
    simpa [prefixWord, tailWord_1364622, baseEnd_1364622] using wordTrace_append hprefix tailTrace_1364622
  have hstable : (prefixWord ++ tailWord_1364622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364622).length < 2 ^ (prefixWord ++ tailWord_1364622).sum := by decide
  have hdescent : baseEnd_1364622 < baseStart_1364622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364628 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1364628 : Nat := 118140960795 + 1364628 * 2 ^ 59
def prefixEnd_1364628 : Nat := 4983230072969 + 3 ^ 40 * 1364628 * 2
def baseEnd_1364628 : Nat := 467140052389194746916131

theorem tailTrace_1364628 : CollatzResearch.WordTrace tailWord_1364628 prefixEnd_1364628 467140052389194746916131 := by
  unfold tailWord_1364628
  simp only [CollatzResearch.WordTrace]
  refine ⟨24886036050096645376331269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33181381400128860501775025 24886036050096645376331269)
  ·
    refine ⟨4666131759393121008062113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24886036050096645376331269 4666131759393121008062113)
    ·
      refine ⟨3499598819544840756046585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4666131759393121008062113 3499598819544840756046585)
      ·
        refine ⟨2624699114658630567034939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3499598819544840756046585 2624699114658630567034939)
        ·
          refine ⟨3937048671987945850552409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624699114658630567034939 3937048671987945850552409)
          ·
            refine ⟨2952786503990959387914307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3937048671987945850552409 2952786503990959387914307)
            ·
              refine ⟨4429179755986439081871461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952786503990959387914307 4429179755986439081871461)
              ·
                refine ⟨830471204247457327850899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4429179755986439081871461 830471204247457327850899)
                ·
                  refine ⟨1245706806371185991776349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830471204247457327850899 1245706806371185991776349)
                  ·
                    refine ⟨467140052389194746916131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245706806371185991776349 467140052389194746916131)
                    ·
                      rfl

theorem cell22_1364628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1364628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364628 prefixEnd_1364628 := by exact prefixLift 1364628
  have htrace : WordTrace (prefixWord ++ tailWord_1364628) baseStart_1364628 baseEnd_1364628 := by
    simpa [prefixWord, tailWord_1364628, baseEnd_1364628] using wordTrace_append hprefix tailTrace_1364628
  have hstable : (prefixWord ++ tailWord_1364628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364628).length < 2 ^ (prefixWord ++ tailWord_1364628).sum := by decide
  have hdescent : baseEnd_1364628 < baseStart_1364628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364637 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1364637 : Nat := 118140960795 + 1364637 * 2 ^ 59
def prefixEnd_1364637 : Nat := 4983230072969 + 3 ^ 40 * 1364637 * 2
def baseEnd_1364637 : Nat := 467143133273121723441103

theorem tailTrace_1364637 : CollatzResearch.WordTrace tailWord_1364637 prefixEnd_1364637 467143133273121723441103 := by
  unfold tailWord_1364637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49772400357160685289740165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33181600238107123526493443 49772400357160685289740165)
  ·
    refine ⟨9332325066967628491826281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49772400357160685289740165 9332325066967628491826281)
    ·
      refine ⟨6999243800225721368869711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9332325066967628491826281 6999243800225721368869711)
      ·
        refine ⟨10498865700338582053304567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999243800225721368869711 10498865700338582053304567)
        ·
          refine ⟨15748298550507873079956851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498865700338582053304567 15748298550507873079956851)
          ·
            refine ⟨23622447825761809619935277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15748298550507873079956851 23622447825761809619935277)
            ·
              refine ⟨8858417934660678607475729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23622447825761809619935277 8858417934660678607475729)
              ·
                refine ⟨6643813450995508955606797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8858417934660678607475729 6643813450995508955606797)
                ·
                  refine ⟨2491430044123315858352549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6643813450995508955606797 2491430044123315858352549)
                  ·
                    refine ⟨467143133273121723441103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491430044123315858352549 467143133273121723441103)
                    ·
                      rfl

theorem cell22_1364637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1364637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364637 prefixEnd_1364637 := by exact prefixLift 1364637
  have htrace : WordTrace (prefixWord ++ tailWord_1364637) baseStart_1364637 baseEnd_1364637 := by
    simpa [prefixWord, tailWord_1364637, baseEnd_1364637] using wordTrace_append hprefix tailTrace_1364637
  have hstable : (prefixWord ++ tailWord_1364637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364637).length < 2 ^ (prefixWord ++ tailWord_1364637).sum := by decide
  have hdescent : baseEnd_1364637 < baseStart_1364637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364669 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 4]
def baseStart_1364669 : Nat := 118140960795 + 1364669 * 2 ^ 59
def prefixEnd_1364669 : Nat := 4983230072969 + 3 ^ 40 * 1364669 * 2
def baseEnd_1364669 : Nat := 155718029175694768880335

theorem tailTrace_1364669 : CollatzResearch.WordTrace tailWord_1364669 prefixEnd_1364669 155718029175694768880335 := by
  unfold tailWord_1364669
  simp only [CollatzResearch.WordTrace]
  refine ⟨49773567493044754754905061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33182378328696503169936707 49773567493044754754905061)
  ·
    refine ⟨9332543904945891516544699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49773567493044754754905061 9332543904945891516544699)
    ·
      refine ⟨13998815857418837274817049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9332543904945891516544699 13998815857418837274817049)
      ·
        refine ⟨10499111893064127956112787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13998815857418837274817049 10499111893064127956112787)
        ·
          refine ⟨15748667839596191934169181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10499111893064127956112787 15748667839596191934169181)
          ·
            refine ⟨5905750439848571975313443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15748667839596191934169181 5905750439848571975313443)
            ·
              refine ⟨8858625659772857962970165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905750439848571975313443 8858625659772857962970165)
              ·
                refine ⟨830496155603705434028453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8858625659772857962970165 830496155603705434028453)
                ·
                  refine ⟨155718029175694768880335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830496155603705434028453 155718029175694768880335)
                  ·
                    rfl

theorem cell22_1364669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_1364669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364669 prefixEnd_1364669 := by exact prefixLift 1364669
  have htrace : WordTrace (prefixWord ++ tailWord_1364669) baseStart_1364669 baseEnd_1364669 := by
    simpa [prefixWord, tailWord_1364669, baseEnd_1364669] using wordTrace_append hprefix tailTrace_1364669
  have hstable : (prefixWord ++ tailWord_1364669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364669).length < 2 ^ (prefixWord ++ tailWord_1364669).sum := by decide
  have hdescent : baseEnd_1364669 < baseStart_1364669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364671 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 1, 4]
def baseStart_1364671 : Nat := 118140960795 + 1364671 * 2 ^ 59
def prefixEnd_1364671 : Nat := 4983230072969 + 3 ^ 40 * 1364671 * 2
def baseEnd_1364671 : Nat := 467154772167956968090999

theorem tailTrace_1364671 : CollatzResearch.WordTrace tailWord_1364671 prefixEnd_1364671 467154772167956968090999 := by
  unfold tailWord_1364671
  simp only [CollatzResearch.WordTrace]
  refine ⟨49773640439037509096477867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33182426959358339397651911 49773640439037509096477867)
  ·
    refine ⟨74660460658556263644716801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49773640439037509096477867 74660460658556263644716801)
    ·
      refine ⟨55995345493917197733537601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74660460658556263644716801 55995345493917197733537601)
      ·
        refine ⟨41996509120437898300153201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55995345493917197733537601 41996509120437898300153201)
        ·
          refine ⟨31497381840328423725114901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41996509120437898300153201 31497381840328423725114901)
          ·
            refine ⟨1476439773765394862114761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31497381840328423725114901 1476439773765394862114761)
            ·
              refine ⟨1107329830324046146586071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476439773765394862114761 1107329830324046146586071)
              ·
                refine ⟨1660994745486069219879107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107329830324046146586071 1660994745486069219879107)
                ·
                  refine ⟨2491492118229103829818661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660994745486069219879107 2491492118229103829818661)
                  ·
                    refine ⟨467154772167956968090999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2491492118229103829818661 467154772167956968090999)
                    ·
                      rfl

theorem cell22_1364671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 1, 4].length) (baseStart_1364671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364671 prefixEnd_1364671 := by exact prefixLift 1364671
  have htrace : WordTrace (prefixWord ++ tailWord_1364671) baseStart_1364671 baseEnd_1364671 := by
    simpa [prefixWord, tailWord_1364671, baseEnd_1364671] using wordTrace_append hprefix tailTrace_1364671
  have hstable : (prefixWord ++ tailWord_1364671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364671).length < 2 ^ (prefixWord ++ tailWord_1364671).sum := by decide
  have hdescent : baseEnd_1364671 < baseStart_1364671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364757 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1364757 : Nat := 118140960795 + 1364757 * 2 ^ 59
def prefixEnd_1364757 : Nat := 4983230072969 + 3 ^ 40 * 1364757 * 2
def baseEnd_1364757 : Nat := 467184211725481410440735

theorem tailTrace_1364757 : CollatzResearch.WordTrace tailWord_1364757 prefixEnd_1364757 467184211725481410440735 := by
  unfold tailWord_1364757
  simp only [CollatzResearch.WordTrace]
  refine ⟨49776777116725945784108525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33184518077817297189405683 49776777116725945784108525)
  ·
    refine ⟨18666291418772229669040697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49776777116725945784108525 18666291418772229669040697)
    ·
      refine ⟨13999718564079172251780523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18666291418772229669040697 13999718564079172251780523)
      ·
        refine ⟨20999577846118758377670785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13999718564079172251780523 20999577846118758377670785)
        ·
          refine ⟨15749683384589068783253089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20999577846118758377670785 15749683384589068783253089)
          ·
            refine ⟨11812262538441801587439817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15749683384589068783253089 11812262538441801587439817)
            ·
              refine ⟨8859196903831351190579863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11812262538441801587439817 8859196903831351190579863)
              ·
                refine ⟨13288795355747026785869795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8859196903831351190579863 13288795355747026785869795)
                ·
                  refine ⟨19933193033620540178804693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13288795355747026785869795 19933193033620540178804693)
                  ·
                    refine ⟨467184211725481410440735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19933193033620540178804693 467184211725481410440735)
                    ·
                      rfl

theorem cell22_1364757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1364757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364757 prefixEnd_1364757 := by exact prefixLift 1364757
  have htrace : WordTrace (prefixWord ++ tailWord_1364757) baseStart_1364757 baseEnd_1364757 := by
    simpa [prefixWord, tailWord_1364757, baseEnd_1364757] using wordTrace_append hprefix tailTrace_1364757
  have hstable : (prefixWord ++ tailWord_1364757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364757).length < 2 ^ (prefixWord ++ tailWord_1364757).sum := by decide
  have hdescent : baseEnd_1364757 < baseStart_1364757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364797 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_1364797 : Nat := 118140960795 + 1364797 * 2 ^ 59
def prefixEnd_1364797 : Nat := 4983230072969 + 3 ^ 40 * 1364797 * 2
def baseEnd_1364797 : Nat := 467197904542934639440613

theorem tailTrace_1364797 : CollatzResearch.WordTrace tailWord_1364797 prefixEnd_1364797 467197904542934639440613 := by
  unfold tailWord_1364797
  simp only [CollatzResearch.WordTrace]
  refine ⟨49778236036581032615564645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33185490691054021743709763 49778236036581032615564645)
  ·
    refine ⟨9333419256858943615418371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49778236036581032615564645 9333419256858943615418371)
    ·
      refine ⟨14000128885288415423127557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9333419256858943615418371 14000128885288415423127557)
      ·
        refine ⟨2625024165991577891836417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14000128885288415423127557 2625024165991577891836417)
        ·
          refine ⟨1968768124493683418877313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625024165991577891836417 1968768124493683418877313)
          ·
            refine ⟨1476576093370262564157985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968768124493683418877313 1476576093370262564157985)
            ·
              refine ⟨1107432070027696923118489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476576093370262564157985 1107432070027696923118489)
              ·
                refine ⟨830574052520772692338867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107432070027696923118489 830574052520772692338867)
                ·
                  refine ⟨1245861078781159038508301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830574052520772692338867 1245861078781159038508301)
                  ·
                    refine ⟨467197904542934639440613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245861078781159038508301 467197904542934639440613)
                    ·
                      rfl

theorem cell22_1364797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_1364797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364797 prefixEnd_1364797 := by exact prefixLift 1364797
  have htrace : WordTrace (prefixWord ++ tailWord_1364797) baseStart_1364797 baseEnd_1364797 := by
    simpa [prefixWord, tailWord_1364797, baseEnd_1364797] using wordTrace_append hprefix tailTrace_1364797
  have hstable : (prefixWord ++ tailWord_1364797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364797).length < 2 ^ (prefixWord ++ tailWord_1364797).sum := by decide
  have hdescent : baseEnd_1364797 < baseStart_1364797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364847 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_1364847 : Nat := 118140960795 + 1364847 * 2 ^ 59
def prefixEnd_1364847 : Nat := 4983230072969 + 3 ^ 40 * 1364847 * 2
def baseEnd_1364847 : Nat := 467215020564751175690459

theorem tailTrace_1364847 : CollatzResearch.WordTrace tailWord_1364847 prefixEnd_1364847 467215020564751175690459 := by
  unfold tailWord_1364847
  simp only [CollatzResearch.WordTrace]
  refine ⟨49780059686399891154884795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33186706457599927436589863 49780059686399891154884795)
  ·
    refine ⟨74670089529599836732327193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49780059686399891154884795 74670089529599836732327193)
    ·
      refine ⟨56002567147199877549245395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74670089529599836732327193 56002567147199877549245395)
      ·
        refine ⟨84003850720799816323868093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56002567147199877549245395 84003850720799816323868093)
        ·
          refine ⟨31501444020299931121450535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84003850720799816323868093 31501444020299931121450535)
          ·
            refine ⟨47252166030449896682175803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31501444020299931121450535 47252166030449896682175803)
            ·
              refine ⟨70878249045674845023263705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47252166030449896682175803 70878249045674845023263705)
              ·
                refine ⟨53158686784256133767447779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70878249045674845023263705 53158686784256133767447779)
                ·
                  refine ⟨79738030176384200651171669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53158686784256133767447779 79738030176384200651171669)
                  ·
                    refine ⟨467215020564751175690459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79738030176384200651171669 467215020564751175690459)
                    ·
                      rfl

theorem cell22_1364847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_1364847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364847 prefixEnd_1364847 := by exact prefixLift 1364847
  have htrace : WordTrace (prefixWord ++ tailWord_1364847) baseStart_1364847 baseEnd_1364847 := by
    simpa [prefixWord, tailWord_1364847, baseEnd_1364847] using wordTrace_append hprefix tailTrace_1364847
  have hstable : (prefixWord ++ tailWord_1364847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364847).length < 2 ^ (prefixWord ++ tailWord_1364847).sum := by decide
  have hdescent : baseEnd_1364847 < baseStart_1364847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364853 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1364853 : Nat := 118140960795 + 1364853 * 2 ^ 59
def prefixEnd_1364853 : Nat := 4983230072969 + 3 ^ 40 * 1364853 * 2
def baseEnd_1364853 : Nat := 467217074487369160040441

theorem tailTrace_1364853 : CollatzResearch.WordTrace tailWord_1364853 prefixEnd_1364853 467217074487369160040441 := by
  unfold tailWord_1364853
  simp only [CollatzResearch.WordTrace]
  refine ⟨49780278524378154179603213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33186852349585436119735475 49780278524378154179603213)
  ·
    refine ⟨18667604446641807817351205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49780278524378154179603213 18667604446641807817351205)
    ·
      refine ⟨3500175833745338965753351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18667604446641807817351205 3500175833745338965753351)
      ·
        refine ⟨5250263750618008448630027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500175833745338965753351 5250263750618008448630027)
        ·
          refine ⟨7875395625927012672945041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250263750618008448630027 7875395625927012672945041)
          ·
            refine ⟨5906546719445259504708781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7875395625927012672945041 5906546719445259504708781)
            ·
              refine ⟨2214955019791972314265793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5906546719445259504708781 2214955019791972314265793)
              ·
                refine ⟨1661216264843979235699345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214955019791972314265793 1661216264843979235699345)
                ·
                  refine ⟨1245912198632984426774509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1661216264843979235699345 1245912198632984426774509)
                  ·
                    refine ⟨467217074487369160040441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1245912198632984426774509 467217074487369160040441)
                    ·
                      rfl

theorem cell22_1364853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1364853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364853 prefixEnd_1364853 := by exact prefixLift 1364853
  have htrace : WordTrace (prefixWord ++ tailWord_1364853) baseStart_1364853 baseEnd_1364853 := by
    simpa [prefixWord, tailWord_1364853, baseEnd_1364853] using wordTrace_append hprefix tailTrace_1364853
  have hstable : (prefixWord ++ tailWord_1364853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364853).length < 2 ^ (prefixWord ++ tailWord_1364853).sum := by decide
  have hdescent : baseEnd_1364853 < baseStart_1364853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364928 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_1364928 : Nat := 118140960795 + 1364928 * 2 ^ 59
def prefixEnd_1364928 : Nat := 4983230072969 + 3 ^ 40 * 1364928 * 2
def baseEnd_1364928 : Nat := 155747582840031321471737

theorem tailTrace_1364928 : CollatzResearch.WordTrace tailWord_1364928 prefixEnd_1364928 155747582840031321471737 := by
  unfold tailWord_1364928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891506999553220994291719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33188675999404294659055625 24891506999553220994291719)
  ·
    refine ⟨37337260499329831491437579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24891506999553220994291719 37337260499329831491437579)
    ·
      refine ⟨56005890748994747237156369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37337260499329831491437579 56005890748994747237156369)
      ·
        refine ⟨42004418061746060427867277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56005890748994747237156369 42004418061746060427867277)
        ·
          refine ⟨15751656773154772660450229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42004418061746060427867277 15751656773154772660450229)
          ·
            refine ⟨1476717822483259936917209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15751656773154772660450229 1476717822483259936917209)
            ·
              refine ⟨1107538366862444952687907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476717822483259936917209 1107538366862444952687907)
              ·
                refine ⟨1661307550293667429031861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107538366862444952687907 1661307550293667429031861)
                ·
                  refine ⟨155747582840031321471737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661307550293667429031861 155747582840031321471737)
                  ·
                    rfl

theorem cell22_1364928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_1364928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364928 prefixEnd_1364928 := by exact prefixLift 1364928
  have htrace : WordTrace (prefixWord ++ tailWord_1364928) baseStart_1364928 baseEnd_1364928 := by
    simpa [prefixWord, tailWord_1364928, baseEnd_1364928] using wordTrace_append hprefix tailTrace_1364928
  have hstable : (prefixWord ++ tailWord_1364928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364928).length < 2 ^ (prefixWord ++ tailWord_1364928).sum := by decide
  have hdescent : baseEnd_1364928 < baseStart_1364928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1364988 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1364988 : Nat := 118140960795 + 1364988 * 2 ^ 59
def prefixEnd_1364988 : Nat := 4983230072969 + 3 ^ 40 * 1364988 * 2
def baseEnd_1364988 : Nat := 467263287746273807915027

theorem tailTrace_1364988 : CollatzResearch.WordTrace tailWord_1364988 prefixEnd_1364988 467263287746273807915027 := by
  unfold tailWord_1364988
  simp only [CollatzResearch.WordTrace]
  refine ⟨24892601189444536117883809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33190134919259381490511745 24892601189444536117883809)
  ·
    refine ⟨18669450892083402088412857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24892601189444536117883809 18669450892083402088412857)
    ·
      refine ⟨14002088169062551566309643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18669450892083402088412857 14002088169062551566309643)
      ·
        refine ⟨21003132253593827349464465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14002088169062551566309643 21003132253593827349464465)
        ·
          refine ⟨15752349190195370512098349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21003132253593827349464465 15752349190195370512098349)
          ·
            refine ⟨5907130946323263942036881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15752349190195370512098349 5907130946323263942036881)
            ·
              refine ⟨4430348209742447956527661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5907130946323263942036881 4430348209742447956527661)
              ·
                refine ⟨1661380578653417983697873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4430348209742447956527661 1661380578653417983697873)
                ·
                  refine ⟨1246035433990063487773405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1661380578653417983697873 1246035433990063487773405)
                  ·
                    refine ⟨467263287746273807915027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246035433990063487773405 467263287746273807915027)
                    ·
                      rfl

theorem cell22_1364988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1364988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1364988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1364988 prefixEnd_1364988 := by exact prefixLift 1364988
  have htrace : WordTrace (prefixWord ++ tailWord_1364988) baseStart_1364988 baseEnd_1364988 := by
    simpa [prefixWord, tailWord_1364988, baseEnd_1364988] using wordTrace_append hprefix tailTrace_1364988
  have hstable : (prefixWord ++ tailWord_1364988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1364988).length < 2 ^ (prefixWord ++ tailWord_1364988).sum := by decide
  have hdescent : baseEnd_1364988 < baseStart_1364988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1364988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365003 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 2, 4]
def baseStart_1365003 : Nat := 118140960795 + 1365003 * 2 ^ 59
def prefixEnd_1365003 : Nat := 4983230072969 + 3 ^ 40 * 1365003 * 2
def baseEnd_1365003 : Nat := 467268422552818768789981

theorem tailTrace_1365003 : CollatzResearch.WordTrace tailWord_1365003 prefixEnd_1365003 467268422552818768789981 := by
  unfold tailWord_1365003
  simp only [CollatzResearch.WordTrace]
  refine ⟨49785749473834729797563663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33190499649223153198375775 49785749473834729797563663)
  ·
    refine ⟨74678624210752094696345495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49785749473834729797563663 74678624210752094696345495)
    ·
      refine ⟨112017936316128142044518243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74678624210752094696345495 112017936316128142044518243)
      ·
        refine ⟨168026904474192213066777365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112017936316128142044518243 168026904474192213066777365)
        ·
          refine ⟨7876261147227759987505189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 168026904474192213066777365 7876261147227759987505189)
          ·
            refine ⟨1476798965105204997657223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7876261147227759987505189 1476798965105204997657223)
            ·
              refine ⟨2215198447657807496485835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476798965105204997657223 2215198447657807496485835)
              ·
                refine ⟨3322797671486711244728753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215198447657807496485835 3322797671486711244728753)
                ·
                  refine ⟨2492098253615033433546565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3322797671486711244728753 2492098253615033433546565)
                  ·
                    refine ⟨467268422552818768789981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492098253615033433546565 467268422552818768789981)
                    ·
                      rfl

theorem cell22_1365003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4].length) (baseStart_1365003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365003 prefixEnd_1365003 := by exact prefixLift 1365003
  have htrace : WordTrace (prefixWord ++ tailWord_1365003) baseStart_1365003 baseEnd_1365003 := by
    simpa [prefixWord, tailWord_1365003, baseEnd_1365003] using wordTrace_append hprefix tailTrace_1365003
  have hstable : (prefixWord ++ tailWord_1365003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365003).length < 2 ^ (prefixWord ++ tailWord_1365003).sum := by decide
  have hdescent : baseEnd_1365003 < baseStart_1365003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365168 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_1365168 : Nat := 118140960795 + 1365168 * 2 ^ 59
def prefixEnd_1365168 : Nat := 4983230072969 + 3 ^ 40 * 1365168 * 2
def baseEnd_1365168 : Nat := 467324905424813338414475

theorem tailTrace_1365168 : CollatzResearch.WordTrace tailWord_1365168 prefixEnd_1365168 467324905424813338414475 := by
  unfold tailWord_1365168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24895883759118481488660079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33194511678824641984880105 24895883759118481488660079)
  ·
    refine ⟨37343825638677722232990119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24895883759118481488660079 37343825638677722232990119)
    ·
      refine ⟨56015738458016583349485179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37343825638677722232990119 56015738458016583349485179)
      ·
        refine ⟨84023607687024875024227769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56015738458016583349485179 84023607687024875024227769)
        ·
          refine ⟨63017705765268656268170827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84023607687024875024227769 63017705765268656268170827)
          ·
            refine ⟨94526558647902984402256241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63017705765268656268170827 94526558647902984402256241)
            ·
              refine ⟨70894918985927238301692181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94526558647902984402256241 70894918985927238301692181)
              ·
                refine ⟨3323199327465339295391821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70894918985927238301692181 3323199327465339295391821)
                ·
                  refine ⟨1246199747799502235771933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3323199327465339295391821 1246199747799502235771933)
                  ·
                    refine ⟨467324905424813338414475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246199747799502235771933 467324905424813338414475)
                    ·
                      rfl

theorem cell22_1365168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_1365168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365168 prefixEnd_1365168 := by exact prefixLift 1365168
  have htrace : WordTrace (prefixWord ++ tailWord_1365168) baseStart_1365168 baseEnd_1365168 := by
    simpa [prefixWord, tailWord_1365168, baseEnd_1365168] using wordTrace_append hprefix tailTrace_1365168
  have hstable : (prefixWord ++ tailWord_1365168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365168).length < 2 ^ (prefixWord ++ tailWord_1365168).sum := by decide
  have hdescent : baseEnd_1365168 < baseStart_1365168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365202 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1365202 : Nat := 118140960795 + 1365202 * 2 ^ 59
def prefixEnd_1365202 : Nat := 4983230072969 + 3 ^ 40 * 1365202 * 2
def baseEnd_1365202 : Nat := 467336544319648583064371

theorem tailTrace_1365202 : CollatzResearch.WordTrace tailWord_1365202 prefixEnd_1365202 467336544319648583064371 := by
  unfold tailWord_1365202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448251900028446696014465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33195338400075857856038573 12448251900028446696014465)
  ·
    refine ⟨9336188925021335022010849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12448251900028446696014465 9336188925021335022010849)
    ·
      refine ⟨7002141693766001266508137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9336188925021335022010849 7002141693766001266508137)
      ·
        refine ⟨5251606270324500949881103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7002141693766001266508137 5251606270324500949881103)
        ·
          refine ⟨7877409405486751424821655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251606270324500949881103 7877409405486751424821655)
          ·
            refine ⟨11816114108230127137232483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7877409405486751424821655 11816114108230127137232483)
            ·
              refine ⟨17724171162345190705848725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816114108230127137232483 17724171162345190705848725)
              ·
                refine ⟨830820523234930814336659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17724171162345190705848725 830820523234930814336659)
                ·
                  refine ⟨1246230784852396221504989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830820523234930814336659 1246230784852396221504989)
                  ·
                    refine ⟨467336544319648583064371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246230784852396221504989 467336544319648583064371)
                    ·
                      rfl

theorem cell22_1365202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1365202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365202 prefixEnd_1365202 := by exact prefixLift 1365202
  have htrace : WordTrace (prefixWord ++ tailWord_1365202) baseStart_1365202 baseEnd_1365202 := by
    simpa [prefixWord, tailWord_1365202, baseEnd_1365202] using wordTrace_append hprefix tailTrace_1365202
  have hstable : (prefixWord ++ tailWord_1365202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365202).length < 2 ^ (prefixWord ++ tailWord_1365202).sum := by decide
  have hdescent : baseEnd_1365202 < baseStart_1365202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365260 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_1365260 : Nat := 118140960795 + 1365260 * 2 ^ 59
def prefixEnd_1365260 : Nat := 4983230072969 + 3 ^ 40 * 1365260 * 2
def baseEnd_1365260 : Nat := 155785466301651921704731

theorem tailTrace_1365260 : CollatzResearch.WordTrace tailWord_1365260 prefixEnd_1365260 155785466301651921704731 := by
  unfold tailWord_1365260
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897561516951831344834617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33196748689269108459779489 24897561516951831344834617)
  ·
    refine ⟨18673171137713873508625963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24897561516951831344834617 18673171137713873508625963)
    ·
      refine ⟨28009756706570810262938945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18673171137713873508625963 28009756706570810262938945)
      ·
        refine ⟨21007317529928107697204209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28009756706570810262938945 21007317529928107697204209)
        ·
          refine ⟨15755488147446080772903157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21007317529928107697204209 15755488147446080772903157)
          ·
            refine ⟨1477077013823070072459671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15755488147446080772903157 1477077013823070072459671)
            ·
              refine ⟨2215615520734605108689507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477077013823070072459671 2215615520734605108689507)
              ·
                refine ⟨3323423281101907663034261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2215615520734605108689507 3323423281101907663034261)
                ·
                  refine ⟨155785466301651921704731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3323423281101907663034261 155785466301651921704731)
                  ·
                    rfl

theorem cell22_1365260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_1365260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365260 prefixEnd_1365260 := by exact prefixLift 1365260
  have htrace : WordTrace (prefixWord ++ tailWord_1365260) baseStart_1365260 baseEnd_1365260 := by
    simpa [prefixWord, tailWord_1365260, baseEnd_1365260] using wordTrace_append hprefix tailTrace_1365260
  have hstable : (prefixWord ++ tailWord_1365260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365260).length < 2 ^ (prefixWord ++ tailWord_1365260).sum := by decide
  have hdescent : baseEnd_1365260 < baseStart_1365260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365266 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1365266 : Nat := 118140960795 + 1365266 * 2 ^ 59
def prefixEnd_1365266 : Nat := 4983230072969 + 3 ^ 40 * 1365266 * 2
def baseEnd_1365266 : Nat := 155786150942524583154725

theorem tailTrace_1365266 : CollatzResearch.WordTrace tailWord_1365266 prefixEnd_1365266 155786150942524583154725 := by
  unfold tailWord_1365266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448835467970481428596913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33196894581254617142925101 12448835467970481428596913)
  ·
    refine ⟨9336626600977861071447685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12448835467970481428596913 9336626600977861071447685)
    ·
      refine ⟨1750617487683348950896441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9336626600977861071447685 1750617487683348950896441)
      ·
        refine ⟨1312963115762511713172331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1750617487683348950896441 1312963115762511713172331)
        ·
          refine ⟨1969444673643767569758497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312963115762511713172331 1969444673643767569758497)
          ·
            refine ⟨1477083505232825677318873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969444673643767569758497 1477083505232825677318873)
            ·
              refine ⟨1107812628924619257989155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477083505232825677318873 1107812628924619257989155)
              ·
                refine ⟨1661718943386928886983733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107812628924619257989155 1661718943386928886983733)
                ·
                  refine ⟨155786150942524583154725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1661718943386928886983733 155786150942524583154725)
                  ·
                    rfl

theorem cell22_1365266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1365266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365266 prefixEnd_1365266 := by exact prefixLift 1365266
  have htrace : WordTrace (prefixWord ++ tailWord_1365266) baseStart_1365266 baseEnd_1365266 := by
    simpa [prefixWord, tailWord_1365266, baseEnd_1365266] using wordTrace_append hprefix tailTrace_1365266
  have hstable : (prefixWord ++ tailWord_1365266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365266).length < 2 ^ (prefixWord ++ tailWord_1365266).sum := by decide
  have hdescent : baseEnd_1365266 < baseStart_1365266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365279 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 1, 4]
def baseStart_1365279 : Nat := 118140960795 + 1365279 * 2 ^ 59
def prefixEnd_1365279 : Nat := 4983230072969 + 3 ^ 40 * 1365279 * 2
def baseEnd_1365279 : Nat := 467362902993246048889135

theorem tailTrace_1365279 : CollatzResearch.WordTrace tailWord_1365279 prefixEnd_1365279 467362902993246048889135 := by
  unfold tailWord_1365279
  simp only [CollatzResearch.WordTrace]
  refine ⟨49795816020834828934610891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33197210680556552623073927 49795816020834828934610891)
  ·
    refine ⟨74693724031252243401916337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49795816020834828934610891 74693724031252243401916337)
    ·
      refine ⟨56020293023439182551437253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74693724031252243401916337 56020293023439182551437253)
      ·
        refine ⟨10503804941894846728394485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56020293023439182551437253 10503804941894846728394485)
        ·
          refine ⟨984731713302641880786983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10503804941894846728394485 984731713302641880786983)
          ·
            refine ⟨1477097569953962821180475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984731713302641880786983 1477097569953962821180475)
            ·
              refine ⟨2215646354930944231770713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477097569953962821180475 2215646354930944231770713)
              ·
                refine ⟨1661734766198208173828035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215646354930944231770713 1661734766198208173828035)
                ·
                  refine ⟨2492602149297312260742053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661734766198208173828035 2492602149297312260742053)
                  ·
                    refine ⟨467362902993246048889135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2492602149297312260742053 467362902993246048889135)
                    ·
                      rfl

theorem cell22_1365279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_1365279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365279 prefixEnd_1365279 := by exact prefixLift 1365279
  have htrace : WordTrace (prefixWord ++ tailWord_1365279) baseStart_1365279 baseEnd_1365279 := by
    simpa [prefixWord, tailWord_1365279, baseEnd_1365279] using wordTrace_append hprefix tailTrace_1365279
  have hstable : (prefixWord ++ tailWord_1365279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365279).length < 2 ^ (prefixWord ++ tailWord_1365279).sum := by decide
  have hdescent : baseEnd_1365279 < baseStart_1365279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365305 : List Nat := [1, 2, 1, 6, 3, 9]
def baseStart_1365305 : Nat := 118140960795 + 1365305 * 2 ^ 59
def prefixEnd_1365305 : Nat := 4983230072969 + 3 ^ 40 * 1365305 * 2
def baseEnd_1365305 : Nat := 5770022263266551206655

theorem tailTrace_1365305 : CollatzResearch.WordTrace tailWord_1365305 prefixEnd_1365305 5770022263266551206655 := by
  unfold tailWord_1365305
  simp only [CollatzResearch.WordTrace]
  refine ⟨49796764318740635375057369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33197842879160423583371579 49796764318740635375057369)
  ·
    refine ⟨37347573239055476531293027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49796764318740635375057369 37347573239055476531293027)
    ·
      refine ⟨56021359858583214796939541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37347573239055476531293027 56021359858583214796939541)
      ·
        refine ⟨2626001243371088193606541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56021359858583214796939541 2626001243371088193606541)
        ·
          refine ⟨984750466264158072602453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2626001243371088193606541 984750466264158072602453)
          ·
            refine ⟨5770022263266551206655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 984750466264158072602453 5770022263266551206655)
            ·
              rfl

theorem cell22_1365305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 9].length) (baseStart_1365305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365305 prefixEnd_1365305 := by exact prefixLift 1365305
  have htrace : WordTrace (prefixWord ++ tailWord_1365305) baseStart_1365305 baseEnd_1365305 := by
    simpa [prefixWord, tailWord_1365305, baseEnd_1365305] using wordTrace_append hprefix tailTrace_1365305
  have hstable : (prefixWord ++ tailWord_1365305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365305).length < 2 ^ (prefixWord ++ tailWord_1365305).sum := by decide
  have hdescent : baseEnd_1365305 < baseStart_1365305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365320 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1365320 : Nat := 118140960795 + 1365320 * 2 ^ 59
def prefixEnd_1365320 : Nat := 4983230072969 + 3 ^ 40 * 1365320 * 2
def baseEnd_1365320 : Nat := 467376938131135608614009

theorem tailTrace_1365320 : CollatzResearch.WordTrace tailWord_1365320 prefixEnd_1365320 467376938131135608614009 := by
  unfold tailWord_1365320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24898655706843146468426707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33198207609124195291235609 24898655706843146468426707)
  ·
    refine ⟨37347983560264719702640061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24898655706843146468426707 37347983560264719702640061)
    ·
      refine ⟨14005493835099269888490023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37347983560264719702640061 14005493835099269888490023)
      ·
        refine ⟨21008240752648904832735035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14005493835099269888490023 21008240752648904832735035)
        ·
          refine ⟨31512361128973357249102553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21008240752648904832735035 31512361128973357249102553)
          ·
            refine ⟨23634270846730017936826915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31512361128973357249102553 23634270846730017936826915)
            ·
              refine ⟨35451406270095026905240373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23634270846730017936826915 35451406270095026905240373)
              ·
                refine ⟨3323569337821408772366285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35451406270095026905240373 3323569337821408772366285)
                ·
                  refine ⟨1246338501683028289637357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3323569337821408772366285 1246338501683028289637357)
                  ·
                    refine ⟨467376938131135608614009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246338501683028289637357 467376938131135608614009)
                    ·
                      rfl

theorem cell22_1365320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1365320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365320 prefixEnd_1365320 := by exact prefixLift 1365320
  have htrace : WordTrace (prefixWord ++ tailWord_1365320) baseStart_1365320 baseEnd_1365320 := by
    simpa [prefixWord, tailWord_1365320, baseEnd_1365320] using wordTrace_append hprefix tailTrace_1365320
  have hstable : (prefixWord ++ tailWord_1365320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365320).length < 2 ^ (prefixWord ++ tailWord_1365320).sum := by decide
  have hdescent : baseEnd_1365320 < baseStart_1365320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365500 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1365500 : Nat := 118140960795 + 1365500 * 2 ^ 59
def prefixEnd_1365500 : Nat := 4983230072969 + 3 ^ 40 * 1365500 * 2
def baseEnd_1365500 : Nat := 467438555809675139113457

theorem tailTrace_1365500 : CollatzResearch.WordTrace tailWord_1365500 prefixEnd_1365500 467438555809675139113457 := by
  unfold tailWord_1365500
  simp only [CollatzResearch.WordTrace]
  refine ⟨24901938276517091839202977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33202584368689455785603969 24901938276517091839202977)
  ·
    refine ⟨18676453707387818879402233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24901938276517091839202977 18676453707387818879402233)
    ·
      refine ⟨14007340280540864159551675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18676453707387818879402233 14007340280540864159551675)
      ·
        refine ⟨21011010420811296239327513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14007340280540864159551675 21011010420811296239327513)
        ·
          refine ⟨15758257815608472179495635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21011010420811296239327513 15758257815608472179495635)
          ·
            refine ⟨23637386723412708269243453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15758257815608472179495635 23637386723412708269243453)
            ·
              refine ⟨8864020021279765600966295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23637386723412708269243453 8864020021279765600966295)
              ·
                refine ⟨13296030031919648401449443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8864020021279765600966295 13296030031919648401449443)
                ·
                  refine ⟨19944045047879472602174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13296030031919648401449443 19944045047879472602174165)
                  ·
                    refine ⟨467438555809675139113457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19944045047879472602174165 467438555809675139113457)
                    ·
                      rfl

theorem cell22_1365500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1365500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365500 prefixEnd_1365500 := by exact prefixLift 1365500
  have htrace : WordTrace (prefixWord ++ tailWord_1365500) baseStart_1365500 baseEnd_1365500 := by
    simpa [prefixWord, tailWord_1365500, baseEnd_1365500] using wordTrace_append hprefix tailTrace_1365500
  have hstable : (prefixWord ++ tailWord_1365500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365500).length < 2 ^ (prefixWord ++ tailWord_1365500).sum := by decide
  have hdescent : baseEnd_1365500 < baseStart_1365500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365506 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1365506 : Nat := 118140960795 + 1365506 * 2 ^ 59
def prefixEnd_1365506 : Nat := 4983230072969 + 3 ^ 40 * 1365506 * 2
def baseEnd_1365506 : Nat := 467440609732293123463439

theorem tailTrace_1365506 : CollatzResearch.WordTrace tailWord_1365506 prefixEnd_1365506 467440609732293123463439 := by
  unfold tailWord_1365506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451023847753111675781093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33202730260674964468749581 12451023847753111675781093)
  ·
    refine ⟨2334566971453708439208955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12451023847753111675781093 2334566971453708439208955)
    ·
      refine ⟨3501850457180562658813433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2334566971453708439208955 3501850457180562658813433)
      ·
        refine ⟨2626387842885421994110075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3501850457180562658813433 2626387842885421994110075)
        ·
          refine ⟨3939581764328132991165113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626387842885421994110075 3939581764328132991165113)
          ·
            refine ⟨2954686323246099743373835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939581764328132991165113 2954686323246099743373835)
            ·
              refine ⟨4432029484869149615060753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2954686323246099743373835 4432029484869149615060753)
              ·
                refine ⟨3324022113651862211295565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4432029484869149615060753 3324022113651862211295565)
                ·
                  refine ⟨1246508292619448329235837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3324022113651862211295565 1246508292619448329235837)
                  ·
                    refine ⟨467440609732293123463439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246508292619448329235837 467440609732293123463439)
                    ·
                      rfl

theorem cell22_1365506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1365506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365506 prefixEnd_1365506 := by exact prefixLift 1365506
  have htrace : WordTrace (prefixWord ++ tailWord_1365506) baseStart_1365506 baseEnd_1365506 := by
    simpa [prefixWord, tailWord_1365506, baseEnd_1365506] using wordTrace_append hprefix tailTrace_1365506
  have hstable : (prefixWord ++ tailWord_1365506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365506).length < 2 ^ (prefixWord ++ tailWord_1365506).sum := by decide
  have hdescent : baseEnd_1365506 < baseStart_1365506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365510 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1365510 : Nat := 118140960795 + 1365510 * 2 ^ 59
def prefixEnd_1365510 : Nat := 4983230072969 + 3 ^ 40 * 1365510 * 2
def baseEnd_1365510 : Nat := 467441979014038446363427

theorem tailTrace_1365510 : CollatzResearch.WordTrace tailWord_1365510 prefixEnd_1365510 467441979014038446363427 := by
  unfold tailWord_1365510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556382540093686105820937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33202827521998636924179989 1556382540093686105820937)
  ·
    refine ⟨1167286905070264579365703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1556382540093686105820937 1167286905070264579365703)
    ·
      refine ⟨1750930357605396869048555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167286905070264579365703 1750930357605396869048555)
      ·
        refine ⟨2626395536408095303572833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750930357605396869048555 2626395536408095303572833)
        ·
          refine ⟨1969796652306071477679625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2626395536408095303572833 1969796652306071477679625)
          ·
            refine ⟨1477347489229553608259719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969796652306071477679625 1477347489229553608259719)
            ·
              refine ⟨2216021233844330412389579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477347489229553608259719 2216021233844330412389579)
              ·
                refine ⟨3324031850766495618584369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216021233844330412389579 3324031850766495618584369)
                ·
                  refine ⟨2493023888074871713938277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324031850766495618584369 2493023888074871713938277)
                  ·
                    refine ⟨467441979014038446363427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493023888074871713938277 467441979014038446363427)
                    ·
                      rfl

theorem cell22_1365510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1365510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365510 prefixEnd_1365510 := by exact prefixLift 1365510
  have htrace : WordTrace (prefixWord ++ tailWord_1365510) baseStart_1365510 baseEnd_1365510 := by
    simpa [prefixWord, tailWord_1365510, baseEnd_1365510] using wordTrace_append hprefix tailTrace_1365510
  have hstable : (prefixWord ++ tailWord_1365510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365510).length < 2 ^ (prefixWord ++ tailWord_1365510).sum := by decide
  have hdescent : baseEnd_1365510 < baseStart_1365510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365530 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_1365530 : Nat := 118140960795 + 1365530 * 2 ^ 59
def prefixEnd_1365530 : Nat := 4983230072969 + 3 ^ 40 * 1365530 * 2
def baseEnd_1365530 : Nat := 155816275140921686954455

theorem tailTrace_1365530 : CollatzResearch.WordTrace tailWord_1365530 prefixEnd_1365530 155816275140921686954455 := by
  unfold tailWord_1365530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451242685731374700499511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33203313828616999201332029 12451242685731374700499511)
  ·
    refine ⟨18676864028597062050749267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12451242685731374700499511 18676864028597062050749267)
    ·
      refine ⟨28015296042895593076123901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18676864028597062050749267 28015296042895593076123901)
      ·
        refine ⟨10505736016085847403546463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28015296042895593076123901 10505736016085847403546463)
        ·
          refine ⟨15758604024128771105319695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505736016085847403546463 15758604024128771105319695)
          ·
            refine ⟨23637906036193156657979543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15758604024128771105319695 23637906036193156657979543)
            ·
              refine ⟨35456859054289734986969315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23637906036193156657979543 35456859054289734986969315)
              ·
                refine ⟨53185288581434602480453973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35456859054289734986969315 53185288581434602480453973)
                ·
                  refine ⟨155816275140921686954455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 53185288581434602480453973 155816275140921686954455)
                  ·
                    rfl

theorem cell22_1365530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_1365530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365530 prefixEnd_1365530 := by exact prefixLift 1365530
  have htrace : WordTrace (prefixWord ++ tailWord_1365530) baseStart_1365530 baseEnd_1365530 := by
    simpa [prefixWord, tailWord_1365530, baseEnd_1365530] using wordTrace_append hprefix tailTrace_1365530
  have hstable : (prefixWord ++ tailWord_1365530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365530).length < 2 ^ (prefixWord ++ tailWord_1365530).sum := by decide
  have hdescent : baseEnd_1365530 < baseStart_1365530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365667 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_1365667 : Nat := 118140960795 + 1365667 * 2 ^ 59
def prefixEnd_1365667 : Nat := 4983230072969 + 3 ^ 40 * 1365667 * 2
def baseEnd_1365667 : Nat := 467495723322542370187945

theorem tailTrace_1365667 : CollatzResearch.WordTrace tailWord_1365667 prefixEnd_1365667 467495723322542370187945 := by
  unfold tailWord_1365667
  simp only [CollatzResearch.WordTrace]
  refine ⟨49809967543429171199735255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33206645028952780799823503 49809967543429171199735255)
  ·
    refine ⟨74714951315143756799602883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49809967543429171199735255 74714951315143756799602883)
    ·
      refine ⟨112072426972715635199404325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74714951315143756799602883 112072426972715635199404325)
      ·
        refine ⟨21013580057384181599888311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112072426972715635199404325 21013580057384181599888311)
        ·
          refine ⟨31520370086076272399832467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013580057384181599888311 31520370086076272399832467)
          ·
            refine ⟨47280555129114408599748701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31520370086076272399832467 47280555129114408599748701)
            ·
              refine ⟨17730208173417903224905763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47280555129114408599748701 17730208173417903224905763)
              ·
                refine ⟨26595312260126854837358645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17730208173417903224905763 26595312260126854837358645)
                ·
                  refine ⟨2493310524386892641002373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26595312260126854837358645 2493310524386892641002373)
                  ·
                    refine ⟨467495723322542370187945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493310524386892641002373 467495723322542370187945)
                    ·
                      rfl

theorem cell22_1365667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_1365667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365667 prefixEnd_1365667 := by exact prefixLift 1365667
  have htrace : WordTrace (prefixWord ++ tailWord_1365667) baseStart_1365667 baseEnd_1365667 := by
    simpa [prefixWord, tailWord_1365667, baseEnd_1365667] using wordTrace_append hprefix tailTrace_1365667
  have hstable : (prefixWord ++ tailWord_1365667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365667).length < 2 ^ (prefixWord ++ tailWord_1365667).sum := by decide
  have hdescent : baseEnd_1365667 < baseStart_1365667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365682 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1365682 : Nat := 118140960795 + 1365682 * 2 ^ 59
def prefixEnd_1365682 : Nat := 4983230072969 + 3 ^ 40 * 1365682 * 2
def baseEnd_1365682 : Nat := 155833619376362443687633

theorem tailTrace_1365682 : CollatzResearch.WordTrace tailWord_1365682 prefixEnd_1365682 155833619376362443687633 := by
  unfold tailWord_1365682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452628659593707190382825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33207009758916552507687533 12452628659593707190382825)
  ·
    refine ⟨9339471494695280392787119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12452628659593707190382825 9339471494695280392787119)
    ·
      refine ⟨14009207242042920589180679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9339471494695280392787119 14009207242042920589180679)
      ·
        refine ⟨21013810863064380883771019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14009207242042920589180679 21013810863064380883771019)
        ·
          refine ⟨31520716294596571325656529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013810863064380883771019 31520716294596571325656529)
          ·
            refine ⟨23640537220947428494242397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31520716294596571325656529 23640537220947428494242397)
            ·
              refine ⟨8865201457855285685340899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23640537220947428494242397 8865201457855285685340899)
              ·
                refine ⟨13297802186782928528011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8865201457855285685340899 13297802186782928528011349)
                ·
                  refine ⟨155833619376362443687633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13297802186782928528011349 155833619376362443687633)
                  ·
                    rfl

theorem cell22_1365682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1365682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365682 prefixEnd_1365682 := by exact prefixLift 1365682
  have htrace : WordTrace (prefixWord ++ tailWord_1365682) baseStart_1365682 baseEnd_1365682 := by
    simpa [prefixWord, tailWord_1365682, baseEnd_1365682] using wordTrace_append hprefix tailTrace_1365682
  have hstable : (prefixWord ++ tailWord_1365682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365682).length < 2 ^ (prefixWord ++ tailWord_1365682).sum := by decide
  have hdescent : baseEnd_1365682 < baseStart_1365682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365716 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1365716 : Nat := 118140960795 + 1365716 * 2 ^ 59
def prefixEnd_1365716 : Nat := 4983230072969 + 3 ^ 40 * 1365716 * 2
def baseEnd_1365716 : Nat := 155837499007974191904265

theorem tailTrace_1365716 : CollatzResearch.WordTrace tailWord_1365716 prefixEnd_1365716 155837499007974191904265 := by
  unfold tailWord_1365716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905877360125826284134501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33207836480167768378846001 24905877360125826284134501)
  ·
    refine ⟨4669852005023592428275219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24905877360125826284134501 4669852005023592428275219)
    ·
      refine ⟨7004778007535388642412829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669852005023592428275219 7004778007535388642412829)
      ·
        refine ⟨2626791752825770740904811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7004778007535388642412829 2626791752825770740904811)
        ·
          refine ⟨3940187629238656111357217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626791752825770740904811 3940187629238656111357217)
          ·
            refine ⟨2955140721928992083517913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3940187629238656111357217 2955140721928992083517913)
            ·
              refine ⟨2216355541446744062638435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955140721928992083517913 2216355541446744062638435)
              ·
                refine ⟨3324533312170116093957653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216355541446744062638435 3324533312170116093957653)
                ·
                  refine ⟨155837499007974191904265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3324533312170116093957653 155837499007974191904265)
                  ·
                    rfl

theorem cell22_1365716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1365716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365716 prefixEnd_1365716 := by exact prefixLift 1365716
  have htrace : WordTrace (prefixWord ++ tailWord_1365716) baseStart_1365716 baseEnd_1365716 := by
    simpa [prefixWord, tailWord_1365716, baseEnd_1365716] using wordTrace_append hprefix tailTrace_1365716
  have hstable : (prefixWord ++ tailWord_1365716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365716).length < 2 ^ (prefixWord ++ tailWord_1365716).sum := by decide
  have hdescent : baseEnd_1365716 < baseStart_1365716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365727 : List Nat := [1, 1, 2, 3, 2, 2, 2, 9]
def baseStart_1365727 : Nat := 118140960795 + 1365727 * 2 ^ 59
def prefixEnd_1365727 : Nat := 4983230072969 + 3 ^ 40 * 1365727 * 2
def baseEnd_1365727 : Nat := 51946251394302468187529

theorem tailTrace_1365727 : CollatzResearch.WordTrace tailWord_1365727 prefixEnd_1365727 51946251394302468187529 := by
  unfold tailWord_1365727
  simp only [CollatzResearch.WordTrace]
  refine ⟨49812155923211801446919435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33208103948807867631279623 49812155923211801446919435)
  ·
    refine ⟨74718233884817702170379153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49812155923211801446919435 74718233884817702170379153)
    ·
      refine ⟨56038675413613276627784365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74718233884817702170379153 56038675413613276627784365)
      ·
        refine ⟨21014503280104978735419137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56038675413613276627784365 21014503280104978735419137)
        ·
          refine ⟨15760877460078734051564353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21014503280104978735419137 15760877460078734051564353)
          ·
            refine ⟨11820658095059050538673265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15760877460078734051564353 11820658095059050538673265)
            ·
              refine ⟨8865493571294287904004949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11820658095059050538673265 8865493571294287904004949)
              ·
                refine ⟨51946251394302468187529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8865493571294287904004949 51946251394302468187529)
                ·
                  rfl

theorem cell22_1365727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 9].length) (baseStart_1365727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365727 prefixEnd_1365727 := by exact prefixLift 1365727
  have htrace : WordTrace (prefixWord ++ tailWord_1365727) baseStart_1365727 baseEnd_1365727 := by
    simpa [prefixWord, tailWord_1365727, baseEnd_1365727] using wordTrace_append hprefix tailTrace_1365727
  have hstable : (prefixWord ++ tailWord_1365727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365727).length < 2 ^ (prefixWord ++ tailWord_1365727).sum := by decide
  have hdescent : baseEnd_1365727 < baseStart_1365727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365759 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 5, 3]
def baseStart_1365759 : Nat := 118140960795 + 1365759 * 2 ^ 59
def prefixEnd_1365759 : Nat := 4983230072969 + 3 ^ 40 * 1365759 * 2
def baseEnd_1365759 : Nat := 467527216802684796887663

theorem tailTrace_1365759 : CollatzResearch.WordTrace tailWord_1365759 prefixEnd_1365759 467527216802684796887663 := by
  unfold tailWord_1365759
  simp only [CollatzResearch.WordTrace]
  refine ⟨49813323059095870912084331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33208882039397247274722887 49813323059095870912084331)
  ·
    refine ⟨74719984588643806368126497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49813323059095870912084331 74719984588643806368126497)
    ·
      refine ⟨56039988441482854776094873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74719984588643806368126497 56039988441482854776094873)
      ·
        refine ⟨42029991331112141082071155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56039988441482854776094873 42029991331112141082071155)
        ·
          refine ⟨63044986996668211623106733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42029991331112141082071155 63044986996668211623106733)
          ·
            refine ⟨23641870123750579358665025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63044986996668211623106733 23641870123750579358665025)
            ·
              refine ⟨17731402592812934518998769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23641870123750579358665025 17731402592812934518998769)
              ·
                refine ⟨13298551944609700889249077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17731402592812934518998769 13298551944609700889249077)
                ·
                  refine ⟨1246739244807159458367101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13298551944609700889249077 1246739244807159458367101)
                  ·
                    refine ⟨467527216802684796887663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246739244807159458367101 467527216802684796887663)
                    ·
                      rfl

theorem cell22_1365759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_1365759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365759 prefixEnd_1365759 := by exact prefixLift 1365759
  have htrace : WordTrace (prefixWord ++ tailWord_1365759) baseStart_1365759 baseEnd_1365759 := by
    simpa [prefixWord, tailWord_1365759, baseEnd_1365759] using wordTrace_append hprefix tailTrace_1365759
  have hstable : (prefixWord ++ tailWord_1365759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365759).length < 2 ^ (prefixWord ++ tailWord_1365759).sum := by decide
  have hdescent : baseEnd_1365759 < baseStart_1365759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365834 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_1365834 : Nat := 118140960795 + 1365834 * 2 ^ 59
def prefixEnd_1365834 : Nat := 4983230072969 + 3 ^ 40 * 1365834 * 2
def baseEnd_1365834 : Nat := 155850963611803200420811

theorem tailTrace_1365834 : CollatzResearch.WordTrace tailWord_1365834 prefixEnd_1365834 155850963611803200420811 := by
  unfold tailWord_1365834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454014633456039680266139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33210705689216105814043037 12454014633456039680266139)
  ·
    refine ⟨18681021950184059520399209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12454014633456039680266139 18681021950184059520399209)
    ·
      refine ⟨14010766462638044640299407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18681021950184059520399209 14010766462638044640299407)
      ·
        refine ⟨21016149693957066960449111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14010766462638044640299407 21016149693957066960449111)
        ·
          refine ⟨31524224540935600440673667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21016149693957066960449111 31524224540935600440673667)
          ·
            refine ⟨47286336811403400661010501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31524224540935600440673667 47286336811403400661010501)
            ·
              refine ⟨8866188152138137623939469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47286336811403400661010501 8866188152138137623939469)
              ·
                refine ⟨3324820557051801608977301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8866188152138137623939469 3324820557051801608977301)
                ·
                  refine ⟨155850963611803200420811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3324820557051801608977301 155850963611803200420811)
                  ·
                    rfl

theorem cell22_1365834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_1365834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365834 prefixEnd_1365834 := by exact prefixLift 1365834
  have htrace : WordTrace (prefixWord ++ tailWord_1365834) baseStart_1365834 baseEnd_1365834 := by
    simpa [prefixWord, tailWord_1365834, baseEnd_1365834] using wordTrace_append hprefix tailTrace_1365834
  have hstable : (prefixWord ++ tailWord_1365834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365834).length < 2 ^ (prefixWord ++ tailWord_1365834).sum := by decide
  have hdescent : baseEnd_1365834 < baseStart_1365834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365868 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_1365868 : Nat := 118140960795 + 1365868 * 2 ^ 59
def prefixEnd_1365868 : Nat := 4983230072969 + 3 ^ 40 * 1365868 * 2
def baseEnd_1365868 : Nat := 155854843243414948637443

theorem tailTrace_1365868 : CollatzResearch.WordTrace tailWord_1365868 prefixEnd_1365868 155854843243414948637443 := by
  unfold tailWord_1365868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24908649307850491263901129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33211532410467321685201505 24908649307850491263901129)
  ·
    refine ⟨18681486980887868447925847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24908649307850491263901129 18681486980887868447925847)
    ·
      refine ⟨28022230471331802671888771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18681486980887868447925847 28022230471331802671888771)
      ·
        refine ⟨42033345706997704007833157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28022230471331802671888771 42033345706997704007833157)
        ·
          refine ⟨7881252320062069501468717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42033345706997704007833157 7881252320062069501468717)
          ·
            refine ⟨2955469620023276063050769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7881252320062069501468717 2955469620023276063050769)
            ·
              refine ⟨2216602215017457047288077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955469620023276063050769 2216602215017457047288077)
              ·
                refine ⟨831225830631546392733029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2216602215017457047288077 831225830631546392733029)
                ·
                  refine ⟨155854843243414948637443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831225830631546392733029 155854843243414948637443)
                  ·
                    rfl

theorem cell22_1365868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_1365868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365868 prefixEnd_1365868 := by exact prefixLift 1365868
  have htrace : WordTrace (prefixWord ++ tailWord_1365868) baseStart_1365868 baseEnd_1365868 := by
    simpa [prefixWord, tailWord_1365868, baseEnd_1365868] using wordTrace_append hprefix tailTrace_1365868
  have hstable : (prefixWord ++ tailWord_1365868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365868).length < 2 ^ (prefixWord ++ tailWord_1365868).sum := by decide
  have hdescent : baseEnd_1365868 < baseStart_1365868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365870 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1365870 : Nat := 118140960795 + 1365870 * 2 ^ 59
def prefixEnd_1365870 : Nat := 4983230072969 + 3 ^ 40 * 1365870 * 2
def baseEnd_1365870 : Nat := 467565214371117507362323

theorem tailTrace_1365870 : CollatzResearch.WordTrace tailWord_1365870 prefixEnd_1365870 467565214371117507362323 := by
  unfold tailWord_1365870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227171445211717108671883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33211581041129157912916709 6227171445211717108671883)
  ·
    refine ⟨9340757167817575663007825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6227171445211717108671883 9340757167817575663007825)
    ·
      refine ⟨7005567875863181747255869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9340757167817575663007825 7005567875863181747255869)
      ·
        refine ⟨2627087953448693155220951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7005567875863181747255869 2627087953448693155220951)
        ·
          refine ⟨3940631930173039732831427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627087953448693155220951 3940631930173039732831427)
          ·
            refine ⟨5910947895259559599247141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940631930173039732831427 5910947895259559599247141)
            ·
              refine ⟨1108302730361167424858839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5910947895259559599247141 1108302730361167424858839)
              ·
                refine ⟨1662454095541751137288259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108302730361167424858839 1662454095541751137288259)
                ·
                  refine ⟨2493681143312626705932389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662454095541751137288259 2493681143312626705932389)
                  ·
                    refine ⟨467565214371117507362323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493681143312626705932389 467565214371117507362323)
                    ·
                      rfl

theorem cell22_1365870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1365870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365870 prefixEnd_1365870 := by exact prefixLift 1365870
  have htrace : WordTrace (prefixWord ++ tailWord_1365870) baseStart_1365870 baseEnd_1365870 := by
    simpa [prefixWord, tailWord_1365870, baseEnd_1365870] using wordTrace_append hprefix tailTrace_1365870
  have hstable : (prefixWord ++ tailWord_1365870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365870).length < 2 ^ (prefixWord ++ tailWord_1365870).sum := by decide
  have hdescent : baseEnd_1365870 < baseStart_1365870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365941 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 7]
def baseStart_1365941 : Nat := 118140960795 + 1365941 * 2 ^ 59
def prefixEnd_1365941 : Nat := 4983230072969 + 3 ^ 40 * 1365941 * 2
def baseEnd_1365941 : Nat := 155863173040698996279035

theorem tailTrace_1365941 : CollatzResearch.WordTrace tailWord_1365941 prefixEnd_1365941 155863173040698996279035 := by
  unfold tailWord_1365941
  simp only [CollatzResearch.WordTrace]
  refine ⟨49819961144436515995209677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33213307429624343996806451 49819961144436515995209677)
  ·
    refine ⟨18682485429163693498203629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49819961144436515995209677 18682485429163693498203629)
    ·
      refine ⟨7005932035936385061826361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18682485429163693498203629 7005932035936385061826361)
      ·
        refine ⟨5254449026952288796369771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7005932035936385061826361 5254449026952288796369771)
        ·
          refine ⟨7881673540428433194554657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5254449026952288796369771 7881673540428433194554657)
          ·
            refine ⟨5911255155321324895915993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7881673540428433194554657 5911255155321324895915993)
            ·
              refine ⟨4433441366490993671936995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5911255155321324895915993 4433441366490993671936995)
              ·
                refine ⟨6650162049736490507905493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433441366490993671936995 6650162049736490507905493)
                ·
                  refine ⟨155863173040698996279035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6650162049736490507905493 155863173040698996279035)
                  ·
                    rfl

theorem cell22_1365941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_1365941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1365941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1365941 prefixEnd_1365941 := by exact prefixLift 1365941
  have htrace : WordTrace (prefixWord ++ tailWord_1365941) baseStart_1365941 baseEnd_1365941 := by
    simpa [prefixWord, tailWord_1365941, baseEnd_1365941] using wordTrace_append hprefix tailTrace_1365941
  have hstable : (prefixWord ++ tailWord_1365941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365941).length < 2 ^ (prefixWord ++ tailWord_1365941).sum := by decide
  have hdescent : baseEnd_1365941 < baseStart_1365941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366020 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1366020 : Nat := 118140960795 + 1366020 * 2 ^ 59
def prefixEnd_1366020 : Nat := 4983230072969 + 3 ^ 40 * 1366020 * 2
def baseEnd_1366020 : Nat := 155872187478855705370621

theorem tailTrace_1366020 : CollatzResearch.WordTrace tailWord_1366020 prefixEnd_1366020 155872187478855705370621 := by
  unfold tailWord_1366020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24911421255575156243667757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33215228340766874991557009 24911421255575156243667757)
  ·
    refine ⟨9341782970840683591375409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24911421255575156243667757 9341782970840683591375409)
    ·
      refine ⟨7006337228130512693531557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9341782970840683591375409 7006337228130512693531557)
      ·
        refine ⟨1313688230274471130037167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7006337228130512693531557 1313688230274471130037167)
        ·
          refine ⟨1970532345411706695055751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313688230274471130037167 1970532345411706695055751)
          ·
            refine ⟨2955798518117560042583627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970532345411706695055751 2955798518117560042583627)
            ·
              refine ⟨4433697777176340063875441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955798518117560042583627 4433697777176340063875441)
              ·
                refine ⟨3325273332882255047906581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433697777176340063875441 3325273332882255047906581)
                ·
                  refine ⟨155872187478855705370621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3325273332882255047906581 155872187478855705370621)
                  ·
                    rfl

theorem cell22_1366020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1366020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366020 prefixEnd_1366020 := by exact prefixLift 1366020
  have htrace : WordTrace (prefixWord ++ tailWord_1366020) baseStart_1366020 baseEnd_1366020 := by
    simpa [prefixWord, tailWord_1366020, baseEnd_1366020] using wordTrace_append hprefix tailTrace_1366020
  have hstable : (prefixWord ++ tailWord_1366020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366020).length < 2 ^ (prefixWord ++ tailWord_1366020).sum := by decide
  have hdescent : baseEnd_1366020 < baseStart_1366020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366039 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 1, 4]
def baseStart_1366039 : Nat := 118140960795 + 1366039 * 2 ^ 59
def prefixEnd_1366039 : Nat := 4983230072969 + 3 ^ 40 * 1366039 * 2
def baseEnd_1366039 : Nat := 467623066524857399886805

theorem tailTrace_1366039 : CollatzResearch.WordTrace tailWord_1366039 prefixEnd_1366039 467623066524857399886805 := by
  unfold tailWord_1366039
  simp only [CollatzResearch.WordTrace]
  refine ⟨49823535498081478732277171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33215690332054319154851447 49823535498081478732277171)
  ·
    refine ⟨74735303247122218098415757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49823535498081478732277171 74735303247122218098415757)
    ·
      refine ⟨28025738717670831786905909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74735303247122218098415757 28025738717670831786905909)
      ·
        refine ⟨2627413004781640480022429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28025738717670831786905909 2627413004781640480022429)
        ·
          refine ⟨985279876793115180008411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2627413004781640480022429 985279876793115180008411)
          ·
            refine ⟨1477919815189672770012617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985279876793115180008411 1477919815189672770012617)
            ·
              refine ⟨1108439861392254577509463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477919815189672770012617 1108439861392254577509463)
              ·
                refine ⟨1662659792088381866264195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108439861392254577509463 1662659792088381866264195)
                ·
                  refine ⟨2493989688132572799396293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662659792088381866264195 2493989688132572799396293)
                  ·
                    refine ⟨467623066524857399886805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2493989688132572799396293 467623066524857399886805)
                    ·
                      rfl

theorem cell22_1366039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_1366039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366039 prefixEnd_1366039 := by exact prefixLift 1366039
  have htrace : WordTrace (prefixWord ++ tailWord_1366039) baseStart_1366039 baseEnd_1366039 := by
    simpa [prefixWord, tailWord_1366039, baseEnd_1366039] using wordTrace_append hprefix tailTrace_1366039
  have hstable : (prefixWord ++ tailWord_1366039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366039).length < 2 ^ (prefixWord ++ tailWord_1366039).sum := by decide
  have hdescent : baseEnd_1366039 < baseStart_1366039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366093 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1366093 : Nat := 118140960795 + 1366093 * 2 ^ 59
def prefixEnd_1366093 : Nat := 4983230072969 + 3 ^ 40 * 1366093 * 2
def baseEnd_1366093 : Nat := 155880517276139753012213

theorem tailTrace_1366093 : CollatzResearch.WordTrace tailWord_1366093 prefixEnd_1366093 155880517276139753012213 := by
  unfold tailWord_1366093
  simp only [CollatzResearch.WordTrace]
  refine ⟨49825505039885845954742933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33217003359923897303161955 49825505039885845954742933)
  ·
    refine ⟨2335570548744649029128575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49825505039885845954742933 2335570548744649029128575)
    ·
      refine ⟨3503355823116973543692863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335570548744649029128575 3503355823116973543692863)
      ·
        refine ⟨5255033734675460315539295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503355823116973543692863 5255033734675460315539295)
        ·
          refine ⟨7882550602013190473308943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5255033734675460315539295 7882550602013190473308943)
          ·
            refine ⟨11823825903019785709963415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7882550602013190473308943 11823825903019785709963415)
            ·
              refine ⟨17735738854529678564945123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11823825903019785709963415 17735738854529678564945123)
              ·
                refine ⟨26603608281794517847417685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17735738854529678564945123 26603608281794517847417685)
                ·
                  refine ⟨155880517276139753012213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26603608281794517847417685 155880517276139753012213)
                  ·
                    rfl

theorem cell22_1366093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1366093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366093 prefixEnd_1366093 := by exact prefixLift 1366093
  have htrace : WordTrace (prefixWord ++ tailWord_1366093) baseStart_1366093 baseEnd_1366093 := by
    simpa [prefixWord, tailWord_1366093, baseEnd_1366093] using wordTrace_append hprefix tailTrace_1366093
  have hstable : (prefixWord ++ tailWord_1366093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366093).length < 2 ^ (prefixWord ++ tailWord_1366093).sum := by decide
  have hdescent : baseEnd_1366093 < baseStart_1366093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366114 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1366114 : Nat := 118140960795 + 1366114 * 2 ^ 59
def prefixEnd_1366114 : Nat := 4983230072969 + 3 ^ 40 * 1366114 * 2
def baseEnd_1366114 : Nat := 467648740557582204261575

theorem tailTrace_1366114 : CollatzResearch.WordTrace tailWord_1366114 prefixEnd_1366114 467648740557582204261575 := by
  unfold tailWord_1366114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456567743202441635314349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33217513981873177694171597 12456567743202441635314349)
  ·
    refine ⟨4671212903700915613242881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12456567743202441635314349 4671212903700915613242881)
    ·
      refine ⟨3503409677775686709932161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4671212903700915613242881 3503409677775686709932161)
      ·
        refine ⟨2627557258331765032449121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3503409677775686709932161 2627557258331765032449121)
        ·
          refine ⟨1970667943748823774336841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627557258331765032449121 1970667943748823774336841)
          ·
            refine ⟨1478000957811617830752631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970667943748823774336841 1478000957811617830752631)
            ·
              refine ⟨2217001436717426746128947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478000957811617830752631 2217001436717426746128947)
              ·
                refine ⟨3325502155076140119193421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217001436717426746128947 3325502155076140119193421)
                ·
                  refine ⟨1247063308153552544697533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3325502155076140119193421 1247063308153552544697533)
                  ·
                    refine ⟨467648740557582204261575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247063308153552544697533 467648740557582204261575)
                    ·
                      rfl

theorem cell22_1366114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1366114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366114 prefixEnd_1366114 := by exact prefixLift 1366114
  have htrace : WordTrace (prefixWord ++ tailWord_1366114) baseStart_1366114 baseEnd_1366114 := by
    simpa [prefixWord, tailWord_1366114, baseEnd_1366114] using wordTrace_append hprefix tailTrace_1366114
  have hstable : (prefixWord ++ tailWord_1366114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366114).length < 2 ^ (prefixWord ++ tailWord_1366114).sum := by decide
  have hdescent : baseEnd_1366114 < baseStart_1366114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366140 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1366140 : Nat := 118140960795 + 1366140 * 2 ^ 59
def prefixEnd_1366140 : Nat := 4983230072969 + 3 ^ 40 * 1366140 * 2
def baseEnd_1366140 : Nat := 467657640888926803111495

theorem tailTrace_1366140 : CollatzResearch.WordTrace tailWord_1366140 prefixEnd_1366140 467657640888926803111495 := by
  unfold tailWord_1366140
  simp only [CollatzResearch.WordTrace]
  refine ⟨24913609635357786490851937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33218146180477048654469249 24913609635357786490851937)
  ·
    refine ⟨18685207226518339868138953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24913609635357786490851937 18685207226518339868138953)
    ·
      refine ⟨14013905419888754901104215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18685207226518339868138953 14013905419888754901104215)
      ·
        refine ⟨21020858129833132351656323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013905419888754901104215 21020858129833132351656323)
        ·
          refine ⟨31531287194749698527484485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21020858129833132351656323 31531287194749698527484485)
          ·
            refine ⟨5912116349015568473903341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31531287194749698527484485 5912116349015568473903341)
            ·
              refine ⟨2217043630880838177713753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5912116349015568473903341 2217043630880838177713753)
              ·
                refine ⟨1662782723160628633285315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217043630880838177713753 1662782723160628633285315)
                ·
                  refine ⟨2494174084740942949927973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662782723160628633285315 2494174084740942949927973)
                  ·
                    refine ⟨467657640888926803111495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494174084740942949927973 467657640888926803111495)
                    ·
                      rfl

theorem cell22_1366140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1366140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366140 prefixEnd_1366140 := by exact prefixLift 1366140
  have htrace : WordTrace (prefixWord ++ tailWord_1366140) baseStart_1366140 baseEnd_1366140 := by
    simpa [prefixWord, tailWord_1366140, baseEnd_1366140] using wordTrace_append hprefix tailTrace_1366140
  have hstable : (prefixWord ++ tailWord_1366140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366140).length < 2 ^ (prefixWord ++ tailWord_1366140).sum := by decide
  have hdescent : baseEnd_1366140 < baseStart_1366140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366153 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_1366153 : Nat := 118140960795 + 1366153 * 2 ^ 59
def prefixEnd_1366153 : Nat := 4983230072969 + 3 ^ 40 * 1366153 * 2
def baseEnd_1366153 : Nat := 467662091054599102536455

theorem tailTrace_1366153 : CollatzResearch.WordTrace tailWord_1366153 prefixEnd_1366153 467662091054599102536455 := by
  unfold tailWord_1366153
  simp only [CollatzResearch.WordTrace]
  refine ⟨49827693419668476201927113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33218462279778984134618075 49827693419668476201927113)
  ·
    refine ⟨37370770064751357151445335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49827693419668476201927113 37370770064751357151445335)
    ·
      refine ⟨56056155097127035727168003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37370770064751357151445335 56056155097127035727168003)
      ·
        refine ⟨84084232645690553590752005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56056155097127035727168003 84084232645690553590752005)
        ·
          refine ⟨15765793621066978798266001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84084232645690553590752005 15765793621066978798266001)
          ·
            refine ⟨11824345215800234098699501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15765793621066978798266001 11824345215800234098699501)
            ·
              refine ⟨4434129455925087787012313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11824345215800234098699501 4434129455925087787012313)
              ·
                refine ⟨3325597091943815840259235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434129455925087787012313 3325597091943815840259235)
                ·
                  refine ⟨4988395637915723760388853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325597091943815840259235 4988395637915723760388853)
                  ·
                    refine ⟨467662091054599102536455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4988395637915723760388853 467662091054599102536455)
                    ·
                      rfl

theorem cell22_1366153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_1366153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366153 prefixEnd_1366153 := by exact prefixLift 1366153
  have htrace : WordTrace (prefixWord ++ tailWord_1366153) baseStart_1366153 baseEnd_1366153 := by
    simpa [prefixWord, tailWord_1366153, baseEnd_1366153] using wordTrace_append hprefix tailTrace_1366153
  have hstable : (prefixWord ++ tailWord_1366153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366153).length < 2 ^ (prefixWord ++ tailWord_1366153).sum := by decide
  have hdescent : baseEnd_1366153 < baseStart_1366153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366232 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1366232 : Nat := 118140960795 + 1366232 * 2 ^ 59
def prefixEnd_1366232 : Nat := 4983230072969 + 3 ^ 40 * 1366232 * 2
def baseEnd_1366232 : Nat := 467689134369069229811213

theorem tailTrace_1366232 : CollatzResearch.WordTrace tailWord_1366232 prefixEnd_1366232 467689134369069229811213 := by
  unfold tailWord_1366232
  simp only [CollatzResearch.WordTrace]
  refine ⟨24915287393191136347026475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33220383190921515129368633 24915287393191136347026475)
  ·
    refine ⟨37372931089786704520539713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24915287393191136347026475 37372931089786704520539713)
    ·
      refine ⟨28029698317340028390404785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37372931089786704520539713 28029698317340028390404785)
      ·
        refine ⟨21022273738005021292803589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28029698317340028390404785 21022273738005021292803589)
        ·
          refine ⟨3941676325875941492400673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21022273738005021292803589 3941676325875941492400673)
          ·
            refine ⟨2956257244406956119300505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3941676325875941492400673 2956257244406956119300505)
            ·
              refine ⟨2217192933305217089475379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956257244406956119300505 2217192933305217089475379)
              ·
                refine ⟨3325789399957825634213069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217192933305217089475379 3325789399957825634213069)
                ·
                  refine ⟨1247171024984184612829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3325789399957825634213069 1247171024984184612829901)
                  ·
                    refine ⟨467689134369069229811213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247171024984184612829901 467689134369069229811213)
                    ·
                      rfl

theorem cell22_1366232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1366232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366232 prefixEnd_1366232 := by exact prefixLift 1366232
  have htrace : WordTrace (prefixWord ++ tailWord_1366232) baseStart_1366232 baseEnd_1366232 := by
    simpa [prefixWord, tailWord_1366232, baseEnd_1366232] using wordTrace_append hprefix tailTrace_1366232
  have hstable : (prefixWord ++ tailWord_1366232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366232).length < 2 ^ (prefixWord ++ tailWord_1366232).sum := by decide
  have hdescent : baseEnd_1366232 < baseStart_1366232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366275 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 1, 4]
def baseStart_1366275 : Nat := 118140960795 + 1366275 * 2 ^ 59
def prefixEnd_1366275 : Nat := 4983230072969 + 3 ^ 40 * 1366275 * 2
def baseEnd_1366275 : Nat := 467703854147831450986081

theorem tailTrace_1366275 : CollatzResearch.WordTrace tailWord_1366275 prefixEnd_1366275 467703854147831450986081 := by
  unfold tailWord_1366275
  simp only [CollatzResearch.WordTrace]
  refine ⟨49832143125226491037868279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33221428750150994025245519 49832143125226491037868279)
  ·
    refine ⟨74748214687839736556802419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49832143125226491037868279 74748214687839736556802419)
    ·
      refine ⟨112122322031759604835203629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74748214687839736556802419 112122322031759604835203629)
      ·
        refine ⟨42045870761909851813201361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112122322031759604835203629 42045870761909851813201361)
        ·
          refine ⟨31534403071432388859901021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42045870761909851813201361 31534403071432388859901021)
          ·
            refine ⟨11825401151787145822462883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31534403071432388859901021 11825401151787145822462883)
            ·
              refine ⟨17738101727680718733694325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11825401151787145822462883 17738101727680718733694325)
              ·
                refine ⟨1662947036970067381283843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17738101727680718733694325 1662947036970067381283843)
                ·
                  refine ⟨2494420555455101071925765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662947036970067381283843 2494420555455101071925765)
                  ·
                    refine ⟨467703854147831450986081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494420555455101071925765 467703854147831450986081)
                    ·
                      rfl

theorem cell22_1366275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4].length) (baseStart_1366275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366275 prefixEnd_1366275 := by exact prefixLift 1366275
  have htrace : WordTrace (prefixWord ++ tailWord_1366275) baseStart_1366275 baseEnd_1366275 := by
    simpa [prefixWord, tailWord_1366275, baseEnd_1366275] using wordTrace_append hprefix tailTrace_1366275
  have hstable : (prefixWord ++ tailWord_1366275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366275).length < 2 ^ (prefixWord ++ tailWord_1366275).sum := by decide
  have hdescent : baseEnd_1366275 < baseStart_1366275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366309 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_1366309 : Nat := 118140960795 + 1366309 * 2 ^ 59
def prefixEnd_1366309 : Nat := 4983230072969 + 3 ^ 40 * 1366309 * 2
def baseEnd_1366309 : Nat := 467715493042666695635977

theorem tailTrace_1366309 : CollatzResearch.WordTrace tailWord_1366309 prefixEnd_1366309 467715493042666695635977 := by
  unfold tailWord_1366309
  simp only [CollatzResearch.WordTrace]
  refine ⟨49833383207103314844605981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33222255471402209896403987 49833383207103314844605981)
  ·
    refine ⟨18687518702663743066727243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49833383207103314844605981 18687518702663743066727243)
    ·
      refine ⟨28031278053995614600090865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18687518702663743066727243 28031278053995614600090865)
      ·
        refine ⟨21023458540496710950068149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28031278053995614600090865 21023458540496710950068149)
        ·
          refine ⟨1970949238171566651568889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21023458540496710950068149 1970949238171566651568889)
          ·
            refine ⟨1478211928628674988676667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970949238171566651568889 1478211928628674988676667)
            ·
              refine ⟨2217317892943012483015001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478211928628674988676667 2217317892943012483015001)
              ·
                refine ⟨1662988419707259362261251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217317892943012483015001 1662988419707259362261251)
                ·
                  refine ⟨2494482629560889043391877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662988419707259362261251 2494482629560889043391877)
                  ·
                    refine ⟨467715493042666695635977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494482629560889043391877 467715493042666695635977)
                    ·
                      rfl

theorem cell22_1366309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_1366309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366309 prefixEnd_1366309 := by exact prefixLift 1366309
  have htrace : WordTrace (prefixWord ++ tailWord_1366309) baseStart_1366309 baseEnd_1366309 := by
    simpa [prefixWord, tailWord_1366309, baseEnd_1366309] using wordTrace_append hprefix tailTrace_1366309
  have hstable : (prefixWord ++ tailWord_1366309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366309).length < 2 ^ (prefixWord ++ tailWord_1366309).sum := by decide
  have hdescent : baseEnd_1366309 < baseStart_1366309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366322 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1366322 : Nat := 118140960795 + 1366322 * 2 ^ 59
def prefixEnd_1366322 : Nat := 4983230072969 + 3 ^ 40 * 1366322 * 2
def baseEnd_1366322 : Nat := 467719943208338995060937

theorem tailTrace_1366322 : CollatzResearch.WordTrace tailWord_1366322 prefixEnd_1366322 467719943208338995060937 := by
  unfold tailWord_1366322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12458464339014054516207305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33222571570704145376552813 12458464339014054516207305)
  ·
    refine ⟨9343848254260540887155479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12458464339014054516207305 9343848254260540887155479)
    ·
      refine ⟨14015772381390811330733219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343848254260540887155479 14015772381390811330733219)
      ·
        refine ⟨21023658572086216996099829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14015772381390811330733219 21023658572086216996099829)
        ·
          refine ⟨1970967991133082843384359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21023658572086216996099829 1970967991133082843384359)
          ·
            refine ⟨2956451986699624265076539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970967991133082843384359 2956451986699624265076539)
            ·
              refine ⟨4434677980049436397614809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956451986699624265076539 4434677980049436397614809)
              ·
                refine ⟨3326008485037077298211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434677980049436397614809 3326008485037077298211107)
                ·
                  refine ⟨4989012727555615947316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326008485037077298211107 4989012727555615947316661)
                  ·
                    refine ⟨467719943208338995060937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4989012727555615947316661 467719943208338995060937)
                    ·
                      rfl

theorem cell22_1366322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1366322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366322 prefixEnd_1366322 := by exact prefixLift 1366322
  have htrace : WordTrace (prefixWord ++ tailWord_1366322) baseStart_1366322 baseEnd_1366322 := by
    simpa [prefixWord, tailWord_1366322, baseEnd_1366322] using wordTrace_append hprefix tailTrace_1366322
  have hstable : (prefixWord ++ tailWord_1366322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366322).length < 2 ^ (prefixWord ++ tailWord_1366322).sum := by decide
  have hdescent : baseEnd_1366322 < baseStart_1366322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366384 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 1, 3]
def baseStart_1366384 : Nat := 118140960795 + 1366384 * 2 ^ 59
def prefixEnd_1366384 : Nat := 4983230072969 + 3 ^ 40 * 1366384 * 2
def baseEnd_1366384 : Nat := 467741167075391500010747

theorem tailTrace_1366384 : CollatzResearch.WordTrace tailWord_1366384 prefixEnd_1366384 467741167075391500010747 := by
  unfold tailWord_1366384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24918059340915801326793103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33224079121221068435724137 24918059340915801326793103)
  ·
    refine ⟨37377089011373701990189655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24918059340915801326793103 37377089011373701990189655)
    ·
      refine ⟨56065633517060552985284483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37377089011373701990189655 56065633517060552985284483)
      ·
        refine ⟨84098450275590829477926725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56065633517060552985284483 84098450275590829477926725)
        ·
          refine ⟨15768459426673280527111261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84098450275590829477926725 15768459426673280527111261)
          ·
            refine ⟨5913172285002480197666723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15768459426673280527111261 5913172285002480197666723)
            ·
              refine ⟨8869758427503720296500085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913172285002480197666723 8869758427503720296500085)
              ·
                refine ⟨831539852578473777796883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8869758427503720296500085 831539852578473777796883)
                ·
                  refine ⟨1247309778867710666695325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831539852578473777796883 1247309778867710666695325)
                  ·
                    refine ⟨467741167075391500010747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247309778867710666695325 467741167075391500010747)
                    ·
                      rfl

theorem cell22_1366384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_1366384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366384 prefixEnd_1366384 := by exact prefixLift 1366384
  have htrace : WordTrace (prefixWord ++ tailWord_1366384) baseStart_1366384 baseEnd_1366384 := by
    simpa [prefixWord, tailWord_1366384, baseEnd_1366384] using wordTrace_append hprefix tailTrace_1366384
  have hstable : (prefixWord ++ tailWord_1366384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366384).length < 2 ^ (prefixWord ++ tailWord_1366384).sum := by decide
  have hdescent : baseEnd_1366384 < baseStart_1366384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366390 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1366390 : Nat := 118140960795 + 1366390 * 2 ^ 59
def prefixEnd_1366390 : Nat := 4983230072969 + 3 ^ 40 * 1366390 * 2
def baseEnd_1366390 : Nat := 467743220998009484360729

theorem tailTrace_1366390 : CollatzResearch.WordTrace tailWord_1366390 prefixEnd_1366390 467743220998009484360729 := by
  unfold tailWord_1366390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114771094988116604894039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33224225013206577118869749 3114771094988116604894039)
  ·
    refine ⟨4672156642482174907341059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3114771094988116604894039 4672156642482174907341059)
    ·
      refine ⟨7008234963723262361011589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4672156642482174907341059 7008234963723262361011589)
      ·
        refine ⟨1314044055698111692689673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7008234963723262361011589 1314044055698111692689673)
        ·
          refine ⟨985533041773583769517255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1314044055698111692689673 985533041773583769517255)
          ·
            refine ⟨1478299562660375654275883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985533041773583769517255 1478299562660375654275883)
            ·
              refine ⟨2217449343990563481413825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478299562660375654275883 2217449343990563481413825)
              ·
                refine ⟨1663087007992922611060369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217449343990563481413825 1663087007992922611060369)
                ·
                  refine ⟨1247315255994691958295277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1663087007992922611060369 1247315255994691958295277)
                  ·
                    refine ⟨467743220998009484360729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247315255994691958295277 467743220998009484360729)
                    ·
                      rfl

theorem cell22_1366390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1366390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366390 prefixEnd_1366390 := by exact prefixLift 1366390
  have htrace : WordTrace (prefixWord ++ tailWord_1366390) baseStart_1366390 baseEnd_1366390 := by
    simpa [prefixWord, tailWord_1366390, baseEnd_1366390] using wordTrace_append hprefix tailTrace_1366390
  have hstable : (prefixWord ++ tailWord_1366390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366390).length < 2 ^ (prefixWord ++ tailWord_1366390).sum := by decide
  have hdescent : baseEnd_1366390 < baseStart_1366390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366395 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_1366395 : Nat := 118140960795 + 1366395 * 2 ^ 59
def prefixEnd_1366395 : Nat := 4983230072969 + 3 ^ 40 * 1366395 * 2
def baseEnd_1366395 : Nat := 467744932600191137985713

theorem tailTrace_1366395 : CollatzResearch.WordTrace tailWord_1366395 prefixEnd_1366395 467744932600191137985713 := by
  unfold tailWord_1366395
  simp only [CollatzResearch.WordTrace]
  refine ⟨49836519884791751532236639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33224346589861167688157759 49836519884791751532236639)
  ·
    refine ⟨74754779827187627298354959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49836519884791751532236639 74754779827187627298354959)
    ·
      refine ⟨112132169740781440947532439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74754779827187627298354959 112132169740781440947532439)
      ·
        refine ⟨168198254611172161421298659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112132169740781440947532439 168198254611172161421298659)
        ·
          refine ⟨252297381916758242131947989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168198254611172161421298659 252297381916758242131947989)
          ·
            refine ⟨5913219888674021299967531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 252297381916758242131947989 5913219888674021299967531)
            ·
              refine ⟨8869829833011031949951297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913219888674021299967531 8869829833011031949951297)
              ·
                refine ⟨6652372374758273962463473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8869829833011031949951297 6652372374758273962463473)
                ·
                  refine ⟨4989279281068705471847605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6652372374758273962463473 4989279281068705471847605)
                  ·
                    refine ⟨467744932600191137985713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4989279281068705471847605 467744932600191137985713)
                    ·
                      rfl

theorem cell22_1366395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_1366395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366395 prefixEnd_1366395 := by exact prefixLift 1366395
  have htrace : WordTrace (prefixWord ++ tailWord_1366395) baseStart_1366395 baseEnd_1366395 := by
    simpa [prefixWord, tailWord_1366395, baseEnd_1366395] using wordTrace_append hprefix tailTrace_1366395
  have hstable : (prefixWord ++ tailWord_1366395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366395).length < 2 ^ (prefixWord ++ tailWord_1366395).sum := by decide
  have hdescent : baseEnd_1366395 < baseStart_1366395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366397 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 5]
def baseStart_1366397 : Nat := 118140960795 + 1366397 * 2 ^ 59
def prefixEnd_1366397 : Nat := 4983230072969 + 3 ^ 40 * 1366397 * 2
def baseEnd_1366397 : Nat := 155915205747021266478569

theorem tailTrace_1366397 : CollatzResearch.WordTrace tailWord_1366397 prefixEnd_1366397 155915205747021266478569 := by
  unfold tailWord_1366397
  simp only [CollatzResearch.WordTrace]
  refine ⟨49836592830784505873809445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33224395220523003915872963 49836592830784505873809445)
  ·
    refine ⟨9344361155772094851339271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49836592830784505873809445 9344361155772094851339271)
    ·
      refine ⟨14016541733658142277008907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9344361155772094851339271 14016541733658142277008907)
      ·
        refine ⟨21024812600487213415513361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14016541733658142277008907 21024812600487213415513361)
        ·
          refine ⟨15768609450365410061635021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21024812600487213415513361 15768609450365410061635021)
          ·
            refine ⟨5913228543887028773113133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15768609450365410061635021 5913228543887028773113133)
            ·
              refine ⟨2217460703957635789917425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5913228543887028773113133 2217460703957635789917425)
              ·
                refine ⟨1663095527968226842438069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217460703957635789917425 1663095527968226842438069)
                ·
                  refine ⟨155915205747021266478569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663095527968226842438069 155915205747021266478569)
                  ·
                    rfl

theorem cell22_1366397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_1366397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366397 prefixEnd_1366397 := by exact prefixLift 1366397
  have htrace : WordTrace (prefixWord ++ tailWord_1366397) baseStart_1366397 baseEnd_1366397 := by
    simpa [prefixWord, tailWord_1366397, baseEnd_1366397] using wordTrace_append hprefix tailTrace_1366397
  have hstable : (prefixWord ++ tailWord_1366397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366397).length < 2 ^ (prefixWord ++ tailWord_1366397).sum := by decide
  have hdescent : baseEnd_1366397 < baseStart_1366397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366401 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1366401 : Nat := 118140960795 + 1366401 * 2 ^ 59
def prefixEnd_1366401 : Nat := 4983230072969 + 3 ^ 40 * 1366401 * 2
def baseEnd_1366401 : Nat := 467746986522809122335695

theorem tailTrace_1366401 : CollatzResearch.WordTrace tailWord_1366401 prefixEnd_1366401 467746986522809122335695 := by
  unfold tailWord_1366401
  simp only [CollatzResearch.WordTrace]
  refine ⟨49836738722770014556955057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33224492481846676371303371 49836738722770014556955057)
  ·
    refine ⟨37377554042077510917716293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49836738722770014556955057 37377554042077510917716293)
    ·
      refine ⟨7008291382889533297071805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37377554042077510917716293 7008291382889533297071805)
      ·
        refine ⟨2628109268583574986401927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7008291382889533297071805 2628109268583574986401927)
        ·
          refine ⟨3942163902875362479602891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628109268583574986401927 3942163902875362479602891)
          ·
            refine ⟨5913245854313043719404337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942163902875362479602891 5913245854313043719404337)
            ·
              refine ⟨4434934390734782789553253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5913245854313043719404337 4434934390734782789553253)
              ·
                refine ⟨831550198262771773041235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4434934390734782789553253 831550198262771773041235)
                ·
                  refine ⟨1247325297394157659561853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831550198262771773041235 1247325297394157659561853)
                  ·
                    refine ⟨467746986522809122335695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247325297394157659561853 467746986522809122335695)
                    ·
                      rfl

theorem cell22_1366401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1366401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366401 prefixEnd_1366401 := by exact prefixLift 1366401
  have htrace : WordTrace (prefixWord ++ tailWord_1366401) baseStart_1366401 baseEnd_1366401 := by
    simpa [prefixWord, tailWord_1366401, baseEnd_1366401] using wordTrace_append hprefix tailTrace_1366401
  have hstable : (prefixWord ++ tailWord_1366401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366401).length < 2 ^ (prefixWord ++ tailWord_1366401).sum := by decide
  have hdescent : baseEnd_1366401 < baseStart_1366401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366425 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 6]
def baseStart_1366425 : Nat := 118140960795 + 1366425 * 2 ^ 59
def prefixEnd_1366425 : Nat := 4983230072969 + 3 ^ 40 * 1366425 * 2
def baseEnd_1366425 : Nat := 155918400737760353245207

theorem tailTrace_1366425 : CollatzResearch.WordTrace tailWord_1366425 prefixEnd_1366425 155918400737760353245207 := by
  unfold tailWord_1366425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49837614074683066655828729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33225076049788711103885819 49837614074683066655828729)
  ·
    refine ⟨37378210556012299991871547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49837614074683066655828729 37378210556012299991871547)
    ·
      refine ⟨56067315834018449987807321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37378210556012299991871547 56067315834018449987807321)
      ·
        refine ⟨42050486875513837490855491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56067315834018449987807321 42050486875513837490855491)
        ·
          refine ⟨63075730313270756236283237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42050486875513837490855491 63075730313270756236283237)
          ·
            refine ⟨11826699433738266794303107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63075730313270756236283237 11826699433738266794303107)
            ·
              refine ⟨17740049150607400191454661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11826699433738266794303107 17740049150607400191454661)
              ·
                refine ⟨3326259215738887535897749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17740049150607400191454661 3326259215738887535897749)
                ·
                  refine ⟨155918400737760353245207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3326259215738887535897749 155918400737760353245207)
                  ·
                    rfl

theorem cell22_1366425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_1366425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366425 prefixEnd_1366425 := by exact prefixLift 1366425
  have htrace : WordTrace (prefixWord ++ tailWord_1366425) baseStart_1366425 baseEnd_1366425 := by
    simpa [prefixWord, tailWord_1366425, baseEnd_1366425] using wordTrace_append hprefix tailTrace_1366425
  have hstable : (prefixWord ++ tailWord_1366425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366425).length < 2 ^ (prefixWord ++ tailWord_1366425).sum := by decide
  have hdescent : baseEnd_1366425 < baseStart_1366425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366452 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1366452 : Nat := 118140960795 + 1366452 * 2 ^ 59
def prefixEnd_1366452 : Nat := 4983230072969 + 3 ^ 40 * 1366452 * 2
def baseEnd_1366452 : Nat := 467764444865061989310539

theorem tailTrace_1366452 : CollatzResearch.WordTrace tailWord_1366452 prefixEnd_1366452 467764444865061989310539 := by
  unfold tailWord_1366452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919299422792625133530805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33225732563723500178041073 24919299422792625133530805)
  ·
    refine ⟨2336184320886808606268513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24919299422792625133530805 2336184320886808606268513)
    ·
      refine ⟨1752138240665106454701385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2336184320886808606268513 1752138240665106454701385)
      ·
        refine ⟨1314103680498829841026039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1752138240665106454701385 1314103680498829841026039)
        ·
          refine ⟨1971155520748244761539059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314103680498829841026039 1971155520748244761539059)
          ·
            refine ⟨2956733281122367142308589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971155520748244761539059 2956733281122367142308589)
            ·
              refine ⟨1108774980420887678365721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2956733281122367142308589 1108774980420887678365721)
              ·
                refine ⟨831581235315665758774291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108774980420887678365721 831581235315665758774291)
                ·
                  refine ⟨1247371852973498638161437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831581235315665758774291 1247371852973498638161437)
                  ·
                    refine ⟨467764444865061989310539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247371852973498638161437 467764444865061989310539)
                    ·
                      rfl

theorem cell22_1366452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1366452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366452 prefixEnd_1366452 := by exact prefixLift 1366452
  have htrace : WordTrace (prefixWord ++ tailWord_1366452) baseStart_1366452 baseEnd_1366452 := by
    simpa [prefixWord, tailWord_1366452, baseEnd_1366452] using wordTrace_append hprefix tailTrace_1366452
  have hstable : (prefixWord ++ tailWord_1366452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366452).length < 2 ^ (prefixWord ++ tailWord_1366452).sum := by decide
  have hdescent : baseEnd_1366452 < baseStart_1366452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366465 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 5]
def baseStart_1366465 : Nat := 118140960795 + 1366465 * 2 ^ 59
def prefixEnd_1366465 : Nat := 4983230072969 + 3 ^ 40 * 1366465 * 2
def baseEnd_1366465 : Nat := 155922965010244762911833

theorem tailTrace_1366465 : CollatzResearch.WordTrace tailWord_1366465 prefixEnd_1366465 155922965010244762911833 := by
  unfold tailWord_1366465
  simp only [CollatzResearch.WordTrace]
  refine ⟨49839072994538153487284849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33226048663025435658189899 49839072994538153487284849)
  ·
    refine ⟨37379304745903615115463637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49839072994538153487284849 37379304745903615115463637)
    ·
      refine ⟨876077454982115979268679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37379304745903615115463637 876077454982115979268679)
      ·
        refine ⟨1314116182473173968903019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876077454982115979268679 1314116182473173968903019)
        ·
          refine ⟨1971174273709760953354529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314116182473173968903019 1971174273709760953354529)
          ·
            refine ⟨1478380705282320715015897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971174273709760953354529 1478380705282320715015897)
            ·
              refine ⟨1108785528961740536261923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478380705282320715015897 1108785528961740536261923)
              ·
                refine ⟨1663178293442610804392885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108785528961740536261923 1663178293442610804392885)
                ·
                  refine ⟨155922965010244762911833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663178293442610804392885 155922965010244762911833)
                  ·
                    rfl

theorem cell22_1366465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_1366465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366465 prefixEnd_1366465 := by exact prefixLift 1366465
  have htrace : WordTrace (prefixWord ++ tailWord_1366465) baseStart_1366465 baseEnd_1366465 := by
    simpa [prefixWord, tailWord_1366465, baseEnd_1366465] using wordTrace_append hprefix tailTrace_1366465
  have hstable : (prefixWord ++ tailWord_1366465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366465).length < 2 ^ (prefixWord ++ tailWord_1366465).sum := by decide
  have hdescent : baseEnd_1366465 < baseStart_1366465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366474 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1366474 : Nat := 118140960795 + 1366474 * 2 ^ 59
def prefixEnd_1366474 : Nat := 4983230072969 + 3 ^ 40 * 1366474 * 2
def baseEnd_1366474 : Nat := 467771975914661265260471

theorem tailTrace_1366474 : CollatzResearch.WordTrace tailWord_1366474 prefixEnd_1366474 467771975914661265260471 := by
  unfold tailWord_1366474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459850312876387006090619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33226267501003698682908317 12459850312876387006090619)
  ·
    refine ⟨18689775469314580509135929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12459850312876387006090619 18689775469314580509135929)
    ·
      refine ⟨14017331601985935381851947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18689775469314580509135929 14017331601985935381851947)
      ·
        refine ⟨21025997402978903072777921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14017331601985935381851947 21025997402978903072777921)
        ·
          refine ⟨15769498052234177304583441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21025997402978903072777921 15769498052234177304583441)
          ·
            refine ⟨11827123539175632978437581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15769498052234177304583441 11827123539175632978437581)
            ·
              refine ⟨4435171327190862366914093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11827123539175632978437581 4435171327190862366914093)
              ·
                refine ⟨1663189247696573387592785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4435171327190862366914093 1663189247696573387592785)
                ·
                  refine ⟨1247391935772430040694589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1663189247696573387592785 1247391935772430040694589)
                  ·
                    refine ⟨467771975914661265260471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247391935772430040694589 467771975914661265260471)
                    ·
                      rfl

theorem cell22_1366474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1366474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366474 prefixEnd_1366474 := by exact prefixLift 1366474
  have htrace : WordTrace (prefixWord ++ tailWord_1366474) baseStart_1366474 baseEnd_1366474 := by
    simpa [prefixWord, tailWord_1366474, baseEnd_1366474] using wordTrace_append hprefix tailTrace_1366474
  have hstable : (prefixWord ++ tailWord_1366474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366474).length < 2 ^ (prefixWord ++ tailWord_1366474).sum := by decide
  have hdescent : baseEnd_1366474 < baseStart_1366474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366577 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 6]
def baseStart_1366577 : Nat := 118140960795 + 1366577 * 2 ^ 59
def prefixEnd_1366577 : Nat := 4983230072969 + 3 ^ 40 * 1366577 * 2
def baseEnd_1366577 : Nat := 155935744973201109978385

theorem tailTrace_1366577 : CollatzResearch.WordTrace tailWord_1366577 prefixEnd_1366577 155935744973201109978385 := by
  unfold tailWord_1366577
  simp only [CollatzResearch.WordTrace]
  refine ⟨49843157970132396615361985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33228771980088264410241323 49843157970132396615361985)
  ·
    refine ⟨37382368477599297461521489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49843157970132396615361985 37382368477599297461521489)
    ·
      refine ⟨28036776358199473096141117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37382368477599297461521489 28036776358199473096141117)
      ·
        refine ⟨10513791134324802411052919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28036776358199473096141117 10513791134324802411052919)
        ·
          refine ⟨15770686701487203616579379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10513791134324802411052919 15770686701487203616579379)
          ·
            refine ⟨23656030052230805424869069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15770686701487203616579379 23656030052230805424869069)
            ·
              refine ⟨8871011269586552034325901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23656030052230805424869069 8871011269586552034325901)
              ·
                refine ⟨3326629226094957012872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8871011269586552034325901 3326629226094957012872213)
                ·
                  refine ⟨155935744973201109978385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3326629226094957012872213 155935744973201109978385)
                  ·
                    rfl

theorem cell22_1366577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_1366577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366577 prefixEnd_1366577 := by exact prefixLift 1366577
  have htrace : WordTrace (prefixWord ++ tailWord_1366577) baseStart_1366577 baseEnd_1366577 := by
    simpa [prefixWord, tailWord_1366577, baseEnd_1366577] using wordTrace_append hprefix tailTrace_1366577
  have hstable : (prefixWord ++ tailWord_1366577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366577).length < 2 ^ (prefixWord ++ tailWord_1366577).sum := by decide
  have hdescent : baseEnd_1366577 < baseStart_1366577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366607 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_1366607 : Nat := 118140960795 + 1366607 * 2 ^ 59
def prefixEnd_1366607 : Nat := 4983230072969 + 3 ^ 40 * 1366607 * 2
def baseEnd_1366607 : Nat := 467817504532693251685063

theorem tailTrace_1366607 : CollatzResearch.WordTrace tailWord_1366607 prefixEnd_1366607 467817504532693251685063 := by
  unfold tailWord_1366607
  simp only [CollatzResearch.WordTrace]
  refine ⟨49844252160023711738954075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33229501440015807825969383 49844252160023711738954075)
  ·
    refine ⟨74766378240035567608431113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49844252160023711738954075 74766378240035567608431113)
    ·
      refine ⟨56074783680026675706323335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74766378240035567608431113 56074783680026675706323335)
      ·
        refine ⟨84112175520040013559485003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56074783680026675706323335 84112175520040013559485003)
        ·
          refine ⟨126168263280060020339227505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84112175520040013559485003 126168263280060020339227505)
          ·
            refine ⟨94626197460045015254420629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126168263280060020339227505 94626197460045015254420629)
            ·
              refine ⟨4435603005939610090050967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94626197460045015254420629 4435603005939610090050967)
              ·
                refine ⟨6653404508909415135076451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435603005939610090050967 6653404508909415135076451)
                ·
                  refine ⟨9980106763364122702614677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653404508909415135076451 9980106763364122702614677)
                  ·
                    refine ⟨467817504532693251685063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9980106763364122702614677 467817504532693251685063)
                    ·
                      rfl

theorem cell22_1366607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_1366607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366607 prefixEnd_1366607 := by exact prefixLift 1366607
  have htrace : WordTrace (prefixWord ++ tailWord_1366607) baseStart_1366607 baseEnd_1366607 := by
    simpa [prefixWord, tailWord_1366607, baseEnd_1366607] using wordTrace_append hprefix tailTrace_1366607
  have hstable : (prefixWord ++ tailWord_1366607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366607).length < 2 ^ (prefixWord ++ tailWord_1366607).sum := by decide
  have hdescent : baseEnd_1366607 < baseStart_1366607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366609 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_1366609 : Nat := 118140960795 + 1366609 * 2 ^ 59
def prefixEnd_1366609 : Nat := 4983230072969 + 3 ^ 40 * 1366609 * 2
def baseEnd_1366609 : Nat := 467818189173565913135057

theorem tailTrace_1366609 : CollatzResearch.WordTrace tailWord_1366609 prefixEnd_1366609 467818189173565913135057 := by
  unfold tailWord_1366609
  simp only [CollatzResearch.WordTrace]
  refine ⟨49844325106016466080526881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33229550070677644053684587 49844325106016466080526881)
  ·
    refine ⟨37383243829512349560395161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49844325106016466080526881 37383243829512349560395161)
    ·
      refine ⟨28037432872134262170296371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37383243829512349560395161 28037432872134262170296371)
      ·
        refine ⟨42056149308201393255444557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28037432872134262170296371 42056149308201393255444557)
        ·
          refine ⟨15771055990575522470791709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42056149308201393255444557 15771055990575522470791709)
          ·
            refine ⟨5914145996465820926546891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15771055990575522470791709 5914145996465820926546891)
            ·
              refine ⟨8871218994698731389820337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914145996465820926546891 8871218994698731389820337)
              ·
                refine ⟨6653414246024048542365253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8871218994698731389820337 6653414246024048542365253)
                ·
                  refine ⟨1247515171129509101693485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6653414246024048542365253 1247515171129509101693485)
                  ·
                    refine ⟨467818189173565913135057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247515171129509101693485 467818189173565913135057)
                    ·
                      rfl

theorem cell22_1366609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_1366609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366609 prefixEnd_1366609 := by exact prefixLift 1366609
  have htrace : WordTrace (prefixWord ++ tailWord_1366609) baseStart_1366609 baseEnd_1366609 := by
    simpa [prefixWord, tailWord_1366609, baseEnd_1366609] using wordTrace_append hprefix tailTrace_1366609
  have hstable : (prefixWord ++ tailWord_1366609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366609).length < 2 ^ (prefixWord ++ tailWord_1366609).sum := by decide
  have hdescent : baseEnd_1366609 < baseStart_1366609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366667 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 7]
def baseStart_1366667 : Nat := 118140960795 + 1366667 * 2 ^ 59
def prefixEnd_1366667 : Nat := 4983230072969 + 3 ^ 40 * 1366667 * 2
def baseEnd_1366667 : Nat := 155946014586291031728293

theorem tailTrace_1366667 : CollatzResearch.WordTrace tailWord_1366667 prefixEnd_1366667 155946014586291031728293 := by
  unfold tailWord_1366667
  simp only [CollatzResearch.WordTrace]
  refine ⟨49846440539806341986138255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33230960359870894657425503 49846440539806341986138255)
  ·
    refine ⟨74769660809709512979207383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49846440539806341986138255 74769660809709512979207383)
    ·
      refine ⟨112154491214564269468811075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74769660809709512979207383 112154491214564269468811075)
      ·
        refine ⟨168231736821846404203216613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112154491214564269468811075 168231736821846404203216613)
        ·
          refine ⟨31543450654096200788103115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168231736821846404203216613 31543450654096200788103115)
          ·
            refine ⟨47315175981144301182154673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31543450654096200788103115 47315175981144301182154673)
            ·
              refine ⟨35486381985858225886616005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47315175981144301182154673 35486381985858225886616005)
              ·
                refine ⟨6653696622348417353740501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35486381985858225886616005 6653696622348417353740501)
                ·
                  refine ⟨155946014586291031728293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6653696622348417353740501 155946014586291031728293)
                  ·
                    rfl

theorem cell22_1366667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_1366667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366667 prefixEnd_1366667 := by exact prefixLift 1366667
  have htrace : WordTrace (prefixWord ++ tailWord_1366667) baseStart_1366667 baseEnd_1366667 := by
    simpa [prefixWord, tailWord_1366667, baseEnd_1366667] using wordTrace_append hprefix tailTrace_1366667
  have hstable : (prefixWord ++ tailWord_1366667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366667).length < 2 ^ (prefixWord ++ tailWord_1366667).sum := by decide
  have hdescent : baseEnd_1366667 < baseStart_1366667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_1366697 : Nat := 118140960795 + 1366697 * 2 ^ 59
def prefixEnd_1366697 : Nat := 4983230072969 + 3 ^ 40 * 1366697 * 2
def baseEnd_1366697 : Nat := 467848313371963016934787

theorem tailTrace_1366697 : CollatzResearch.WordTrace tailWord_1366697 prefixEnd_1366697 467848313371963016934787 := by
  unfold tailWord_1366697
  simp only [CollatzResearch.WordTrace]
  refine ⟨49847534729697657109730345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33231689819798438073153563 49847534729697657109730345)
  ·
    refine ⟨37385651047273242832297759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49847534729697657109730345 37385651047273242832297759)
    ·
      refine ⟨56078476570909864248446639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37385651047273242832297759 56078476570909864248446639)
      ·
        refine ⟨84117714856364796372669959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56078476570909864248446639 84117714856364796372669959)
        ·
          refine ⟨126176572284547194559004939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84117714856364796372669959 126176572284547194559004939)
          ·
            refine ⟨189264858426820791838507409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126176572284547194559004939 189264858426820791838507409)
            ·
              refine ⟨141948643820115593878880557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189264858426820791838507409 141948643820115593878880557)
              ·
                refine ⟨53230741432543347704580209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141948643820115593878880557 53230741432543347704580209)
                ·
                  refine ⟨39923056074407510778435157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53230741432543347704580209 39923056074407510778435157)
                  ·
                    refine ⟨467848313371963016934787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39923056074407510778435157 467848313371963016934787)
                    ·
                      rfl

theorem cell22_1366697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_1366697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366697 prefixEnd_1366697 := by exact prefixLift 1366697
  have htrace : WordTrace (prefixWord ++ tailWord_1366697) baseStart_1366697 baseEnd_1366697 := by
    simpa [prefixWord, tailWord_1366697, baseEnd_1366697] using wordTrace_append hprefix tailTrace_1366697
  have hstable : (prefixWord ++ tailWord_1366697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366697).length < 2 ^ (prefixWord ++ tailWord_1366697).sum := by decide
  have hdescent : baseEnd_1366697 < baseStart_1366697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366701 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1366701 : Nat := 118140960795 + 1366701 * 2 ^ 59
def prefixEnd_1366701 : Nat := 4983230072969 + 3 ^ 40 * 1366701 * 2
def baseEnd_1366701 : Nat := 155949894217902779944925

theorem tailTrace_1366701 : CollatzResearch.WordTrace tailWord_1366701 prefixEnd_1366701 155949894217902779944925 := by
  unfold tailWord_1366701
  simp only [CollatzResearch.WordTrace]
  refine ⟨49847680621683165792875957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33231787081122110528583971 49847680621683165792875957)
  ·
    refine ⟨4673220058282796793082121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49847680621683165792875957 4673220058282796793082121)
    ·
      refine ⟨3504915043712097594811591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673220058282796793082121 3504915043712097594811591)
      ·
        refine ⟨5257372565568146392217387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504915043712097594811591 5257372565568146392217387)
        ·
          refine ⟨7886058848352219588326081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257372565568146392217387 7886058848352219588326081)
          ·
            refine ⟨5914544136264164691244561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886058848352219588326081 5914544136264164691244561)
            ·
              refine ⟨4435908102198123518433421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914544136264164691244561 4435908102198123518433421)
              ·
                refine ⟨1663465538324296319412533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4435908102198123518433421 1663465538324296319412533)
                ·
                  refine ⟨155949894217902779944925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663465538324296319412533 155949894217902779944925)
                  ·
                    rfl

theorem cell22_1366701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1366701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366701 prefixEnd_1366701 := by exact prefixLift 1366701
  have htrace : WordTrace (prefixWord ++ tailWord_1366701) baseStart_1366701 baseEnd_1366701 := by
    simpa [prefixWord, tailWord_1366701, baseEnd_1366701] using wordTrace_append hprefix tailTrace_1366701
  have hstable : (prefixWord ++ tailWord_1366701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366701).length < 2 ^ (prefixWord ++ tailWord_1366701).sum := by decide
  have hdescent : baseEnd_1366701 < baseStart_1366701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366714 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1366714 : Nat := 118140960795 + 1366714 * 2 ^ 59
def prefixEnd_1366714 : Nat := 4983230072969 + 3 ^ 40 * 1366714 * 2
def baseEnd_1366714 : Nat := 467854132819380639259735

theorem tailTrace_1366714 : CollatzResearch.WordTrace tailWord_1366714 prefixEnd_1366714 467854132819380639259735 := by
  unfold tailWord_1366714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462038692659017253274799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33232103180424046008732797 12462038692659017253274799)
  ·
    refine ⟨18693058038988525879912199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12462038692659017253274799 18693058038988525879912199)
    ·
      refine ⟨28039587058482788819868299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18693058038988525879912199 28039587058482788819868299)
      ·
        refine ⟨42059380587724183229802449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28039587058482788819868299 42059380587724183229802449)
        ·
          refine ⟨31544535440793137422351837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42059380587724183229802449 31544535440793137422351837)
          ·
            refine ⟨11829200790297426533381939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31544535440793137422351837 11829200790297426533381939)
            ·
              refine ⟨17743801185446139800072909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829200790297426533381939 17743801185446139800072909)
              ·
                refine ⟨6653925444542302425027341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17743801185446139800072909 6653925444542302425027341)
                ·
                  refine ⟨2495222041703363409385253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6653925444542302425027341 2495222041703363409385253)
                  ·
                    refine ⟨467854132819380639259735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495222041703363409385253 467854132819380639259735)
                    ·
                      rfl

theorem cell22_1366714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1366714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366714 prefixEnd_1366714 := by exact prefixLift 1366714
  have htrace : WordTrace (prefixWord ++ tailWord_1366714) baseStart_1366714 baseEnd_1366714 := by
    simpa [prefixWord, tailWord_1366714, baseEnd_1366714] using wordTrace_append hprefix tailTrace_1366714
  have hstable : (prefixWord ++ tailWord_1366714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366714).length < 2 ^ (prefixWord ++ tailWord_1366714).sum := by decide
  have hdescent : baseEnd_1366714 < baseStart_1366714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366746 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_1366746 : Nat := 118140960795 + 1366746 * 2 ^ 59
def prefixEnd_1366746 : Nat := 4983230072969 + 3 ^ 40 * 1366746 * 2
def baseEnd_1366746 : Nat := 155955029024447740819879

theorem tailTrace_1366746 : CollatzResearch.WordTrace tailWord_1366746 prefixEnd_1366746 155955029024447740819879 := by
  unfold tailWord_1366746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462330476630034619566023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33232881271013425652176061 12462330476630034619566023)
  ·
    refine ⟨18693495714945051929349035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12462330476630034619566023 18693495714945051929349035)
    ·
      refine ⟨28040243572417577894023553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18693495714945051929349035 28040243572417577894023553)
      ·
        refine ⟨21030182679313183420517665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28040243572417577894023553 21030182679313183420517665)
        ·
          refine ⟨15772637009484887565388249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21030182679313183420517665 15772637009484887565388249)
          ·
            refine ⟨11829477757113665674041187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15772637009484887565388249 11829477757113665674041187)
            ·
              refine ⟨17744216635670498511061781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11829477757113665674041187 17744216635670498511061781)
              ·
                refine ⟨831760154797054617706021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17744216635670498511061781 831760154797054617706021)
                ·
                  refine ⟨155955029024447740819879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831760154797054617706021 155955029024447740819879)
                  ·
                    rfl

theorem cell22_1366746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_1366746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366746 prefixEnd_1366746 := by exact prefixLift 1366746
  have htrace : WordTrace (prefixWord ++ tailWord_1366746) baseStart_1366746 baseEnd_1366746 := by
    simpa [prefixWord, tailWord_1366746, baseEnd_1366746] using wordTrace_append hprefix tailTrace_1366746
  have hstable : (prefixWord ++ tailWord_1366746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366746).length < 2 ^ (prefixWord ++ tailWord_1366746).sum := by decide
  have hdescent : baseEnd_1366746 < baseStart_1366746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366761 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_1366761 : Nat := 118140960795 + 1366761 * 2 ^ 59
def prefixEnd_1366761 : Nat := 4983230072969 + 3 ^ 40 * 1366761 * 2
def baseEnd_1366761 : Nat := 467870221879888183334591

theorem tailTrace_1366761 : CollatzResearch.WordTrace tailWord_1366761 prefixEnd_1366761 467870221879888183334591 := by
  unfold tailWord_1366761
  simp only [CollatzResearch.WordTrace]
  refine ⟨49849869001465796040060137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33233246000977197360040091 49849869001465796040060137)
  ·
    refine ⟨37387401751099347030045103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49849869001465796040060137 37387401751099347030045103)
    ·
      refine ⟨56081102626649020545067655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37387401751099347030045103 56081102626649020545067655)
      ·
        refine ⟨84121653939973530817601483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56081102626649020545067655 84121653939973530817601483)
        ·
          refine ⟨126182480909960296226402225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84121653939973530817601483 126182480909960296226402225)
          ·
            refine ⟨94636860682470222169801669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126182480909960296226402225 94636860682470222169801669)
            ·
              refine ⟨17744411377963166656837813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94636860682470222169801669 17744411377963166656837813)
              ·
                refine ⟨1663538566684046874078545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17744411377963166656837813 1663538566684046874078545)
                ·
                  refine ⟨1247653925013035155558909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1663538566684046874078545 1247653925013035155558909)
                  ·
                    refine ⟨467870221879888183334591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247653925013035155558909 467870221879888183334591)
                    ·
                      rfl

theorem cell22_1366761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_1366761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366761 prefixEnd_1366761 := by exact prefixLift 1366761
  have htrace : WordTrace (prefixWord ++ tailWord_1366761) baseStart_1366761 baseEnd_1366761 := by
    simpa [prefixWord, tailWord_1366761, baseEnd_1366761] using wordTrace_append hprefix tailTrace_1366761
  have hstable : (prefixWord ++ tailWord_1366761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366761).length < 2 ^ (prefixWord ++ tailWord_1366761).sum := by decide
  have hdescent : baseEnd_1366761 < baseStart_1366761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366791 : List Nat := [1, 1, 4, 4, 1, 3, 8]
def baseStart_1366791 : Nat := 118140960795 + 1366791 * 2 ^ 59
def prefixEnd_1366791 : Nat := 4983230072969 + 3 ^ 40 * 1366791 * 2
def baseEnd_1366791 : Nat := 17328907092332522410537

theorem tailTrace_1366791 : CollatzResearch.WordTrace tailWord_1366791 prefixEnd_1366791 17328907092332522410537 := by
  unfold tailWord_1366791
  simp only [CollatzResearch.WordTrace]
  refine ⟨49850963191357111163652227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33233975460904740775768151 49850963191357111163652227)
  ·
    refine ⟨74776444787035666745478341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49850963191357111163652227 74776444787035666745478341)
    ·
      refine ⟨14020583397569187514777189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74776444787035666745478341 14020583397569187514777189)
      ·
        refine ⟨2628859387044222659020723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14020583397569187514777189 2628859387044222659020723)
        ·
          refine ⟨3943289080566333988531085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628859387044222659020723 3943289080566333988531085)
          ·
            refine ⟨1478733405212375245699157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3943289080566333988531085 1478733405212375245699157)
            ·
              refine ⟨17328907092332522410537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1478733405212375245699157 17328907092332522410537)
              ·
                rfl

theorem cell22_1366791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 8].length) (baseStart_1366791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366791 prefixEnd_1366791 := by exact prefixLift 1366791
  have htrace : WordTrace (prefixWord ++ tailWord_1366791) baseStart_1366791 baseEnd_1366791 := by
    simpa [prefixWord, tailWord_1366791, baseEnd_1366791] using wordTrace_append hprefix tailTrace_1366791
  have hstable : (prefixWord ++ tailWord_1366791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366791).length < 2 ^ (prefixWord ++ tailWord_1366791).sum := by decide
  have hdescent : baseEnd_1366791 < baseStart_1366791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366857 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 1, 3]
def baseStart_1366857 : Nat := 118140960795 + 1366857 * 2 ^ 59
def prefixEnd_1366857 : Nat := 4983230072969 + 3 ^ 40 * 1366857 * 2
def baseEnd_1366857 : Nat := 467903084641775932934297

theorem tailTrace_1366857 : CollatzResearch.WordTrace tailWord_1366857 prefixEnd_1366857 467903084641775932934297 := by
  unfold tailWord_1366857
  simp only [CollatzResearch.WordTrace]
  refine ⟨49853370409118004435554825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33235580272745336290369883 49853370409118004435554825)
  ·
    refine ⟨37390027806838503326666119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49853370409118004435554825 37390027806838503326666119)
    ·
      refine ⟨56085041710257754989999179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37390027806838503326666119 56085041710257754989999179)
      ·
        refine ⟨84127562565386632484998769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56085041710257754989999179 84127562565386632484998769)
        ·
          refine ⟨63095671924039974363749077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84127562565386632484998769 63095671924039974363749077)
          ·
            refine ⟨1478804810719686899150369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 63095671924039974363749077 1478804810719686899150369)
            ·
              refine ⟨1109103608039765174362777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478804810719686899150369 1109103608039765174362777)
              ·
                refine ⟨831827706029823880772083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109103608039765174362777 831827706029823880772083)
                ·
                  refine ⟨1247741559044735821158125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831827706029823880772083 1247741559044735821158125)
                  ·
                    refine ⟨467903084641775932934297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247741559044735821158125 467903084641775932934297)
                    ·
                      rfl

theorem cell22_1366857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_1366857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366857 prefixEnd_1366857 := by exact prefixLift 1366857
  have htrace : WordTrace (prefixWord ++ tailWord_1366857) baseStart_1366857 baseEnd_1366857 := by
    simpa [prefixWord, tailWord_1366857, baseEnd_1366857] using wordTrace_append hprefix tailTrace_1366857
  have hstable : (prefixWord ++ tailWord_1366857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366857).length < 2 ^ (prefixWord ++ tailWord_1366857).sum := by decide
  have hdescent : baseEnd_1366857 < baseStart_1366857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366866 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1366866 : Nat := 118140960795 + 1366866 * 2 ^ 59
def prefixEnd_1366866 : Nat := 4983230072969 + 3 ^ 40 * 1366866 * 2
def baseEnd_1366866 : Nat := 467906165525702909459269

theorem tailTrace_1366866 : CollatzResearch.WordTrace tailWord_1366866 prefixEnd_1366866 467906165525702909459269 := by
  unfold tailWord_1366866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12463424666521349743158113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33235799110723599315088301 12463424666521349743158113)
  ·
    refine ⟨9347568499891012307368585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12463424666521349743158113 9347568499891012307368585)
    ·
      refine ⟨7010676374918259230526439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9347568499891012307368585 7010676374918259230526439)
      ·
        refine ⟨10516014562377388845789659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010676374918259230526439 10516014562377388845789659)
        ·
          refine ⟨15774021843566083268684489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10516014562377388845789659 15774021843566083268684489)
          ·
            refine ⟨11830516382674562451513367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15774021843566083268684489 11830516382674562451513367)
            ·
              refine ⟨17745774574011843677270051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830516382674562451513367 17745774574011843677270051)
              ·
                refine ⟨26618661861017765515905077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17745774574011843677270051 26618661861017765515905077)
                ·
                  refine ⟨2495499549470415517116101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26618661861017765515905077 2495499549470415517116101)
                  ·
                    refine ⟨467906165525702909459269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495499549470415517116101 467906165525702909459269)
                    ·
                      rfl

theorem cell22_1366866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1366866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366866 prefixEnd_1366866 := by exact prefixLift 1366866
  have htrace : WordTrace (prefixWord ++ tailWord_1366866) baseStart_1366866 baseEnd_1366866 := by
    simpa [prefixWord, tailWord_1366866, baseEnd_1366866] using wordTrace_append hprefix tailTrace_1366866
  have hstable : (prefixWord ++ tailWord_1366866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366866).length < 2 ^ (prefixWord ++ tailWord_1366866).sum := by decide
  have hdescent : baseEnd_1366866 < baseStart_1366866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366868 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1366868 : Nat := 118140960795 + 1366868 * 2 ^ 59
def prefixEnd_1366868 : Nat := 4983230072969 + 3 ^ 40 * 1366868 * 2
def baseEnd_1366868 : Nat := 467906850166575570909263

theorem tailTrace_1366868 : CollatzResearch.WordTrace tailWord_1366868 prefixEnd_1366868 467906850166575570909263 := by
  unfold tailWord_1366868
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926885806039076657102629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33235847741385435542803505 24926885806039076657102629)
  ·
    refine ⟨4673791088632326873206743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24926885806039076657102629 4673791088632326873206743)
    ·
      refine ⟨7010686632948490309810115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673791088632326873206743 7010686632948490309810115)
      ·
        refine ⟨10516029949422735464715173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010686632948490309810115 10516029949422735464715173)
        ·
          refine ⟨1971755615516762899634095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10516029949422735464715173 1971755615516762899634095)
          ·
            refine ⟨2957633423275144349451143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971755615516762899634095 2957633423275144349451143)
            ·
              refine ⟨4436450134912716524176715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2957633423275144349451143 4436450134912716524176715)
              ·
                refine ⟨6654675202369074786265073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4436450134912716524176715 6654675202369074786265073)
                ·
                  refine ⟨4991006401776806089698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6654675202369074786265073 4991006401776806089698805)
                  ·
                    refine ⟨467906850166575570909263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4991006401776806089698805 467906850166575570909263)
                    ·
                      rfl

theorem cell22_1366868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1366868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366868 prefixEnd_1366868 := by exact prefixLift 1366868
  have htrace : WordTrace (prefixWord ++ tailWord_1366868) baseStart_1366868 baseEnd_1366868 := by
    simpa [prefixWord, tailWord_1366868, baseEnd_1366868] using wordTrace_append hprefix tailTrace_1366868
  have hstable : (prefixWord ++ tailWord_1366868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366868).length < 2 ^ (prefixWord ++ tailWord_1366868).sum := by decide
  have hdescent : baseEnd_1366868 < baseStart_1366868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366896 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_1366896 : Nat := 118140960795 + 1366896 * 2 ^ 59
def prefixEnd_1366896 : Nat := 4983230072969 + 3 ^ 40 * 1366896 * 2
def baseEnd_1366896 : Nat := 467916435138792831209177

theorem tailTrace_1366896 : CollatzResearch.WordTrace tailWord_1366896 prefixEnd_1366896 467916435138792831209177 := by
  unfold tailWord_1366896
  simp only [CollatzResearch.WordTrace]
  refine ⟨24927396427988357048112271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33236528570651142730816361 24927396427988357048112271)
  ·
    refine ⟨37391094641982535572168407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24927396427988357048112271 37391094641982535572168407)
    ·
      refine ⟨56086641962973803358252611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37391094641982535572168407 56086641962973803358252611)
      ·
        refine ⟨84129962944460705037378917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56086641962973803358252611 84129962944460705037378917)
        ·
          refine ⟨15774368052086382194508547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84129962944460705037378917 15774368052086382194508547)
          ·
            refine ⟨23661552078129573291762821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15774368052086382194508547 23661552078129573291762821)
            ·
              refine ⟨4436541014649294992205529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23661552078129573291762821 4436541014649294992205529)
              ·
                refine ⟨3327405760986971244154147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436541014649294992205529 3327405760986971244154147)
                ·
                  refine ⟨4991108641480456866231221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327405760986971244154147 4991108641480456866231221)
                  ·
                    refine ⟨467916435138792831209177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4991108641480456866231221 467916435138792831209177)
                    ·
                      rfl

theorem cell22_1366896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_1366896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366896 prefixEnd_1366896 := by exact prefixLift 1366896
  have htrace : WordTrace (prefixWord ++ tailWord_1366896) baseStart_1366896 baseEnd_1366896 := by
    simpa [prefixWord, tailWord_1366896, baseEnd_1366896] using wordTrace_append hprefix tailTrace_1366896
  have hstable : (prefixWord ++ tailWord_1366896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366896).length < 2 ^ (prefixWord ++ tailWord_1366896).sum := by decide
  have hdescent : baseEnd_1366896 < baseStart_1366896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366898 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_1366898 : Nat := 118140960795 + 1366898 * 2 ^ 59
def prefixEnd_1366898 : Nat := 4983230072969 + 3 ^ 40 * 1366898 * 2
def baseEnd_1366898 : Nat := 155972373259888497553057

theorem tailTrace_1366898 : CollatzResearch.WordTrace tailWord_1366898 prefixEnd_1366898 155972373259888497553057 := by
  unfold tailWord_1366898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12463716450492367109449337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33236577201312978958531565 12463716450492367109449337)
  ·
    refine ⟨9347787337869275332087003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12463716450492367109449337 9347787337869275332087003)
    ·
      refine ⟨14021681006803912998130505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9347787337869275332087003 14021681006803912998130505)
      ·
        refine ⟨10516260755102934748597879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14021681006803912998130505 10516260755102934748597879)
        ·
          refine ⟨15774391132654402122896819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10516260755102934748597879 15774391132654402122896819)
          ·
            refine ⟨23661586698981603184345229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15774391132654402122896819 23661586698981603184345229)
            ·
              refine ⟨8873095012118101194129461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23661586698981603184345229 8873095012118101194129461)
              ·
                refine ⟨831852657386071986949637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8873095012118101194129461 831852657386071986949637)
                ·
                  refine ⟨155972373259888497553057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 831852657386071986949637 155972373259888497553057)
                  ·
                    rfl

theorem cell22_1366898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_1366898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366898 prefixEnd_1366898 := by exact prefixLift 1366898
  have htrace : WordTrace (prefixWord ++ tailWord_1366898) baseStart_1366898 baseEnd_1366898 := by
    simpa [prefixWord, tailWord_1366898, baseEnd_1366898] using wordTrace_append hprefix tailTrace_1366898
  have hstable : (prefixWord ++ tailWord_1366898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366898).length < 2 ^ (prefixWord ++ tailWord_1366898).sum := by decide
  have hdescent : baseEnd_1366898 < baseStart_1366898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366911 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_1366911 : Nat := 118140960795 + 1366911 * 2 ^ 59
def prefixEnd_1366911 : Nat := 4983230072969 + 3 ^ 40 * 1366911 * 2
def baseEnd_1366911 : Nat := 467921569945337792084131

theorem tailTrace_1366911 : CollatzResearch.WordTrace tailWord_1366911 prefixEnd_1366911 467921569945337792084131 := by
  unfold tailWord_1366911
  simp only [CollatzResearch.WordTrace]
  refine ⟨49855339950922371658020587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33236893300614914438680391 49855339950922371658020587)
  ·
    refine ⟨74783009926383557487030881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49855339950922371658020587 74783009926383557487030881)
    ·
      refine ⟨56087257444787668115273161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74783009926383557487030881 56087257444787668115273161)
      ·
        refine ⟨42065443083590751086454871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56087257444787668115273161 42065443083590751086454871)
        ·
          refine ⟨63098164625386126629682307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42065443083590751086454871 63098164625386126629682307)
          ·
            refine ⟨94647246938079189944523461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63098164625386126629682307 94647246938079189944523461)
            ·
              refine ⟨17746358800889848114598149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94647246938079189944523461 17746358800889848114598149)
              ·
                refine ⟨3327442275166846521487153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17746358800889848114598149 3327442275166846521487153)
                ·
                  refine ⟨2495581706375134891115365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3327442275166846521487153 2495581706375134891115365)
                  ·
                    refine ⟨467921569945337792084131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495581706375134891115365 467921569945337792084131)
                    ·
                      rfl

theorem cell22_1366911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_1366911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366911 prefixEnd_1366911 := by exact prefixLift 1366911
  have htrace : WordTrace (prefixWord ++ tailWord_1366911) baseStart_1366911 baseEnd_1366911 := by
    simpa [prefixWord, tailWord_1366911, baseEnd_1366911] using wordTrace_append hprefix tailTrace_1366911
  have hstable : (prefixWord ++ tailWord_1366911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366911).length < 2 ^ (prefixWord ++ tailWord_1366911).sum := by decide
  have hdescent : baseEnd_1366911 < baseStart_1366911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366934 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1366934 : Nat := 118140960795 + 1366934 * 2 ^ 59
def prefixEnd_1366934 : Nat := 4983230072969 + 3 ^ 40 * 1366934 * 2
def baseEnd_1366934 : Nat := 467929443315373398759061

theorem tailTrace_1366934 : CollatzResearch.WordTrace tailWord_1366934 prefixEnd_1366934 467929443315373398759061 := by
  unfold tailWord_1366934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116011176864940411631741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33237452553226031057405237 3116011176864940411631741)
  ·
    refine ⟨1168504191324352654361903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3116011176864940411631741 1168504191324352654361903)
    ·
      refine ⟨1752756286986528981542855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168504191324352654361903 1752756286986528981542855)
      ·
        refine ⟨2629134430479793472314283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752756286986528981542855 2629134430479793472314283)
        ·
          refine ⟨3943701645719690208471425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629134430479793472314283 3943701645719690208471425)
          ·
            refine ⟨2957776234289767656353569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3943701645719690208471425 2957776234289767656353569)
            ·
              refine ⟨2218332175717325742265177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957776234289767656353569 2218332175717325742265177)
              ·
                refine ⟨1663749131787994306698883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218332175717325742265177 1663749131787994306698883)
                ·
                  refine ⟨2495623697681991460048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663749131787994306698883 2495623697681991460048325)
                  ·
                    refine ⟨467929443315373398759061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495623697681991460048325 467929443315373398759061)
                    ·
                      rfl

theorem cell22_1366934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1366934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366934 prefixEnd_1366934 := by exact prefixLift 1366934
  have htrace : WordTrace (prefixWord ++ tailWord_1366934) baseStart_1366934 baseEnd_1366934 := by
    simpa [prefixWord, tailWord_1366934, baseEnd_1366934] using wordTrace_append hprefix tailTrace_1366934
  have hstable : (prefixWord ++ tailWord_1366934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366934).length < 2 ^ (prefixWord ++ tailWord_1366934).sum := by decide
  have hdescent : baseEnd_1366934 < baseStart_1366934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366941 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1366941 : Nat := 118140960795 + 1366941 * 2 ^ 59
def prefixEnd_1366941 : Nat := 4983230072969 + 3 ^ 40 * 1366941 * 2
def baseEnd_1366941 : Nat := 467931839558427713834039

theorem tailTrace_1366941 : CollatzResearch.WordTrace tailWord_1366941 prefixEnd_1366941 467931839558427713834039 := by
  unfold tailWord_1366941
  simp only [CollatzResearch.WordTrace]
  refine ⟨49856434140813686781612677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33237622760542457854408451 49856434140813686781612677)
  ·
    refine ⟨9348081401402566271552377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49856434140813686781612677 9348081401402566271552377)
    ·
      refine ⟨7011061051051924703664283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9348081401402566271552377 7011061051051924703664283)
      ·
        refine ⟨10516591576577887055496425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011061051051924703664283 10516591576577887055496425)
        ·
          refine ⟨7887443682433415291622319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10516591576577887055496425 7887443682433415291622319)
          ·
            refine ⟨11831165523650122937433479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887443682433415291622319 11831165523650122937433479)
            ·
              refine ⟨17746748285475184406150219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11831165523650122937433479 17746748285475184406150219)
              ·
                refine ⟨26620122428212776609225329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17746748285475184406150219 26620122428212776609225329)
                ·
                  refine ⟨19965091821159582456918997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26620122428212776609225329 19965091821159582456918997)
                  ·
                    refine ⟨467931839558427713834039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19965091821159582456918997 467931839558427713834039)
                    ·
                      rfl

theorem cell22_1366941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1366941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366941 prefixEnd_1366941 := by exact prefixLift 1366941
  have htrace : WordTrace (prefixWord ++ tailWord_1366941) baseStart_1366941 baseEnd_1366941 := by
    simpa [prefixWord, tailWord_1366941, baseEnd_1366941] using wordTrace_append hprefix tailTrace_1366941
  have hstable : (prefixWord ++ tailWord_1366941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366941).length < 2 ^ (prefixWord ++ tailWord_1366941).sum := by decide
  have hdescent : baseEnd_1366941 < baseStart_1366941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366943 : List Nat := [1, 1, 2, 5, 2, 1, 4, 6]
def baseStart_1366943 : Nat := 118140960795 + 1366943 * 2 ^ 59
def prefixEnd_1366943 : Nat := 4983230072969 + 3 ^ 40 * 1366943 * 2
def baseEnd_1366943 : Nat := 51992502688811152809337

theorem tailTrace_1366943 : CollatzResearch.WordTrace tailWord_1366943 prefixEnd_1366943 51992502688811152809337 := by
  unfold tailWord_1366943
  simp only [CollatzResearch.WordTrace]
  refine ⟨49856507086806441123185483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33237671391204294082123655 49856507086806441123185483)
  ·
    refine ⟨74784760630209661684778225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49856507086806441123185483 74784760630209661684778225)
    ·
      refine ⟨56088570472657246263583669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74784760630209661684778225 56088570472657246263583669)
      ·
        refine ⟨5258303481811616837210969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56088570472657246263583669 5258303481811616837210969)
        ·
          refine ⟨3943727611358712627908227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5258303481811616837210969 3943727611358712627908227)
          ·
            refine ⟨5915591417038068941862341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943727611358712627908227 5915591417038068941862341)
            ·
              refine ⟨1109173390694637926599189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5915591417038068941862341 1109173390694637926599189)
              ·
                refine ⟨51992502688811152809337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1109173390694637926599189 51992502688811152809337)
                ·
                  rfl

theorem cell22_1366943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 6].length) (baseStart_1366943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366943 prefixEnd_1366943 := by exact prefixLift 1366943
  have htrace : WordTrace (prefixWord ++ tailWord_1366943) baseStart_1366943 baseEnd_1366943 := by
    simpa [prefixWord, tailWord_1366943, baseEnd_1366943] using wordTrace_append hprefix tailTrace_1366943
  have hstable : (prefixWord ++ tailWord_1366943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366943).length < 2 ^ (prefixWord ++ tailWord_1366943).sum := by decide
  have hdescent : baseEnd_1366943 < baseStart_1366943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366966 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1366966 : Nat := 118140960795 + 1366966 * 2 ^ 59
def prefixEnd_1366966 : Nat := 4983230072969 + 3 ^ 40 * 1366966 * 2
def baseEnd_1366966 : Nat := 155980132523111993986321

theorem tailTrace_1366966 : CollatzResearch.WordTrace tailWord_1366966 prefixEnd_1366966 155980132523111993986321 := by
  unfold tailWord_1366966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116084122857694753204547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33238230643815410700848501 3116084122857694753204547)
  ·
    refine ⟨4674126184286542129806821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116084122857694753204547 4674126184286542129806821)
    ·
      refine ⟨876398659553726649338779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4674126184286542129806821 876398659553726649338779)
      ·
        refine ⟨1314597989330589974008169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876398659553726649338779 1314597989330589974008169)
        ·
          refine ⟨985948491997942480506127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1314597989330589974008169 985948491997942480506127)
          ·
            refine ⟨1478922737996913720759191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985948491997942480506127 1478922737996913720759191)
            ·
              refine ⟨2218384106995370581138787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478922737996913720759191 2218384106995370581138787)
              ·
                refine ⟨3327576160493055871708181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218384106995370581138787 3327576160493055871708181)
                ·
                  refine ⟨155980132523111993986321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3327576160493055871708181 155980132523111993986321)
                  ·
                    rfl

theorem cell22_1366966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1366966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366966 prefixEnd_1366966 := by exact prefixLift 1366966
  have htrace : WordTrace (prefixWord ++ tailWord_1366966) baseStart_1366966 baseEnd_1366966 := by
    simpa [prefixWord, tailWord_1366966, baseEnd_1366966] using wordTrace_append hprefix tailTrace_1366966
  have hstable : (prefixWord ++ tailWord_1366966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366966).length < 2 ^ (prefixWord ++ tailWord_1366966).sum := by decide
  have hdescent : baseEnd_1366966 < baseStart_1366966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366986 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1366986 : Nat := 118140960795 + 1366986 * 2 ^ 59
def prefixEnd_1366986 : Nat := 4983230072969 + 3 ^ 40 * 1366986 * 2
def baseEnd_1366986 : Nat := 467947243978062596458901

theorem tailTrace_1366986 : CollatzResearch.WordTrace tailWord_1366986 prefixEnd_1366986 467947243978062596458901 := by
  unfold tailWord_1366986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12464518856412664866750203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33238716950433772978000541 12464518856412664866750203)
  ·
    refine ⟨18696778284618997300125305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12464518856412664866750203 18696778284618997300125305)
    ·
      refine ⟨14022583713464247975093979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18696778284618997300125305 14022583713464247975093979)
      ·
        refine ⟨21033875570196371962640969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14022583713464247975093979 21033875570196371962640969)
        ·
          refine ⟨15775406677647278971980727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21033875570196371962640969 15775406677647278971980727)
          ·
            refine ⟨23663110016470918457971091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15775406677647278971980727 23663110016470918457971091)
            ·
              refine ⟨35494665024706377686956637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23663110016470918457971091 35494665024706377686956637)
              ·
                refine ⟨13310499384264891632608739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35494665024706377686956637 13310499384264891632608739)
                ·
                  refine ⟨19965749076397337448913109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13310499384264891632608739 19965749076397337448913109)
                  ·
                    refine ⟨467947243978062596458901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19965749076397337448913109 467947243978062596458901)
                    ·
                      rfl

theorem cell22_1366986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1366986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366986 prefixEnd_1366986 := by exact prefixLift 1366986
  have htrace : WordTrace (prefixWord ++ tailWord_1366986) baseStart_1366986 baseEnd_1366986 := by
    simpa [prefixWord, tailWord_1366986, baseEnd_1366986] using wordTrace_append hprefix tailTrace_1366986
  have hstable : (prefixWord ++ tailWord_1366986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366986).length < 2 ^ (prefixWord ++ tailWord_1366986).sum := by decide
  have hdescent : baseEnd_1366986 < baseStart_1366986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366988 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_1366988 : Nat := 118140960795 + 1366988 * 2 ^ 59
def prefixEnd_1366988 : Nat := 4983230072969 + 3 ^ 40 * 1366988 * 2
def baseEnd_1366988 : Nat := 155982642872978419302965

theorem tailTrace_1366988 : CollatzResearch.WordTrace tailWord_1366988 prefixEnd_1366988 155982642872978419302965 := by
  unfold tailWord_1366988
  simp only [CollatzResearch.WordTrace]
  refine ⟨24929074185821706904286809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33238765581095609205715745 24929074185821706904286809)
  ·
    refine ⟨18696805639366280178215107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24929074185821706904286809 18696805639366280178215107)
    ·
      refine ⟨28045208459049420267322661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18696805639366280178215107 28045208459049420267322661)
      ·
        refine ⟨5258476586071766300122999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28045208459049420267322661 5258476586071766300122999)
        ·
          refine ⟨7887714879107649450184499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258476586071766300122999 7887714879107649450184499)
          ·
            refine ⟨11831572318661474175276749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887714879107649450184499 11831572318661474175276749)
            ·
              refine ⟨4436839619498052815728781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11831572318661474175276749 4436839619498052815728781)
              ·
                refine ⟨1663814857311769805898293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4436839619498052815728781 1663814857311769805898293)
                ·
                  refine ⟨155982642872978419302965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1663814857311769805898293 155982642872978419302965)
                  ·
                    rfl

theorem cell22_1366988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_1366988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1366988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1366988 prefixEnd_1366988 := by exact prefixLift 1366988
  have htrace : WordTrace (prefixWord ++ tailWord_1366988) baseStart_1366988 baseEnd_1366988 := by
    simpa [prefixWord, tailWord_1366988, baseEnd_1366988] using wordTrace_append hprefix tailTrace_1366988
  have hstable : (prefixWord ++ tailWord_1366988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366988).length < 2 ^ (prefixWord ++ tailWord_1366988).sum := by decide
  have hdescent : baseEnd_1366988 < baseStart_1366988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367048 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1367048 : Nat := 118140960795 + 1367048 * 2 ^ 59
def prefixEnd_1367048 : Nat := 4983230072969 + 3 ^ 40 * 1367048 * 2
def baseEnd_1367048 : Nat := 467968467845115101408711

theorem tailTrace_1367048 : CollatzResearch.WordTrace tailWord_1367048 prefixEnd_1367048 467968467845115101408711 := by
  unfold tailWord_1367048
  simp only [CollatzResearch.WordTrace]
  refine ⟨24930168375713022027878899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33240224500950696037171865 24930168375713022027878899)
  ·
    refine ⟨37395252563569533041818349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24930168375713022027878899 37395252563569533041818349)
    ·
      refine ⟨14023219711338574890681881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37395252563569533041818349 14023219711338574890681881)
      ·
        refine ⟨10517414783503931168011411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14023219711338574890681881 10517414783503931168011411)
        ·
          refine ⟨15776122175255896752017117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10517414783503931168011411 15776122175255896752017117)
          ·
            refine ⟨5916045815720961282006419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15776122175255896752017117 5916045815720961282006419)
            ·
              refine ⟨8874068723581441923009629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916045815720961282006419 8874068723581441923009629)
              ·
                refine ⟨3327775771343040721128611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8874068723581441923009629 3327775771343040721128611)
                ·
                  refine ⟨4991663657014561081692917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327775771343040721128611 4991663657014561081692917)
                  ·
                    refine ⟨467968467845115101408711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4991663657014561081692917 467968467845115101408711)
                    ·
                      rfl

theorem cell22_1367048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1367048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367048 prefixEnd_1367048 := by exact prefixLift 1367048
  have htrace : WordTrace (prefixWord ++ tailWord_1367048) baseStart_1367048 baseEnd_1367048 := by
    simpa [prefixWord, tailWord_1367048, baseEnd_1367048] using wordTrace_append hprefix tailTrace_1367048
  have hstable : (prefixWord ++ tailWord_1367048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367048).length < 2 ^ (prefixWord ++ tailWord_1367048).sum := by decide
  have hdescent : baseEnd_1367048 < baseStart_1367048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367069 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1367069 : Nat := 118140960795 + 1367069 * 2 ^ 59
def prefixEnd_1367069 : Nat := 4983230072969 + 3 ^ 40 * 1367069 * 2
def baseEnd_1367069 : Nat := 467975656574278046633647

theorem tailTrace_1367069 : CollatzResearch.WordTrace tailWord_1367069 prefixEnd_1367069 467975656574278046633647 := by
  unfold tailWord_1367069
  simp only [CollatzResearch.WordTrace]
  refine ⟨49861102684349964642272261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33240735122899976428181507 49861102684349964642272261)
  ·
    refine ⟨9348956753315618370426049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49861102684349964642272261 9348956753315618370426049)
    ·
      refine ⟨7011717564986713777819537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9348956753315618370426049 7011717564986713777819537)
      ·
        refine ⟨5258788173740035333364653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7011717564986713777819537 5258788173740035333364653)
        ·
          refine ⟨1972045565152513250011745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5258788173740035333364653 1972045565152513250011745)
          ·
            refine ⟨1479034173864384937508809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1972045565152513250011745 1479034173864384937508809)
            ·
              refine ⟨1109275630398288703131607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479034173864384937508809 1109275630398288703131607)
              ·
                refine ⟨1663913445597433054697411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109275630398288703131607 1663913445597433054697411)
                ·
                  refine ⟨2495870168396149582046117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663913445597433054697411 2495870168396149582046117)
                  ·
                    refine ⟨467975656574278046633647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2495870168396149582046117 467975656574278046633647)
                    ·
                      rfl

theorem cell22_1367069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1367069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367069 prefixEnd_1367069 := by exact prefixLift 1367069
  have htrace : WordTrace (prefixWord ++ tailWord_1367069) baseStart_1367069 baseEnd_1367069 := by
    simpa [prefixWord, tailWord_1367069, baseEnd_1367069] using wordTrace_append hprefix tailTrace_1367069
  have hstable : (prefixWord ++ tailWord_1367069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367069).length < 2 ^ (prefixWord ++ tailWord_1367069).sum := by decide
  have hdescent : baseEnd_1367069 < baseStart_1367069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367082 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1367082 : Nat := 118140960795 + 1367082 * 2 ^ 59
def prefixEnd_1367082 : Nat := 4983230072969 + 3 ^ 40 * 1367082 * 2
def baseEnd_1367082 : Nat := 467980106739950346058607

theorem tailTrace_1367082 : CollatzResearch.WordTrace tailWord_1367082 prefixEnd_1367082 467980106739950346058607 := by
  unfold tailWord_1367082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465394208325716965623875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33241051222201911908330333 12465394208325716965623875)
  ·
    refine ⟨18698091312488575448435813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12465394208325716965623875 18698091312488575448435813)
    ·
      refine ⟨3505892121091607896581715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18698091312488575448435813 3505892121091607896581715)
      ·
        refine ⟨5258838181637411844872573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505892121091607896581715 5258838181637411844872573)
        ·
          refine ⟨1972064318114029441827215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5258838181637411844872573 1972064318114029441827215)
          ·
            refine ⟨2958096477171044162740823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972064318114029441827215 2958096477171044162740823)
            ·
              refine ⟨4437144715756566244111235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958096477171044162740823 4437144715756566244111235)
              ·
                refine ⟨6655717073634849366166853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437144715756566244111235 6655717073634849366166853)
                ·
                  refine ⟨1247946951306534256156285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6655717073634849366166853 1247946951306534256156285)
                  ·
                    refine ⟨467980106739950346058607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1247946951306534256156285 467980106739950346058607)
                    ·
                      rfl

theorem cell22_1367082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1367082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367082 prefixEnd_1367082 := by exact prefixLift 1367082
  have htrace : WordTrace (prefixWord ++ tailWord_1367082) baseStart_1367082 baseEnd_1367082 := by
    simpa [prefixWord, tailWord_1367082, baseEnd_1367082] using wordTrace_append hprefix tailTrace_1367082
  have hstable : (prefixWord ++ tailWord_1367082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367082).length < 2 ^ (prefixWord ++ tailWord_1367082).sum := by decide
  have hdescent : baseEnd_1367082 < baseStart_1367082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367168 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_1367168 : Nat := 118140960795 + 1367168 * 2 ^ 59
def prefixEnd_1367168 : Nat := 4983230072969 + 3 ^ 40 * 1367168 * 2
def baseEnd_1367168 : Nat := 156003182099158262802781

theorem tailTrace_1367168 : CollatzResearch.WordTrace tailWord_1367168 prefixEnd_1367168 156003182099158262802781 := by
  unfold tailWord_1367168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24932356755495652275063079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33243142340660869700084105 24932356755495652275063079)
  ·
    refine ⟨37398535133243478412594619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24932356755495652275063079 37398535133243478412594619)
    ·
      refine ⟨56097802699865217618891929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37398535133243478412594619 56097802699865217618891929)
      ·
        refine ⟨42073352024898913214168947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56097802699865217618891929 42073352024898913214168947)
        ·
          refine ⟨63110028037348369821253421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42073352024898913214168947 63110028037348369821253421)
          ·
            refine ⟨23666260514005638682970033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63110028037348369821253421 23666260514005638682970033)
            ·
              refine ⟨17749695385504229012227525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23666260514005638682970033 17749695385504229012227525)
              ·
                refine ⟨3328067884782042939792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17749695385504229012227525 3328067884782042939792661)
                ·
                  refine ⟨156003182099158262802781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3328067884782042939792661 156003182099158262802781)
                  ·
                    rfl

theorem cell22_1367168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_1367168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367168 prefixEnd_1367168 := by exact prefixLift 1367168
  have htrace : WordTrace (prefixWord ++ tailWord_1367168) baseStart_1367168 baseEnd_1367168 := by
    simpa [prefixWord, tailWord_1367168, baseEnd_1367168] using wordTrace_append hprefix tailTrace_1367168
  have hstable : (prefixWord ++ tailWord_1367168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367168).length < 2 ^ (prefixWord ++ tailWord_1367168).sum := by decide
  have hdescent : baseEnd_1367168 < baseStart_1367168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367217 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_1367217 : Nat := 118140960795 + 1367217 * 2 ^ 59
def prefixEnd_1367217 : Nat := 4983230072969 + 3 ^ 40 * 1367217 * 2
def baseEnd_1367217 : Nat := 468026319998854993933193

theorem tailTrace_1367217 : CollatzResearch.WordTrace tailWord_1367217 prefixEnd_1367217 468026319998854993933193 := by
  unfold tailWord_1367217
  simp only [CollatzResearch.WordTrace]
  refine ⟨49866500687813785918659905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33244333791875857279106603 49866500687813785918659905)
  ·
    refine ⟨37399875515860339438994929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49866500687813785918659905 37399875515860339438994929)
    ·
      refine ⟨28049906636895254579246197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37399875515860339438994929 28049906636895254579246197)
      ·
        refine ⟨2629678747208930116804331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28049906636895254579246197 2629678747208930116804331)
        ·
          refine ⟨3944518120813395175206497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629678747208930116804331 3944518120813395175206497)
          ·
            refine ⟨2958388590610046381404873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3944518120813395175206497 2958388590610046381404873)
            ·
              refine ⟨2218791442957534786053655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2958388590610046381404873 2218791442957534786053655)
              ·
                refine ⟨3328187164436302179080483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218791442957534786053655 3328187164436302179080483)
                ·
                  refine ⟨4992280746654453268620725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328187164436302179080483 4992280746654453268620725)
                  ·
                    refine ⟨468026319998854993933193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4992280746654453268620725 468026319998854993933193)
                    ·
                      rfl

theorem cell22_1367217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_1367217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1367217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1367217 prefixEnd_1367217 := by exact prefixLift 1367217
  have htrace : WordTrace (prefixWord ++ tailWord_1367217) baseStart_1367217 baseEnd_1367217 := by
    simpa [prefixWord, tailWord_1367217, baseEnd_1367217] using wordTrace_append hprefix tailTrace_1367217
  have hstable : (prefixWord ++ tailWord_1367217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367217).length < 2 ^ (prefixWord ++ tailWord_1367217).sum := by decide
  have hdescent : baseEnd_1367217 < baseStart_1367217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
